(**
 * Values, the scoping discipline of join points, and the fact the rule
 * `letjoin j (x̄ : τ̄) : τ = e1 in v  →  v` (spec 06 §Join points) needs.
 *
 * ## Join-point scoping
 *
 * `jp_scoped n e` holds when every `jump` of `e` targets a join point of the
 * join context `Δ` it tracks at that `jump`, `n` being the size of `Δ` at
 * `e`'s root (design §4.3). `letjoin` extends `Δ` in both its definition
 * and its body, `Δ` is discarded (reset to size 0) at the boundaries
 *
 *   - the body of `λ`, `Λ (a : κ)` and `Λ (_ : C)`;
 *   - the handled computation, the return clause and every operation
 *     clause of `handle`;
 *   - the body of `region` (not its initial values);
 *   - every initializer of `letrec` (not its body);
 *   - the subterm of `fill ν e`, and the cells and body of `region⟨ℓ⟩`,
 *
 * and every other position keeps the `Δ` of the form above it.
 *
 * `jp_scoped` over-approximates the typing rules (spec 04 §Join points,
 * spec 05 §Basic rules, spec 06 §Run-time forms; `Stella.Core.Typing`).
 * The rules empty `Δ` at the boundaries and also at every non-tail
 * position, such as both sides of an application, the bound side of `let`,
 * the scrutinees of `case` and the arguments of `jump`, where `jp_scoped`
 * keeps it. The `Δ` of the rules at a position is thus a prefix of the one
 * `jp_scoped` tracks there, its innermost join points, and every
 * well-typed term is `jp_scoped |Δ|`. Scoping is a real restriction on
 * syntax: a `λ` body may syntactically mention a join index bound outside
 * the `λ`, and only the discarding of `Δ` rules that out.
 *
 * ## The join-point value lemma
 *
 * In `ELetJoin ts t e1 v`, `v` stands under the join binder, and the
 * reduct must drop that binder. A value only contains join indices inside a
 * `Δ`-discarding body, so a `jp_scoped` value has no free join index at all
 * (`value_jp_scoped`), and every join renaming fixes it (`value_ren_jp`).
 * In particular the downward renaming `jp_down` fixes it, so the reduct of
 * the rule is `v` itself.
 *
 * A family over terms is a mutual induction over all term classes; the
 * interface exports its instances at `exp` and `dtree`.
 *)
module Stella.Core.Value
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
module L = FStar.List.Tot

(** * Join-point scoping *)

let rec jp_scoped (n: nat) (e: exp) : Tot bool (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> true
  | ELam _ _ b -> jp_scoped 0 b
  | EApp e1 e2 -> jp_scoped n e1 && jp_scoped n e2
  | ETyLam _ b -> jp_scoped 0 b
  | ETyApp b _ -> jp_scoped n b
  | ECLam _ b -> jp_scoped 0 b
  | ECApp b -> jp_scoped n b
  | ELet _ e1 e2 -> jp_scoped n e1 && jp_scoped n e2
  | ELetRec bs b -> jp_scoped_binds 0 bs && jp_scoped n b
  | ECase es dt -> jp_scoped_exps n es && jp_scoped_dt n dt
  | ELetJoin _ _ e1 e2 -> jp_scoped (n + 1) e1 && jp_scoped (n + 1) e2
  | EJump j es -> j < n && jp_scoped_exps n es
  | EExtend _ e1 e2 -> jp_scoped n e1 && jp_scoped n e2
  | ESelect _ b -> jp_scoped n b
  | ERestrict _ b -> jp_scoped n b
  | EUpdate _ e1 e2 -> jp_scoped n e1 && jp_scoped n e2
  | EMerge e1 e2 -> jp_scoped n e1 && jp_scoped n e2
  | EInject _ _ b -> jp_scoped n b
  | EWeaken _ _ b -> jp_scoped n b
  | EAbsurd _ b -> jp_scoped n b
  | EPerform _ _ _ b -> jp_scoped n b
  | EHandle b h -> jp_scoped 0 b && jp_scoped 0 h.h_ret && jp_scoped_cls 0 h.h_clauses
  | EOpenEff _ b -> jp_scoped n b
  | ERegion _ es b -> jp_scoped_exps n es && jp_scoped 0 b
  | EWriteCell _ _ b -> jp_scoped n b
  | EMatch th dt -> jp_scoped_exps n th && jp_scoped_dt n dt
  | EOpenEffC _ b -> jp_scoped n b
  | EFill _ b -> jp_scoped 0 b
  | ERegionOpen _ th b -> jp_scoped_cells 0 th && jp_scoped 0 b

and jp_scoped_exps (n: nat) (es: list exp) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> jp_scoped n e && jp_scoped_exps n es

and jp_scoped_binds (n: nat) (bs: list (typ & exp)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, e) :: bs -> jp_scoped n e && jp_scoped_binds n bs

and jp_scoped_cells (n: nat) (th: list (key & exp)) : Tot bool (decreases th) =
  match th with
  | [] -> true
  | (_, e) :: th -> jp_scoped n e && jp_scoped_cells n th

and jp_scoped_dt (n: nat) (dt: dtree) : Tot bool (decreases dt) =
  match dt with
  | DLeaf e -> jp_scoped n e
  | DBind _ dt -> jp_scoped_dt n dt
  | DSwitchCtor _ bs df -> jp_scoped_brs n bs && jp_scoped_odt n df
  | DSwitchLit _ bs df -> jp_scoped_brs n bs && jp_scoped_dt n df
  | DSwitchKey _ bs df -> jp_scoped_brs n bs && jp_scoped_odt n df
  | DGuard e dt1 dt2 -> jp_scoped n e && jp_scoped_dt n dt1 && jp_scoped_dt n dt2

and jp_scoped_odt (n: nat) (df: option dtree) : Tot bool (decreases df) =
  match df with
  | None -> true
  | Some dt -> jp_scoped_dt n dt

and jp_scoped_brs (#lb: eqtype) (n: nat) (bs: list (lb & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, dt) :: bs -> jp_scoped_dt n dt && jp_scoped_brs n bs

and jp_scoped_cls (n: nat) (cs: list clause) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | CFull _ _ _ _ b :: cs -> jp_scoped n b && jp_scoped_cls n cs
  | CFast _ _ _ b :: cs -> jp_scoped n b && jp_scoped_cls n cs

val jp_scoped_mono (n: nat) (m: nat) (e: exp)
  : Lemma (requires n <= m /\ jp_scoped n e)
          (ensures jp_scoped m e)

val jp_scoped_mono_dt (n: nat) (m: nat) (dt: dtree)
  : Lemma (requires n <= m /\ jp_scoped_dt n dt)
          (ensures jp_scoped_dt m dt)

(** A join renaming that fixes the `n` join points in scope fixes the
    term. *)
val ren_jp_scoped (n: nat) (xi: ren) (e: exp)
  : Lemma (requires jp_scoped n e /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp xi e == e)

val ren_jp_scoped_dt (n: nat) (xi: ren) (dt: dtree)
  : Lemma (requires jp_scoped_dt n dt /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp_dt xi dt == dt)

(** * Scoping under renaming and substitution

    Term renamings and type substitutions leave join indices alone, so they
    preserve scoping exactly. A join renaming preserves it when it maps the
    `n` join points in scope into `m` (`jp_scoped_ren_jp`, the join-context
    weakening).

    A term substitution preserves scoping when every substitute is
    `jp_scoped 0`, i.e. mentions no free join index. Scoping under the
    ambient `n` is not enough: a substitute can land under a `λ`, where the
    join context is empty, and `EVar 0` under `λ` with `σ 0 = EJump 0 []`
    turns a scoped term into an unscoped one. The values that reduction
    substitutes satisfy the hypothesis (`jp_scoped_subst1_value`). *)

val jp_scoped_ren_tm (n: nat) (xi: ren) (e: exp)
  : Lemma (ensures jp_scoped n (ren_tm xi e) == jp_scoped n e)

val jp_scoped_ren_tm_dt (n: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures jp_scoped_dt n (ren_tm_dt xi dt) == jp_scoped_dt n dt)

val jp_scoped_sub_ty (n: nat) (sigma: tsub) (e: exp)
  : Lemma (ensures jp_scoped n (sub_ty_exp sigma e) == jp_scoped n e)

val jp_scoped_sub_ty_dt (n: nat) (sigma: tsub) (dt: dtree)
  : Lemma (ensures jp_scoped_dt n (sub_ty_dt sigma dt) == jp_scoped_dt n dt)

val jp_scoped_ren_ty_exp (n: nat) (xi: ren) (e: exp)
  : Lemma (jp_scoped n (ren_ty_exp xi e) == jp_scoped n e)

val jp_scoped_ren_jp (n: nat) (m: nat) (xi: ren) (e: exp)
  : Lemma (requires jp_scoped n e /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped m (ren_jp xi e))

val jp_scoped_ren_jp_dt (n: nat) (m: nat) (xi: ren) (dt: dtree)
  : Lemma (requires jp_scoped_dt n dt /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped_dt m (ren_jp_dt xi dt))

val jp_scoped_sub_tm (n: nat) (sigma: esub) (e: exp)
  : Lemma (requires jp_scoped n e /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped n (sub_tm sigma e))

val jp_scoped_sub_tm_dt (n: nat) (sigma: esub) (dt: dtree)
  : Lemma (requires jp_scoped_dt n dt /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped_dt n (sub_tm_dt sigma dt))

(** * Values (spec 06 §Values)

    `is_value sg e` is the value grammar of spec 06 §Values:

      v ::= c | λ (x : τ) / ρ . e | Λ (a : κ). v | Λ (_ : C). v
          | M.Ctor [[κ̄]] ᾱ | M.f [[κ̄]] ᾱ  (not saturated)
          | {} | extend k v1 v2 | inject k [ρ] v | weaken k [τ] v
          | openEff [ρ] v | opaque ω [τ]

    where `M.g [[κ̄]] ᾱ` is a global application chain (design §3,
    `decompose_global_app`) whose value arguments are all values
    (`chain_values`). Whether its head makes it a value depends on `Σ`
    (`value_head`):

      - a chain headed by a data constructor is a value, saturated or not.
        A constructor's arrows are pure and its result is a data type, never
        an arrow, so an over-applied constructor chain is ill-typed and
        needs no case of its own;
      - a chain headed by a foreign is a value while it is not saturated
        (`spine_unsaturated`, which requires the cursor to be defined). A
        saturated one is a redex (`foreign_redex`).

    The atomic reference `M.g [[κ̄]]` is the chain with no argument. A
    global with a body to unfold, a top-level value, heads no value. *)

let value_head (sg: sig) (e: exp) : bool =
  match decompose_global_app e with
  | Some (q, ks, args) ->
    (match global_scheme sg q with
     | Some (GCtor, _, _) -> true
     | Some (GForeign, _, _) -> spine_unsaturated sg q ks args
     | None -> false)
  | None -> false

let rec is_value (sg: sig) (e: exp) : Tot bool (decreases %[e; 1]) =
  match e with
  | ELit _ | ELam _ _ _ | ERecEmpty | EOpaque _ _ -> true
  | ETyLam _ v | ECLam _ v | EInject _ _ v | EWeaken _ _ v | EOpenEff _ v -> is_value sg v
  | EExtend _ v1 v2 -> is_value sg v1 && is_value sg v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> value_head sg e && chain_values sg e
  | _ -> false

(** `e` is a global application chain and each of its value arguments is a
    value. *)
and chain_values (sg: sig) (e: exp) : Tot bool (decreases %[e; 0]) =
  match e with
  | EGlobal _ _ -> true
  | EApp f v -> chain_values sg f && is_value sg v
  | ETyApp f _ | ECApp f -> chain_values sg f
  | _ -> false

(** Each value argument among the arguments of a chain is a value. *)
let rec args_values (sg: sig) (args: list spine_arg) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | SVal v :: args -> is_value sg v && args_values sg args
  | _ :: args -> args_values sg args

(** `chain_values` read through the view. *)
val chain_values_view (sg: sig) (e: exp)
  : Lemma (chain_values sg e ==
           (match decompose_global_app e with
            | Some (_, _, args) -> args_values sg args
            | None -> false))

(** `M.f [[κ̄]] ᾱ`, a saturated chain of the foreign `M.f` whose every value
    argument is a value: the redex of `M.f [[κ̄]] ᾱ → δ_f(values(ᾱ))` (spec 06
    §Chains of a constructor or a foreign). *)
let foreign_redex (sg: sig) (e: exp) : bool =
  match decompose_global_app e with
  | Some (q, ks, args) ->
    (match global_scheme sg q with
     | Some (GForeign, _, _) -> spine_saturated sg q ks args && chain_values sg e
     | _ -> false)
  | None -> false

(** A foreign redex is no value. *)
val foreign_redex_not_value (sg: sig) (e: exp)
  : Lemma (requires foreign_redex sg e) (ensures not (is_value sg e))

(** * The join-point value lemma *)

(** A scoped value is scoped under every join context: its join indices
    all stand under a `Δ`-discarding body. *)
val value_jp_scoped (sg: sig) (n: nat) (v: exp)
  : Lemma (requires is_value sg v /\ jp_scoped n v) (ensures jp_scoped 0 v)

(** Hence it is scoped under any `m` join points. *)
val value_jp_scoped_any (sg: sig) (n m: nat) (v: exp)
  : Lemma (requires is_value sg v /\ jp_scoped n v) (ensures jp_scoped m v)

(** A scoped value has no free join index: every join renaming fixes it. *)
val value_ren_jp (sg: sig) (n: nat) (xi: ren) (v: exp)
  : Lemma (requires is_value sg v /\ jp_scoped n v) (ensures ren_jp xi v == v)

(** The renaming that removes join index 0 from scope, lowering the others
    (`0` itself is sent to `0`, but no index of a term it is applied to is
    meant to be `0`). *)
let jp_down (j: nat) : nat = if j = 0 then 0 else j - 1

(** `letjoin j (x̄ : τ̄) : τ = e1 in v  →  v`: the value `v`, under the join
    binder, stands for itself outside it. *)
val letjoin_value (sg: sig) (n: nat) (v: exp)
  : Lemma (requires is_value sg v /\ jp_scoped (n + 1) v) (ensures ren_jp jp_down v == v)

(** A β-step, `let` or `bind` substitutes a value, which keeps the
    result scoped: `e[x := v]` is `jp_scoped n` when `e` is. *)
val jp_scoped_subst1_value (sg: sig) (n k: nat) (v e: exp)
  : Lemma (requires jp_scoped n e /\ is_value sg v /\ jp_scoped k v)
          (ensures jp_scoped n (subst1_tm v e))
