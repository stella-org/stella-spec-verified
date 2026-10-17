(**
 * Kinds, keys, row elements, constraints, and the kinding of types
 * (spec 01 §Kinds, §Kinding).
 *
 * Every judgement is a total boolean function (design §2.3). Kinding is
 * bidirectional, because `()` has every row kind and so no unique kind:
 *
 *   - `synth_kind sg g τ` computes the kind of a variable, a constructor, an
 *     application, a `forall`, and a constrained type;
 *   - `check sg g τ κ` checks the row formers against a row kind, and any
 *     other type by comparing its synthesized kind with `κ`.
 *
 * ## Ex falso
 *
 * Entailment is consulted in exactly two places, the sharpness premises of
 * row extension and row union. An inconsistent context entails every
 * constraint (design §2.2 item 4), so only these two premises become
 * trivially true there. Every structural check (the scope of an index, the
 * kind of an application, a lookup in `Σ`, the class of a key) is made
 * whatever the context's assumptions are.
 *)
module Stella.Core.Kinding
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Context
module L = FStar.List.Tot

(** * Kinds (spec 01 §Kinds) *)

(** `Γ ⊢ κ kind`, with `nk` kind variables in scope. A row kind takes only
    a row element kind, so `KRow` needs no condition. *)
let rec kind_wf (nk: nat) (k: kind) : Tot bool (decreases k) =
  match k with
  | KVar i -> i < nk
  | KType | KEffect | KRow _ -> true
  | KArrow k1 k2 -> kind_wf nk k1 && kind_wf nk k2

(** What a kind produces once it is fully applied. *)
let rec result (k: kind) : Tot kind (decreases k) =
  match k with
  | KArrow _ k2 -> result k2
  | _ -> k

(** `Γ ⊢ κ qkind`: the kinds that may be quantified over. `Effect` is not
    one (D24), and an arrow must produce `Type`, so that only row syntax
    and row variables have a row kind. *)
let rec qkind (nk: nat) (k: kind) : Tot bool (decreases k) =
  match k with
  | KVar i -> i < nk
  | KType | KRow _ -> true
  | KEffect -> false
  | KArrow q1 q2 -> qkind nk q1 && qkind nk q2 && result q2 = KType

val qkind_kind_wf (nk: nat) (k: kind) : Lemma (requires qkind nk k) (ensures kind_wf nk k)

(** Every kind of `ks` is a well-formed quantifiable kind. *)
let rec qkinds_wf (nk: nat) (ks: list kind) : Tot bool (decreases ks) =
  match ks with
  | [] -> true
  | k :: ks -> kind_wf nk k && qkind nk k && qkinds_wf nk ks

(** * Keys (spec 01 §Constraint well-formedness) *)

(** The structural keys. *)
let struct_key (k: key) : bool = SymbolKey? k || TagKey? k || PositionKey? k

(** `Γ ⊢ k key ε` *)
let key_ok (sg: sig) (g: ctx) (k: key) (e: elt_kind) : bool =
  match k, e with
  | SymbolKey _, _ -> true
  | TagKey _, EType | PositionKey _, EType -> true
  | EffectKey q, EEffect -> Some? (sg.effects q)
  | RegionKey (RFree a), EEffect -> L.mem a (rdom g)
  | _ -> false

(** * Types (spec 01 §Kinding, §Row elements, §Constraint well-formedness)

    Recursion is structural. The measures `%[τ; 0]` of `synth_kind` and
    `%[τ; 1]` of `check` let `check τ` defer to `synth_kind τ` on the same
    type; every other call is on a proper subterm. *)

(** `Γ ⊢ τ : κ`, synthesizing `κ`. The row formers synthesize nothing. *)
let rec synth_kind (sg: sig) (g: ctx) (t: typ) : Tot (option kind) (decreases %[t; 0]) =
  match t with
  | TVar i -> L.nth g.tvars i
  | TCon q ks ->
    (match sg.tycons q with
     | Some ti ->
       if L.length ks = ti.tc_nk && qkinds_wf g.nk ks then Some (kinst_kind ks ti.tc_kind)
       else None
     | None -> None)
  | TApp t1 t2 ->
    (match synth_kind sg g t1 with
     | Some (KArrow k1 k2) -> if check sg g t2 k1 then Some k2 else None
     | _ -> None)
  | TForall k t1 ->
    if kind_wf g.nk k && qkind g.nk k && check sg (push_tvar g k) t1 KType then Some KType
    else None
  | TConstr c t1 ->
    if constr_ok sg g c && check sg (add_assump g c) t1 KType then Some KType else None
  | TRowEmpty | TRowExt _ _ | TRowUnion _ _ -> None

(** `Γ ⊢ τ : κ`, checking against `κ`. *)
and check (sg: sig) (g: ctx) (t: typ) (k: kind) : Tot bool (decreases %[t; 1]) =
  match t with
  | TRowEmpty -> KRow? k
  | TRowExt en r ->
    (match k with
     | KRow e ->
       entry_ok sg g en e && check sg g r k && entails (hyps g) (CLacks (ent_key en) r)
     | _ -> false)
  | TRowUnion r1 r2 ->
    KRow? k && check sg g r1 k && check sg g r2 k && entails (hyps g) (CDisj r1 r2)
  | _ -> synth_kind sg g t = Some k

(** `Γ ⊢ ent : ε entry`. A region element names a region in scope; an
    `RBound` reference is never in scope, since a type is kinded only after
    its region binders are opened (design §1.3). *)
and entry_ok (sg: sig) (g: ctx) (en: entry) (e: elt_kind) : Tot bool (decreases en) =
  match en with
  | EntTy k t -> e = EType && struct_key k && check sg g t KType
  | EntEff _ q ts ->
    e = EEffect &&
    (match sg.effects q with
     | Some ei -> check_tys sg g ts ei.eff_params
     | None -> false)
  | EntRegion (RFree a) -> e = EEffect && L.mem a (rdom g)
  | EntRegion (RBound _) -> false

(** `Γ ⊢ τ̄ : κ̄`, the lengths agreeing. *)
and check_tys (sg: sig) (g: ctx) (ts: list typ) (ks: list kind)
  : Tot bool (decreases ts) =
  match ts, ks with
  | [], [] -> true
  | t :: ts, k :: ks -> check sg g t k && check_tys sg g ts ks
  | _ -> false

(** `Γ ⊢ C ok`, at either row element kind. *)
and constr_ok (sg: sig) (g: ctx) (c: constr) : Tot bool (decreases c) =
  match c with
  | CLacks k r ->
    (check sg g r (KRow EType) && key_ok sg g k EType) ||
    (check sg g r (KRow EEffect) && key_ok sg g k EEffect)
  | CDisj r1 r2 ->
    (check sg g r1 (KRow EType) && check sg g r2 (KRow EType)) ||
    (check sg g r1 (KRow EEffect) && check sg g r2 (KRow EEffect))

(** * Well-formed parts of a context *)

(** Every type variable has a well-formed quantifiable kind. *)
let tvars_wf (g: ctx) : bool = qkinds_wf g.nk g.tvars

let rec constrs_ok (sg: sig) (g: ctx) (cs: list constr) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: cs -> constr_ok sg g c && constrs_ok sg g cs

(** Every fact and every assumption is well formed. *)
let wf_hyps (sg: sig) (g: ctx) : bool = constrs_ok sg g (hyps g)
