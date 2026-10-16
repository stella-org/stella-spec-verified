(**
 * Binder-aware operations on the Core AST for its de Bruijn index sorts
 * (design §1.1, §1.2).
 *
 * Every index sort gets a PARALLEL renaming and, where the sort can be
 * substituted, a PARALLEL substitution, in the style of the σ-calculus (the
 * calculus of explicit substitutions used by Autosubst and PLFA): a renaming
 * or substitution is a function on indices, applied to every free index at
 * once, and lifted explicitly when it passes under a binder.
 *
 *   | sort              | renaming          | substitution        |
 *   | ----------------- | ----------------- | ------------------- |
 *   | type variables    | `ren_ty*` ξ       | `sub_ty*` σ         |
 *   | (types in terms)  | `ren_ty_exp*` ξ   | `sub_ty_exp*` σ     |
 *   | term variables    | `ren_tm*` ξ       | `sub_tm*` σ         |
 *   | join points       | `ren_jp*` ξ       | —                   |
 *
 * with `ξ : ren = nat -> nat` and `σ : tsub = nat -> typ` or
 * `σ : esub = nat -> exp`. Nothing substitutes a join point: the jump rule
 * substitutes terms for a join point's parameters, and moving a join point's
 * body to the jump site is a renaming. Kind instantiation (`kinst_*`)
 * replaces kind variables simultaneously; kinds bind nothing, so it needs no
 * lifting. Region names are locally nameless and live in
 * `Stella.Core.Region`.
 *
 * Every operation is written out as explicit structural recursion over the
 * mutual types, one function per syntactic class (and per list shape), so
 * that it unfolds to the constructor directly: proofs about the operations
 * reason constructor by constructor, which is what Z3 handles best.
 *
 * ## Lifting under binders
 *
 * `upn_ren n ξ` and `upn_tsub n σ` / `upn_esub n σ` lift across `n` binders
 * OF THEIR OWN SORT: the `n` new variables map to themselves and the others
 * are shifted past them (`0 ↦ 0`, `i+1 ↦ ξ i + 1` for `n = 1`). `up_*` is the
 * case `n = 1`. Telescopes (`letrec`, a join point's parameters, a clause's
 * `b̄` and its `x`/`k`) use the `n`-fold form directly.
 *
 * Crossing a binder of ANOTHER sort leaves a renaming alone, since it renames
 * indices of its own sort only. A term substitution, however, carries terms,
 * and a term mentions all three sorts:
 *
 *   - under `m` type binders (`ETyLam`, a clause's `b̄`) it becomes
 *     `tyup_esub m σ = σ >> ren_ty_exp (shift m)`;
 *   - under a join binder (`ELetJoin`) it becomes
 *     `jup_esub σ = σ >> ren_jp (shift 1)`;
 *   - under term binders it is `upn_esub`, as above.
 *
 * (`f >> g` is `fun i -> g (f i)`.)
 *
 * Region binders lift nothing: substitutes are assumed locally closed with
 * respect to regions (design §1.3, §3.1; `Stella.Core.Region.lc_*`).
 *
 * ## The cutoff-style operations
 *
 * The end of the module derives the cutoff-style operations from the
 * parallel ones: `shift_ty c d`, `subst_ty c ss`, `subst1_ty`, and their term
 * counterparts. In particular `τ[ā := τ̄]` for a telescope `ā = a1 … an`
 * (index 0 is the LAST binder, see `Stella.Core.Syntax`) is
 * `subst_ty 0 (L.rev τ̄) τ`, i.e. `sub_ty (list_tsub (L.rev τ̄)) τ`, and an
 * operation's `σ` under `forall b̄` with the effect's `ā` outside
 * (design §3.1, §4.1) is instantiated at `ā` by `subst_ty m (L.rev τ̄) σ`.
 *)
module Stella.Core.Subst
open Stella.Core.Syntax
module L = FStar.List.Tot

(** * Kind instantiation (spec 01 §Kind schemes)

    `kinst_* ks` replaces `KVar i` by `ks[i]`. Indices beyond the vector are
    lowered by `length ks`, which is what instantiating a prenex binder of
    `length ks` variables means; for the closed schemes of `Σ` that case does
    not arise. *)

let rec kinst_kind (ks: list kind) (k: kind) : Tot kind (decreases k) =
  match k with
  | KVar i -> if i < L.length ks then L.index ks i else KVar (i - L.length ks)
  | KType | KEffect | KRow _ -> k
  | KArrow k1 k2 -> KArrow (kinst_kind ks k1) (kinst_kind ks k2)

let rec kinst_kinds (ks: list kind) (kl: list kind) : Tot (list kind) (decreases kl) =
  match kl with
  | [] -> []
  | k :: kl -> kinst_kind ks k :: kinst_kinds ks kl

let rec kinst_ty (ks: list kind) (t: typ) : Tot typ (decreases t) =
  match t with
  | TVar _ | TRowEmpty -> t
  | TCon n kl -> TCon n (kinst_kinds ks kl)
  | TApp t1 t2 -> TApp (kinst_ty ks t1) (kinst_ty ks t2)
  | TForall k t -> TForall (kinst_kind ks k) (kinst_ty ks t)
  | TConstr c t -> TConstr (kinst_constr ks c) (kinst_ty ks t)
  | TRowExt en t -> TRowExt (kinst_ent ks en) (kinst_ty ks t)
  | TRowUnion t1 t2 -> TRowUnion (kinst_ty ks t1) (kinst_ty ks t2)

and kinst_ent (ks: list kind) (en: entry) : Tot entry (decreases en) =
  match en with
  | EntTy k t -> EntTy k (kinst_ty ks t)
  | EntEff s n ts -> EntEff s n (kinst_tys ks ts)
  | EntRegion _ -> en

and kinst_constr (ks: list kind) (c: constr) : Tot constr (decreases c) =
  match c with
  | CLacks k t -> CLacks k (kinst_ty ks t)
  | CDisj t1 t2 -> CDisj (kinst_ty ks t1) (kinst_ty ks t2)

and kinst_tys (ks: list kind) (ts: list typ) : Tot (list typ) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> kinst_ty ks t :: kinst_tys ks ts

let rec kinst_layout (ks: list kind) (l: list (key & typ)) : Tot (list (key & typ)) (decreases l) =
  match l with
  | [] -> []
  | (k, t) :: l -> (k, kinst_ty ks t) :: kinst_layout ks l

(** * Kind instantiation on terms *)

let rec kinst_exp (ks: list kind) (e: exp) : Tot exp (decreases e) =
  match e with
  | EVar _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> e
  | EGlobal n kl -> EGlobal n (kinst_kinds ks kl)
  | ELam t r b -> ELam (kinst_ty ks t) (kinst_ty ks r) (kinst_exp ks b)
  | EApp e1 e2 -> EApp (kinst_exp ks e1) (kinst_exp ks e2)
  | ETyLam k b -> ETyLam (kinst_kind ks k) (kinst_exp ks b)
  | ETyApp b t -> ETyApp (kinst_exp ks b) (kinst_ty ks t)
  | ECLam cn b -> ECLam (kinst_constr ks cn) (kinst_exp ks b)
  | ECApp b -> ECApp (kinst_exp ks b)
  | ELet t e1 e2 -> ELet (kinst_ty ks t) (kinst_exp ks e1) (kinst_exp ks e2)
  | ELetRec bs b -> ELetRec (kinst_binds ks bs) (kinst_exp ks b)
  | ECase es dt -> ECase (kinst_exps ks es) (kinst_dt ks dt)
  | ELetJoin ts t e1 e2 ->
    ELetJoin (kinst_tys ks ts) (kinst_ty ks t) (kinst_exp ks e1) (kinst_exp ks e2)
  | EJump j es -> EJump j (kinst_exps ks es)
  | EExtend k e1 e2 -> EExtend k (kinst_exp ks e1) (kinst_exp ks e2)
  | ESelect k b -> ESelect k (kinst_exp ks b)
  | ERestrict k b -> ERestrict k (kinst_exp ks b)
  | EUpdate k e1 e2 -> EUpdate k (kinst_exp ks e1) (kinst_exp ks e2)
  | EMerge e1 e2 -> EMerge (kinst_exp ks e1) (kinst_exp ks e2)
  | EInject k t b -> EInject k (kinst_ty ks t) (kinst_exp ks b)
  | EWeaken k t b -> EWeaken k (kinst_ty ks t) (kinst_exp ks b)
  | EAbsurd t b -> EAbsurd (kinst_ty ks t) (kinst_exp ks b)
  | EPerform k op ts b -> EPerform k op (kinst_tys ks ts) (kinst_exp ks b)
  | EHandle b h ->
    EHandle (kinst_exp ks b)
      { h_ent = kinst_ent ks h.h_ent;
        h_ret_ty = kinst_ty ks h.h_ret_ty;
        h_ret = kinst_exp ks h.h_ret;
        h_clauses = kinst_cls ks h.h_clauses }
  | EOpenEff t b -> EOpenEff (kinst_ty ks t) (kinst_exp ks b)
  | ERegion l es b -> ERegion (kinst_layout ks l) (kinst_exps ks es) (kinst_exp ks b)
  | EWriteCell r k b -> EWriteCell r k (kinst_exp ks b)
  | ESpine n sp -> ESpine n (kinst_spine ks sp)
  | EMatch th dt -> EMatch (kinst_exps ks th) (kinst_dt ks dt)
  | EOpenEffC t b -> EOpenEffC (kinst_ty ks t) (kinst_exp ks b)
  | EFill a b -> EFill a (kinst_exp ks b)
  | ERegionOpen a th b -> ERegionOpen a (kinst_cells ks th) (kinst_exp ks b)
  | EOpaque w t -> EOpaque w (kinst_ty ks t)

and kinst_exps (ks: list kind) (es: list exp) : Tot (list exp) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> kinst_exp ks e :: kinst_exps ks es

and kinst_binds (ks: list kind) (bs: list (typ & exp)) : Tot (list (typ & exp)) (decreases bs) =
  match bs with
  | [] -> []
  | (t, e) :: bs -> (kinst_ty ks t, kinst_exp ks e) :: kinst_binds ks bs

and kinst_cells (ks: list kind) (th: list (key & exp)) : Tot (list (key & exp)) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> (k, kinst_exp ks e) :: kinst_cells ks th

and kinst_spine (ks: list kind) (sp: list spine_arg) : Tot (list spine_arg) (decreases sp) =
  match sp with
  | [] -> []
  | SKinds kl :: sp -> SKinds (kinst_kinds ks kl) :: kinst_spine ks sp
  | STy t :: sp -> STy (kinst_ty ks t) :: kinst_spine ks sp
  | SConstr :: sp -> SConstr :: kinst_spine ks sp
  | SVal v :: sp -> SVal (kinst_exp ks v) :: kinst_spine ks sp

and kinst_dt (ks: list kind) (dt: dtree) : Tot dtree (decreases dt) =
  match dt with
  | DLeaf e -> DLeaf (kinst_exp ks e)
  | DBind o dt -> DBind o (kinst_dt ks dt)
  | DSwitchCtor o bs d -> DSwitchCtor o (kinst_brs ks bs) (kinst_odt ks d)
  | DSwitchLit o bs d -> DSwitchLit o (kinst_brs ks bs) (kinst_dt ks d)
  | DSwitchKey o bs d -> DSwitchKey o (kinst_brs ks bs) (kinst_odt ks d)
  | DGuard e dt1 dt2 -> DGuard (kinst_exp ks e) (kinst_dt ks dt1) (kinst_dt ks dt2)

and kinst_odt (ks: list kind) (d: option dtree) : Tot (option dtree) (decreases d) =
  match d with
  | None -> None
  | Some dt -> Some (kinst_dt ks dt)

and kinst_brs (#a: eqtype) (ks: list kind) (bs: list (a & dtree))
  : Tot (list (a & dtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (l, dt) :: bs -> (l, kinst_dt ks dt) :: kinst_brs ks bs

and kinst_cls (ks: list kind) (cs: list clause) : Tot (list clause) (decreases cs) =
  match cs with
  | [] -> []
  | CFull op m s kt b :: cs ->
    CFull op m (kinst_ty ks s) (kinst_ty ks kt) (kinst_exp ks b) :: kinst_cls ks cs
  | CFast op m s b :: cs -> CFast op m (kinst_ty ks s) (kinst_exp ks b) :: kinst_cls ks cs

(** * The σ-calculus primitives *)

(** A renaming of one index sort. *)
type ren = nat -> nat

(** A parallel substitution of types for type variables. *)
type tsub = nat -> typ

(** A parallel substitution of terms for term variables. *)
type esub = nat -> exp

(** The identity renaming. *)
let id_ren (i: nat) : nat = i

(** `↑k`: every index moves up by `k`. *)
let shift (k: nat) (i: nat) : nat = i + k

(** `ξ` lifted across `n` binders of its sort: the `n` innermost indices are
    fixed and the others are renamed by `ξ` above them. *)
let upn_ren (n: nat) (xi: ren) (i: nat) : nat = if i < n then i else xi (i - n) + n

(** `0 ↦ 0`, `i+1 ↦ ξ i + 1`. *)
unfold let up_ren (xi: ren) : ren = upn_ren 1 xi

(** `x .: f`, the environment with `x` at index 0 and `f` above it. *)
let scons (#a: Type) (x: a) (f: nat -> a) (i: nat) : a = if i = 0 then x else f (i - 1)

(** The identity substitutions, `ids` of the σ-calculus. *)
let tvar (i: nat) : typ = TVar i

let evar (i: nat) : exp = EVar i

(** * Types: renaming *)

let rec ren_ty (xi: ren) (t: typ) : Tot typ (decreases t) =
  match t with
  | TCon _ _ | TRowEmpty -> t
  | TVar i -> TVar (xi i)
  | TApp t1 t2 -> TApp (ren_ty xi t1) (ren_ty xi t2)
  | TForall k t -> TForall k (ren_ty (up_ren xi) t)
  | TConstr cn t -> TConstr (ren_constr xi cn) (ren_ty xi t)
  | TRowExt en t -> TRowExt (ren_ent xi en) (ren_ty xi t)
  | TRowUnion t1 t2 -> TRowUnion (ren_ty xi t1) (ren_ty xi t2)

and ren_ent (xi: ren) (en: entry) : Tot entry (decreases en) =
  match en with
  | EntRegion _ -> en
  | EntTy k t -> EntTy k (ren_ty xi t)
  | EntEff s q ts -> EntEff s q (ren_tys xi ts)

and ren_constr (xi: ren) (cn: constr) : Tot constr (decreases cn) =
  match cn with
  | CLacks k t -> CLacks k (ren_ty xi t)
  | CDisj t1 t2 -> CDisj (ren_ty xi t1) (ren_ty xi t2)

and ren_tys (xi: ren) (ts: list typ) : Tot (list typ) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> ren_ty xi t :: ren_tys xi ts

and ren_layout (xi: ren) (l: list (key & typ)) : Tot (list (key & typ)) (decreases l) =
  match l with
  | [] -> []
  | (k, t) :: l -> (k, ren_ty xi t) :: ren_layout xi l

(** `σ` lifted across `n` type binders. *)
let upn_tsub (n: nat) (sigma: tsub) (i: nat) : typ =
  if i < n then TVar i else ren_ty (shift n) (sigma (i - n))

unfold let up_tsub (sigma: tsub) : tsub = upn_tsub 1 sigma

(** * Types: substitution *)

let rec sub_ty (sigma: tsub) (t: typ) : Tot typ (decreases t) =
  match t with
  | TCon _ _ | TRowEmpty -> t
  | TVar i -> sigma i
  | TApp t1 t2 -> TApp (sub_ty sigma t1) (sub_ty sigma t2)
  | TForall k t -> TForall k (sub_ty (up_tsub sigma) t)
  | TConstr cn t -> TConstr (sub_constr sigma cn) (sub_ty sigma t)
  | TRowExt en t -> TRowExt (sub_ent sigma en) (sub_ty sigma t)
  | TRowUnion t1 t2 -> TRowUnion (sub_ty sigma t1) (sub_ty sigma t2)

and sub_ent (sigma: tsub) (en: entry) : Tot entry (decreases en) =
  match en with
  | EntRegion _ -> en
  | EntTy k t -> EntTy k (sub_ty sigma t)
  | EntEff s q ts -> EntEff s q (sub_tys sigma ts)

and sub_constr (sigma: tsub) (cn: constr) : Tot constr (decreases cn) =
  match cn with
  | CLacks k t -> CLacks k (sub_ty sigma t)
  | CDisj t1 t2 -> CDisj (sub_ty sigma t1) (sub_ty sigma t2)

and sub_tys (sigma: tsub) (ts: list typ) : Tot (list typ) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> sub_ty sigma t :: sub_tys sigma ts

and sub_layout (sigma: tsub) (l: list (key & typ)) : Tot (list (key & typ)) (decreases l) =
  match l with
  | [] -> []
  | (k, t) :: l -> (k, sub_ty sigma t) :: sub_layout sigma l

(** * The type sort on terms

    Type binders of terms: `ETyLam` (one) and a clause's `b̄` (`nb`), the
    latter scoping over the clause's annotations as well as its body. No other
    binder of a term changes the type context. *)

let rec ren_ty_exp (xi: ren) (e: exp) : Tot exp (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> e
  | ELam t r b -> ELam (ren_ty xi t) (ren_ty xi r) (ren_ty_exp xi b)
  | EApp e1 e2 -> EApp (ren_ty_exp xi e1) (ren_ty_exp xi e2)
  | ETyLam k b -> ETyLam k (ren_ty_exp (up_ren xi) b)
  | ETyApp b t -> ETyApp (ren_ty_exp xi b) (ren_ty xi t)
  | ECLam cn b -> ECLam (ren_constr xi cn) (ren_ty_exp xi b)
  | ECApp b -> ECApp (ren_ty_exp xi b)
  | ELet t e1 e2 -> ELet (ren_ty xi t) (ren_ty_exp xi e1) (ren_ty_exp xi e2)
  | ELetRec bs b -> ELetRec (ren_ty_binds xi bs) (ren_ty_exp xi b)
  | ECase es dt -> ECase (ren_ty_exps xi es) (ren_ty_dt xi dt)
  | ELetJoin ts t e1 e2 ->
    ELetJoin (ren_tys xi ts) (ren_ty xi t) (ren_ty_exp xi e1) (ren_ty_exp xi e2)
  | EJump j es -> EJump j (ren_ty_exps xi es)
  | EExtend k e1 e2 -> EExtend k (ren_ty_exp xi e1) (ren_ty_exp xi e2)
  | ESelect k b -> ESelect k (ren_ty_exp xi b)
  | ERestrict k b -> ERestrict k (ren_ty_exp xi b)
  | EUpdate k e1 e2 -> EUpdate k (ren_ty_exp xi e1) (ren_ty_exp xi e2)
  | EMerge e1 e2 -> EMerge (ren_ty_exp xi e1) (ren_ty_exp xi e2)
  | EInject k t b -> EInject k (ren_ty xi t) (ren_ty_exp xi b)
  | EWeaken k t b -> EWeaken k (ren_ty xi t) (ren_ty_exp xi b)
  | EAbsurd t b -> EAbsurd (ren_ty xi t) (ren_ty_exp xi b)
  | EPerform k op ts b -> EPerform k op (ren_tys xi ts) (ren_ty_exp xi b)
  | EHandle b h ->
    EHandle (ren_ty_exp xi b)
      { h_ent = ren_ent xi h.h_ent;
        h_ret_ty = ren_ty xi h.h_ret_ty;
        h_ret = ren_ty_exp xi h.h_ret;
        h_clauses = ren_ty_cls xi h.h_clauses }
  | EOpenEff t b -> EOpenEff (ren_ty xi t) (ren_ty_exp xi b)
  | ERegion l es b -> ERegion (ren_layout xi l) (ren_ty_exps xi es) (ren_ty_exp xi b)
  | EWriteCell r k b -> EWriteCell r k (ren_ty_exp xi b)
  | ESpine q sp -> ESpine q (ren_ty_spine xi sp)
  | EMatch th dt -> EMatch (ren_ty_exps xi th) (ren_ty_dt xi dt)
  | EOpenEffC t b -> EOpenEffC (ren_ty xi t) (ren_ty_exp xi b)
  | EFill nu b -> EFill nu (ren_ty_exp xi b)
  | ERegionOpen ell th b -> ERegionOpen ell (ren_ty_cells xi th) (ren_ty_exp xi b)
  | EOpaque w t -> EOpaque w (ren_ty xi t)

and ren_ty_exps (xi: ren) (es: list exp) : Tot (list exp) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> ren_ty_exp xi e :: ren_ty_exps xi es

and ren_ty_binds (xi: ren) (bs: list (typ & exp)) : Tot (list (typ & exp)) (decreases bs) =
  match bs with
  | [] -> []
  | (t, e) :: bs -> (ren_ty xi t, ren_ty_exp xi e) :: ren_ty_binds xi bs

and ren_ty_cells (xi: ren) (th: list (key & exp)) : Tot (list (key & exp)) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> (k, ren_ty_exp xi e) :: ren_ty_cells xi th

and ren_ty_spine (xi: ren) (sp: list spine_arg) : Tot (list spine_arg) (decreases sp) =
  match sp with
  | [] -> []
  | SKinds kl :: sp -> SKinds kl :: ren_ty_spine xi sp
  | STy t :: sp -> STy (ren_ty xi t) :: ren_ty_spine xi sp
  | SConstr :: sp -> SConstr :: ren_ty_spine xi sp
  | SVal v :: sp -> SVal (ren_ty_exp xi v) :: ren_ty_spine xi sp

and ren_ty_dt (xi: ren) (dt: dtree) : Tot dtree (decreases dt) =
  match dt with
  | DLeaf e -> DLeaf (ren_ty_exp xi e)
  | DBind o dt -> DBind o (ren_ty_dt xi dt)
  | DSwitchCtor o bs df -> DSwitchCtor o (ren_ty_brs xi bs) (ren_ty_odt xi df)
  | DSwitchLit o bs df -> DSwitchLit o (ren_ty_brs xi bs) (ren_ty_dt xi df)
  | DSwitchKey o bs df -> DSwitchKey o (ren_ty_brs xi bs) (ren_ty_odt xi df)
  | DGuard e dt1 dt2 -> DGuard (ren_ty_exp xi e) (ren_ty_dt xi dt1) (ren_ty_dt xi dt2)

and ren_ty_odt (xi: ren) (df: option dtree) : Tot (option dtree) (decreases df) =
  match df with
  | None -> None
  | Some dt -> Some (ren_ty_dt xi dt)

and ren_ty_brs (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Tot (list (lb & dtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (l, dt) :: bs -> (l, ren_ty_dt xi dt) :: ren_ty_brs xi bs

and ren_ty_cls (xi: ren) (cs: list clause) : Tot (list clause) (decreases cs) =
  match cs with
  | [] -> []
  | CFull op nb s kt b :: cs ->
    CFull op nb (ren_ty (upn_ren nb xi) s) (ren_ty (upn_ren nb xi) kt)
      (ren_ty_exp (upn_ren nb xi) b)
      :: ren_ty_cls xi cs
  | CFast op nb s b :: cs ->
    CFast op nb (ren_ty (upn_ren nb xi) s) (ren_ty_exp (upn_ren nb xi) b) :: ren_ty_cls xi cs

let rec sub_ty_exp (sigma: tsub) (e: exp) : Tot exp (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> e
  | ELam t r b -> ELam (sub_ty sigma t) (sub_ty sigma r) (sub_ty_exp sigma b)
  | EApp e1 e2 -> EApp (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)
  | ETyLam k b -> ETyLam k (sub_ty_exp (up_tsub sigma) b)
  | ETyApp b t -> ETyApp (sub_ty_exp sigma b) (sub_ty sigma t)
  | ECLam cn b -> ECLam (sub_constr sigma cn) (sub_ty_exp sigma b)
  | ECApp b -> ECApp (sub_ty_exp sigma b)
  | ELet t e1 e2 -> ELet (sub_ty sigma t) (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)
  | ELetRec bs b -> ELetRec (sub_ty_binds sigma bs) (sub_ty_exp sigma b)
  | ECase es dt -> ECase (sub_ty_exps sigma es) (sub_ty_dt sigma dt)
  | ELetJoin ts t e1 e2 ->
    ELetJoin (sub_tys sigma ts) (sub_ty sigma t) (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)
  | EJump j es -> EJump j (sub_ty_exps sigma es)
  | EExtend k e1 e2 -> EExtend k (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)
  | ESelect k b -> ESelect k (sub_ty_exp sigma b)
  | ERestrict k b -> ERestrict k (sub_ty_exp sigma b)
  | EUpdate k e1 e2 -> EUpdate k (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)
  | EMerge e1 e2 -> EMerge (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)
  | EInject k t b -> EInject k (sub_ty sigma t) (sub_ty_exp sigma b)
  | EWeaken k t b -> EWeaken k (sub_ty sigma t) (sub_ty_exp sigma b)
  | EAbsurd t b -> EAbsurd (sub_ty sigma t) (sub_ty_exp sigma b)
  | EPerform k op ts b -> EPerform k op (sub_tys sigma ts) (sub_ty_exp sigma b)
  | EHandle b h ->
    EHandle (sub_ty_exp sigma b)
      { h_ent = sub_ent sigma h.h_ent;
        h_ret_ty = sub_ty sigma h.h_ret_ty;
        h_ret = sub_ty_exp sigma h.h_ret;
        h_clauses = sub_ty_cls sigma h.h_clauses }
  | EOpenEff t b -> EOpenEff (sub_ty sigma t) (sub_ty_exp sigma b)
  | ERegion l es b -> ERegion (sub_layout sigma l) (sub_ty_exps sigma es) (sub_ty_exp sigma b)
  | EWriteCell r k b -> EWriteCell r k (sub_ty_exp sigma b)
  | ESpine q sp -> ESpine q (sub_ty_spine sigma sp)
  | EMatch th dt -> EMatch (sub_ty_exps sigma th) (sub_ty_dt sigma dt)
  | EOpenEffC t b -> EOpenEffC (sub_ty sigma t) (sub_ty_exp sigma b)
  | EFill nu b -> EFill nu (sub_ty_exp sigma b)
  | ERegionOpen ell th b -> ERegionOpen ell (sub_ty_cells sigma th) (sub_ty_exp sigma b)
  | EOpaque w t -> EOpaque w (sub_ty sigma t)

and sub_ty_exps (sigma: tsub) (es: list exp) : Tot (list exp) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> sub_ty_exp sigma e :: sub_ty_exps sigma es

and sub_ty_binds (sigma: tsub) (bs: list (typ & exp)) : Tot (list (typ & exp)) (decreases bs) =
  match bs with
  | [] -> []
  | (t, e) :: bs -> (sub_ty sigma t, sub_ty_exp sigma e) :: sub_ty_binds sigma bs

and sub_ty_cells (sigma: tsub) (th: list (key & exp)) : Tot (list (key & exp)) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> (k, sub_ty_exp sigma e) :: sub_ty_cells sigma th

and sub_ty_spine (sigma: tsub) (sp: list spine_arg) : Tot (list spine_arg) (decreases sp) =
  match sp with
  | [] -> []
  | SKinds kl :: sp -> SKinds kl :: sub_ty_spine sigma sp
  | STy t :: sp -> STy (sub_ty sigma t) :: sub_ty_spine sigma sp
  | SConstr :: sp -> SConstr :: sub_ty_spine sigma sp
  | SVal v :: sp -> SVal (sub_ty_exp sigma v) :: sub_ty_spine sigma sp

and sub_ty_dt (sigma: tsub) (dt: dtree) : Tot dtree (decreases dt) =
  match dt with
  | DLeaf e -> DLeaf (sub_ty_exp sigma e)
  | DBind o dt -> DBind o (sub_ty_dt sigma dt)
  | DSwitchCtor o bs df -> DSwitchCtor o (sub_ty_brs sigma bs) (sub_ty_odt sigma df)
  | DSwitchLit o bs df -> DSwitchLit o (sub_ty_brs sigma bs) (sub_ty_dt sigma df)
  | DSwitchKey o bs df -> DSwitchKey o (sub_ty_brs sigma bs) (sub_ty_odt sigma df)
  | DGuard e dt1 dt2 -> DGuard (sub_ty_exp sigma e) (sub_ty_dt sigma dt1) (sub_ty_dt sigma dt2)

and sub_ty_odt (sigma: tsub) (df: option dtree) : Tot (option dtree) (decreases df) =
  match df with
  | None -> None
  | Some dt -> Some (sub_ty_dt sigma dt)

and sub_ty_brs (#lb: eqtype) (sigma: tsub) (bs: list (lb & dtree))
  : Tot (list (lb & dtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (l, dt) :: bs -> (l, sub_ty_dt sigma dt) :: sub_ty_brs sigma bs

and sub_ty_cls (sigma: tsub) (cs: list clause) : Tot (list clause) (decreases cs) =
  match cs with
  | [] -> []
  | CFull op nb s kt b :: cs ->
    CFull op nb (sub_ty (upn_tsub nb sigma) s) (sub_ty (upn_tsub nb sigma) kt)
      (sub_ty_exp (upn_tsub nb sigma) b)
      :: sub_ty_cls sigma cs
  | CFast op nb s b :: cs ->
    CFast op nb (sub_ty (upn_tsub nb sigma) s) (sub_ty_exp (upn_tsub nb sigma) b)
      :: sub_ty_cls sigma cs

(** * The term sort: renaming

    Term binders: `ELam`, `ELet` (in its body), `ELetRec` (all members, in
    every initializer and in the body), `ELetJoin` (the parameters, in the
    definition only), `DBind`, the handler's return binder, and a clause's
    `x` (and `k` for `full`). Types contain no term variable. *)

let rec ren_tm (xi: ren) (e: exp) : Tot exp (decreases e) =
  match e with
  | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> e
  | EVar i -> EVar (xi i)
  | ELam t r b -> ELam t r (ren_tm (up_ren xi) b)
  | EApp e1 e2 -> EApp (ren_tm xi e1) (ren_tm xi e2)
  | ETyLam k b -> ETyLam k (ren_tm xi b)
  | ETyApp b t -> ETyApp (ren_tm xi b) t
  | ECLam cn b -> ECLam cn (ren_tm xi b)
  | ECApp b -> ECApp (ren_tm xi b)
  | ELet t e1 e2 -> ELet t (ren_tm xi e1) (ren_tm (up_ren xi) e2)
  | ELetRec bs b ->
    ELetRec (ren_tm_binds (upn_ren (L.length bs) xi) bs) (ren_tm (upn_ren (L.length bs) xi) b)
  | ECase es dt -> ECase (ren_tm_exps xi es) (ren_tm_dt xi dt)
  | ELetJoin ts t e1 e2 -> ELetJoin ts t (ren_tm (upn_ren (L.length ts) xi) e1) (ren_tm xi e2)
  | EJump j es -> EJump j (ren_tm_exps xi es)
  | EExtend k e1 e2 -> EExtend k (ren_tm xi e1) (ren_tm xi e2)
  | ESelect k b -> ESelect k (ren_tm xi b)
  | ERestrict k b -> ERestrict k (ren_tm xi b)
  | EUpdate k e1 e2 -> EUpdate k (ren_tm xi e1) (ren_tm xi e2)
  | EMerge e1 e2 -> EMerge (ren_tm xi e1) (ren_tm xi e2)
  | EInject k t b -> EInject k t (ren_tm xi b)
  | EWeaken k t b -> EWeaken k t (ren_tm xi b)
  | EAbsurd t b -> EAbsurd t (ren_tm xi b)
  | EPerform k op ts b -> EPerform k op ts (ren_tm xi b)
  | EHandle b h ->
    EHandle (ren_tm xi b)
      { h_ent = h.h_ent;
        h_ret_ty = h.h_ret_ty;
        h_ret = ren_tm (up_ren xi) h.h_ret;
        h_clauses = ren_tm_cls xi h.h_clauses }
  | EOpenEff t b -> EOpenEff t (ren_tm xi b)
  | ERegion l es b -> ERegion l (ren_tm_exps xi es) (ren_tm xi b)
  | EWriteCell r k b -> EWriteCell r k (ren_tm xi b)
  | ESpine q sp -> ESpine q (ren_tm_spine xi sp)
  | EMatch th dt -> EMatch (ren_tm_exps xi th) (ren_tm_dt xi dt)
  | EOpenEffC t b -> EOpenEffC t (ren_tm xi b)
  | EFill nu b -> EFill nu (ren_tm xi b)
  | ERegionOpen ell th b -> ERegionOpen ell (ren_tm_cells xi th) (ren_tm xi b)

and ren_tm_exps (xi: ren) (es: list exp) : Tot (list exp) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> ren_tm xi e :: ren_tm_exps xi es

and ren_tm_binds (xi: ren) (bs: list (typ & exp)) : Tot (list (typ & exp)) (decreases bs) =
  match bs with
  | [] -> []
  | (t, e) :: bs -> (t, ren_tm xi e) :: ren_tm_binds xi bs

and ren_tm_cells (xi: ren) (th: list (key & exp)) : Tot (list (key & exp)) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> (k, ren_tm xi e) :: ren_tm_cells xi th

and ren_tm_spine (xi: ren) (sp: list spine_arg) : Tot (list spine_arg) (decreases sp) =
  match sp with
  | [] -> []
  | SKinds kl :: sp -> SKinds kl :: ren_tm_spine xi sp
  | STy t :: sp -> STy t :: ren_tm_spine xi sp
  | SConstr :: sp -> SConstr :: ren_tm_spine xi sp
  | SVal v :: sp -> SVal (ren_tm xi v) :: ren_tm_spine xi sp

and ren_tm_dt (xi: ren) (dt: dtree) : Tot dtree (decreases dt) =
  match dt with
  | DLeaf e -> DLeaf (ren_tm xi e)
  | DBind o dt -> DBind o (ren_tm_dt (up_ren xi) dt)
  | DSwitchCtor o bs df -> DSwitchCtor o (ren_tm_brs xi bs) (ren_tm_odt xi df)
  | DSwitchLit o bs df -> DSwitchLit o (ren_tm_brs xi bs) (ren_tm_dt xi df)
  | DSwitchKey o bs df -> DSwitchKey o (ren_tm_brs xi bs) (ren_tm_odt xi df)
  | DGuard e dt1 dt2 -> DGuard (ren_tm xi e) (ren_tm_dt xi dt1) (ren_tm_dt xi dt2)

and ren_tm_odt (xi: ren) (df: option dtree) : Tot (option dtree) (decreases df) =
  match df with
  | None -> None
  | Some dt -> Some (ren_tm_dt xi dt)

and ren_tm_brs (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Tot (list (lb & dtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (l, dt) :: bs -> (l, ren_tm_dt xi dt) :: ren_tm_brs xi bs

and ren_tm_cls (xi: ren) (cs: list clause) : Tot (list clause) (decreases cs) =
  match cs with
  | [] -> []
  | CFull op nb s kt b :: cs -> CFull op nb s kt (ren_tm (upn_ren 2 xi) b) :: ren_tm_cls xi cs
  | CFast op nb s b :: cs -> CFast op nb s (ren_tm (up_ren xi) b) :: ren_tm_cls xi cs

(** * The join sort

    Only `ELetJoin` binds a join point, in both its definition and its body.
    The other binders leave join indices alone; that `λ`, `Λ`, `handle` and a
    region body make every outer join point unreachable is a typing matter
    (spec 04 §Join points; `Stella.Core.Value.jp_scoped`), not a scoping
    one. *)

let rec ren_jp (xi: ren) (e: exp) : Tot exp (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> e
  | ELam t r b -> ELam t r (ren_jp xi b)
  | EApp e1 e2 -> EApp (ren_jp xi e1) (ren_jp xi e2)
  | ETyLam k b -> ETyLam k (ren_jp xi b)
  | ETyApp b t -> ETyApp (ren_jp xi b) t
  | ECLam cn b -> ECLam cn (ren_jp xi b)
  | ECApp b -> ECApp (ren_jp xi b)
  | ELet t e1 e2 -> ELet t (ren_jp xi e1) (ren_jp xi e2)
  | ELetRec bs b -> ELetRec (ren_jp_binds xi bs) (ren_jp xi b)
  | ECase es dt -> ECase (ren_jp_exps xi es) (ren_jp_dt xi dt)
  | ELetJoin ts t e1 e2 -> ELetJoin ts t (ren_jp (up_ren xi) e1) (ren_jp (up_ren xi) e2)
  | EJump j es -> EJump (xi j) (ren_jp_exps xi es)
  | EExtend k e1 e2 -> EExtend k (ren_jp xi e1) (ren_jp xi e2)
  | ESelect k b -> ESelect k (ren_jp xi b)
  | ERestrict k b -> ERestrict k (ren_jp xi b)
  | EUpdate k e1 e2 -> EUpdate k (ren_jp xi e1) (ren_jp xi e2)
  | EMerge e1 e2 -> EMerge (ren_jp xi e1) (ren_jp xi e2)
  | EInject k t b -> EInject k t (ren_jp xi b)
  | EWeaken k t b -> EWeaken k t (ren_jp xi b)
  | EAbsurd t b -> EAbsurd t (ren_jp xi b)
  | EPerform k op ts b -> EPerform k op ts (ren_jp xi b)
  | EHandle b h ->
    EHandle (ren_jp xi b)
      { h_ent = h.h_ent;
        h_ret_ty = h.h_ret_ty;
        h_ret = ren_jp xi h.h_ret;
        h_clauses = ren_jp_cls xi h.h_clauses }
  | EOpenEff t b -> EOpenEff t (ren_jp xi b)
  | ERegion l es b -> ERegion l (ren_jp_exps xi es) (ren_jp xi b)
  | EWriteCell r k b -> EWriteCell r k (ren_jp xi b)
  | ESpine q sp -> ESpine q (ren_jp_spine xi sp)
  | EMatch th dt -> EMatch (ren_jp_exps xi th) (ren_jp_dt xi dt)
  | EOpenEffC t b -> EOpenEffC t (ren_jp xi b)
  | EFill nu b -> EFill nu (ren_jp xi b)
  | ERegionOpen ell th b -> ERegionOpen ell (ren_jp_cells xi th) (ren_jp xi b)

and ren_jp_exps (xi: ren) (es: list exp) : Tot (list exp) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> ren_jp xi e :: ren_jp_exps xi es

and ren_jp_binds (xi: ren) (bs: list (typ & exp)) : Tot (list (typ & exp)) (decreases bs) =
  match bs with
  | [] -> []
  | (t, e) :: bs -> (t, ren_jp xi e) :: ren_jp_binds xi bs

and ren_jp_cells (xi: ren) (th: list (key & exp)) : Tot (list (key & exp)) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> (k, ren_jp xi e) :: ren_jp_cells xi th

and ren_jp_spine (xi: ren) (sp: list spine_arg) : Tot (list spine_arg) (decreases sp) =
  match sp with
  | [] -> []
  | SKinds kl :: sp -> SKinds kl :: ren_jp_spine xi sp
  | STy t :: sp -> STy t :: ren_jp_spine xi sp
  | SConstr :: sp -> SConstr :: ren_jp_spine xi sp
  | SVal v :: sp -> SVal (ren_jp xi v) :: ren_jp_spine xi sp

and ren_jp_dt (xi: ren) (dt: dtree) : Tot dtree (decreases dt) =
  match dt with
  | DLeaf e -> DLeaf (ren_jp xi e)
  | DBind o dt -> DBind o (ren_jp_dt xi dt)
  | DSwitchCtor o bs df -> DSwitchCtor o (ren_jp_brs xi bs) (ren_jp_odt xi df)
  | DSwitchLit o bs df -> DSwitchLit o (ren_jp_brs xi bs) (ren_jp_dt xi df)
  | DSwitchKey o bs df -> DSwitchKey o (ren_jp_brs xi bs) (ren_jp_odt xi df)
  | DGuard e dt1 dt2 -> DGuard (ren_jp xi e) (ren_jp_dt xi dt1) (ren_jp_dt xi dt2)

and ren_jp_odt (xi: ren) (df: option dtree) : Tot (option dtree) (decreases df) =
  match df with
  | None -> None
  | Some dt -> Some (ren_jp_dt xi dt)

and ren_jp_brs (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Tot (list (lb & dtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (l, dt) :: bs -> (l, ren_jp_dt xi dt) :: ren_jp_brs xi bs

and ren_jp_cls (xi: ren) (cs: list clause) : Tot (list clause) (decreases cs) =
  match cs with
  | [] -> []
  | CFull op nb s kt b :: cs -> CFull op nb s kt (ren_jp xi b) :: ren_jp_cls xi cs
  | CFast op nb s b :: cs -> CFast op nb s (ren_jp xi b) :: ren_jp_cls xi cs

(** * The term sort: substitution *)

(** `σ` lifted across `n` term binders. *)
let upn_esub (n: nat) (sigma: esub) (i: nat) : exp =
  if i < n then EVar i else ren_tm (shift n) (sigma (i - n))

unfold let up_esub (sigma: esub) : esub = upn_esub 1 sigma

(** `σ` carried under `m` type binders: its terms are shifted in the type
    sort. *)
let tyup_esub (m: nat) (sigma: esub) (i: nat) : exp = ren_ty_exp (shift m) (sigma i)

(** `σ` carried under one join binder: its terms are shifted in the join
    sort. *)
let jup_esub (sigma: esub) (i: nat) : exp = ren_jp (shift 1) (sigma i)

let rec sub_tm (sigma: esub) (e: exp) : Tot exp (decreases e) =
  match e with
  | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> e
  | EVar i -> sigma i
  | ELam t r b -> ELam t r (sub_tm (up_esub sigma) b)
  | EApp e1 e2 -> EApp (sub_tm sigma e1) (sub_tm sigma e2)
  | ETyLam k b -> ETyLam k (sub_tm (tyup_esub 1 sigma) b)
  | ETyApp b t -> ETyApp (sub_tm sigma b) t
  | ECLam cn b -> ECLam cn (sub_tm sigma b)
  | ECApp b -> ECApp (sub_tm sigma b)
  | ELet t e1 e2 -> ELet t (sub_tm sigma e1) (sub_tm (up_esub sigma) e2)
  | ELetRec bs b ->
    ELetRec (sub_tm_binds (upn_esub (L.length bs) sigma) bs)
      (sub_tm (upn_esub (L.length bs) sigma) b)
  | ECase es dt -> ECase (sub_tm_exps sigma es) (sub_tm_dt sigma dt)
  | ELetJoin ts t e1 e2 ->
    ELetJoin ts t (sub_tm (upn_esub (L.length ts) (jup_esub sigma)) e1) (sub_tm (jup_esub sigma) e2)
  | EJump j es -> EJump j (sub_tm_exps sigma es)
  | EExtend k e1 e2 -> EExtend k (sub_tm sigma e1) (sub_tm sigma e2)
  | ESelect k b -> ESelect k (sub_tm sigma b)
  | ERestrict k b -> ERestrict k (sub_tm sigma b)
  | EUpdate k e1 e2 -> EUpdate k (sub_tm sigma e1) (sub_tm sigma e2)
  | EMerge e1 e2 -> EMerge (sub_tm sigma e1) (sub_tm sigma e2)
  | EInject k t b -> EInject k t (sub_tm sigma b)
  | EWeaken k t b -> EWeaken k t (sub_tm sigma b)
  | EAbsurd t b -> EAbsurd t (sub_tm sigma b)
  | EPerform k op ts b -> EPerform k op ts (sub_tm sigma b)
  | EHandle b h ->
    EHandle (sub_tm sigma b)
      { h_ent = h.h_ent;
        h_ret_ty = h.h_ret_ty;
        h_ret = sub_tm (up_esub sigma) h.h_ret;
        h_clauses = sub_tm_cls sigma h.h_clauses }
  | EOpenEff t b -> EOpenEff t (sub_tm sigma b)
  | ERegion l es b -> ERegion l (sub_tm_exps sigma es) (sub_tm sigma b)
  | EWriteCell r k b -> EWriteCell r k (sub_tm sigma b)
  | ESpine q sp -> ESpine q (sub_tm_spine sigma sp)
  | EMatch th dt -> EMatch (sub_tm_exps sigma th) (sub_tm_dt sigma dt)
  | EOpenEffC t b -> EOpenEffC t (sub_tm sigma b)
  | EFill nu b -> EFill nu (sub_tm sigma b)
  | ERegionOpen ell th b -> ERegionOpen ell (sub_tm_cells sigma th) (sub_tm sigma b)

and sub_tm_exps (sigma: esub) (es: list exp) : Tot (list exp) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> sub_tm sigma e :: sub_tm_exps sigma es

and sub_tm_binds (sigma: esub) (bs: list (typ & exp)) : Tot (list (typ & exp)) (decreases bs) =
  match bs with
  | [] -> []
  | (t, e) :: bs -> (t, sub_tm sigma e) :: sub_tm_binds sigma bs

and sub_tm_cells (sigma: esub) (th: list (key & exp)) : Tot (list (key & exp)) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> (k, sub_tm sigma e) :: sub_tm_cells sigma th

and sub_tm_spine (sigma: esub) (sp: list spine_arg) : Tot (list spine_arg) (decreases sp) =
  match sp with
  | [] -> []
  | SKinds kl :: sp -> SKinds kl :: sub_tm_spine sigma sp
  | STy t :: sp -> STy t :: sub_tm_spine sigma sp
  | SConstr :: sp -> SConstr :: sub_tm_spine sigma sp
  | SVal v :: sp -> SVal (sub_tm sigma v) :: sub_tm_spine sigma sp

and sub_tm_dt (sigma: esub) (dt: dtree) : Tot dtree (decreases dt) =
  match dt with
  | DLeaf e -> DLeaf (sub_tm sigma e)
  | DBind o dt -> DBind o (sub_tm_dt (up_esub sigma) dt)
  | DSwitchCtor o bs df -> DSwitchCtor o (sub_tm_brs sigma bs) (sub_tm_odt sigma df)
  | DSwitchLit o bs df -> DSwitchLit o (sub_tm_brs sigma bs) (sub_tm_dt sigma df)
  | DSwitchKey o bs df -> DSwitchKey o (sub_tm_brs sigma bs) (sub_tm_odt sigma df)
  | DGuard e dt1 dt2 -> DGuard (sub_tm sigma e) (sub_tm_dt sigma dt1) (sub_tm_dt sigma dt2)

and sub_tm_odt (sigma: esub) (df: option dtree) : Tot (option dtree) (decreases df) =
  match df with
  | None -> None
  | Some dt -> Some (sub_tm_dt sigma dt)

and sub_tm_brs (#lb: eqtype) (sigma: esub) (bs: list (lb & dtree))
  : Tot (list (lb & dtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (l, dt) :: bs -> (l, sub_tm_dt sigma dt) :: sub_tm_brs sigma bs

and sub_tm_cls (sigma: esub) (cs: list clause) : Tot (list clause) (decreases cs) =
  match cs with
  | [] -> []
  | CFull op nb s kt b :: cs ->
    CFull op nb s kt (sub_tm (upn_esub 2 (tyup_esub nb sigma)) b) :: sub_tm_cls sigma cs
  | CFast op nb s b :: cs ->
    CFast op nb s (sub_tm (up_esub (tyup_esub nb sigma)) b) :: sub_tm_cls sigma cs

(** * Lengths

    `letrec` and `letjoin` bind as many term variables as they have members
    or parameters, so an operation that rewrites the member list or the
    parameter types must keep their number. These facts carry SMT patterns,
    so every proof that depends on this module uses them automatically. *)

val ren_tys_length (xi: ren) (l: list typ)
  : Lemma (ensures L.length (ren_tys xi l) == L.length l)
          [SMTPat (L.length (ren_tys xi l))]

val sub_tys_length (sigma: tsub) (l: list typ)
  : Lemma (ensures L.length (sub_tys sigma l) == L.length l)
          [SMTPat (L.length (sub_tys sigma l))]

val ren_ty_binds_length (xi: ren) (l: list (typ & exp))
  : Lemma (ensures L.length (ren_ty_binds xi l) == L.length l)
          [SMTPat (L.length (ren_ty_binds xi l))]

val sub_ty_binds_length (sigma: tsub) (l: list (typ & exp))
  : Lemma (ensures L.length (sub_ty_binds sigma l) == L.length l)
          [SMTPat (L.length (sub_ty_binds sigma l))]

val ren_tm_binds_length (xi: ren) (l: list (typ & exp))
  : Lemma (ensures L.length (ren_tm_binds xi l) == L.length l)
          [SMTPat (L.length (ren_tm_binds xi l))]

val ren_jp_binds_length (xi: ren) (l: list (typ & exp))
  : Lemma (ensures L.length (ren_jp_binds xi l) == L.length l)
          [SMTPat (L.length (ren_jp_binds xi l))]

val sub_tm_binds_length (sigma: esub) (l: list (typ & exp))
  : Lemma (ensures L.length (sub_tm_binds sigma l) == L.length l)
          [SMTPat (L.length (sub_tm_binds sigma l))]

(** * The cutoff-style operations

    Shift above a cutoff and simultaneous substitution of a list, defined
    through the parallel operations. `shift_from c d` moves every index
    `>= c` up by `d`. *)

let shift_from (c d: nat) : ren = upn_ren c (shift d)

(** `ss` as a substitution: `ss[i]` at index `i < |ss|`, the indices above
    lowered by `|ss|` (the substituted variables leave the context). *)
let list_tsub (ss: list typ) (i: nat) : typ =
  if i < L.length ss then L.index ss i else TVar (i - L.length ss)

let list_esub (vs: list exp) (i: nat) : exp =
  if i < L.length vs then L.index vs i else EVar (i - L.length vs)

(** `shift_ty c d`: indices `>= c` up by `d`. *)
let shift_ty (c d: nat) (t: typ) : typ = ren_ty (shift_from c d) t

(** `subst_ty c ss t` replaces the type variables `c … c+n-1` (n = |ss|)
    simultaneously, `TVar (c+i)` by `ss[i]` shifted by `c`, and lowers the
    ones above by `n`. *)
let subst_ty (c: nat) (ss: list typ) (t: typ) : typ = sub_ty (upn_tsub c (list_tsub ss)) t

(** `τ[a := σ]` for the body `τ` of `forall (a : κ). τ`. *)
let subst1_ty (s: typ) (t: typ) : typ = sub_ty (scons s tvar) t

let shift_ty_exp (c d: nat) (e: exp) : exp = ren_ty_exp (shift_from c d) e

let subst_ty_exp (c: nat) (ss: list typ) (e: exp) : exp =
  sub_ty_exp (upn_tsub c (list_tsub ss)) e

(** `v[a := σ]` for the body `v` of `Λ (a : κ). v` (spec 06 §Ordinary
    reduction). *)
let subst1_ty_exp (s: typ) (e: exp) : exp = sub_ty_exp (scons s tvar) e

let shift_tm (c d: nat) (e: exp) : exp = ren_tm (shift_from c d) e

(** `subst_tm c vs e` replaces the term variables `c … c+n-1` (n = |vs|) by
    `vs`, shifted by `c` term binders, and lowers the ones above. Under
    binders of the other sorts the substitution lifts itself (`tyup_esub`,
    `jup_esub`). *)
let subst_tm (c: nat) (vs: list exp) (e: exp) : exp = sub_tm (upn_esub c (list_esub vs)) e

(** `e[x := v]` for the body `e` of a single term binder (`λ`, `let`,
    `bind`, the return clause): spec 06 §Ordinary reduction. *)
let subst1_tm (v: exp) (e: exp) : exp = sub_tm (scons v evar) e

let shift_jp (c d: nat) (e: exp) : exp = ren_jp (shift_from c d) e
