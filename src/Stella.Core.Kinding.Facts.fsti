(**
 * Facts about kinding that the metatheory of typing reads (spec 01
 * §Kinding; design §1.3, §2.3, §4.1).
 *
 *   - A kinded type is locally closed for regions, and every region it
 *     names is in scope. So a region opened with an atom outside the scope
 *     occurs in no type kinded outside it (design §1.3).
 *   - A kinded type mentions only the type variables in scope, so a
 *     substitution fixing them fixes it, and with no kind variable in scope
 *     it is fixed by every kind instantiation.
 *   - Under `prim_wf`, a type built by `Stella.Core.Prim` is kinded exactly
 *     when its parts are.
 *   - A row extension, a row union, a `forall` and a constrained type are
 *     kinded exactly when their parts are.
 *   - Kinding does not read the term variables of a context.
 *)
module Stella.Core.Kinding.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Prim
module L = FStar.List.Tot

(** * Local closure and region names *)

(** Every atom of `l` names a region in scope in `g`. *)
let in_rdom (l: list atom) (g: ctx) : prop = forall (a: atom). L.mem a l ==> L.mem a (rdom g)

val synth_kind_lc (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires Some? (synth_kind sg g t)) (ensures lc_ty t /\ in_rdom (frn_ty t) g)

val check_lc (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg g t k) (ensures lc_ty t /\ in_rdom (frn_ty t) g)

val entry_ok_lc (sg: sig) (g: ctx) (en: entry) (e: elt_kind)
  : Lemma (requires entry_ok sg g en e) (ensures lc_ent_at 0 en /\ in_rdom (frn_ent en) g)

val check_tys_lc (sg: sig) (g: ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ts ks) (ensures lc_tys_at 0 ts /\ in_rdom (frn_tys ts) g)

val constr_ok_lc (sg: sig) (g: ctx) (c: constr)
  : Lemma (requires constr_ok sg g c) (ensures lc_constr_at 0 c /\ in_rdom (frn_constr c) g)

(** A region not in scope occurs in no kinded type. *)
val check_fresh (sg: sig) (g: ctx) (t: typ) (k: kind) (a: atom)
  : Lemma (requires check sg g t k /\ not (L.mem a (rdom g))) (ensures not (L.mem a (frn_ty t)))

(** * Type variables and kind variables in scope *)

(** Every free type variable of `t` is below `n`. *)
let rec tvs_below (n: nat) (t: typ) : Tot bool (decreases t) =
  match t with
  | TVar i -> i < n
  | TCon _ _ | TRowEmpty -> true
  | TApp t1 t2 | TRowUnion t1 t2 -> tvs_below n t1 && tvs_below n t2
  | TForall _ b -> tvs_below (n + 1) b
  | TConstr c b -> tvs_below_constr n c && tvs_below n b
  | TRowExt en r -> tvs_below_ent n en && tvs_below n r

and tvs_below_ent (n: nat) (en: entry) : Tot bool (decreases en) =
  match en with
  | EntTy _ t -> tvs_below n t
  | EntEff _ _ ts -> tvs_below_tys n ts
  | EntRegion _ -> true

and tvs_below_constr (n: nat) (c: constr) : Tot bool (decreases c) =
  match c with
  | CLacks _ t -> tvs_below n t
  | CDisj t1 t2 -> tvs_below n t1 && tvs_below n t2

and tvs_below_tys (n: nat) (ts: list typ) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | t :: ts -> tvs_below n t && tvs_below_tys n ts

(** A kinded type mentions only the type variables in scope. *)
val check_tvs_below (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg g t k) (ensures tvs_below (L.length g.tvars) t)

(** Two substitutions that agree below `n` agree on a type whose free type
    variables are below `n`. *)
val sub_tvs_ext (n: nat) (sigma sigma': tsub) (t: typ)
  : Lemma (requires tvs_below n t /\ (forall (i: nat). i < n ==> sigma i == sigma' i))
          (ensures sub_ty sigma t == sub_ty sigma' t)

(** A substitution that fixes the variables below `n` fixes a type whose
    free type variables are below `n`. *)
val sub_tvs_below (n: nat) (sigma: tsub) (t: typ)
  : Lemma (requires tvs_below n t /\ (forall (i: nat). i < n ==> sigma i == TVar i))
          (ensures sub_ty sigma t == t)

(** Kind instantiation keeps the type variables. *)
val kinst_tvs_below (ks: list kind) (n: nat) (t: typ)
  : Lemma (tvs_below n (kinst_ty ks t) == tvs_below n t)

(** A type kinded with no kind variable in scope is fixed by every kind
    instantiation. *)
val check_kinst_fixed (sg: sig) (g: ctx) (t: typ) (k: kind) (ks: list kind)
  : Lemma (requires g.nk == 0 /\ check sg g t k) (ensures kinst_ty ks t == t)

(** * The types of `Prim` *)

val check_t_fun (sg: sig) (g: ctx) (t1 r t2: typ)
  : Lemma (requires prim_wf sg)
          (ensures check sg g (t_fun t1 r t2) KType <==>
                   check sg g t1 KType /\ check sg g r (KRow EEffect) /\ check sg g t2 KType)

val check_t_record (sg: sig) (g: ctx) (r: typ)
  : Lemma (requires prim_wf sg) (ensures check sg g (t_record r) KType <==> check sg g r (KRow EType))

val check_t_variant (sg: sig) (g: ctx) (r: typ)
  : Lemma (requires prim_wf sg)
          (ensures check sg g (t_variant r) KType <==> check sg g r (KRow EType))

val check_t_unit (sg: sig) (g: ctx) : Lemma (requires prim_wf sg) (ensures check sg g t_unit KType)

val check_t_bool (sg: sig) (g: ctx) : Lemma (requires prim_wf sg) (ensures check sg g t_bool KType)

val check_lit_type (sg: sig) (g: ctx) (c: lit)
  : Lemma (requires prim_wf sg) (ensures check sg g (lit_type c) KType)

(** * Rows and binders *)

(** A key of a `Row Type` element is structural. *)
val key_ok_struct (sg: sig) (g: ctx) (k: key)
  : Lemma (requires key_ok sg g k EType) (ensures struct_key k)

val check_ext (sg: sig) (g: ctx) (en: entry) (r: typ) (e: elt_kind)
  : Lemma (check sg g (TRowExt en r) (KRow e) <==>
           entry_ok sg g en e /\ check sg g r (KRow e) /\ entails (hyps g) (CLacks (ent_key en) r))

(** `( k : τ | ρ ) : Row Type` *)
val check_ext_ty (sg: sig) (g: ctx) (k: key) (t r: typ)
  : Lemma (check sg g (TRowExt (EntTy k t) r) (KRow EType) <==>
           struct_key k /\ check sg g t KType /\ check sg g r (KRow EType) /\
           entails (hyps g) (CLacks k r))

val check_union (sg: sig) (g: ctx) (r1 r2: typ) (e: elt_kind)
  : Lemma (check sg g (TRowUnion r1 r2) (KRow e) <==>
           check sg g r1 (KRow e) /\ check sg g r2 (KRow e) /\ entails (hyps g) (CDisj r1 r2))

val check_forall (sg: sig) (g: ctx) (k: kind) (t: typ)
  : Lemma (check sg g (TForall k t) KType <==>
           kind_wf g.nk k /\ qkind g.nk k /\ check sg (push_tvar g k) t KType)

val check_constr (sg: sig) (g: ctx) (c: constr) (t: typ)
  : Lemma (check sg g (TConstr c t) KType <==> constr_ok sg g c /\ check sg (add_assump g c) t KType)

(** Well-formed quantifiable kinds stay so with more kind variables. *)
val qkinds_wf_mono (n m: nat) (ks: list kind)
  : Lemma (requires n <= m /\ qkinds_wf n ks) (ensures qkinds_wf m ks)

(** * Term variables *)

(** `g` and `g'` agree on everything kinding reads, which is all but their
    term variables. *)
let same_kinding (g g': ctx) : prop =
  g'.nk == g.nk /\ g'.tvars == g.tvars /\ g'.facts == g.facts /\ g'.assumps == g.assumps /\
  g'.regions == g.regions

val same_kinding_ext (g g': ctx)
  : Lemma (requires same_kinding g g') (ensures ctx_ext g g' /\ ctx_ext g' g)

val same_kinding_push_var (g: ctx) (t: typ) : Lemma (same_kinding g (push_var g t))

val same_kinding_push_vars (g: ctx) (ts: list typ) : Lemma (same_kinding g (push_vars g ts))

val check_same_kinding (sg: sig) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires same_kinding g g') (ensures check sg g' t k == check sg g t k)
