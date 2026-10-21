(**
 * Generation lemmas: inverting a derivation of a value form (design §2,
 * §4.2; spec 05).
 *
 * Each value form inverted here has one rule of its own: `T_Lam`, `T_TyLam`,
 * `T_CLam`, `T_RecEmpty` and `T_Extend`, and for a variant value `T_Inject`
 * and `T_Weaken`, besides `T_VariantValue`. A derivation of such a form is
 * one of these rules under a stack of conversions. A global application
 * chain has several derivations, by `T_Chain` and by the nodes `T_Global`,
 * `T_App`, `T_TyApp` and `T_CApp`; `Stella.Core.Typing.Chain` inverts it.
 *
 *   - Type equality is injective on the non-row type formers: two
 *     applications, two constructors, two quantifiers or two constrained
 *     types are equal exactly when their components are (`ty_eq_app`, …),
 *     and so are two function, record or variant types.
 *   - The conversions at the bottom of a derivation compose into one,
 *     since `ty_eq` is an equality of canonical forms: every derivation is
 *     a derivation whose last rule is not `T_Conv`, at an equal type and an
 *     equal row (`strip_conv`).
 *   - A derivation of a λ, a `Λ`, a constraint `Λ`, a record or a variant
 *     value at a type equal to one of the matching shape gives the
 *     premises of the form's rule, and the type equalities between the
 *     components of the two types (`inv_lam`, `inv_tylam`, `inv_clam`,
 *     `inv_rec_empty`, `inv_extend`, `inv_variant`).
 *
 * Each inversion takes a derivation at any type `t` equal to the shape,
 * so it applies under conversions and to a derivation at the shape itself
 * alike. The premise derivations of a record or a variant are returned at
 * the ambient row of the given derivation, converted, which needs the
 * regularity of `Stella.Core.Typing.Regularity` and thus a well-formed `Σ`
 * and `Γ`. The other inversions have no hypothesis.
 *)
module Stella.Core.Typing.Inversion
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot

(** * Injectivity of type equality (design §2)

    `canon` keeps the structure of `TApp`, `TCon`, `TForall` and `TConstr`,
    so type equality between two types with the same one of these outer
    formers is componentwise. There is no such statement for the row
    formers: a row with no entries and a single tail canonicalizes to that
    tail, so `TRowUnion a ()` is equal to `a` whatever `a` is, and a row
    former can equal a type of any other shape. *)

val ty_eq_app (a b a' b': typ)
  : Lemma (ty_eq (TApp a b) (TApp a' b') <==> (ty_eq a a' /\ ty_eq b b'))

val ty_eq_con (q q': qname) (ks ks': list kind)
  : Lemma (ty_eq (TCon q ks) (TCon q' ks') <==> (q == q' /\ ks == ks'))

val ty_eq_forall (k k': kind) (a a': typ)
  : Lemma (ty_eq (TForall k a) (TForall k' a') <==> (k == k' /\ ty_eq a a'))

(** Constraints compare through `canon_constr`, as `constr_eq`. *)
val ty_eq_constr (c c': constr) (a a': typ)
  : Lemma (ty_eq (TConstr c a) (TConstr c' a') <==> (constr_eq c c' /\ ty_eq a a'))

(** `τ1 -{ρ}-> τ2`, for any constructor names `q` and `q'`
    (`Stella.Core.Syntax.fun_ty`). *)
val ty_eq_fun_ty (q q': qname) (t1 r t2 t1' r' t2': typ)
  : Lemma (ty_eq (fun_ty q t1 r t2) (fun_ty q' t1' r' t2') <==>
           (q == q' /\ ty_eq t1 t1' /\ ty_eq r r' /\ ty_eq t2 t2'))

(** The rows of two record types compare as rows. *)
val ty_eq_record (r r': typ) : Lemma (ty_eq (t_record r) (t_record r') <==> ty_eq r r')

(** The rows of two variant types compare as rows. *)
val ty_eq_variant (r r': typ) : Lemma (ty_eq (t_variant r) (t_variant r') <==> ty_eq r r')

(** A record type is no variant type. *)
val ty_eq_record_variant (r r': typ) : Lemma (~(ty_eq (t_record r) (t_variant r')))

(** * Stripping conversions *)

(** A derivation of `e` whose last rule is not `T_Conv`, at a type
    `cf_t ≡ t` and a row `cf_r ≡ r`. *)
noeq type conv_free (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (e: exp) (t r: typ) = {
  cf_t: typ;
  cf_r: typ;
  cf_h: (h0: typing sg ln g d e cf_t cf_r{~(T_Conv? h0)});
  cf_eq: squash (ty_eq cf_t t /\ ty_eq cf_r r);
}

(** The conversions at the bottom of `h` compose into one. The derivation
    returned is `h` itself when `h` ends in another rule, and a proper
    subderivation of `h` otherwise, so an induction on `h` may recurse on
    its premises. *)
val strip_conv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r)
  : Pure (conv_free sg ln g d e t r)
         (requires True)
         (ensures fun s -> if T_Conv? h then s.cf_h << h
                            else (s.cf_h <: typing sg ln g d e s.cf_t s.cf_r) === h)

(** * Abstractions *)

(** The premises of `T_Lam` for `λ (x : t1) / r1 . b` at a type equal to
    `a -{ρ}-> c`: the body has a type `lam_res ≡ c` at the row `r1 ≡ ρ`
    that the λ writes, and the parameter type `t1 ≡ a` and `r1` are
    kinded. *)
noeq type lam_inv (sg: sig) (ln: lctx) (g: ctx) (t1 r1: typ) (b: exp) (a rho c: typ) = {
  lam_res: typ;
  lam_body: typing sg ln (push_var g t1) [] b lam_res r1;
  lam_facts: squash (ty_eq a t1 /\ ty_eq rho r1 /\ ty_eq lam_res c /\
                     check sg g t1 KType /\ check sg g r1 (KRow EEffect));
}

(** A λ at a type equal to the function type `fun_ty q a ρ c`, whose
    constructor `q` is then `Prim.Function`. *)
val inv_lam (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t1 #r1: typ) (#b: exp) (#t #r: typ)
  (h: typing sg ln g d (ELam t1 r1 b) t r) (q: qname) (a rho c: typ)
  : Pure (lam_inv sg ln g t1 r1 b a rho c)
         (requires ty_eq t (fun_ty q a rho c))
         (ensures fun _ -> q == prim_function)

(** The premises of `T_TyLam` for `Λ (a : k). b` at a type equal to
    `forall (a : k). s`. The body is typed in `push_tvar g k`, which shifts
    the types of `Γ` and nothing else: its type `tylam_res` and `s` both
    stand under the binder, as the bodies of the two quantifiers, and are
    compared there with no shift. *)
noeq type tylam_inv (sg: sig) (ln: lctx) (g: ctx) (k: kind) (b: exp) (s: typ) = {
  tylam_res: typ;
  tylam_body: typing sg ln (push_tvar g k) [] b tylam_res TRowEmpty;
  tylam_facts: squash (ty_eq tylam_res s /\ kind_wf g.nk k /\ qkind g.nk k /\ value_form sg b);
}

(** A `Λ` at a type equal to `forall (a : k'). s`, whose kind `k'` is then
    the kind `k` the `Λ` writes. *)
val inv_tylam (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: kind) (#b: exp) (#t #r: typ)
  (h: typing sg ln g d (ETyLam k b) t r) (k': kind) (s: typ)
  : Pure (tylam_inv sg ln g k b s)
         (requires ty_eq t (TForall k' s))
         (ensures fun _ -> k == k')

(** The premises of `T_CLam` for `Λ (_ : c). b` at a type equal to
    `c' => s`: the body is typed under the assumption `c` the `Λ` writes,
    at a type `clam_res ≡ s`. *)
noeq type clam_inv (sg: sig) (ln: lctx) (g: ctx) (c: constr) (b: exp) (s: typ) = {
  clam_res: typ;
  clam_body: typing sg ln (add_assump g c) [] b clam_res TRowEmpty;
  clam_facts: squash (ty_eq clam_res s /\ constr_ok sg g c /\ value_form sg b);
}

(** A constraint `Λ` at a type equal to `c' => s`, whose constraint `c'`
    is then equal to `c`. *)
val inv_clam (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#c: constr) (#b: exp) (#t #r: typ)
  (h: typing sg ln g d (ECLam c b) t r) (c': constr) (s: typ)
  : Pure (clam_inv sg ln g c b s)
         (requires ty_eq t (TConstr c' s))
         (ensures fun _ -> constr_eq c c')

(** * Records *)

(** `{}` at a type equal to `Record rr`: `rr ≡ ()`. *)
val inv_rec_empty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t #r: typ)
  (h: typing sg ln g d ERecEmpty t r) (rr: typ)
  : Lemma (requires ty_eq t (t_record rr)) (ensures ty_eq rr TRowEmpty)

(** The premises of `T_Extend` for `extend k v1 v2` at a type equal to
    `Record rr`, at the ambient row `r`: the field `v1` has a type
    `ext_ty`, the rest `v2` has the type `Record ext_rest`, `k` is a key
    that `ext_rest` lacks, and `rr ≡ ( k : ext_ty | ext_rest )`. *)
noeq type extend_inv (sg: sig) (ln: lctx) (g: ctx) (r: typ) (k: key) (v1 v2: exp) (rr: typ) = {
  ext_ty: typ;
  ext_rest: typ;
  ext_head: typing sg ln g [] v1 ext_ty r;
  ext_tail: typing sg ln g [] v2 (t_record ext_rest) r;
  ext_facts: squash (ty_eq rr (TRowExt (EntTy k ext_ty) ext_rest) /\
                     key_ok sg g k EType /\ entails (hyps g) (CLacks k ext_rest));
}

val inv_extend (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: key) (#v1 #v2: exp)
  (#t #r: typ) (h: typing sg ln g d (EExtend k v1 v2) t r) (rr: typ)
  : Pure (extend_inv sg ln g r k v1 v2 rr)
         (requires sig_ok sg /\ wf_ctx sg g /\ ty_eq t (t_record rr))
         (ensures fun _ -> True)

(** * Variants *)

(** The payload `w` of a variant value with the key `k`, at a type equal
    to `Variant rr`, at the ambient row `r`: `w` has a kinded type
    `var_ty`, and `rr` holds `k` at the payload type `var_ty`, its
    canonical form being an entry of `canon rr`, as `T_VariantValue`
    reads it. The rest of `rr` is unconstrained. *)
noeq type variant_inv (sg: sig) (ln: lctx) (g: ctx) (r: typ) (k: key) (w: exp) (rr: typ) = {
  var_ty: typ;
  var_h: typing sg ln g [] w var_ty r;
  var_facts: squash (check sg g var_ty KType /\
                     L.mem (k, PTy (canon var_ty)) (row_entries (canon rr)));
}

(** A variant value `inject k [ρ0] w`, under any number of `weaken`s
    (`variant_view e == Some (k, w)`), at a type equal to `Variant rr`,
    whether its derivation ends in `T_Inject`, `T_Weaken` or
    `T_VariantValue`. A `weaken` adds an entry in front of the row of its
    operand, so the entry of `k` survives every one. *)
val inv_variant (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (k: key) (w: exp) (rr: typ)
  : Pure (variant_inv sg ln g r k w rr)
         (requires sig_ok sg /\ wf_ctx sg g /\ variant_view e == Some (k, w) /\
                   ty_eq t (t_variant rr))
         (ensures fun _ -> True)
