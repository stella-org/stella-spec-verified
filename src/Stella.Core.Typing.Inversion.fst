(* Proof structure.

   The injectivity lemmas unfold `canon` once on each side: the non-row
   formers canonicalize to the matching constructor of `ctyp`, which is
   injective. The function, record and variant corollaries chain them.

   `strip_conv` recurses through the `T_Conv` nodes at the bottom of a
   derivation, composing their type equalities by transitivity.

   Each inversion strips the conversions and matches the derivation left,
   whose last rule is the syntax-directed one of the form (`*_rule`): the
   other rules conclude other forms, `T_Chain` a chain, which a λ, a `Λ`, a
   record or a variant value is not (`not_chain`), and `T_VariantValue` a
   term with a variant view. The equalities between components then follow
   from the injectivity lemmas.

   A variant value is inverted by a recursion on the derivation itself
   (`variant_go`), through `T_Conv`, through `T_Weaken` on its operand, at
   the row of the operand's variant type, and down to `T_Inject` or
   `T_VariantValue`; the payload derivation it finds stands at a row equal
   to the ambient one, to which `inv_variant` converts it once, kinded by
   regularity. The entries of a row are, by `view_nrow`, the normalized
   entries of its extensions, so the entry of the injected key is among
   those of every row a `weaken` extends. *)
module Stella.Core.Typing.Inversion
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.OrdSet
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Regularity
module L = FStar.List.Tot

(** * Injectivity *)

let ty_eq_app a b a' b' = ()

let ty_eq_con q q' ks ks' = ()

let ty_eq_forall k k' a a' = ()

let ty_eq_constr c c' a a' = ()

let ty_eq_fun_ty q q' t1 r t2 t1' r' t2' =
  ty_eq_app (TApp (TApp (TCon q []) t1) r) t2 (TApp (TApp (TCon q' []) t1') r') t2';
  ty_eq_app (TApp (TCon q []) t1) r (TApp (TCon q' []) t1') r';
  ty_eq_app (TCon q []) t1 (TCon q' []) t1';
  ty_eq_con q q' [] []

let ty_eq_record r r' =
  ty_eq_app (TCon prim_record []) r (TCon prim_record []) r'

let ty_eq_variant r r' =
  ty_eq_app (TCon prim_variant []) r (TCon prim_variant []) r'

let ty_eq_record_variant r r' =
  ty_eq_app (TCon prim_record []) r (TCon prim_variant []) r';
  ty_eq_con prim_record prim_variant [] []

(** * Stripping conversions *)

let rec strip_conv #sg #ln #g #d #e #t #r h
  : Pure (conv_free sg ln g d e t r)
         (requires True)
         (ensures fun s -> if T_Conv? h then s.cf_h << h
                            else (s.cf_h <: typing sg ln g d e s.cf_t s.cf_r) === h)
         (decreases h) =
  match h with
  | T_Conv h1 _ _ ->
    let s = strip_conv h1 in
    { cf_t = s.cf_t; cf_r = s.cf_r; cf_h = s.cf_h; cf_eq = () }
  | _ -> { cf_t = t; cf_r = r; cf_h = h; cf_eq = () }

(** * Shapes *)

(** A λ, a `Λ`, a constraint `Λ`, a record or a variant value is no
    chain. *)
let not_chain (sg: sig) (e: exp)
  : Lemma (requires ELam? e \/ ETyLam? e \/ ECLam? e \/ ERecEmpty? e \/ EExtend? e \/
                    EInject? e \/ EWeaken? e)
          (ensures chain_cursor sg e == None) = ()

let variant_view_shape (e: exp)
  : Lemma (requires Some? (variant_view e)) (ensures EInject? e \/ EWeaken? e) =
  match e with
  | EInject _ _ _ -> ()
  | EWeaken _ _ _ -> ()

(** * Abstractions *)

let lam_rule (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t1 #r1: typ) (#b: exp) (#t #r: typ)
  (h: typing sg ln g d (ELam t1 r1 b) t r{~(T_Conv? h)})
  : Pure (t2: typ & typing sg ln (push_var g t1) [] b t2 r1)
         (requires True)
         (ensures fun (| t2, _ |) -> t == t_fun t1 r1 t2 /\
                                    check sg g t1 KType /\ check sg g r1 (KRow EEffect)) =
  not_chain sg (ELam t1 r1 b);
  match h with
  | T_Lam #_ #_ #_ #_ #_ #_ #_ #t2 _ _ hb -> (| t2, hb |)
  | _ -> false_elim ()

let inv_lam #sg #ln #g #d #t1 #r1 #b #t #r h q a rho c =
  let s = strip_conv h in
  let (| t2, hb |) = lam_rule s.cf_h in
  ty_eq_fun_ty prim_function q t1 r1 t2 a rho c;
  { lam_res = t2; lam_body = hb; lam_facts = () }

let tylam_rule (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: kind) (#b: exp) (#t #r: typ)
  (h: typing sg ln g d (ETyLam k b) t r{~(T_Conv? h)})
  : Pure (t0: typ & typing sg ln (push_tvar g k) [] b t0 TRowEmpty)
         (requires True)
         (ensures fun (| t0, _ |) -> t == TForall k t0 /\
                                    kind_wf g.nk k /\ qkind g.nk k /\ value_form sg b) =
  not_chain sg (ETyLam k b);
  match h with
  | T_TyLam #_ #_ #_ #_ #_ #_ #t0 _ _ _ hb -> (| t0, hb |)
  | _ -> false_elim ()

let inv_tylam #sg #ln #g #d #k #b #t #r h k' s =
  let st = strip_conv h in
  let (| t0, hb |) = tylam_rule st.cf_h in
  ty_eq_forall k k' t0 s;
  { tylam_res = t0; tylam_body = hb; tylam_facts = () }

let clam_rule (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#c: constr) (#b: exp) (#t #r: typ)
  (h: typing sg ln g d (ECLam c b) t r{~(T_Conv? h)})
  : Pure (t0: typ & typing sg ln (add_assump g c) [] b t0 TRowEmpty)
         (requires True)
         (ensures fun (| t0, _ |) -> t == TConstr c t0 /\ constr_ok sg g c /\ value_form sg b) =
  not_chain sg (ECLam c b);
  match h with
  | T_CLam #_ #_ #_ #_ #_ #_ #t0 _ _ _ hb -> (| t0, hb |)
  | _ -> false_elim ()

let inv_clam #sg #ln #g #d #c #b #t #r h c' s =
  let st = strip_conv h in
  let (| t0, hb |) = clam_rule st.cf_h in
  ty_eq_constr c c' t0 s;
  { clam_res = t0; clam_body = hb; clam_facts = () }

(** * Records *)

let rec_empty_rule (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t #r: typ)
  (h: typing sg ln g d ERecEmpty t r{~(T_Conv? h)})
  : Lemma (t == t_record TRowEmpty) =
  not_chain sg ERecEmpty;
  match h with
  | T_RecEmpty _ -> ()
  | _ -> false_elim ()

let inv_rec_empty #sg #ln #g #d #t #r h rr =
  let s = strip_conv h in
  rec_empty_rule s.cf_h;
  ty_eq_record TRowEmpty rr

(** The premises of `T_Extend`, at the row of the derivation. *)
noeq type extend_prem (sg: sig) (ln: lctx) (g: ctx) (r: typ) (k: key) (v1 v2: exp) = {
  xp_ty: typ;
  xp_rest: typ;
  xp_head: typing sg ln g [] v1 xp_ty r;
  xp_tail: typing sg ln g [] v2 (t_record xp_rest) r;
  xp_facts: squash (key_ok sg g k EType /\ entails (hyps g) (CLacks k xp_rest));
}

let extend_rule (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: key) (#v1 #v2: exp) (#t #r: typ)
  (h: typing sg ln g d (EExtend k v1 v2) t r{~(T_Conv? h)})
  : Pure (extend_prem sg ln g r k v1 v2)
         (requires True)
         (ensures fun p -> t == t_record (TRowExt (EntTy k p.xp_ty) p.xp_rest)) =
  not_chain sg (EExtend k v1 v2);
  match h with
  | T_Extend #_ #_ #_ #_ #_ #_ #_ #t1 #r0 h1 h2 _ ->
    { xp_ty = t1; xp_rest = r0; xp_head = h1; xp_tail = h2; xp_facts = () }
  | _ -> false_elim ()

(** A derivation converted to an equal, kinded row. *)
let conv_row (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (r': typ)
  : Pure (typing sg ln g d e t r')
         (requires sig_ok sg /\ wf_ctx sg g /\ ty_eq r r' /\ check sg g r' (KRow EEffect))
         (ensures fun _ -> True) =
  typing_regular h;
  T_Conv h () ()

let inv_extend #sg #ln #g #d #k #v1 #v2 #t #r h rr =
  typing_regular h;
  let s = strip_conv h in
  let p = extend_rule s.cf_h in
  ty_eq_record (TRowExt (EntTy k p.xp_ty) p.xp_rest) rr;
  { ext_ty = p.xp_ty; ext_rest = p.xp_rest;
    ext_head = conv_row p.xp_head r; ext_tail = conv_row p.xp_tail r; ext_facts = () }

(** * Variants *)

(** The payload derivation of a variant value, at a row `vp_r ≡ r`. *)
noeq type variant_prem (sg: sig) (ln: lctx) (g: ctx) (r: typ) (k: key) (w: exp) (rr: typ) = {
  vp_ty: typ;
  vp_r: typ;
  vp_h: typing sg ln g [] w vp_ty vp_r;
  vp_facts: squash (ty_eq vp_r r /\ L.mem (k, PTy (canon vp_ty)) (row_entries (canon rr)));
}

(** The entries of `( en | r0 )` are those of `r0` and the entry of
    `en`. *)
let mem_entries_ext (en: entry) (r0: typ) (x: centry)
  : Lemma (requires x == canon_ent en \/ L.mem x (row_entries (canon r0)))
          (ensures L.mem x (row_entries (canon (TRowExt en r0)))) =
  let v = view_row (canon r0) in
  view_nrow (canon_ent en :: fst v) (snd v);
  mem_norm ord_centry (canon_ent en :: fst v) x

(** Equal rows have the same entries. *)
let mem_entries_eq (r1 r2: typ) (x: centry)
  : Lemma (requires ty_eq r1 r2 /\ L.mem x (row_entries (canon r1)))
          (ensures L.mem x (row_entries (canon r2))) = ()

let rec variant_go (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (k: key) (w: exp) (rr: typ)
  : Pure (variant_prem sg ln g r k w rr)
         (requires variant_view e == Some (k, w) /\ ty_eq t (t_variant rr))
         (ensures fun _ -> True)
         (decreases h) =
  variant_view_shape e;
  not_chain sg e;
  match h with
  | T_Conv h1 _ _ ->
    let p = variant_go h1 k w rr in
    { vp_ty = p.vp_ty; vp_r = p.vp_r; vp_h = p.vp_h; vp_facts = () }
  | T_Inject #_ #_ #_ #_ #_ #r0 #_ #t1 h1 _ _ ->
    ty_eq_variant (TRowExt (EntTy k t1) r0) rr;
    mem_entries_ext (EntTy k t1) r0 (k, PTy (canon t1));
    mem_entries_eq (TRowExt (EntTy k t1) r0) rr (k, PTy (canon t1));
    { vp_ty = t1; vp_r = r; vp_h = h1; vp_facts = () }
  | T_Weaken #_ #_ #_ #_ #k' #t' #_ #r0 h1 _ _ ->
    let p = variant_go h1 k w r0 in
    ty_eq_variant (TRowExt (EntTy k' t') r0) rr;
    mem_entries_ext (EntTy k' t') r0 (k, PTy (canon p.vp_ty));
    mem_entries_eq (TRowExt (EntTy k' t') r0) rr (k, PTy (canon p.vp_ty));
    { vp_ty = p.vp_ty; vp_r = p.vp_r; vp_h = p.vp_h; vp_facts = () }
  | T_VariantValue #_ #_ #_ #_ #_ #_ #_ #pt vr0 vr _ _ h2 _ ->
    ty_eq_variant vr rr;
    mem_entries_eq vr rr (k, PTy (canon pt));
    { vp_ty = pt; vp_r = r; vp_h = h2; vp_facts = () }
  | _ -> false_elim ()

let inv_variant #sg #ln #g #d #e #t #r h k w rr =
  typing_regular h;
  let p = variant_go h k w rr in
  typing_regular p.vp_h;
  { var_ty = p.vp_ty; var_h = conv_row p.vp_h r; var_facts = () }
