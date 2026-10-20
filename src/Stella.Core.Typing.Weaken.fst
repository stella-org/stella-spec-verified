(* Proof structure.

   Weakening by binders composes the one-binder morphisms
   (`ty_ren_ok_shift`, `tm_ren_ok_shift`) along the telescope; weakening
   in place is the identity term renaming, whose image of a term is the
   term (`ren_tm_id`). Extending `Γ_N` is a direct induction over the
   judgements, which rebuilds every derivation with the same premises: only
   `force` and `fill` read `Γ_N`, at a location the old one has. *)
module Stella.Core.Typing.Weaken
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.Tm
open Stella.Core.Region
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Ty
open Stella.Core.Typing.Rename.Tm
module L = FStar.List.Tot

let rec nth_length (#a: Type) (l: list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures i < L.length l) (decreases l) =
  match l with
  | _ :: tl -> if i = 0 then () else nth_length tl (i - 1)

let rec nth_some (#a: Type) (l: list a) (i: nat)
  : Lemma (requires i < L.length l) (ensures Some? (L.nth l i)) (decreases l) =
  match l with
  | _ :: tl -> if i = 0 then () else nth_some tl (i - 1)

let rec map_wit (#a #b: eqtype) (f: a -> b) (l: list a) (y: b)
  : Pure a (requires L.mem y (L.map f l)) (ensures fun x -> L.mem x l /\ f x == y) (decreases l) =
  match l with
  | x :: tl -> if f x = y then x else map_wit f tl y

let entails_into (xi: ren) (g g': ctx) (c: constr)
  : Lemma (requires ren_ok xi g g' /\ entails (hyps g) c)
          (ensures entails (hyps g') (ren_constr xi c)) =
  entails_ren xi (hyps g) c;
  introduce forall (h': constr). L.mem h' (L.map (ren_constr xi) (hyps g)) ==> entails (hyps g') h'
  with introduce _ ==> _
  with (let _ = map_wit (ren_constr xi) (hyps g) h' in ());
  entails_cut_all (L.map (ren_constr xi) (hyps g)) (hyps g') (ren_constr xi c)

(* Type variables. *)

let ty_ren_ok_comp xi zeta g1 g2 g3 =
  let th (i: nat) : nat = zeta (xi i) in
  introduce forall (i: nat). i < L.length g1.tvars ==> L.nth g3.tvars (th i) == L.nth g1.tvars i
  with introduce _ ==> _
  with (nth_some g1.tvars i;
        assert (L.nth g1.tvars i == L.nth g1.tvars i);
        nth_length g2.tvars (xi i);
        assert (L.nth g2.tvars (xi i) == L.nth g2.tvars (xi i)));
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g3) (ren_constr th h)
  with introduce _ ==> _
  with (entails_into zeta g2 g3 (ren_constr xi h);
        ren_ren_constr zeta xi th h);
  introduce forall (i: nat). (match L.nth g1.vars i with
                              | Some t -> L.nth g3.vars i == Some (ren_ty th t)
                              | None -> True)
  with (match L.nth g1.vars i with
        | Some t ->
          assert (L.nth g2.vars i == L.nth g2.vars i);
          ren_ren_ty zeta xi th t
        | None -> ());
  introduce forall (a: atom). (match L.assoc a g1.regions with
                               | Some l -> L.assoc a g3.regions == Some (ren_layout th l)
                               | None -> True)
  with (match L.assoc a g1.regions with
        | Some l ->
          assert (L.assoc a g2.regions == L.assoc a g2.regions);
          ren_ren_layout zeta xi th l
        | None -> ())

let ty_ren_ok_refl (g: ctx) : Lemma (ty_ren_ok (shift 0) g g) =
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g) (ren_constr (shift 0) h)
  with introduce _ ==> _
  with (ren_id_constr (shift 0) h; entails_hyp (hyps g) h);
  introduce forall (i: nat). (match L.nth g.vars i with
                              | Some t -> L.nth g.vars i == Some (ren_ty (shift 0) t)
                              | None -> True)
  with (match L.nth g.vars i with Some t -> ren_ty_shift0 t | None -> ());
  introduce forall (a: atom). (match L.assoc a g.regions with
                               | Some l -> L.assoc a g.regions == Some (ren_layout (shift 0) l)
                               | None -> True)
  with (match L.assoc a g.regions with Some l -> ren_id_layout (shift 0) l | None -> ())

let rec ty_ren_ok_shifts (g: ctx) (ks: list kind)
  : Lemma (ensures ty_ren_ok (shift (L.length ks)) g (push_tvars g ks)) (decreases ks) =
  match ks with
  | [] -> ty_ren_ok_refl g
  | k :: ks' ->
    ty_ren_ok_shift g k;
    ty_ren_ok_shifts (push_tvar g k) ks';
    ty_ren_ok_comp (shift 1) (shift (L.length ks')) g (push_tvar g k)
      (push_tvars (push_tvar g k) ks');
    ty_ren_ok_ext (fun i -> shift (L.length ks') (shift 1 i)) (shift (L.length ks)) g
      (push_tvars (push_tvar g k) ks')

let typing_weaken_tvar #sg #ln #g #d #e #t #r h k =
  ty_ren_ok_shift g k;
  typing_ren_ty h (shift 1) (push_tvar g k)

let typing_weaken_tvars #sg #ln #g #d #e #t #r h ks =
  ty_ren_ok_shifts g ks;
  typing_ren_ty h (shift (L.length ks)) (push_tvars g ks)

(* Term variables. *)

let tm_ren_ok_comp xi zeta g1 g2 g3 =
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g3) h
  with introduce _ ==> _
  with entails_cut_all (hyps g2) (hyps g3) h;
  introduce forall (i: nat). i < L.length g1.vars ==> L.nth g3.vars (zeta (xi i)) == L.nth g1.vars i
  with introduce _ ==> _
  with (nth_some g1.vars i;
        assert (L.nth g1.vars i == L.nth g1.vars i);
        nth_length g2.vars (xi i);
        assert (L.nth g2.vars (xi i) == L.nth g2.vars (xi i)))

let ctx_ext_refl (g: ctx) : Lemma (ctx_ext g g) =
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g) h
  with introduce _ ==> _
  with entails_hyp (hyps g) h

let rec tm_ren_ok_shifts (g: ctx) (ts: list typ)
  : Lemma (ensures tm_ren_ok (shift (L.length ts)) g (push_vars g ts)) (decreases ts) =
  match ts with
  | [] -> ctx_ext_refl g
  | t :: ts' ->
    tm_ren_ok_shift g t;
    tm_ren_ok_shifts (push_var g t) ts';
    tm_ren_ok_comp (shift 1) (shift (L.length ts')) g (push_var g t) (push_vars (push_var g t) ts');
    tm_ren_ok_ext (fun i -> shift (L.length ts') (shift 1 i)) (shift (L.length ts)) g
      (push_vars (push_var g t) ts')

let typing_weaken_var #sg #ln #g #d #e #t #r h t' =
  tm_ren_ok_shift g t';
  typing_ren_tm h (shift 1) (push_var g t')

let typing_weaken_vars #sg #ln #g #d #e #t #r h ts =
  tm_ren_ok_shifts g ts;
  typing_ren_tm h (shift (L.length ts)) (push_vars g ts)

(* Extending the context in place. *)

let typing_weaken_ext #sg #ln #g #d #e #t #r h g' =
  tm_ren_ok_id g g';
  ren_tm_id e;
  typing_ren_tm h id_ren g'

let typing_weaken_assumps #sg #ln #g #d #e #t #r h cs =
  ctx_ext_add_assumps g cs;
  typing_weaken_ext h (add_assumps g cs)

let rec assoc_mem (a: atom) (rs: list (atom & layout))
  : Lemma (requires Some? (L.assoc a rs)) (ensures L.mem a (L.map fst rs)) (decreases rs) =
  match rs with
  | (b, _) :: rs' -> if a = b then () else assoc_mem a rs'

let typing_weaken_region #sg #ln #g #d #e #t #r h a l =
  let g' = { g with regions = (a, l) :: g.regions } in
  assert (hyps g' == hyps g);
  ctx_ext_refl g;
  introduce forall (b: atom). (match L.assoc b g.regions with
                               | Some l0 -> L.assoc b g'.regions == Some l0
                               | None -> True)
  with (match L.assoc b g.regions with
        | Some _ -> assoc_mem b g.regions
        | None -> ());
  typing_weaken_ext h g'

(* The location context. *)

let rec nth_append (#a: Type) (l l': list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures L.nth (L.append l l') i == L.nth l i)
    (decreases l) =
  match l with
  | _ :: tl -> if i = 0 then () else nth_append tl l' (i - 1)

let lctx_incl_append ln ln' =
  introduce forall (nu: nat). Some? (L.nth ln nu) ==> L.nth (L.append ln ln') nu == L.nth ln nu
  with introduce _ ==> _
  with nth_append ln ln' nu

let rec typing_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (ln': lctx)
  : Pure (typing sg ln' g d e t r) (requires lctx_incl ln ln') (ensures fun _ -> True)
         (decreases h) =
  match h with
  | T_Var sq1 sq2 -> T_Var sq1 sq2
  | T_Global sq1 sq2 sq3 -> T_Global sq1 sq2 sq3
  | T_Lit #_ #_ #_ #_ #c sq -> T_Lit #sg #ln' #g #d #c #r sq
  | T_Lam sq1 sq2 hb -> T_Lam sq1 sq2 (typing_ln hb ln')
  | T_App h1 h2 -> T_App (typing_ln h1 ln') (typing_ln h2 ln')
  | T_Chain hc sq -> T_Chain (chain_ln hc ln') sq
  | T_TyLam sq1 sq2 sq3 hb -> T_TyLam sq1 sq2 sq3 (typing_ln hb ln')
  | T_TyApp h1 sq -> T_TyApp (typing_ln h1 ln') sq
  | T_CLam sq1 sq2 sq3 hb -> T_CLam sq1 sq2 sq3 (typing_ln hb ln')
  | T_CApp h1 sq -> T_CApp (typing_ln h1 ln') sq
  | T_Let sq h1 h2 -> T_Let sq (typing_ln h1 ln') (typing_ln h2 ln')
  | T_LetRec sq hbs hb -> T_LetRec sq (binds_ln hbs ln') (typing_ln hb ln')
  | T_Conv h1 sq1 sq2 -> T_Conv (typing_ln h1 ln') sq1 sq2
  | T_Case hes hdt -> T_Case (exps_ln hes ln') (dt_ln hdt ln')
  | T_LetJoin sq h1 h2 -> T_LetJoin sq (typing_ln h1 ln') (typing_ln h2 ln')
  | T_Jump sq1 sq2 hes -> T_Jump sq1 sq2 (exps_ln hes ln')
  | T_RecEmpty sq -> T_RecEmpty sq
  | T_Extend h1 h2 sq -> T_Extend (typing_ln h1 ln') (typing_ln h2 ln') sq
  | T_Select h1 sq -> T_Select (typing_ln h1 ln') sq
  | T_Restrict h1 sq -> T_Restrict (typing_ln h1 ln') sq
  | T_Update h1 h2 sq -> T_Update (typing_ln h1 ln') (typing_ln h2 ln') sq
  | T_Merge h1 h2 sq -> T_Merge (typing_ln h1 ln') (typing_ln h2 ln') sq
  | T_Inject h1 sq1 sq2 -> T_Inject (typing_ln h1 ln') sq1 sq2
  | T_Weaken h1 sq1 sq2 -> T_Weaken (typing_ln h1 ln') sq1 sq2
  | T_VariantValue vr0 vr h1 sq1 h2 sq2 ->
    T_VariantValue vr0 vr (typing_ln h1 ln') sq1 (typing_ln h2 ln') sq2
  | T_Absurd h1 sq -> T_Absurd (typing_ln h1 ln') sq
  | T_Perform ts sq1 sq2 sq3 h1 -> T_Perform ts sq1 sq2 sq3 (typing_ln h1 ln')
  | T_Handle sq1 sq2 sq3 sq4 h1 h2 hcl ->
    T_Handle sq1 sq2 sq3 sq4 (typing_ln h1 ln') (typing_ln h2 ln') (clauses_ln hcl ln')
  | T_OpenEff h1 sq -> T_OpenEff (typing_ln h1 ln') sq
  | T_Region #_ #_ #_ #_ #lay #_ #body #b sq1 sq2 hes hbody ->
    let hb' (a: atom{~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body))})
      : typing sg ln' (enter_region g a lay) [] (open_region a body) b
          (TRowExt (EntRegion (RFree a)) r) =
      typing_ln (hbody a) ln'
    in
    T_Region sq1 sq2 (exps_ln hes ln') hb'
  | T_ReadCell sq1 sq2 sq3 -> T_ReadCell sq1 sq2 sq3
  | T_WriteCell sq1 sq2 h1 -> T_WriteCell sq1 sq2 (typing_ln h1 ln')
  | T_Match om hes sq hm hdt -> T_Match om (exps_ln hes ln') sq (match_ln hm ln') (dt_ln hdt ln')
  | T_OpenEffC h1 sq -> T_OpenEffC (typing_ln h1 ln') sq
  | T_Force #_ #_ #_ #_ #nu _ sq2 -> T_Force #sg #ln' #g #d #nu #t #r () sq2
  | T_Fill #_ #_ #_ #_ #nu _ sq2 h1
    -> T_Fill #sg #ln' #g #d #nu #_ #t #r () sq2 (typing_ln h1 ln')
  | T_RegionOpen sq1 sq2 sq3 hc hb -> T_RegionOpen sq1 sq2 sq3 (cells_ln hc ln') (typing_ln hb ln')
  | T_Opaque #_ #_ #_ #_ #w sq1 sq2 -> T_Opaque #sg #ln' #g #d #w #t #r sq1 sq2

and exps_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#es: list exp)
  (#ts: list typ) (h: exps_typing sg ln g d r es ts) (ln': lctx)
  : Pure (exps_typing sg ln' g d r es ts) (requires lctx_incl ln ln') (ensures fun _ -> True)
         (decreases h) =
  match h with
  | TE_Nil sq -> TE_Nil sq
  | TE_Cons h1 h2 -> TE_Cons (typing_ln h1 ln') (exps_ln h2 ln')

and chain_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (ln': lctx)
  : Pure (chain_typing sg ln' g d r e) (requires lctx_incl ln ln') (ensures fun _ -> True)
         (decreases h) =
  match h with
  | TS_Head sq1 sq2 sq3 -> TS_Head sq1 sq2 sq3
  | TS_Ty h0 sq1 sq2 -> TS_Ty (chain_ln h0 ln') sq1 sq2
  | TS_Constr h0 sq1 sq2 -> TS_Constr (chain_ln h0 ln') sq1 sq2
  | TS_Val h0 sq hv -> TS_Val (chain_ln h0 ln') sq (typing_ln hv ln')

and binds_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (ln': lctx)
  : Pure (binds_typing sg ln' g bs) (requires lctx_incl ln ln') (ensures fun _ -> True)
         (decreases h) =
  match h with
  | TB_Nil -> TB_Nil
  | TB_Cons sq h1 h2 -> TB_Cons sq (typing_ln h1 ln') (binds_ln h2 ln')

and cells_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (ln': lctx)
  : Pure (cells_typing sg ln' g cells lay) (requires lctx_incl ln ln') (ensures fun _ -> True)
         (decreases h) =
  match h with
  | TC_Nil -> TC_Nil
  | TC_Cons #_ #_ #_ #k sq h1 h2 -> TC_Cons #sg #ln' #g #k sq (typing_ln h1 ln') (cells_ln h2 ln')

and match_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp) (#om: octx)
  (h: match_typing sg ln g d r th om) (ln': lctx)
  : Pure (match_typing sg ln' g d r th om) (requires lctx_incl ln ln') (ensures fun _ -> True)
         (decreases h) =
  match h with
  | TM_Nil sq -> TM_Nil sq
  | TM_Cons sq h1 h2 -> TM_Cons sq (typing_ln h1 ln') (match_ln h2 ln')

and dt_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#dt: dtree)
  (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (ln': lctx)
  : Pure (dt_typing sg ln' g d om dt t r) (requires lctx_incl ln ln') (ensures fun _ -> True)
         (decreases h) =
  match h with
  | TD_Leaf h1 -> TD_Leaf (typing_ln h1 ln')
  | TD_Bind ho hdt -> TD_Bind ho (dt_ln hdt ln')
  | TD_SwitchCtor tq ks ss cs ho sq1 sq2 sq3 hbr ->
    TD_SwitchCtor tq ks ss cs ho sq1 sq2 sq3 (cb_ln hbr ln')
  | TD_SwitchCtorDef tq ks ss cs ho sq1 sq2 sq3 hbr hdf ->
    TD_SwitchCtorDef tq ks ss cs ho sq1 sq2 sq3 (cb_ln hbr ln') (dt_ln hdf ln')
  | TD_SwitchLit lq ho sq1 sq2 hbr hdf -> TD_SwitchLit lq ho sq1 sq2 (lb_ln hbr ln') (dt_ln hdf ln')
  | TD_SwitchKey vr kts ho sq1 sq2 sq3 hbr -> TD_SwitchKey vr kts ho sq1 sq2 sq3 (kb_ln hbr ln')
  | TD_SwitchKeyDef vr vr' kts ho sq1 sq2 sq3 hbr hdf ->
    TD_SwitchKeyDef vr vr' kts ho sq1 sq2 sq3 (kb_ln hbr ln') (dt_ln hdf ln')
  | TD_Guard h1 h2 h3 -> TD_Guard (typing_ln h1 ln') (dt_ln h2 ln') (dt_ln h3 ln')

and cb_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#o: occ)
  (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree)) (#t #r: typ)
  (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (ln': lctx)
  : Pure (ctor_brs_typing sg ln' g d om o ks ss cs bs t r) (requires lctx_incl ln ln')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCB_Nil sq -> TCB_Nil sq
  | TCB_Cons sq hdt h2 -> TCB_Cons sq (dt_ln hdt ln') (cb_ln h2 ln')

and lb_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#lt: typ)
  (#bs: list (lit & dtree)) (#t #r: typ) (h: lit_brs_typing sg ln g d om lt bs t r) (ln': lctx)
  : Pure (lit_brs_typing sg ln' g d om lt bs t r) (requires lctx_incl ln ln')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TLB_Nil sq -> TLB_Nil sq
  | TLB_Cons sq hdt h2 -> TLB_Cons sq (dt_ln hdt ln') (lb_ln h2 ln')

and kb_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#o: occ)
  (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (ln': lctx)
  : Pure (key_brs_typing sg ln' g d om o kts bs t r) (requires lctx_incl ln ln')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TKB_Nil sq -> TKB_Nil sq
  | TKB_Cons sq hdt h2 -> TKB_Cons sq (dt_ln hdt ln') (kb_ln h2 ln')

and clauses_ln (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ) (#r #b: typ)
  (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs) (ln': lctx)
  : Pure (clauses_typing sg ln' g ei ts r b cs) (requires lctx_incl ln ln')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCL_Nil sq -> TCL_Nil sq
  | TCL_Full sq1 sq2 sq3 hb hcs -> TCL_Full sq1 sq2 sq3 (typing_ln hb ln') (clauses_ln hcs ln')
  | TCL_Fast sq1 sq2 hb hcs -> TCL_Fast sq1 sq2 (typing_ln hb ln') (clauses_ln hcs ln')

let typing_lctx_ext #sg #ln #g #d #e #t #r h ln' = typing_ln h ln'

let exps_typing_lctx_ext #sg #ln #g #d #r #es #ts h ln' = exps_ln h ln'

(* Closed terms. *)

let typing_closed_ext #sg #ln #g #d #e #t #r h ln' g' =
  lctx_incl_append ln ln';
  typing_lctx_ext (typing_weaken_ext h g') (L.append ln ln')
