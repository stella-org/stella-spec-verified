(* Proof structure.

   The context lemmas. The conditions on the contexts read no term
   variable, so a context and the context with its term variables removed
   (`novars`) satisfy the same ones, and the extension of contexts under a
   type binder, an assumption or a region is the term renaming case
   (`Stella.Core.Typing.Rename.Tm`) at the identity between such contexts.
   The substitutes are lifted one entry at a time: a variable is moved to
   its image, a value is weakened (`Stella.Core.Typing.Weaken`). A
   telescope is lifted binder by binder, and the substitution of the
   telescope is pointwise the iterated one (`Stella.Core.Subst.Lemmas.Tm`,
   `ren_ren_ty_exp`).

   The judgements are one mutual induction on the derivation, as in
   `Stella.Core.Typing.Rename.Tm`: each rule of `typing` has a builder that
   takes the substituted premises and concludes the substituted judgement.
   The variable rule is the only one that reads the substitutes: a variable
   is typed by `T_Var`, a value by `Stella.Core.Typing.Values.value_typing`
   at the row and the `Δ` of the use. Under every binder the
   well-formedness of `Γ'` is re-established from the kinding premises of
   the rule (`Stella.Core.Typing.Wf`), and that of `Ω` from the occurrence
   and the refinements of a decision tree. *)
module Stella.Core.Typing.Subst.Tm
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Subst.Lemmas.Tm
open Stella.Core.Region
open Stella.Core.Region.Lemmas
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Keys
open Stella.Core.Typing.Wf
open Stella.Core.Typing.Regularity
open Stella.Core.Typing.Rename.Facts
open Stella.Core.Typing.Rename.Ty
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Weaken
open Stella.Core.Typing.Values
open Stella.Core.Typing.Subst.Tm.Facts
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value
module SI = Stella.Core.Typing.Subst.Tm.Init
module SC = Stella.Core.Scope

(* Lists. *)

let rec nth_map (#a #b: Type) (f: a -> b) (l: list a) (i: nat)
  : Lemma (ensures L.nth (L.map f l) i == map_opt f (L.nth l i)) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> if i = 0 then () else nth_map f l (i - 1)

let rec assoc_none (#a: eqtype) (#b: Type) (x: a) (l: list (a & b))
  : Lemma (requires ~(L.mem x (L.map fst l))) (ensures L.assoc x l == None) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> assoc_none x l

(* The conditions on the contexts. *)

let novars (g: ctx) : ctx = { g with vars = [] }

let ext_ok (g g': ctx) : prop = ctx_ext g g' /\ layouts_ext g g'

let ext_ok_novars (g g': ctx)
  : Lemma (ext_ok g g' <==> tm_ren_ok id_ren (novars g) (novars g')) =
  assert (hyps (novars g) == hyps g /\ hyps (novars g') == hyps g');
  assert (rdom (novars g) == rdom g /\ rdom (novars g') == rdom g')

let ctx_ext_novars (g g': ctx)
  : Lemma (ctx_ext (novars g) (novars g') <==> ctx_ext g g') =
  assert (hyps (novars g) == hyps g /\ hyps (novars g') == hyps g');
  assert (rdom (novars g) == rdom g /\ rdom (novars g') == rdom g')

let novars_push_var (g: ctx) (t: typ) : Lemma (novars (push_var g t) == novars g) = ()

let rec novars_push_vars (g: ctx) (ts: list typ)
  : Lemma (ensures novars (push_vars g ts) == novars g) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> novars_push_vars (push_var g t) ts'

let novars_push_tvar (g: ctx) (k: kind)
  : Lemma (novars (push_tvar g k) == push_tvar (novars g) k) =
  assert_norm (L.map (ren_ty (shift 1)) [] == [])

let novars_assump (g: ctx) (c: constr)
  : Lemma (novars (add_assump g c) == add_assump (novars g) c) = ()

let novars_enter_region (g: ctx) (a: atom) (l: layout)
  : Lemma (novars (enter_region g a l) == enter_region (novars g) a l) = ()

let ext_ok_push_var (g g': ctx) (t t': typ)
  : Lemma (requires ext_ok g g') (ensures ext_ok (push_var g t) (push_var g' t')) =
  ext_ok_novars g g';
  ext_ok_novars (push_var g t) (push_var g' t')

let ext_ok_push_tvar (g g': ctx) (k: kind)
  : Lemma (requires ext_ok g g') (ensures ext_ok (push_tvar g k) (push_tvar g' k)) =
  ext_ok_novars g g';
  tm_ren_ok_push_tvar id_ren (novars g) (novars g') k;
  novars_push_tvar g k;
  novars_push_tvar g' k;
  ext_ok_novars (push_tvar g k) (push_tvar g' k)

let ext_ok_assump (g g': ctx) (c: constr)
  : Lemma (requires ext_ok g g') (ensures ext_ok (add_assump g c) (add_assump g' c)) =
  ext_ok_novars g g';
  tm_ren_ok_assump id_ren (novars g) (novars g') c;
  novars_assump g c;
  novars_assump g' c;
  ext_ok_novars (add_assump g c) (add_assump g' c)

let ext_ok_enter_region (g g': ctx) (a: atom) (l: layout)
  : Lemma (requires ext_ok g g') (ensures ext_ok (enter_region g a l) (enter_region g' a l)) =
  ext_ok_novars g g';
  tm_ren_ok_enter_region id_ren (novars g) (novars g') a l;
  novars_enter_region g a l;
  novars_enter_region g' a l;
  ext_ok_novars (enter_region g a l) (enter_region g' a l)

(* The members of a `letrec` and the parameters of a join point leave the
   rest of the context as it is. *)
let ctx_ext_push_vars_left (g g': ctx) (ts: list typ)
  : Lemma (requires ctx_ext g g') (ensures ctx_ext (push_vars g ts) g') =
  novars_push_vars g ts;
  ctx_ext_novars g g';
  ctx_ext_novars (push_vars g ts) g'

(* The substitutes. *)

let cast_entry (#sg: sig) (#ln: lctx) (#g': ctx) (#e: exp) (#t: typ) (s: sub_entry sg ln g' e t)
  (e': exp{e' == e}) : sub_entry sg ln g' e' t = s

let tm_sub_ok_props #sg #ln #sigma #g #g' hs = let TmSubOk _ _ = hs in ()

let tm_sub_ok_ext #sg #ln #sigma #g #g' hs sigma' =
  let TmSubOk _ f = hs in
  let f' (i: nat) (t: typ) (_: squash (L.nth g.vars i == Some t))
    : sub_entry sg ln g' (sigma' i) t =
    cast_entry (f i t ()) (sigma' i)
  in
  TmSubOk () f'

let up_entry (#sg: sig) (#ln: lctx) (#g': ctx) (#e: exp) (#t: typ) (s: sub_entry sg ln g' e t)
  (t': typ)
  : sub_entry sg ln (push_var g' t') (ren_tm (shift 1) e) t =
  match s with
  | SE_Var j _ -> SE_Var (j + 1) ()
  | SE_Val _ hv -> is_value_ren_tm sg (shift 1) e; SE_Val () (typing_weaken_var hv t')

let up_props (sigma: esub) (g g': ctx) (t: typ)
  : Lemma (requires tm_sub_props sigma g g')
          (ensures tm_sub_props (up_esub sigma) (push_var g t) (push_var g' t)) =
  ext_ok_push_var g g' t t;
  introduce forall (i: nat). V.jp_scoped 0 (up_esub sigma i) /\ lc_exp (up_esub sigma i)
  with (if i = 0 then ()
        else (V.jp_scoped_ren_tm 0 (shift 1) (sigma (i - 1)); lc_ren_tm (shift 1) (sigma (i - 1))))

let tm_sub_ok_up #sg #ln #sigma #g #g' hs t =
  let TmSubOk _ f = hs in
  up_props sigma g g' t;
  let f' (i: nat) (t0: typ) (_: squash (L.nth (push_var g t).vars i == Some t0))
    : sub_entry sg ln (push_var g' t) (up_esub sigma i) t0 =
    if i = 0 then SE_Var 0 ()
    else cast_entry (up_entry (f (i - 1) t0 ()) t) (up_esub sigma i)
  in
  TmSubOk () f'

let upn_esub_succ (n: nat) (sigma: esub)
  : Lemma (forall (i: nat). upn_esub n (up_esub sigma) i == upn_esub (n + 1) sigma i) =
  introduce forall (i: nat). upn_esub n (up_esub sigma) i == upn_esub (n + 1) sigma i
  with (if i < n then ()
        else if i = n then ()
        else ren_ren_tm (shift n) (shift 1) (shift (n + 1)) (sigma (i - n - 1)))

let rec tm_sub_ok_upn #sg #ln #sigma #g #g' hs ts
  : Tot (tm_sub_ok sg ln (upn_esub (L.length ts) sigma) (push_vars g ts) (push_vars g' ts))
        (decreases ts) =
  match ts with
  | [] ->
    introduce forall (i: nat). upn_esub 0 sigma i == sigma i with ren_tm_shift0 (sigma i);
    tm_sub_ok_ext hs (upn_esub 0 sigma)
  | t :: ts' ->
    let hs2 = tm_sub_ok_upn (tm_sub_ok_up hs t) ts' in
    upn_esub_succ (L.length ts') sigma;
    tm_sub_ok_ext hs2 (upn_esub (L.length ts) sigma)

let tvar_entry (#sg: sig) (#ln: lctx) (#g': ctx) (#e: exp) (#t: typ) (s: sub_entry sg ln g' e t)
  (k: kind)
  : Pure (sub_entry sg ln (push_tvar g' k) (ren_ty_exp (shift 1) e) (ren_ty (shift 1) t))
         (requires sig_ok sg) (ensures fun _ -> True) =
  match s with
  | SE_Var j _ -> nth_map (ren_ty (shift 1)) g'.vars j; SE_Var j ()
  | SE_Val _ hv ->
    is_value_ren_ty sg (shift 1) e;
    let hv' = typing_weaken_tvar hv k in
    assert_norm (ren_jctx (shift 1) [] == []);
    SE_Val () hv'

let tvar_props (sigma: esub) (g g': ctx) (k: kind)
  : Lemma (requires tm_sub_props sigma g g')
          (ensures tm_sub_props (tyup_esub 1 sigma) (push_tvar g k) (push_tvar g' k)) =
  ext_ok_push_tvar g g' k;
  introduce forall (i: nat). V.jp_scoped 0 (tyup_esub 1 sigma i) /\ lc_exp (tyup_esub 1 sigma i)
  with (V.jp_scoped_ren_ty_exp 0 (shift 1) (sigma i); lc_ren_ty_exp 0 (shift 1) (sigma i))

let tm_sub_ok_push_tvar #sg #ln #sigma #g #g' hs k =
  let TmSubOk _ f = hs in
  tvar_props sigma g g' k;
  let f' (i: nat) (t0: typ) (_: squash (L.nth (push_tvar g k).vars i == Some t0))
    : sub_entry sg ln (push_tvar g' k) (tyup_esub 1 sigma i) t0 =
    nth_map (ren_ty (shift 1)) g.vars i;
    let Some t1 = L.nth g.vars i in
    tvar_entry (f i t1 ()) k
  in
  TmSubOk () f'

let tyup_esub_succ (n: nat) (sigma: esub)
  : Lemma (forall (i: nat). tyup_esub n (tyup_esub 1 sigma) i == tyup_esub (n + 1) sigma i) =
  introduce forall (i: nat). tyup_esub n (tyup_esub 1 sigma) i == tyup_esub (n + 1) sigma i
  with ren_ren_ty_exp (shift n) (shift 1) (shift (n + 1)) (sigma i)

let rec tm_sub_ok_push_tvars #sg #ln #sigma #g #g' hs ks
  : Pure (tm_sub_ok sg ln (tyup_esub (L.length ks) sigma) (push_tvars g ks) (push_tvars g' ks))
         (requires sig_ok sg) (ensures fun _ -> True) (decreases ks) =
  match ks with
  | [] ->
    introduce forall (i: nat). tyup_esub 0 sigma i == sigma i with ren_ty_exp_shift0 (sigma i);
    tm_sub_ok_ext hs (tyup_esub 0 sigma)
  | k :: ks' ->
    let hs2 = tm_sub_ok_push_tvars (tm_sub_ok_push_tvar hs k) ks' in
    tyup_esub_succ (L.length ks') sigma;
    tm_sub_ok_ext hs2 (tyup_esub (L.length ks) sigma)

let tm_sub_ok_jup #sg #ln #sigma #g #g' hs =
  tm_sub_ok_props hs;
  introduce forall (i: nat). jup_esub sigma i == sigma i
  with V.ren_jp_scoped 0 (shift 1) (sigma i);
  tm_sub_ok_ext hs (jup_esub sigma)

let tm_sub_ok_assump #sg #ln #sigma #g #g' hs c =
  let TmSubOk _ f = hs in
  ext_ok_assump g g' c;
  add_assump_assumps g' c;
  let f' (i: nat) (t0: typ) (_: squash (L.nth (add_assump g c).vars i == Some t0))
    : sub_entry sg ln (add_assump g' c) (sigma i) t0 =
    match f i t0 () with
    | SE_Var j _ -> SE_Var j ()
    | SE_Val _ hv -> SE_Val () (typing_weaken_assumps hv [c])
  in
  TmSubOk () f'

let enter_region_weaker (g': ctx) (a: atom) (l: layout)
  : Lemma (requires ~(L.mem a (rdom g'))) (ensures ctx_weaker g' (enter_region g' a l)) =
  ctx_ext_enter_region g' a l;
  assoc_none a g'.regions;
  introduce forall (b: atom). (match L.assoc b g'.regions with
                               | Some l0 -> L.assoc b (enter_region g' a l).regions == Some l0
                               | None -> True)
  with (if b = a then () else ())

let tm_sub_ok_enter_region #sg #ln #sigma #g #g' hs a l =
  let TmSubOk _ f = hs in
  ext_ok_enter_region g g' a l;
  enter_region_weaker g' a l;
  let f' (i: nat) (t0: typ) (_: squash (L.nth (enter_region g a l).vars i == Some t0))
    : sub_entry sg ln (enter_region g' a l) (sigma i) t0 =
    match f i t0 () with
    | SE_Var j _ -> SE_Var j ()
    | SE_Val _ hv -> SE_Val () (typing_weaken_ext hv (enter_region g' a l))
  in
  TmSubOk () f'

let tm_sub_ok_fresh #sg #ln #sigma #g #g' hs a body =
  tm_sub_ok_props hs;
  FStar.Classical.move_requires (frn_sub_tm sigma body) a

(* Weakening along the extension. *)

let entails_ext (g g': ctx) (c: constr)
  : Lemma (requires ctx_ext g g' /\ entails (hyps g) c) (ensures entails (hyps g') c) =
  entails_cut_all (hyps g) (hyps g') c

let rec check_tys_ext (sg: sig) (g g': ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires ctx_ext g g' /\ check_tys sg g ts ks) (ensures check_tys sg g' ts ks)
          (decreases ts) =
  match ts, ks with
  | [], [] -> ()
  | t :: ts, k :: ks -> check_weaken sg g g' t k; check_tys_ext sg g g' ts ks

let closed_ext (sg: sig) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires rdom_incl g g' /\ check sg (closed_ctx g.regions) t k)
          (ensures check sg (closed_ctx g'.regions) t k) =
  introduce forall (a: atom). L.mem a (L.map fst g.regions) ==> L.mem a (L.map fst g'.regions)
  with introduce _ ==> _
  with assert (L.mem a (rdom g));
  check_closed_mono sg g.regions g'.regions t k

let occ_typing_sub_tm #sg #g #om #o #t h g' =
  let rec go (#o: occ) (#t: typ) (h: occ_typing sg g om o t)
    : Pure (occ_typing sg g' om o t) (requires ctx_ext g g') (ensures fun _ -> True)
           (decreases h) =
    match h with
    | TO_Lookup sq -> TO_Lookup sq
    | TO_Field #_ #_ #_ #o0 #k #t_o #_ r0 ho _ _ ->
      check_weaken sg g g' r0 (KRow EType);
      check_weaken sg g g' t KType;
      TO_Field #sg #g' #om #o0 #k #t_o #t r0 (go ho) () ()
  in
  go h

(* The rules, one builder each. *)

let tm (sg: sig) (ln: lctx) (g': ctx) (sigma: esub) (d: jctx) (e: exp) (t r: typ)
  : Type =
  typing sg ln g' d (sub_tm sigma e) t r

let cast (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (e': exp{e' == e}) : typing sg ln g d e' t r = h

let b_var (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  (d: jctx) (e: exp) (t r: typ) (i: nat)
  : Pure (tm sg ln g' sigma d e t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ e == EVar i /\ L.nth g.vars i == Some t /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  let TmSubOk _ f = hs in
  check_weaken sg g g' r (KRow EEffect);
  match f i t () with
  | SE_Var j _ -> cast (T_Var #sg #ln #g' #d #j #t #r () ()) (sub_tm sigma e)
  | SE_Val _ hv -> cast (value_typing hv d r) (sub_tm sigma e)

let b_global (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (q: qname) (ks: list kind) (nk: nat) (t0: typ)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EGlobal q ks /\ t == kinst_ty ks t0 /\
                   global_type sg q == Some (nk, t0) /\ L.length ks == nk /\ qkinds_wf g.nk ks /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' r (KRow EEffect);
  T_Global #sg #ln #g' #d #q #ks #nk #t0 #r () () ()

let b_lit (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (c: lit)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ELit c /\ t == lit_type c /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' r (KRow EEffect);
  T_Lit #sg #ln #g' #d #c #r ()

let b_lam (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (t1 r1: typ) (body: exp) (t2: typ)
  (hb: typing sg ln (push_var g' t1) [] (sub_tm (up_esub sigma) body) t2 r1)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ELam t1 r1 body /\ t == t_fun t1 r1 t2 /\
                   check sg g t1 KType /\ check sg g r1 (KRow EEffect) /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' t1 KType;
  check_weaken sg g g' r1 (KRow EEffect);
  check_weaken sg g g' r (KRow EEffect);
  T_Lam #sg #ln #g' #d #t1 #r1 #(sub_tm (up_esub sigma) body) #t2 #r () () hb

let b_app (#sg: sig) (#ln: lctx) (sigma: esub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1 e2: exp) (t1 t2: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (t_fun t1 r t2) r)
  (h2: typing sg ln g' [] (sub_tm sigma e2) t1 r)
  : Pure (tm sg ln g' sigma d e t r) (requires e == EApp e1 e2 /\ t == t2)
         (ensures fun _ -> True) =
  T_App h1 h2

let b_chain (#sg: sig) (#ln: lctx) (sigma: esub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t0: typ) (th: tsub)
  (hc: chain_typing sg ln g' [] r (sub_tm sigma e))
  : Pure (tm sg ln g' sigma d e t r)
         (requires chain_cursor sg e == Some (t0, th) /\ t == sub_ty th t0)
         (ensures fun _ -> True) =
  chain_cursor_sub_tm sg sigma e;
  T_Chain #sg #ln #g' #d #(sub_tm sigma e) #t0 #th #r hc ()

let b_tylam (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: kind) (body: exp) (t0: typ)
  (hb: typing sg ln (push_tvar g' k) [] (sub_tm (tyup_esub 1 sigma) body) t0 TRowEmpty)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ETyLam k body /\ t == TForall k t0 /\
                   kind_wf g.nk k /\ qkind g.nk k /\ value_form sg body /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  value_form_sub_tm sg (tyup_esub 1 sigma) body;
  check_weaken sg g g' r (KRow EEffect);
  T_TyLam #sg #ln #g' #d #k #(sub_tm (tyup_esub 1 sigma) body) #t0 #r () () () hb

let b_tyapp (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1: exp) (s: typ) (k: kind) (t0: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (TForall k t0) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ETyApp e1 s /\ t == subst1_ty s t0 /\
                   check sg g s k)
         (ensures fun _ -> True) =
  check_weaken sg g g' s k;
  T_TyApp #sg #ln #g' #d #(sub_tm sigma e1) #s h1 ()

let b_clam (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (c: constr) (body: exp) (t0: typ)
  (hb: typing sg ln (add_assump g' c) [] (sub_tm sigma body) t0 TRowEmpty)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ECLam c body /\ t == TConstr c t0 /\
                   constr_ok sg g c /\ value_form sg body /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  constr_ok_weaken sg g g' c;
  value_form_sub_tm sg sigma body;
  check_weaken sg g g' r (KRow EEffect);
  T_CLam #sg #ln #g' #d #c #(sub_tm sigma body) #t0 #r () () () hb

let b_capp (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1: exp) (c: constr)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (TConstr c t) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ECApp e1 /\ entails (hyps g) c)
         (ensures fun _ -> True) =
  entails_ext g g' c;
  T_CApp h1 ()

let sub_let_eq (sigma: esub) (t1: typ) (e1 e2: exp)
  : Lemma (sub_tm sigma (ELet t1 e1 e2) == ELet t1 (sub_tm sigma e1) (sub_tm (up_esub sigma) e2)) =
  ()

let b_let (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1: typ) (e1 e2: exp)
  (h1: typing sg ln g' [] (sub_tm sigma e1) t1 r)
  (h2: typing sg ln (push_var g' t1) d (sub_tm (up_esub sigma) e2) t r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ELet t1 e1 e2 /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  sub_let_eq sigma t1 e1 e2;
  check_weaken sg g g' t1 KType;
  T_Let () h1 h2

let b_letrec (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (bs: list (typ & exp)) (body: exp)
  (hbs: binds_typing sg ln (push_vars g' (L.map fst bs))
      (sub_tm_binds (upn_esub (L.length bs) sigma) bs))
  (hb: typing sg ln (push_vars g' (L.map fst bs)) d
      (sub_tm (upn_esub (L.length bs) sigma) body) t r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ELetRec bs body /\
                   Stella.Core.Init.init_safe_letrec sg bs)
         (ensures fun _ -> True) =
  let sn = upn_esub (L.length bs) sigma in
  introduce forall (i: nat). SC.jps_below_exp 0 (sigma i)
  with SC.jp_scoped_jps_below 0 0 (sigma i);
  SI.init_safe_sub_tm sg sigma bs;
  sub_tm_binds_fst sn bs;
  T_LetRec #sg #ln #g' #d #(sub_tm_binds sn bs) #(sub_tm sn body) #t #r () hbs hb

let b_conv (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (t1 r1: typ) (h1: typing sg ln g' d (sub_tm sigma e) t1 r1)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ ty_eq t1 t /\ ty_eq r1 r /\ check sg g t KType /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
  T_Conv h1 () ()

let b_case (#sg: sig) (#ln: lctx) (sigma: esub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (es: list exp) (dt: dtree) (ts: list typ)
  (hes: exps_typing sg ln g' [] r (sub_tm_exps sigma es) ts)
  (hdt: dt_typing sg ln g' d (scrut_occs 0 ts) (sub_tm_dt sigma dt) t r)
  : Pure (tm sg ln g' sigma d e t r) (requires e == ECase es dt) (ensures fun _ -> True) =
  T_Case hes hdt

let b_letjoin (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (ts: list typ) (e1 e2: exp)
  (h1: typing sg ln (push_vars g' ts) ((ts, t, r) :: d)
      (sub_tm (upn_esub (L.length ts) (jup_esub sigma)) e1) t r)
  (h2: typing sg ln g' ((ts, t, r) :: d) (sub_tm (jup_esub sigma) e2) t r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ELetJoin ts t e1 e2 /\ tys_ok sg g ts /\
                   check sg g t KType)
         (ensures fun _ -> True) =
  tys_ok_weaken sg g g' ts;
  check_weaken sg g g' t KType;
  T_LetJoin #sg #ln #g' #d #ts #t #(sub_tm (upn_esub (L.length ts) (jup_esub sigma)) e1)
    #(sub_tm (jup_esub sigma) e2) #r () h1 h2

let b_jump (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (j: nat) (es: list exp) (ts: list typ)
  (hes: exps_typing sg ln g' [] r (sub_tm_exps sigma es) ts)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EJump j es /\
                   L.nth d j == Some (ts, t, r) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
  T_Jump #sg #ln #g' #d #j #(sub_tm_exps sigma es) #ts #t #r () () hes

let b_recempty (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ERecEmpty /\ t == t_record TRowEmpty /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' r (KRow EEffect);
  T_RecEmpty #sg #ln #g' #d #r ()

let b_extend (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (e1 e2: exp) (t1 r0: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) t1 r)
  (h2: typing sg ln g' [] (sub_tm sigma e2) (t_record r0) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EExtend k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t1) r0) /\ key_ok sg g k EType /\
                   entails (hyps g) (CLacks k r0))
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  entails_ext g g' (CLacks k r0);
  T_Extend #sg #ln #g' #d #k h1 h2 ()

let b_select (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (t_record (TRowExt (EntTy k t) r0)) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ESelect k e1 /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  T_Select h1 ()

let b_restrict (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (e1: exp) (t1 r0: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (t_record (TRowExt (EntTy k t1) r0)) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ERestrict k e1 /\ t == t_record r0 /\
                   key_ok sg g k EType)
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  T_Restrict h1 ()

let b_update (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (e1 e2: exp) (t1 t2 r0: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (t_record (TRowExt (EntTy k t1) r0)) r)
  (h2: typing sg ln g' [] (sub_tm sigma e2) t2 r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EUpdate k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t2) r0) /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  T_Update h1 h2 ()

let b_merge (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1 e2: exp) (r1 r2: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (t_record r1) r)
  (h2: typing sg ln g' [] (sub_tm sigma e2) (t_record r2) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EMerge e1 e2 /\
                   t == t_record (TRowUnion r1 r2) /\ entails (hyps g) (CDisj r1 r2))
         (ensures fun _ -> True) =
  entails_ext g g' (CDisj r1 r2);
  T_Merge h1 h2 ()

let b_inject (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (r0: typ) (e1: exp) (t1: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) t1 r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EInject k r0 e1 /\
                   t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\
                   check sg g r0 (KRow EType))
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  entails_ext g g' (CLacks k r0);
  check_weaken sg g g' r0 (KRow EType);
  T_Inject #sg #ln #g' #d #k #r0 h1 () ()

let b_weaken (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (t1: typ) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (t_variant r0) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EWeaken k t1 e1 /\
                   t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  entails_ext g g' (CLacks k r0);
  check_weaken sg g g' t1 KType;
  T_Weaken #sg #ln #g' #d #k #t1 h1 () ()

let b_variant_value (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (v: exp) (pt vr0 vr: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e) (t_variant vr0) r)
  (h2: typing sg ln g' [] (sub_tm sigma v) pt r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ t == t_variant vr /\ V.is_value sg e /\
                   variant_view e == Some (k, v) /\ check sg g (t_variant vr) KType /\
                   check sg g pt KType /\ L.mem (k, PTy (canon pt)) (row_entries (canon vr)))
         (ensures fun _ -> True) =
  is_value_sub_tm sg sigma e;
  variant_view_sub_tm sigma e;
  check_weaken sg g g' (t_variant vr) KType;
  check_weaken sg g g' pt KType;
  T_VariantValue #sg #ln #g' #d #(sub_tm sigma e) #k #(sub_tm sigma v) #pt #r vr0 vr h1 () h2 ()

let b_absurd (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1: exp) (h1: typing sg ln g' [] (sub_tm sigma e1) (t_variant TRowEmpty) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EAbsurd t e1 /\ check sg g t KType)
         (ensures fun _ -> True) =
  check_weaken sg g g' t KType;
  T_Absurd #sg #ln #g' #d #t h1 ()

let b_perform (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (op: opname) (ss: list typ) (e1: exp) (q: qname) (ei: effect_info)
  (os: op_sig) (ts: list typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (op_inst ts ss os.arg) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EPerform k op ss e1 /\
                   t == op_inst ts ss os.res /\
                   L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)) /\
                   sg.effects q == Some ei /\ op_of ei op == Some os /\
                   check_tys sg g ts ei.eff_params /\ check_tys sg g ss os.binders)
         (ensures fun _ -> True) =
  check_tys_ext sg g g' ts ei.eff_params;
  check_tys_ext sg g g' ss os.binders;
  T_Perform #sg #ln #g' #d #k #op #ss #(sub_tm sigma e1) #r #q #ei #os ts () () () h1

let sub_handler (sigma: esub) (hd: handler) : handler =
  { h_ent = hd.h_ent; h_ret_ty = hd.h_ret_ty; h_ret = sub_tm (up_esub sigma) hd.h_ret;
    h_clauses = sub_tm_cls sigma hd.h_clauses }

let b_handle (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1: exp) (hd: handler) (lbl: option string) (q: qname) (ts: list typ)
  (ei: effect_info)
  (h1: typing sg ln g' [] (sub_tm sigma e1) hd.h_ret_ty (TRowExt hd.h_ent r))
  (h2: typing sg ln (push_var g' hd.h_ret_ty) [] (sub_tm (up_esub sigma) hd.h_ret) t r)
  (hcl: clauses_typing sg ln g' ei ts r t (sub_tm_cls sigma hd.h_clauses))
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EHandle e1 hd /\ hd.h_ent == EntEff lbl q ts /\
                   sg.effects q == Some ei /\
                   check sg g (TRowExt hd.h_ent r) (KRow EEffect) /\ check sg g hd.h_ret_ty KType /\
                   check sg g t KType /\ check sg g r (KRow EEffect) /\
                   clauses_cover ei hd.h_clauses)
         (ensures fun _ -> True) =
  let hd' = sub_handler sigma hd in
  check_weaken sg g g' (TRowExt hd.h_ent r) (KRow EEffect);
  check_weaken sg g g' hd.h_ret_ty KType;
  check_weaken sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  clause_ops_sub_tm sigma hd.h_clauses;
  let h1 : typing sg ln g' [] (sub_tm sigma e1) hd'.h_ret_ty (TRowExt hd'.h_ent r) = h1 in
  let h2 : typing sg ln (push_var g' hd'.h_ret_ty) [] hd'.h_ret t r = h2 in
  let hcl : clauses_typing sg ln g' ei ts r t hd'.h_clauses = hcl in
  T_Handle #sg #ln #g' #d #(sub_tm sigma e1) #hd' #t #r #lbl #q #ts #ei () () () () h1 h2 hcl

let b_openeff (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (r2: typ) (e1: exp) (t1 r1 t2: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) (t_fun t1 r1 t2) r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EOpenEff r2 e1 /\
                   t == t_fun t1 (TRowUnion r1 r2) t2 /\
                   entails (hyps g) (CDisj r1 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  entails_ext g g' (CDisj r1 r2);
  check_weaken sg g g' r2 (KRow EEffect);
  T_OpenEff #sg #ln #g' #d #r2 h1 ()

let b_region (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (lay: layout) (es: list exp) (body: exp)
  (hes: exps_typing sg ln g' [] r (sub_tm_exps sigma es) (L.map snd lay))
  (hb: (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (sub_tm sigma body)))} ->
        typing sg ln (enter_region g' a lay) [] (sub_tm sigma (open_region a body)) t
          (TRowExt (EntRegion (RFree a)) r)))
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ERegion lay es body /\
                   check sg g (layout_row lay) (KRow EType) /\ L.noRepeats (L.map fst lay) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  let body' = sub_tm sigma body in
  check_weaken sg g g' (layout_row lay) (KRow EType);
  check_weaken sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  let hb' (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp body'))})
    : typing sg ln (enter_region g' a lay) [] (open_region a body') t
        (TRowExt (EntRegion (RFree a)) r) =
    open_region_sub_tm 0 a sigma body;
    hb a
  in
  T_Region #sg #ln #g' #d #lay #(sub_tm_exps sigma es) #body' #t #r () () hes hb'

let b_readcell (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (a: atom) (k: key) (lay: layout)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EReadCell (RFree a) k /\
                   L.assoc a g.regions == Some lay /\
                   L.assoc k lay == Some t /\ L.mem (RegionKey (RFree a)) (known_keys r) /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  check_weaken sg g g' r (KRow EEffect);
  T_ReadCell #sg #ln #g' #d #a #k #lay #t #r () () ()

let b_writecell (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (a: atom) (k: key) (e1: exp) (lay: layout) (t1: typ)
  (h1: typing sg ln g' [] (sub_tm sigma e1) t1 r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EWriteCell (RFree a) k e1 /\ t == t_unit /\
                   L.assoc a g.regions == Some lay /\ L.assoc k lay == Some t1 /\
                   L.mem (RegionKey (RFree a)) (known_keys r))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  T_WriteCell #sg #ln #g' #d #a #k #(sub_tm sigma e1) #lay #t1 #r () () h1

let b_match (#sg: sig) (#ln: lctx) (sigma: esub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (th: list exp) (dt: dtree) (ts: list typ) (om: octx)
  (hes: exps_typing sg ln g' [] r (sub_tm_exps sigma th) ts)
  (hm: match_typing sg ln g' [] r (sub_tm_exps sigma th) om)
  (hdt: dt_typing sg ln g' d om (sub_tm_dt sigma dt) t r)
  : Pure (tm sg ln g' sigma d e t r)
         (requires e == EMatch th dt /\ L.for_all (V.is_value sg) th)
         (ensures fun _ -> True) =
  values_sub_tm sg sigma th;
  T_Match om hes () hm hdt

let b_openeffc (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (r2: typ) (e1: exp) (r0: typ) (h1: typing sg ln g' [] (sub_tm sigma e1) t r0)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EOpenEffC r2 e1 /\ r == TRowUnion r0 r2 /\
                   entails (hyps g) (CDisj r0 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  entails_ext g g' (CDisj r0 r2);
  check_weaken sg g g' r2 (KRow EEffect);
  T_OpenEffC #sg #ln #g' #d #r2 h1 ()

let b_force (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (nu: atom)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EForce nu /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_ext sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  T_Force #sg #ln #g' #d #nu #t #r () ()

let b_fill (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (nu: atom) (e1: exp) (h1: typing sg ln g' [] (sub_tm sigma e1) t TRowEmpty)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EFill nu e1 /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_ext sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  T_Fill #sg #ln #g' #d #nu #(sub_tm sigma e1) #t #r () () h1

let b_region_open (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (a: atom) (cells: list (key & exp)) (body: exp) (lay: layout)
  (hc: cells_typing sg ln g' (sub_tm_cells sigma cells) lay)
  (hb: typing sg ln g' [] (sub_tm sigma body) t (TRowExt (EntRegion (RFree a)) r))
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == ERegionOpen a cells body /\
                   L.assoc a g.regions == Some lay /\
                   check sg (closed_ctx g.regions) t KType /\
                   check sg (closed_ctx g.regions) r (KRow EEffect) /\
                   ~(L.mem a (frn_ty t @ frn_ty r)))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  closed_ext sg g g' t KType;
  closed_ext sg g g' r (KRow EEffect);
  T_RegionOpen #sg #ln #g' #d #a #(sub_tm_cells sigma cells) #(sub_tm sigma body) #lay #t #r
    () () () hc hb

let b_opaque (#sg: sig) (#ln: lctx) (sigma: esub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (w: nat)
  : Pure (tm sg ln g' sigma d e t r)
         (requires tm_sub_props sigma g g' /\ e == EOpaque w t /\ opaque_type sg t /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  T_Opaque #sg #ln #g' #d #w #t #r () ()

(* Well-formedness of the extended contexts. *)

let wf_push_var (sg: sig) (g g': ctx) (t: typ)
  : Lemma (requires wf_ctx sg g' /\ ctx_ext g g' /\ check sg g t KType)
          (ensures wf_ctx sg (push_var g' t)) =
  check_weaken sg g g' t KType;
  wf_ctx_push_var sg g' t

let wf_push_vars (sg: sig) (g g': ctx) (ts: list typ)
  : Lemma (requires wf_ctx sg g' /\ ctx_ext g g' /\ tys_ok sg g ts)
          (ensures wf_ctx sg (push_vars g' ts)) =
  tys_ok_weaken sg g g' ts;
  wf_ctx_push_vars sg g' ts

(* The members of a `letrec` are kinded in the context they extend. *)
let wf_push_members (sg: sig) (ln: lctx) (g g': ctx) (bs: list (typ & exp))
  (hbs: binds_typing sg ln (push_vars g (L.map fst bs)) bs)
  : Lemma (requires wf_ctx sg g' /\ ctx_ext g g')
          (ensures wf_ctx sg (push_vars g' (L.map fst bs))) =
  binds_typing_regular hbs;
  ctx_ext_push_vars_left g g' (L.map fst bs);
  tys_ok_weaken sg (push_vars g (L.map fst bs)) g' (L.map fst bs);
  wf_ctx_push_vars sg g' (L.map fst bs)

let ctor_branch_ok (sg: sig) (g': ctx) (om: octx) (o: occ) (ks: list kind) (ss: list typ)
  (cs: list qname) (c: qname) (fs: list typ)
  : Lemma (requires sig_ok sg /\ octx_ok sg g' om /\
                    (exists (tq: qname). check sg g' (tapps (TCon tq ks) ss) KType /\
                       has_class sg tq (TcData cs)) /\
                    L.mem c cs /\ ctor_fields sg c ks ss == Some fs)
          (ensures octx_ok sg g' (L.append (field_occs o c 0 fs) om)) =
  eliminate exists (tq: qname). check sg g' (tapps (TCon tq ks) ss) KType /\
    has_class sg tq (TcData cs)
  with octx_ok_ctor_branch sg g' om o tq ks ss cs c fs

let clause_binders_ok (sg: sig) (g': ctx) (ei: effect_info) (op: opname) (os: op_sig)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g' /\ (exists (q: qname). sg.effects q == Some ei) /\
                    op_of ei op == Some os)
          (ensures wf_ctx sg (push_tvars g' os.binders)) =
  eliminate exists (q: qname). sg.effects q == Some ei
  with wf_ctx_clause_binders sg g' q ei op os

let data_ex (sg: sig) (g': ctx) (tq: qname) (ks: list kind) (ss: list typ) (cs: list qname)
  : Lemma (requires check sg g' (tapps (TCon tq ks) ss) KType /\ has_class sg tq (TcData cs))
          (ensures exists (tq0: qname). check sg g' (tapps (TCon tq0 ks) ss) KType /\
                     has_class sg tq0 (TcData cs)) = ()

let effect_ex (sg: sig) (q: qname) (ei: effect_info)
  : Lemma (requires sg.effects q == Some ei)
          (ensures exists (q0: qname). sg.effects q0 == Some ei) = ()

let sub_tyapp_eq (sigma: esub) (e0: exp) (s: typ)
  : Lemma (sub_tm sigma (ETyApp e0 s) == ETyApp (sub_tm sigma e0) s) = ()

let sub_capp_eq (sigma: esub) (e0: exp)
  : Lemma (sub_tm sigma (ECApp e0) == ECApp (sub_tm sigma e0)) = ()

let sub_app_eq (sigma: esub) (e0 v: exp)
  : Lemma (sub_tm sigma (EApp e0 v) == EApp (sub_tm sigma e0) (sub_tm sigma v)) = ()

(* The mutual induction. *)

let rec typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (sigma: esub) (g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (typing sg ln g' d (sub_tm sigma e) t r)
         (requires sig_ok sg /\ wf_ctx sg g')
         (ensures fun _ -> True) (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | T_Var #_ #_ #_ #_ #i _ _ -> b_var sigma g g' hs d e t r i
  | T_Global #_ #_ #_ #_ #q #ks #nk #t0 _ _ _ -> b_global sigma g g' d e t r q ks nk t0
  | T_Lit #_ #_ #_ #_ #c _ -> b_lit sigma g g' d e t r c
  | T_Lam #_ #_ #_ #_ #t1 #r1 #body #t2 _ _ hb ->
    wf_push_var sg g g' t1;
    b_lam sigma g g' d e t r t1 r1 body t2
      (typing_sub_tm' hb (up_esub sigma) (push_var g' t1) (tm_sub_ok_up hs t1))
  | T_App #_ #_ #_ #_ #e1 #e2 #t1 #t2 h1 h2 ->
    b_app sigma g' d e t r e1 e2 t1 t2 (typing_sub_tm' h1 sigma g' hs)
      (typing_sub_tm' h2 sigma g' hs)
  | T_Chain #_ #_ #_ #_ #_ #t0 #th hc _ ->
    b_chain sigma g' d e t r t0 th (chain_typing_sub_tm' hc sigma g' hs)
  | T_TyLam #_ #_ #_ #_ #k #body #t0 _ _ _ hb ->
    wf_ctx_push_tvar sg g' k;
    b_tylam sigma g g' d e t r k body t0
      (typing_sub_tm' hb (tyup_esub 1 sigma) (push_tvar g' k) (tm_sub_ok_push_tvar hs k))
  | T_TyApp #_ #_ #_ #_ #e1 #s #k #t0 h1 _ ->
    b_tyapp sigma g g' d e t r e1 s k t0 (typing_sub_tm' h1 sigma g' hs)
  | T_CLam #_ #_ #_ #_ #c #body #t0 _ _ _ hb ->
    constr_ok_weaken sg g g' c;
    wf_ctx_add_assump sg g' c;
    b_clam sigma g g' d e t r c body t0
      (typing_sub_tm' hb sigma (add_assump g' c) (tm_sub_ok_assump hs c))
  | T_CApp #_ #_ #_ #_ #e1 #c h1 _ ->
    b_capp sigma g g' d e t r e1 c (typing_sub_tm' h1 sigma g' hs)
  | T_Let #_ #_ #_ #_ #t1 #e1 #e2 _ h1 h2 ->
    wf_push_var sg g g' t1;
    b_let sigma g g' d e t r t1 e1 e2 (typing_sub_tm' h1 sigma g' hs)
      (typing_sub_tm' h2 (up_esub sigma) (push_var g' t1) (tm_sub_ok_up hs t1))
  | T_LetRec #_ #_ #_ #_ #bs #body _ hbs hb ->
    let ts = L.map fst bs in
    let sn = upn_esub (L.length bs) sigma in
    LP.map_lemma fst bs;
    wf_push_members sg ln g g' bs hbs;
    let gb' = push_vars g' ts in
    let hsn = tm_sub_ok_ext (tm_sub_ok_upn hs ts) sn in
    b_letrec sigma g g' d e t r bs body (binds_typing_sub_tm' hbs sn gb' hsn)
      (typing_sub_tm' hb sn gb' hsn)
  | T_Conv #_ #_ #_ #_ #_ #t1 #r1 h1 _ _ ->
    b_conv sigma g g' d e t r t1 r1 (typing_sub_tm' h1 sigma g' hs)
  | T_Case #_ #_ #_ #_ #es #dt #ts hes hdt ->
    let hes' = exps_typing_sub_tm' hes sigma g' hs in
    case_octx_ok hes';
    b_case sigma g' d e t r es dt ts hes' (dt_typing_sub_tm' hdt sigma g' hs)
  | T_LetJoin #_ #_ #_ #_ #ts #_ #e1 #e2 _ h1 h2 ->
    wf_push_vars sg g g' ts;
    let hsj = tm_sub_ok_jup hs in
    b_letjoin sigma g g' d e t r ts e1 e2
      (typing_sub_tm' h1 (upn_esub (L.length ts) (jup_esub sigma)) (push_vars g' ts)
        (tm_sub_ok_upn hsj ts))
      (typing_sub_tm' h2 (jup_esub sigma) g' hsj)
  | T_Jump #_ #_ #_ #_ #j #es #ts _ _ hes ->
    b_jump sigma g g' d e t r j es ts (exps_typing_sub_tm' hes sigma g' hs)
  | T_RecEmpty _ -> b_recempty sigma g g' d e t r
  | T_Extend #_ #_ #_ #_ #k #e1 #e2 #t1 #r0 h1 h2 _ ->
    b_extend sigma g g' d e t r k e1 e2 t1 r0 (typing_sub_tm' h1 sigma g' hs)
      (typing_sub_tm' h2 sigma g' hs)
  | T_Select #_ #_ #_ #_ #k #e1 #_ #r0 h1 _ ->
    b_select sigma g g' d e t r k e1 r0 (typing_sub_tm' h1 sigma g' hs)
  | T_Restrict #_ #_ #_ #_ #k #e1 #t1 #r0 h1 _ ->
    b_restrict sigma g g' d e t r k e1 t1 r0 (typing_sub_tm' h1 sigma g' hs)
  | T_Update #_ #_ #_ #_ #k #e1 #e2 #t1 #t2 #r0 h1 h2 _ ->
    b_update sigma g g' d e t r k e1 e2 t1 t2 r0 (typing_sub_tm' h1 sigma g' hs)
      (typing_sub_tm' h2 sigma g' hs)
  | T_Merge #_ #_ #_ #_ #e1 #e2 #r1 #r2 h1 h2 _ ->
    b_merge sigma g g' d e t r e1 e2 r1 r2 (typing_sub_tm' h1 sigma g' hs)
      (typing_sub_tm' h2 sigma g' hs)
  | T_Inject #_ #_ #_ #_ #k #r0 #e1 #t1 h1 _ _ ->
    b_inject sigma g g' d e t r k r0 e1 t1 (typing_sub_tm' h1 sigma g' hs)
  | T_Weaken #_ #_ #_ #_ #k #t1 #e1 #r0 h1 _ _ ->
    b_weaken sigma g g' d e t r k t1 e1 r0 (typing_sub_tm' h1 sigma g' hs)
  | T_VariantValue #_ #_ #_ #_ #_ #k #v #pt vr0 vr h1 _ h2 _ ->
    b_variant_value sigma g g' d e t r k v pt vr0 vr (typing_sub_tm' h1 sigma g' hs)
      (typing_sub_tm' h2 sigma g' hs)
  | T_Absurd #_ #_ #_ #_ #_ #e1 h1 _ ->
    b_absurd sigma g g' d e t r e1 (typing_sub_tm' h1 sigma g' hs)
  | T_Perform #_ #_ #_ #_ #k #op #ss #e1 #_ #q #ei #os ts _ _ _ h1 ->
    b_perform sigma g g' d e t r k op ss e1 q ei os ts (typing_sub_tm' h1 sigma g' hs)
  | T_Handle #_ #_ #_ #_ #e1 #hd #_ #_ #lbl #q #ts #ei _ _ _ _ h1 h2 hcl ->
    wf_push_var sg g g' hd.h_ret_ty;
    effect_ex sg q ei;
    b_handle sigma g g' d e t r e1 hd lbl q ts ei (typing_sub_tm' h1 sigma g' hs)
      (typing_sub_tm' h2 (up_esub sigma) (push_var g' hd.h_ret_ty) (tm_sub_ok_up hs hd.h_ret_ty))
      (clauses_typing_sub_tm' hcl sigma g' hs)
  | T_OpenEff #_ #_ #_ #_ #r2 #e1 #t1 #r1 #t2 h1 _ ->
    b_openeff sigma g g' d e t r r2 e1 t1 r1 t2 (typing_sub_tm' h1 sigma g' hs)
  | T_Region #_ #_ #_ #_ #lay #es #body _ _ hes hbody ->
    check_weaken sg g g' (layout_row lay) (KRow EType);
    layout_row_ok sg g' lay;
    let hb' (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (sub_tm sigma body)))})
      : typing sg ln (enter_region g' a lay) [] (sub_tm sigma (open_region a body)) t
          (TRowExt (EntRegion (RFree a)) r) =
      tm_sub_ok_fresh hs a body;
      wf_ctx_enter_region sg g' a lay;
      typing_sub_tm' (hbody a) sigma (enter_region g' a lay) (tm_sub_ok_enter_region hs a lay)
    in
    b_region sigma g g' d e t r lay es body (exps_typing_sub_tm' hes sigma g' hs) hb'
  | T_ReadCell #_ #_ #_ #_ #a #k #lay _ _ _ -> b_readcell sigma g g' d e t r a k lay
  | T_WriteCell #_ #_ #_ #_ #a #k #e1 #lay #t1 _ _ h1 ->
    b_writecell sigma g g' d e t r a k e1 lay t1 (typing_sub_tm' h1 sigma g' hs)
  | T_Match #_ #_ #_ #_ #th #dt #ts om hes _ hm hdt ->
    let hm' = match_typing_sub_tm' hm sigma g' hs in
    match_typing_regular hm';
    b_match sigma g' d e t r th dt ts om (exps_typing_sub_tm' hes sigma g' hs) hm'
      (dt_typing_sub_tm' hdt sigma g' hs)
  | T_OpenEffC #_ #_ #_ #_ #r2 #e1 #_ #r0 h1 _ ->
    b_openeffc sigma g g' d e t r r2 e1 r0 (typing_sub_tm' h1 sigma g' hs)
  | T_Force #_ #_ #_ #_ #nu _ _ -> b_force sigma g g' d e t r nu
  | T_Fill #_ #_ #_ #_ #nu #e1 _ _ h1 ->
    b_fill sigma g g' d e t r nu e1 (typing_sub_tm' h1 sigma g' hs)
  | T_RegionOpen #_ #_ #_ #_ #a #cells #body #lay _ _ _ hc hb ->
    b_region_open sigma g g' d e t r a cells body lay (cells_typing_sub_tm' hc sigma g' hs)
      (typing_sub_tm' hb sigma g' hs)
  | T_Opaque #_ #_ #_ #_ #w _ _ -> b_opaque sigma g g' d e t r w

and exps_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (sigma: esub) (g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (exps_typing sg ln g' d r (sub_tm_exps sigma es) ts)
         (requires sig_ok sg /\ wf_ctx sg g') (ensures fun _ -> True) (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TE_Nil _ -> check_weaken sg g g' r (KRow EEffect); TE_Nil ()
  | TE_Cons h1 h2 -> TE_Cons (typing_sub_tm' h1 sigma g' hs) (exps_typing_sub_tm' h2 sigma g' hs)

and chain_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (sigma: esub) (g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (chain_typing sg ln g' d r (sub_tm sigma e))
         (requires sig_ok sg /\ wf_ctx sg g') (ensures fun _ -> True) (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TS_Head #_ #_ #_ #_ #_ #q #ks #c #nk #t0 _ _ _ ->
    check_weaken sg g g' r (KRow EEffect);
    TS_Head #sg #ln #g' #d #r #q #ks #c #nk #t0 () () ()
  | TS_Ty #_ #_ #_ #_ #_ #e0 #s #k #t0 #th h0 _ _ ->
    chain_cursor_sub_tm sg sigma e0;
    sub_tyapp_eq sigma e0 s;
    check_weaken sg g g' s k;
    TS_Ty #sg #ln #g' #d #r #(sub_tm sigma e0) #s #k #t0 #th (chain_typing_sub_tm' h0 sigma g' hs)
      () ()
  | TS_Constr #_ #_ #_ #_ #_ #e0 #c #t0 #th h0 _ _ ->
    chain_cursor_sub_tm sg sigma e0;
    sub_capp_eq sigma e0;
    entails_ext g g' (sub_constr th c);
    TS_Constr #sg #ln #g' #d #r #(sub_tm sigma e0) #c #t0 #th
      (chain_typing_sub_tm' h0 sigma g' hs) () ()
  | TS_Val #_ #_ #_ #_ #_ #e0 #v #t0 #th #t1 #r1 #t2 h0 _ hv ->
    chain_cursor_sub_tm sg sigma e0;
    sub_app_eq sigma e0 v;
    TS_Val #sg #ln #g' #d #r #(sub_tm sigma e0) #(sub_tm sigma v) #t0 #th #t1 #r1 #t2
      (chain_typing_sub_tm' h0 sigma g' hs) () (typing_sub_tm' hv sigma g' hs)

and binds_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (sigma: esub) (g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (binds_typing sg ln g' (sub_tm_binds sigma bs))
         (requires sig_ok sg /\ wf_ctx sg g') (ensures fun _ -> True) (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TB_Nil -> TB_Nil
  | TB_Cons #_ #_ #_ #t0 #e0 #_ _ h1 h2 ->
    check_weaken sg g g' t0 KType;
    TB_Cons () (typing_sub_tm' h1 sigma g' hs) (binds_typing_sub_tm' h2 sigma g' hs)

and cells_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp))
  (#lay: layout) (h: cells_typing sg ln g cells lay) (sigma: esub) (g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (cells_typing sg ln g' (sub_tm_cells sigma cells) lay)
         (requires sig_ok sg /\ wf_ctx sg g') (ensures fun _ -> True) (decreases h) =
  match h with
  | TC_Nil -> TC_Nil
  | TC_Cons #_ #_ #_ #k #v #t0 #cs0 #lay0 _ h1 h2 ->
    is_value_sub_tm sg sigma v;
    TC_Cons #sg #ln #g' #k #(sub_tm sigma v) #t0 #(sub_tm_cells sigma cs0) #lay0 ()
      (typing_sub_tm' h1 sigma g' hs)
      (cells_typing_sub_tm' h2 sigma g' hs)

and match_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om) (sigma: esub) (g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (match_typing sg ln g' d r (sub_tm_exps sigma th) om)
         (requires sig_ok sg /\ wf_ctx sg g') (ensures fun _ -> True) (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TM_Nil _ -> check_weaken sg g g' r (KRow EEffect); TM_Nil ()
  | TM_Cons #_ #_ #_ #_ #_ #_ #o #t0 #om0 #v _ h1 h2 ->
    proj_sub_tm sg sigma th o v;
    TM_Cons #sg #ln #g' #d #r #(sub_tm_exps sigma th) #o #t0 #om0 #(sub_tm sigma v) ()
      (typing_sub_tm' h1 sigma g' hs) (match_typing_sub_tm' h2 sigma g' hs)

and dt_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (sigma: esub) (g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (dt_typing sg ln g' d om (sub_tm_dt sigma dt) t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ octx_ok sg g' om) (ensures fun _ -> True)
         (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TD_Leaf h1 -> TD_Leaf (typing_sub_tm' h1 sigma g' hs)
  | TD_Bind #_ #_ #_ #_ #_ #o #dt0 #t_o ho hdt ->
    let ho' = occ_typing_sub_tm ho g' in
    occ_typing_regular ho';
    wf_ctx_push_var sg g' t_o;
    ctx_ext_push_var g' t_o;
    octx_ok_weaken sg g' (push_var g' t_o) om;
    TD_Bind ho' (dt_typing_sub_tm' hdt (up_esub sigma) (push_var g' t_o) (tm_sub_ok_up hs t_o))
  | TD_SwitchCtor #_ #_ #_ #_ #_ #o #bs #t_o tq ks ss cs ho _ _ _ hbr ->
    check_weaken sg g g' (tapps (TCon tq ks) ss) KType;
    data_ex sg g' tq ks ss cs;
    sub_tm_brs_labels sigma bs;
    TD_SwitchCtor tq ks ss cs (occ_typing_sub_tm ho g') () () ()
      (ctor_brs_typing_sub_tm' hbr sigma g' hs)
  | TD_SwitchCtorDef #_ #_ #_ #_ #_ #o #bs #df #t_o tq ks ss cs ho _ _ _ hbr hdf ->
    check_weaken sg g g' (tapps (TCon tq ks) ss) KType;
    data_ex sg g' tq ks ss cs;
    sub_tm_brs_labels sigma bs;
    TD_SwitchCtorDef tq ks ss cs (occ_typing_sub_tm ho g') () () ()
      (ctor_brs_typing_sub_tm' hbr sigma g' hs) (dt_typing_sub_tm' hdf sigma g' hs)
  | TD_SwitchLit #_ #_ #_ #_ #_ #o #bs #df #t_o lq ho _ _ hbr hdf ->
    sub_tm_brs_labels sigma bs;
    TD_SwitchLit lq (occ_typing_sub_tm ho g') () () (lit_brs_typing_sub_tm' hbr sigma g' hs)
      (dt_typing_sub_tm' hdf sigma g' hs)
  | TD_SwitchKey #_ #_ #_ #_ #_ #o #bs #t_o vr kts ho _ _ _ hbr ->
    check_weaken sg g g' vr (KRow EType);
    sub_tm_brs_labels sigma bs;
    TD_SwitchKey vr kts (occ_typing_sub_tm ho g') () () () (key_brs_typing_sub_tm' hbr sigma g' hs)
  | TD_SwitchKeyDef #_ #_ #_ #_ #_ #o #bs #df #t_o vr vr' kts ho _ _ _ hbr hdf ->
    check_weaken sg g g' vr (KRow EType);
    check_weaken sg g g' vr' (KRow EType);
    sub_tm_brs_labels sigma bs;
    octx_ok_key_default sg g' om o vr';
    TD_SwitchKeyDef vr vr' kts (occ_typing_sub_tm ho g') () () ()
      (key_brs_typing_sub_tm' hbr sigma g' hs)
      (dt_typing_sub_tm' hdf sigma g' hs)
  | TD_Guard h1 h2 h3 ->
    TD_Guard (typing_sub_tm' h1 sigma g' hs) (dt_typing_sub_tm' h2 sigma g' hs)
      (dt_typing_sub_tm' h3 sigma g' hs)

and ctor_brs_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ) (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (sigma: esub) (g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (ctor_brs_typing sg ln g' d om o ks ss cs (sub_tm_brs sigma bs) t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ octx_ok sg g' om /\
                   (exists (tq: qname). check sg g' (tapps (TCon tq ks) ss) KType /\
                      has_class sg tq (TcData cs)))
         (ensures fun _ -> True) (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TCB_Nil _ ->
    check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
    TCB_Nil ()
  | TCB_Cons #_ #_ #_ #_ #_ #_ #_ #_ #_ #c #_ #_ #_ #_ #fs sq hdt h2 ->
    ctor_branch_ok sg g' om o ks ss cs c fs;
    TCB_Cons sq (dt_typing_sub_tm' hdt sigma g' hs) (ctor_brs_typing_sub_tm' h2 sigma g' hs)

and lit_brs_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (sigma: esub) (g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (lit_brs_typing sg ln g' d om lt (sub_tm_brs sigma bs) t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ octx_ok sg g' om) (ensures fun _ -> True)
         (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TLB_Nil _ ->
    check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
    TLB_Nil ()
  | TLB_Cons sq hdt h2 ->
    TLB_Cons sq (dt_typing_sub_tm' hdt sigma g' hs) (lit_brs_typing_sub_tm' h2 sigma g' hs)

and key_brs_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (sigma: esub) (g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (key_brs_typing sg ln g' d om o kts (sub_tm_brs sigma bs) t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ octx_ok sg g' om) (ensures fun _ -> True)
         (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TKB_Nil _ ->
    check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
    TKB_Nil ()
  | TKB_Cons #_ #_ #_ #_ #_ #_ #k #pt _ hdt h2 ->
    check_weaken sg g g' pt KType;
    octx_ok_key_branch sg g' om o k pt;
    TKB_Cons #sg #ln #g' #d #om #o #k #pt () (dt_typing_sub_tm' hdt sigma g' hs)
      (key_brs_typing_sub_tm' h2 sigma g' hs)

and clauses_typing_sub_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs) (sigma: esub)
  (g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (clauses_typing sg ln g' ei ts r b (sub_tm_cls sigma cs))
         (requires sig_ok sg /\ wf_ctx sg g' /\ (exists (q: qname). sg.effects q == Some ei))
         (ensures fun _ -> True) (decreases h) =
  tm_sub_ok_props hs;
  match h with
  | TCL_Nil _ ->
    check_weaken sg g g' b KType; check_weaken sg g g' r (KRow EEffect);
    TCL_Nil ()
  | TCL_Full #_ #_ #_ #_ #_ #_ #_ #op #nb #s #kt #body #cs0 #os _ _ _ hb hcs ->
    let gb = push_tvars g os.binders in
    let gb' = push_tvars g' os.binders in
    let hsb = tm_sub_ok_push_tvars hs os.binders in
    tm_sub_ok_props hsb;
    clause_binders_ok sg g' ei op os;
    wf_push_var sg gb gb' s;
    check_weaken sg gb gb' s KType;
    check_weaken sg gb gb' kt KType;
    ctx_ext_push_var gb' s;
    check_weaken sg gb' (push_var gb' s) kt KType;
    wf_ctx_push_var sg (push_var gb' s) kt;
    let hsk = tm_sub_ok_upn hsb [s; kt] in
    let sk = upn_esub 2 (tyup_esub nb sigma) in
    TCL_Full #sg #ln #g' #ei #ts #r #b #op #nb #s #kt #(sub_tm sk body) #(sub_tm_cls sigma cs0)
      #os () () () (typing_sub_tm' hb sk (push_var (push_var gb' s) kt) hsk)
      (clauses_typing_sub_tm' hcs sigma g' hs)
  | TCL_Fast #_ #_ #_ #_ #_ #_ #_ #op #nb #s #body #cs0 #os _ _ hb hcs ->
    let gb = push_tvars g os.binders in
    let gb' = push_tvars g' os.binders in
    let hsb = tm_sub_ok_push_tvars hs os.binders in
    tm_sub_ok_props hsb;
    clause_binders_ok sg g' ei op os;
    wf_push_var sg gb gb' s;
    check_weaken sg gb gb' s KType;
    TCL_Fast #sg #ln #g' #ei #ts #r #b #op #nb #s #(sub_tm (up_esub (tyup_esub nb sigma)) body)
      #(sub_tm_cls sigma cs0)
      #os () () (typing_sub_tm' hb (up_esub (tyup_esub nb sigma)) (push_var gb' s)
        (tm_sub_ok_up hsb s))
      (clauses_typing_sub_tm' hcs sigma g' hs)

(* The stated theorems. *)

let typing_sub_tm #sg #ln #g #d #e #t #r h #sigma #g' hs = typing_sub_tm' h sigma g' hs

let exps_typing_sub_tm #sg #ln #g #d #r #es #ts h #sigma #g' hs =
  exps_typing_sub_tm' h sigma g' hs

let chain_typing_sub_tm #sg #ln #g #d #r #e h #sigma #g' hs = chain_typing_sub_tm' h sigma g' hs

let binds_typing_sub_tm #sg #ln #g #bs h #sigma #g' hs = binds_typing_sub_tm' h sigma g' hs

let cells_typing_sub_tm #sg #ln #g #cells #lay h #sigma #g' hs =
  cells_typing_sub_tm' h sigma g' hs

let match_typing_sub_tm #sg #ln #g #d #r #th #om h #sigma #g' hs =
  match_typing_sub_tm' h sigma g' hs

let dt_typing_sub_tm #sg #ln #g #d #om #dt #t #r h #sigma #g' hs =
  dt_typing_sub_tm' h sigma g' hs

let ctor_brs_typing_sub_tm #sg #ln #g #d #om #o #ks #ss #cs #bs #t #r h #sigma #g' hs =
  ctor_brs_typing_sub_tm' h sigma g' hs

let lit_brs_typing_sub_tm #sg #ln #g #d #om #lt #bs #t #r h #sigma #g' hs =
  lit_brs_typing_sub_tm' h sigma g' hs

let key_brs_typing_sub_tm #sg #ln #g #d #om #o #kts #bs #t #r h #sigma #g' hs =
  key_brs_typing_sub_tm' h sigma g' hs

let clauses_typing_sub_tm #sg #ln #g #ei #ts #r #b #cs h #sigma #g' hs =
  clauses_typing_sub_tm' h sigma g' hs
