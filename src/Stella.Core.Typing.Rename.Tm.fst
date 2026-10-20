(* Proof structure.

   The context lemmas: a term binder extends both variable lists at the
   head, which `up_ren` fixes; a type binder shifts the stored types of
   both contexts by the same renaming, and entailment is preserved by it
   (`entails_ren`); an assumption and a region add the same hypotheses to
   both contexts, `Γ'` reading them where `Γ` does.

   The judgements are one mutual induction on the derivation, as in
   `Stella.Core.Typing.Rename.Ty`: each rule of `typing` has a builder that
   takes the renamed premises and concludes the renamed judgement, so that
   the side conditions are discharged in the small context of the builder.
   Kinding, entailment and the closed kinding of run-time types weaken
   along `ctx_ext`; the term-level facts are those of
   `Stella.Core.Typing.Rename.Facts`. *)
module Stella.Core.Typing.Rename.Tm
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
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
open Stella.Core.Typing.Rename.Facts
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value
module IR = Stella.Core.Init.Rename

(* Lists. *)

let rec nth_map (#a #b: Type) (f: a -> b) (l: list a) (i: nat)
  : Lemma (ensures L.nth (L.map f l) i == map_opt f (L.nth l i)) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> if i = 0 then () else nth_map f l (i - 1)

let rec nth_length (#a: Type) (l: list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures i < L.length l) (decreases l) =
  match l with
  | _ :: tl -> if i = 0 then () else nth_length tl (i - 1)

let rec nth_some (#a: Type) (l: list a) (i: nat)
  : Lemma (requires i < L.length l) (ensures Some? (L.nth l i)) (decreases l) =
  match l with
  | _ :: tl -> if i = 0 then () else nth_some tl (i - 1)

let rec assoc_ren_regions (xi: ren) (rs: list (atom & layout)) (a: atom)
  : Lemma (ensures L.assoc a (L.map (ren_region xi) rs) == map_opt (ren_layout xi) (L.assoc a rs))
          (decreases rs) =
  match rs with
  | [] -> ()
  | _ :: rs -> assoc_ren_regions xi rs a

let rec map_wit (#a #b: eqtype) (f: a -> b) (l: list a) (y: b)
  : Pure a (requires L.mem y (L.map f l)) (ensures fun x -> L.mem x l /\ f x == y) (decreases l) =
  match l with
  | x :: tl -> if f x = y then x else map_wit f tl y

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

let rec tys_ok_ext (sg: sig) (g g': ctx) (ts: list typ)
  : Lemma (requires ctx_ext g g' /\ tys_ok sg g ts) (ensures tys_ok sg g' ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> check_weaken sg g g' t KType; tys_ok_ext sg g g' ts

let closed_ext (sg: sig) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires rdom_incl g g' /\ check sg (closed_ctx g.regions) t k)
          (ensures check sg (closed_ctx g'.regions) t k) =
  introduce forall (a: atom). L.mem a (L.map fst g.regions) ==> L.mem a (L.map fst g'.regions)
  with introduce _ ==> _
  with assert (L.mem a (rdom g));
  check_closed_mono sg g.regions g'.regions t k

(* The context morphism. *)

let tm_ren_ok_ext xi xi' g g' = ()

let tm_ren_ok_up xi g g' t =
  let g1 = push_var g t in
  let g1' = push_var g' t in
  assert (hyps g1 == hyps g /\ hyps g1' == hyps g');
  assert (rdom g1 == rdom g /\ rdom g1' == rdom g');
  introduce forall (i: nat). i < L.length g1.vars ==>
    L.nth g1'.vars (up_ren xi i) == L.nth g1.vars i
  with introduce _ ==> _
  with (if i = 0 then () else assert (L.nth g.vars (i - 1) == L.nth g.vars (i - 1)))

let rec tm_ren_ok_upn (xi: ren) (g g': ctx) (ts: list typ)
  : Lemma (requires tm_ren_ok xi g g')
          (ensures tm_ren_ok (upn_ren (L.length ts) xi) (push_vars g ts) (push_vars g' ts))
          (decreases ts) =
  match ts with
  | [] -> tm_ren_ok_ext xi (upn_ren 0 xi) g g'
  | t :: ts' ->
    tm_ren_ok_up xi g g' t;
    tm_ren_ok_upn (up_ren xi) (push_var g t) (push_var g' t) ts';
    tm_ren_ok_ext (upn_ren (L.length ts') (up_ren xi)) (upn_ren (L.length ts) xi)
      (push_vars (push_var g t) ts') (push_vars (push_var g' t) ts')

let tm_ren_ok_push_tvar xi g g' k =
  let g1 = push_tvar g k in
  let g1' = push_tvar g' k in
  hyps_push_tvar g k;
  hyps_push_tvar g' k;
  rdom_push_tvar g k;
  rdom_push_tvar g' k;
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g1') h
  with introduce _ ==> _
  with begin
    let h0 = map_wit (ren_constr (shift 1)) (hyps g) h in
    entails_ren (shift 1) (hyps g') h0
  end;
  introduce forall (a: atom). (match L.assoc a g1.regions with
                               | Some l -> L.assoc a g1'.regions == Some l
                               | None -> True)
  with (assoc_ren_regions (shift 1) g.regions a; assoc_ren_regions (shift 1) g'.regions a);
  LP.map_lemma (ren_ty (shift 1)) g.vars;
  introduce forall (i: nat). i < L.length g1.vars ==> L.nth g1'.vars (xi i) == L.nth g1.vars i
  with introduce _ ==> _
  with (nth_map (ren_ty (shift 1)) g.vars i; nth_map (ren_ty (shift 1)) g'.vars (xi i))

let rec tm_ren_ok_push_tvars (xi: ren) (g g': ctx) (ks: list kind)
  : Lemma (requires tm_ren_ok xi g g') (ensures tm_ren_ok xi (push_tvars g ks) (push_tvars g' ks))
          (decreases ks) =
  match ks with
  | [] -> ()
  | k :: ks' ->
    tm_ren_ok_push_tvar xi g g' k;
    tm_ren_ok_push_tvars xi (push_tvar g k) (push_tvar g' k) ks'

let tm_ren_ok_assumps xi g g' cs =
  let g1 = add_assumps g cs in
  let g1' = add_assumps g' cs in
  rdom_add_assumps g cs;
  rdom_add_assumps g' cs;
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g1') h
  with introduce _ ==> _
  with begin
    mem_hyps_add_assumps g cs h;
    if L.mem h cs then begin
      mem_hyps_add_assumps g' cs h;
      entails_hyp (hyps g1') h
    end else begin
      introduce forall (h': constr). L.mem h' (hyps g') ==> L.mem h' (hyps g1')
      with mem_hyps_add_assumps g' cs h';
      entails_weaken (hyps g') (hyps g1') h
    end
  end

let tm_ren_ok_assump xi g g' c =
  add_assump_assumps g c;
  add_assump_assumps g' c;
  tm_ren_ok_assumps xi g g' [c]

let mem_hyps_enter_region (g: ctx) (a: atom) (l: layout) (h: constr)
  : Lemma (L.mem h (hyps (enter_region g a l)) <==>
           L.mem h (region_facts a 0 g.tvars) \/ L.mem h (hyps g)) =
  LP.append_mem (L.append (region_facts a 0 g.tvars) g.facts) g.assumps h;
  LP.append_mem (region_facts a 0 g.tvars) g.facts h;
  LP.append_mem g.facts g.assumps h

let tm_ren_ok_enter_region xi g g' a l =
  let g1 = enter_region g a l in
  let g1' = enter_region g' a l in
  rdom_enter_region g a l;
  rdom_enter_region g' a l;
  assert (g1.tvars == g.tvars /\ g1'.tvars == g'.tvars /\ g1.vars == g.vars /\ g1'.vars == g'.vars);
  introduce forall (h: constr). L.mem h (hyps g') ==> L.mem h (hyps g1')
  with mem_hyps_enter_region g' a l h;
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g1') h
  with introduce _ ==> _
  with begin
    mem_hyps_enter_region g a l h;
    mem_hyps_enter_region g' a l h;
    if L.mem h (region_facts a 0 g.tvars) then entails_hyp (hyps g1') h
    else entails_weaken (hyps g') (hyps g1') h
  end;
  introduce forall (b: atom). (match L.assoc b g1.regions with
                               | Some l0 -> L.assoc b g1'.regions == Some l0
                               | None -> True)
  with (if b = a then () else assert (L.assoc b g.regions == L.assoc b g.regions))

let tm_ren_ok_fresh xi g g' a body = frn_ren_tm xi body

let tm_ren_ok_shift g t =
  ctx_ext_push_var g t;
  introduce forall (i: nat). i < L.length g.vars ==>
    L.nth (push_var g t).vars (shift 1 i) == L.nth g.vars i
  with ()

let tm_ren_ok_id g g' = ()

(* The rules, one builder each. *)

let ren_let_eq (xi: ren) (t1: typ) (e1 e2: exp)
  : Lemma (ren_tm xi (ELet t1 e1 e2) == ELet t1 (ren_tm xi e1) (ren_tm (up_ren xi) e2)) = ()

let tm (sg: sig) (ln: lctx) (g': ctx) (xi: ren) (d: jctx) (e: exp) (t r: typ) : Type =
  typing sg ln g' d (ren_tm xi e) t r

let b_var (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (i: nat)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EVar i /\ L.nth g.vars i == Some t /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' r (KRow EEffect);
  nth_length g.vars i;
  T_Var #sg #ln #g' #d #(xi i) #t #r () ()

let b_global (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (q: qname) (ks: list kind) (nk: nat) (t0: typ)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EGlobal q ks /\ t == kinst_ty ks t0 /\
                   global_type sg q == Some (nk, t0) /\ L.length ks == nk /\ qkinds_wf g.nk ks /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' r (KRow EEffect);
  T_Global #sg #ln #g' #d #q #ks #nk #t0 #r () () ()

let b_lit (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (c: lit)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ELit c /\ t == lit_type c /\
             check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' r (KRow EEffect);
  T_Lit #sg #ln #g' #d #c #r ()

let b_lam (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1 r1: typ) (body: exp) (t2: typ)
  (hb: typing sg ln (push_var g' t1) [] (ren_tm (up_ren xi) body) t2 r1)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ELam t1 r1 body /\ t == t_fun t1 r1 t2 /\
                   check sg g t1 KType /\ check sg g r1 (KRow EEffect) /\
                     check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' t1 KType;
  check_weaken sg g g' r1 (KRow EEffect);
  check_weaken sg g g' r (KRow EEffect);
  T_Lam #sg #ln #g' #d #t1 #r1 #(ren_tm (up_ren xi) body) #t2 #r () () hb

let b_app (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1 e2: exp) (t1 t2: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) (t_fun t1 r t2) r)
  (h2: typing sg ln g' [] (ren_tm xi e2) t1 r)
  : Pure (tm sg ln g' xi d e t r) (requires e == EApp e1 e2 /\ t == t2) (ensures fun _ -> True) =
  T_App h1 h2

let b_chain (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t0: typ) (th: tsub)
  (hc: chain_typing sg ln g' [] r (ren_tm xi e))
  : Pure (tm sg ln g' xi d e t r)
         (requires chain_cursor sg e == Some (t0, th) /\ t == sub_ty th t0)
         (ensures fun _ -> True) =
  chain_cursor_ren_tm sg xi e;
  T_Chain #sg #ln #g' #d #(ren_tm xi e) #t0 #th #r hc ()

let b_tylam (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: kind) (body: exp) (t0: typ)
  (hb: typing sg ln (push_tvar g' k) [] (ren_tm xi body) t0 TRowEmpty)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ETyLam k body /\ t == TForall k t0 /\
                   kind_wf g.nk k /\ qkind g.nk k /\ value_form sg body /\
                     check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  value_form_ren_tm sg xi body;
  check_weaken sg g g' r (KRow EEffect);
  T_TyLam #sg #ln #g' #d #k #(ren_tm xi body) #t0 #r () () () hb

let b_tyapp (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp) (s: typ) (k: kind) (t0: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) (TForall k t0) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ETyApp e1 s /\ t == subst1_ty s t0 /\ check sg g s k)
         (ensures fun _ -> True) =
  check_weaken sg g g' s k;
  T_TyApp #sg #ln #g' #d #(ren_tm xi e1) #s h1 ()

let b_clam (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (c: constr) (body: exp) (t0: typ)
  (hb: typing sg ln (add_assump g' c) [] (ren_tm xi body) t0 TRowEmpty)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ECLam c body /\ t == TConstr c t0 /\ constr_ok sg g c
             /\
                   value_form sg body /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  constr_ok_weaken sg g g' c;
  value_form_ren_tm sg xi body;
  check_weaken sg g g' r (KRow EEffect);
  T_CLam #sg #ln #g' #d #c #(ren_tm xi body) #t0 #r () () () hb

let b_capp (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp) (c: constr)
  (h1: typing sg ln g' [] (ren_tm xi e1) (TConstr c t) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ECApp e1 /\ entails (hyps g) c)
         (ensures fun _ -> True) =
  entails_ext g g' c;
  T_CApp h1 ()

let b_let (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1: typ) (e1 e2: exp)
  (h1: typing sg ln g' [] (ren_tm xi e1) t1 r)
  (h2: typing sg ln (push_var g' t1) d (ren_tm (up_ren xi) e2) t r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ELet t1 e1 e2 /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  ren_let_eq xi t1 e1 e2;
  check_weaken sg g g' t1 KType;
  T_Let () h1 h2

let b_letrec (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (bs: list (typ & exp)) (body: exp)
  (hbs: binds_typing sg ln (push_vars g' (L.map fst bs))
      (ren_tm_binds (upn_ren (L.length bs) xi) bs))
  (hb: typing sg ln (push_vars g' (L.map fst bs)) d (ren_tm (upn_ren (L.length bs) xi) body) t r)
  : Pure (tm sg ln g' xi d e t r)
         (requires e == ELetRec bs body /\ Stella.Core.Init.init_safe_letrec sg bs)
         (ensures fun _ -> True) =
  let xn = upn_ren (L.length bs) xi in
  IR.init_safe_ren_tm sg xi bs;
  ren_tm_binds_fst xn bs;
  T_LetRec #sg #ln #g' #d #(ren_tm_binds xn bs) #(ren_tm xn body) #t #r () hbs hb

let b_conv (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1 r1: typ) (h1: typing sg ln g' d (ren_tm xi e) t1 r1)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ ty_eq t1 t /\ ty_eq r1 r /\ check sg g t KType /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
  T_Conv h1 () ()

let b_case (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (es: list exp) (dt: dtree) (ts: list typ)
  (hes: exps_typing sg ln g' [] r (ren_tm_exps xi es) ts)
  (hdt: dt_typing sg ln g' d (scrut_occs 0 ts) (ren_tm_dt xi dt) t r)
  : Pure (tm sg ln g' xi d e t r) (requires e == ECase es dt) (ensures fun _ -> True) =
  T_Case hes hdt

let b_letjoin (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (ts: list typ) (e1 e2: exp)
  (h1: typing sg ln (push_vars g' ts) ((ts, t, r) :: d)
      (ren_tm (upn_ren (L.length ts) xi) e1) t r)
  (h2: typing sg ln g' ((ts, t, r) :: d) (ren_tm xi e2) t r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ELetJoin ts t e1 e2 /\ tys_ok sg g ts /\
             check sg g t KType)
         (ensures fun _ -> True) =
  tys_ok_ext sg g g' ts;
  check_weaken sg g g' t KType;
  T_LetJoin #sg #ln #g' #d #ts #t #(ren_tm (upn_ren (L.length ts) xi) e1) #(ren_tm xi e2) #r
    () h1 h2

let b_jump (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (j: nat) (es: list exp) (ts: list typ)
  (hes: exps_typing sg ln g' [] r (ren_tm_exps xi es) ts)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EJump j es /\
             L.nth d j == Some (ts, t, r) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
  T_Jump #sg #ln #g' #d #j #(ren_tm_exps xi es) #ts #t #r () () hes

let b_recempty (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ERecEmpty /\ t == t_record TRowEmpty /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' r (KRow EEffect);
  T_RecEmpty #sg #ln #g' #d #r ()

let b_extend (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (e1 e2: exp) (t1 r0: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) t1 r)
  (h2: typing sg ln g' [] (ren_tm xi e2) (t_record r0) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EExtend k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t1) r0) /\ key_ok sg g k EType /\
                   entails (hyps g) (CLacks k r0))
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  entails_ext g g' (CLacks k r0);
  T_Extend #sg #ln #g' #d #k h1 h2 ()

let b_select (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) (t_record (TRowExt (EntTy k t) r0)) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ESelect k e1 /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  T_Select h1 ()

let b_restrict (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (e1: exp) (t1 r0: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) (t_record (TRowExt (EntTy k t1) r0)) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ERestrict k e1 /\ t == t_record r0 /\
             key_ok sg g k EType)
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  T_Restrict h1 ()

let b_update (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (e1 e2: exp) (t1 t2 r0: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) (t_record (TRowExt (EntTy k t1) r0)) r)
  (h2: typing sg ln g' [] (ren_tm xi e2) t2 r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EUpdate k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t2) r0) /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  T_Update h1 h2 ()

let b_merge (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1 e2: exp) (r1 r2: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) (t_record r1) r)
  (h2: typing sg ln g' [] (ren_tm xi e2) (t_record r2) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EMerge e1 e2 /\ t == t_record (TRowUnion r1 r2) /\
                   entails (hyps g) (CDisj r1 r2))
         (ensures fun _ -> True) =
  entails_ext g g' (CDisj r1 r2);
  T_Merge h1 h2 ()

let b_inject (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (r0: typ) (e1: exp) (t1: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) t1 r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EInject k r0 e1 /\
             t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\
                     check sg g r0 (KRow EType))
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  entails_ext g g' (CLacks k r0);
  check_weaken sg g g' r0 (KRow EType);
  T_Inject #sg #ln #g' #d #k #r0 h1 () ()

let b_weaken (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (t1: typ) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) (t_variant r0) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EWeaken k t1 e1 /\
             t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  key_ok_rdom sg g g' k EType;
  entails_ext g g' (CLacks k r0);
  check_weaken sg g g' t1 KType;
  T_Weaken #sg #ln #g' #d #k #t1 h1 () ()

let b_variant_value (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (v: exp) (pt vr0 vr: typ)
  (h1: typing sg ln g' [] (ren_tm xi e) (t_variant vr0) r)
  (h2: typing sg ln g' [] (ren_tm xi v) pt r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ t == t_variant vr /\ V.is_value sg e /\
                   variant_view e == Some (k, v) /\ check sg g (t_variant vr) KType /\
                   check sg g pt KType /\ L.mem (k, PTy (canon pt)) (row_entries (canon vr)))
         (ensures fun _ -> True) =
  is_value_ren_tm sg xi e;
  variant_view_ren_tm xi e;
  check_weaken sg g g' (t_variant vr) KType;
  check_weaken sg g g' pt KType;
  T_VariantValue #sg #ln #g' #d #(ren_tm xi e) #k #(ren_tm xi v) #pt #r vr0 vr h1 () h2 ()

let b_absurd (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp) (h1: typing sg ln g' [] (ren_tm xi e1) (t_variant TRowEmpty) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EAbsurd t e1 /\ check sg g t KType)
         (ensures fun _ -> True) =
  check_weaken sg g g' t KType;
  T_Absurd #sg #ln #g' #d #t h1 ()

let b_perform (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (op: opname) (ss: list typ) (e1: exp) (q: qname) (ei: effect_info) (os: op_sig)
  (ts: list typ) (h1: typing sg ln g' [] (ren_tm xi e1) (op_inst ts ss os.arg) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EPerform k op ss e1 /\ t == op_inst ts ss os.res /\
                   L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)) /\
                   sg.effects q == Some ei /\ op_of ei op == Some os /\
                   check_tys sg g ts ei.eff_params /\ check_tys sg g ss os.binders)
         (ensures fun _ -> True) =
  check_tys_ext sg g g' ts ei.eff_params;
  check_tys_ext sg g g' ss os.binders;
  T_Perform #sg #ln #g' #d #k #op #ss #(ren_tm xi e1) #r #q #ei #os ts () () () h1

let ren_handler (xi: ren) (hd: handler) : handler =
  { h_ent = hd.h_ent; h_ret_ty = hd.h_ret_ty; h_ret = ren_tm (up_ren xi) hd.h_ret;
    h_clauses = ren_tm_cls xi hd.h_clauses }

let rec clause_ops_ren_tm (xi: ren) (cs: list clause)
  : Lemma (ensures clause_ops (ren_tm_cls xi cs) == clause_ops cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ _ :: cs | CFast _ _ _ _ :: cs -> clause_ops_ren_tm xi cs

let b_handle (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp) (hd: handler) (lbl: option string) (q: qname) (ts: list typ) (ei: effect_info)
  (h1: typing sg ln g' [] (ren_tm xi e1) hd.h_ret_ty (TRowExt hd.h_ent r))
  (h2: typing sg ln (push_var g' hd.h_ret_ty) [] (ren_tm (up_ren xi) hd.h_ret) t r)
  (hcl: clauses_typing sg ln g' ei ts r t (ren_tm_cls xi hd.h_clauses))
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EHandle e1 hd /\ hd.h_ent == EntEff lbl q ts /\
                   sg.effects q == Some ei /\
                   check sg g (TRowExt hd.h_ent r) (KRow EEffect) /\ check sg g hd.h_ret_ty KType /\
                   check sg g t KType /\ check sg g r (KRow EEffect) /\
                     clauses_cover ei hd.h_clauses)
         (ensures fun _ -> True) =
  let hd' = ren_handler xi hd in
  check_weaken sg g g' (TRowExt hd.h_ent r) (KRow EEffect);
  check_weaken sg g g' hd.h_ret_ty KType;
  check_weaken sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  clause_ops_ren_tm xi hd.h_clauses;
  let h1 : typing sg ln g' [] (ren_tm xi e1) hd'.h_ret_ty (TRowExt hd'.h_ent r) = h1 in
  let h2 : typing sg ln (push_var g' hd'.h_ret_ty) [] hd'.h_ret t r = h2 in
  let hcl : clauses_typing sg ln g' ei ts r t hd'.h_clauses = hcl in
  T_Handle #sg #ln #g' #d #(ren_tm xi e1) #hd' #t #r #lbl #q #ts #ei () () () () h1 h2 hcl

let b_openeff (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (r2: typ) (e1: exp) (t1 r1 t2: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) (t_fun t1 r1 t2) r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EOpenEff r2 e1 /\ t == t_fun t1 (TRowUnion r1 r2) t2 /\
                   entails (hyps g) (CDisj r1 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  entails_ext g g' (CDisj r1 r2);
  check_weaken sg g g' r2 (KRow EEffect);
  T_OpenEff #sg #ln #g' #d #r2 h1 ()

let b_region (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (lay: layout) (es: list exp) (body: exp)
  (hes: exps_typing sg ln g' [] r (ren_tm_exps xi es) (L.map snd lay))
  (hb: (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (ren_tm xi body)))} ->
        typing sg ln (enter_region g' a lay) [] (ren_tm xi (open_region a body)) t
          (TRowExt (EntRegion (RFree a)) r)))
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ERegion lay es body /\
                   check sg g (layout_row lay) (KRow EType) /\ L.noRepeats (L.map fst lay) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  let body' = ren_tm xi body in
  check_weaken sg g g' (layout_row lay) (KRow EType);
  check_weaken sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  let hb' (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp body'))})
    : typing sg ln (enter_region g' a lay) [] (open_region a body') t
        (TRowExt (EntRegion (RFree a)) r) =
    open_region_ren_tm 0 a xi body;
    hb a
  in
  T_Region #sg #ln #g' #d #lay #(ren_tm_exps xi es) #body' #t #r () () hes hb'

let b_readcell (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (a: atom) (k: key) (lay: layout)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EReadCell (RFree a) k /\
             L.assoc a g.regions == Some lay /\
                   L.assoc k lay == Some t /\ L.mem (RegionKey (RFree a)) (known_keys r) /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  check_weaken sg g g' r (KRow EEffect);
  T_ReadCell #sg #ln #g' #d #a #k #lay #t #r () () ()

let b_writecell (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ)
  (a: atom) (k: key) (e1: exp) (lay: layout) (t1: typ)
  (h1: typing sg ln g' [] (ren_tm xi e1) t1 r)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EWriteCell (RFree a) k e1 /\ t == t_unit /\
                   L.assoc a g.regions == Some lay /\ L.assoc k lay == Some t1 /\
                   L.mem (RegionKey (RFree a)) (known_keys r))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  T_WriteCell #sg #ln #g' #d #a #k #(ren_tm xi e1) #lay #t1 #r () () h1

let b_match (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (th: list exp) (dt: dtree) (ts: list typ) (om: octx)
  (hes: exps_typing sg ln g' [] r (ren_tm_exps xi th) ts)
  (hm: match_typing sg ln g' [] r (ren_tm_exps xi th) om)
  (hdt: dt_typing sg ln g' d om (ren_tm_dt xi dt) t r)
  : Pure (tm sg ln g' xi d e t r)
         (requires e == EMatch th dt /\ L.for_all (V.is_value sg) th)
         (ensures fun _ -> True) =
  values_ren_tm sg xi th;
  T_Match om hes () hm hdt

let b_openeffc (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (r2: typ) (e1: exp) (r0: typ) (h1: typing sg ln g' [] (ren_tm xi e1) t r0)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EOpenEffC r2 e1 /\ r == TRowUnion r0 r2 /\
                   entails (hyps g) (CDisj r0 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  entails_ext g g' (CDisj r0 r2);
  check_weaken sg g g' r2 (KRow EEffect);
  T_OpenEffC #sg #ln #g' #d #r2 h1 ()

let b_force (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (nu: atom)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EForce nu /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_ext sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  T_Force #sg #ln #g' #d #nu #t #r () ()

let b_fill (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (nu: atom) (e1: exp) (h1: typing sg ln g' [] (ren_tm xi e1) t TRowEmpty)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EFill nu e1 /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_ext sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  T_Fill #sg #ln #g' #d #nu #(ren_tm xi e1) #t #r () () h1

let b_region_open (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ)
  (a: atom) (cells: list (key & exp)) (body: exp) (lay: layout)
  (hc: cells_typing sg ln g' (ren_tm_cells xi cells) lay)
  (hb: typing sg ln g' [] (ren_tm xi body) t (TRowExt (EntRegion (RFree a)) r))
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == ERegionOpen a cells body /\
             L.assoc a g.regions == Some lay /\
                   check sg (closed_ctx g.regions) t KType /\
                   check sg (closed_ctx g.regions) r (KRow EEffect) /\
                   ~(L.mem a (frn_ty t @ frn_ty r)))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  closed_ext sg g g' t KType;
  closed_ext sg g g' r (KRow EEffect);
  T_RegionOpen #sg #ln #g' #d #a #(ren_tm_cells xi cells) #(ren_tm xi body) #lay #t #r () ()
    () hc hb

let b_opaque (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (w: nat)
  : Pure (tm sg ln g' xi d e t r)
         (requires tm_ren_ok xi g g' /\ e == EOpaque w t /\ opaque_type sg t /\ check sg g t KType
             /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_weaken sg g g' t KType;
  check_weaken sg g g' r (KRow EEffect);
  T_Opaque #sg #ln #g' #d #w #t #r () ()

let ren_tyapp_eq (xi: ren) (e0: exp) (s: typ) : Lemma
  (ren_tm xi (ETyApp e0 s) == ETyApp (ren_tm xi e0) s) = ()

let ren_capp_eq (xi: ren) (e0: exp) : Lemma (ren_tm xi (ECApp e0) == ECApp (ren_tm xi e0)) = ()

let ren_app_eq (xi: ren) (e0 v: exp) : Lemma
  (ren_tm xi (EApp e0 v) == EApp (ren_tm xi e0) (ren_tm xi v)) =
  ()

(* The mutual induction. *)

let rec typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (xi: ren) (g': ctx)
  : Pure (typing sg ln g' d (ren_tm xi e) t r) (requires tm_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | T_Var #_ #_ #_ #_ #i _ _ -> b_var xi g g' d e t r i
  | T_Global #_ #_ #_ #_ #q #ks #nk #t0 _ _ _ -> b_global xi g g' d e t r q ks nk t0
  | T_Lit #_ #_ #_ #_ #c _ -> b_lit xi g g' d e t r c
  | T_Lam #_ #_ #_ #_ #t1 #r1 #body #t2 _ _ hb ->
    tm_ren_ok_up xi g g' t1;
    b_lam xi g g' d e t r t1 r1 body t2 (typing_ren_tm' hb (up_ren xi) (push_var g' t1))
  | T_App #_ #_ #_ #_ #e1 #e2 #t1 #t2 h1 h2 ->
    b_app xi g' d e t r e1 e2 t1 t2 (typing_ren_tm' h1 xi g') (typing_ren_tm' h2 xi g')
  | T_Chain #_ #_ #_ #_ #_ #t0 #th hc _ ->
    b_chain xi g' d e t r t0 th (chain_typing_ren_tm' hc xi g')
  | T_TyLam #_ #_ #_ #_ #k #body #t0 _ _ _ hb ->
    tm_ren_ok_push_tvar xi g g' k;
    b_tylam xi g g' d e t r k body t0 (typing_ren_tm' hb xi (push_tvar g' k))
  | T_TyApp #_ #_ #_ #_ #e1 #s #k #t0 h1 _ ->
    b_tyapp xi g g' d e t r e1 s k t0 (typing_ren_tm' h1 xi g')
  | T_CLam #_ #_ #_ #_ #c #body #t0 _ _ _ hb ->
    tm_ren_ok_assump xi g g' c;
    b_clam xi g g' d e t r c body t0 (typing_ren_tm' hb xi (add_assump g' c))
  | T_CApp #_ #_ #_ #_ #e1 #c h1 _ ->
    b_capp xi g g' d e t r e1 c (typing_ren_tm' h1 xi g')
  | T_Let #_ #_ #_ #_ #t1 #e1 #e2 _ h1 h2 ->
    tm_ren_ok_up xi g g' t1;
    b_let xi g g' d e t r t1 e1 e2 (typing_ren_tm' h1 xi g')
      (typing_ren_tm' h2 (up_ren xi) (push_var g' t1))
  | T_LetRec #_ #_ #_ #_ #bs #body _ hbs hb ->
    let xn = upn_ren (L.length bs) xi in
    LP.map_lemma fst bs;
    tm_ren_ok_upn xi g g' (L.map fst bs);
    let gb' = push_vars g' (L.map fst bs) in
    b_letrec xi g' d e t r bs body (binds_typing_ren_tm' hbs xn gb') (typing_ren_tm' hb xn gb')
  | T_Conv #_ #_ #_ #_ #_ #t1 #r1 h1 _ _ ->
    b_conv xi g g' d e t r t1 r1 (typing_ren_tm' h1 xi g')
  | T_Case #_ #_ #_ #_ #es #dt #ts hes hdt ->
    b_case xi g' d e t r es dt ts (exps_typing_ren_tm' hes xi g') (dt_typing_ren_tm' hdt xi g')
  | T_LetJoin #_ #_ #_ #_ #ts #_ #e1 #e2 _ h1 h2 ->
    tm_ren_ok_upn xi g g' ts;
    b_letjoin xi g g' d e t r ts e1 e2
      (typing_ren_tm' h1 (upn_ren (L.length ts) xi) (push_vars g' ts)) (typing_ren_tm' h2 xi g')
  | T_Jump #_ #_ #_ #_ #j #es #ts _ _ hes ->
    b_jump xi g g' d e t r j es ts (exps_typing_ren_tm' hes xi g')
  | T_RecEmpty _ -> b_recempty xi g g' d e t r
  | T_Extend #_ #_ #_ #_ #k #e1 #e2 #t1 #r0 h1 h2 _ ->
    b_extend xi g g' d e t r k e1 e2 t1 r0 (typing_ren_tm' h1 xi g') (typing_ren_tm' h2 xi g')
  | T_Select #_ #_ #_ #_ #k #e1 #_ #r0 h1 _ ->
    b_select xi g g' d e t r k e1 r0 (typing_ren_tm' h1 xi g')
  | T_Restrict #_ #_ #_ #_ #k #e1 #t1 #r0 h1 _ ->
    b_restrict xi g g' d e t r k e1 t1 r0 (typing_ren_tm' h1 xi g')
  | T_Update #_ #_ #_ #_ #k #e1 #e2 #t1 #t2 #r0 h1 h2 _ ->
    b_update xi g g' d e t r k e1 e2 t1 t2 r0 (typing_ren_tm' h1 xi g') (typing_ren_tm' h2 xi g')
  | T_Merge #_ #_ #_ #_ #e1 #e2 #r1 #r2 h1 h2 _ ->
    b_merge xi g g' d e t r e1 e2 r1 r2 (typing_ren_tm' h1 xi g') (typing_ren_tm' h2 xi g')
  | T_Inject #_ #_ #_ #_ #k #r0 #e1 #t1 h1 _ _ ->
    b_inject xi g g' d e t r k r0 e1 t1 (typing_ren_tm' h1 xi g')
  | T_Weaken #_ #_ #_ #_ #k #t1 #e1 #r0 h1 _ _ ->
    b_weaken xi g g' d e t r k t1 e1 r0 (typing_ren_tm' h1 xi g')
  | T_VariantValue #_ #_ #_ #_ #_ #k #v #pt vr0 vr h1 _ h2 _ ->
    b_variant_value xi g g' d e t r k v pt vr0 vr (typing_ren_tm' h1 xi g')
      (typing_ren_tm' h2 xi g')
  | T_Absurd #_ #_ #_ #_ #_ #e1 h1 _ ->
    b_absurd xi g g' d e t r e1 (typing_ren_tm' h1 xi g')
  | T_Perform #_ #_ #_ #_ #k #op #ss #e1 #_ #q #ei #os ts _ _ _ h1 ->
    b_perform xi g g' d e t r k op ss e1 q ei os ts (typing_ren_tm' h1 xi g')
  | T_Handle #_ #_ #_ #_ #e1 #hd #_ #_ #lbl #q #ts #ei _ _ _ _ h1 h2 hcl ->
    tm_ren_ok_up xi g g' hd.h_ret_ty;
    b_handle xi g g' d e t r e1 hd lbl q ts ei (typing_ren_tm' h1 xi g')
      (typing_ren_tm' h2 (up_ren xi) (push_var g' hd.h_ret_ty)) (clauses_typing_ren_tm' hcl xi g')
  | T_OpenEff #_ #_ #_ #_ #r2 #e1 #t1 #r1 #t2 h1 _ ->
    b_openeff xi g g' d e t r r2 e1 t1 r1 t2 (typing_ren_tm' h1 xi g')
  | T_Region #_ #_ #_ #_ #lay #es #body _ _ hes hbody ->
    let hb' (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (ren_tm xi body)))})
      : typing sg ln (enter_region g' a lay) [] (ren_tm xi (open_region a body)) t
          (TRowExt (EntRegion (RFree a)) r) =
      tm_ren_ok_fresh xi g g' a body;
      tm_ren_ok_enter_region xi g g' a lay;
      typing_ren_tm' (hbody a) xi (enter_region g' a lay)
    in
    b_region xi g g' d e t r lay es body (exps_typing_ren_tm' hes xi g') hb'
  | T_ReadCell #_ #_ #_ #_ #a #k #lay _ _ _ -> b_readcell xi g g' d e t r a k lay
  | T_WriteCell #_ #_ #_ #_ #a #k #e1 #lay #t1 _ _ h1 ->
    b_writecell xi g g' d e t r a k e1 lay t1 (typing_ren_tm' h1 xi g')
  | T_Match #_ #_ #_ #_ #th #dt #ts om hes _ hm hdt ->
    b_match xi g' d e t r th dt ts om (exps_typing_ren_tm' hes xi g')
      (match_typing_ren_tm' hm xi g')
      (dt_typing_ren_tm' hdt xi g')
  | T_OpenEffC #_ #_ #_ #_ #r2 #e1 #_ #r0 h1 _ ->
    b_openeffc xi g g' d e t r r2 e1 r0 (typing_ren_tm' h1 xi g')
  | T_Force #_ #_ #_ #_ #nu _ _ -> b_force xi g g' d e t r nu
  | T_Fill #_ #_ #_ #_ #nu #e1 _ _ h1
    -> b_fill xi g g' d e t r nu e1 (typing_ren_tm' h1 xi g')
  | T_RegionOpen #_ #_ #_ #_ #a #cells #body #lay _ _ _ hc hb ->
    b_region_open xi g g' d e t r a cells body lay (cells_typing_ren_tm' hc xi g')
      (typing_ren_tm' hb xi g')
  | T_Opaque #_ #_ #_ #_ #w _ _ -> b_opaque xi g g' d e t r w

and exps_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (xi: ren) (g': ctx)
  : Pure (exps_typing sg ln g' d r (ren_tm_exps xi es) ts) (requires tm_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TE_Nil _ -> check_weaken sg g g' r (KRow EEffect); TE_Nil ()
  | TE_Cons h1 h2 -> TE_Cons (typing_ren_tm' h1 xi g') (exps_typing_ren_tm' h2 xi g')

and chain_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (xi: ren) (g': ctx)
  : Pure (chain_typing sg ln g' d r (ren_tm xi e)) (requires tm_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TS_Head #_ #_ #_ #_ #_ #q #ks #c #nk #t0 _ _ _ ->
    check_weaken sg g g' r (KRow EEffect);
    TS_Head #sg #ln #g' #d #r #q #ks #c #nk #t0 () () ()
  | TS_Ty #_ #_ #_ #_ #_ #e0 #s #k #t0 #th h0 _ _ ->
    chain_cursor_ren_tm sg xi e0;
    ren_tyapp_eq xi e0 s;
    check_weaken sg g g' s k;
    TS_Ty #sg #ln #g' #d #r #(ren_tm xi e0) #s #k #t0 #th (chain_typing_ren_tm' h0 xi g') () ()
  | TS_Constr #_ #_ #_ #_ #_ #e0 #c #t0 #th h0 _ _ ->
    chain_cursor_ren_tm sg xi e0;
    ren_capp_eq xi e0;
    entails_ext g g' (sub_constr th c);
    TS_Constr #sg #ln #g' #d #r #(ren_tm xi e0) #c #t0 #th (chain_typing_ren_tm' h0 xi g') () ()
  | TS_Val #_ #_ #_ #_ #_ #e0 #v #t0 #th #t1 #r1 #t2 h0 _ hv ->
    chain_cursor_ren_tm sg xi e0;
    ren_app_eq xi e0 v;
    TS_Val #sg #ln #g' #d #r #(ren_tm xi e0) #(ren_tm xi v) #t0 #th #t1 #r1 #t2
      (chain_typing_ren_tm' h0 xi g') () (typing_ren_tm' hv xi g')

and binds_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (xi: ren) (g': ctx)
  : Pure (binds_typing sg ln g' (ren_tm_binds xi bs)) (requires tm_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TB_Nil -> TB_Nil
  | TB_Cons #_ #_ #_ #t0 #e0 #_ _ h1 h2 ->
    check_weaken sg g g' t0 KType;
    TB_Cons () (typing_ren_tm' h1 xi g') (binds_typing_ren_tm' h2 xi g')

and cells_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (xi: ren) (g': ctx)
  : Pure (cells_typing sg ln g' (ren_tm_cells xi cells) lay) (requires tm_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TC_Nil -> TC_Nil
  | TC_Cons #_ #_ #_ #k #v #t0 #cs0 #lay0 _ h1 h2 ->
    is_value_ren_tm sg xi v;
    TC_Cons #sg #ln #g' #k #(ren_tm xi v) #t0 #(ren_tm_cells xi cs0) #lay0 ()
      (typing_ren_tm' h1 xi g')
      (cells_typing_ren_tm' h2 xi g')

and match_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om) (xi: ren) (g': ctx)
  : Pure (match_typing sg ln g' d r (ren_tm_exps xi th) om) (requires tm_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TM_Nil _ -> check_weaken sg g g' r (KRow EEffect); TM_Nil ()
  | TM_Cons #_ #_ #_ #_ #_ #_ #o #t0 #om0 #v _ h1 h2 ->
    proj_ren_tm sg xi th o;
    TM_Cons #sg #ln #g' #d #r #(ren_tm_exps xi th) #o #t0 #om0 #(ren_tm xi v) ()
      (typing_ren_tm' h1 xi g') (match_typing_ren_tm' h2 xi g')

and dt_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (xi: ren) (g': ctx)
  : Pure (dt_typing sg ln g' d om (ren_tm_dt xi dt) t r) (requires tm_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TD_Leaf h1 -> TD_Leaf (typing_ren_tm' h1 xi g')
  | TD_Bind #_ #_ #_ #_ #_ #o #dt0 #t_o ho hdt ->
    tm_ren_ok_up xi g g' t_o;
    TD_Bind (occ_typing_ren_tm' ho xi g') (dt_typing_ren_tm' hdt (up_ren xi) (push_var g' t_o))
  | TD_SwitchCtor #_ #_ #_ #_ #_ #o #bs #t_o tq ks ss cs ho _ _ _ hbr ->
    check_weaken sg g g' (tapps (TCon tq ks) ss) KType;
    ren_tm_brs_labels xi bs;
    TD_SwitchCtor tq ks ss cs (occ_typing_ren_tm' ho xi g') () () ()
      (ctor_brs_typing_ren_tm' hbr xi g')
  | TD_SwitchCtorDef #_ #_ #_ #_ #_ #o #bs #df #t_o tq ks ss cs ho _ _ _ hbr hdf ->
    check_weaken sg g g' (tapps (TCon tq ks) ss) KType;
    ren_tm_brs_labels xi bs;
    TD_SwitchCtorDef tq ks ss cs (occ_typing_ren_tm' ho xi g') () () ()
      (ctor_brs_typing_ren_tm' hbr xi g') (dt_typing_ren_tm' hdf xi g')
  | TD_SwitchLit #_ #_ #_ #_ #_ #o #bs #df #t_o lq ho _ _ hbr hdf ->
    ren_tm_brs_labels xi bs;
    TD_SwitchLit lq (occ_typing_ren_tm' ho xi g') () () (lit_brs_typing_ren_tm' hbr xi g')
      (dt_typing_ren_tm' hdf xi g')
  | TD_SwitchKey #_ #_ #_ #_ #_ #o #bs #t_o vr kts ho _ _ _ hbr ->
    check_weaken sg g g' vr (KRow EType);
    ren_tm_brs_labels xi bs;
    TD_SwitchKey vr kts (occ_typing_ren_tm' ho xi g') () () () (key_brs_typing_ren_tm' hbr xi g')
  | TD_SwitchKeyDef #_ #_ #_ #_ #_ #o #bs #df #t_o vr vr' kts ho _ _ _ hbr hdf ->
    check_weaken sg g g' vr (KRow EType);
    check_weaken sg g g' vr' (KRow EType);
    ren_tm_brs_labels xi bs;
    TD_SwitchKeyDef vr vr' kts (occ_typing_ren_tm' ho xi g') () () ()
      (key_brs_typing_ren_tm' hbr xi g')
      (dt_typing_ren_tm' hdf xi g')
  | TD_Guard h1 h2 h3 ->
    TD_Guard (typing_ren_tm' h1 xi g') (dt_typing_ren_tm' h2 xi g') (dt_typing_ren_tm' h3 xi g')

and ctor_brs_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ) (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (xi: ren) (g': ctx)
  : Pure (ctor_brs_typing sg ln g' d om o ks ss cs (ren_tm_brs xi bs) t r)
         (requires tm_ren_ok xi g g') (ensures fun _ -> True) (decreases h) =
  match h with
  | TCB_Nil _ ->
    check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
    TCB_Nil ()
  | TCB_Cons sq hdt h2
    -> TCB_Cons sq (dt_typing_ren_tm' hdt xi g') (ctor_brs_typing_ren_tm' h2 xi g')

and lit_brs_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (xi: ren) (g': ctx)
  : Pure (lit_brs_typing sg ln g' d om lt (ren_tm_brs xi bs) t r)
         (requires tm_ren_ok xi g g') (ensures fun _ -> True) (decreases h) =
  match h with
  | TLB_Nil _ ->
    check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
    TLB_Nil ()
  | TLB_Cons sq hdt h2
    -> TLB_Cons sq (dt_typing_ren_tm' hdt xi g') (lit_brs_typing_ren_tm' h2 xi g')

and key_brs_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (xi: ren) (g': ctx)
  : Pure (key_brs_typing sg ln g' d om o kts (ren_tm_brs xi bs) t r)
         (requires tm_ren_ok xi g g') (ensures fun _ -> True) (decreases h) =
  match h with
  | TKB_Nil _ ->
    check_weaken sg g g' t KType; check_weaken sg g g' r (KRow EEffect);
    TKB_Nil ()
  | TKB_Cons #_ #_ #_ #_ #_ #_ #k #pt _ hdt h2 ->
    check_weaken sg g g' pt KType;
    TKB_Cons #sg #ln #g' #d #om #o #k #pt () (dt_typing_ren_tm' hdt xi g')
      (key_brs_typing_ren_tm' h2 xi g')

and clauses_typing_ren_tm' (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs) (xi: ren) (g': ctx)
  : Pure (clauses_typing sg ln g' ei ts r b (ren_tm_cls xi cs)) (requires tm_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCL_Nil _ ->
    check_weaken sg g g' b KType; check_weaken sg g g' r (KRow EEffect);
    TCL_Nil ()
  | TCL_Full #_ #_ #_ #_ #_ #_ #_ #op #nb #s #kt #body #cs0 #os _ _ _ hb hcs ->
    let gb = push_tvars g os.binders in
    let gb' = push_tvars g' os.binders in
    tm_ren_ok_push_tvars xi g g' os.binders;
    check_weaken sg gb gb' s KType;
    check_weaken sg gb gb' kt KType;
    tm_ren_ok_up xi gb gb' s;
    tm_ren_ok_up (up_ren xi) (push_var gb s) (push_var gb' s) kt;
    tm_ren_ok_ext (up_ren (up_ren xi)) (upn_ren 2 xi) (push_var (push_var gb s) kt)
      (push_var (push_var gb' s) kt);
    TCL_Full #sg #ln #g' #ei #ts #r #b #op #nb #s #kt #(ren_tm (upn_ren 2 xi) body)
      #(ren_tm_cls xi cs0)
      #os () () () (typing_ren_tm' hb (upn_ren 2 xi) (push_var (push_var gb' s) kt))
      (clauses_typing_ren_tm' hcs xi g')
  | TCL_Fast #_ #_ #_ #_ #_ #_ #_ #op #nb #s #body #cs0 #os _ _ hb hcs ->
    let gb = push_tvars g os.binders in
    let gb' = push_tvars g' os.binders in
    tm_ren_ok_push_tvars xi g g' os.binders;
    check_weaken sg gb gb' s KType;
    tm_ren_ok_up xi gb gb' s;
    TCL_Fast #sg #ln #g' #ei #ts #r #b #op #nb #s #(ren_tm (up_ren xi) body) #(ren_tm_cls xi cs0)
      #os () () (typing_ren_tm' hb (up_ren xi) (push_var gb' s)) (clauses_typing_ren_tm' hcs xi g')

and occ_typing_ren_tm' (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (xi: ren) (g': ctx)
  : Pure (occ_typing sg g' om o t) (requires tm_ren_ok xi g g') (ensures fun _ -> True)
    (decreases h) =
  match h with
  | TO_Lookup sq -> TO_Lookup sq
  | TO_Field #_ #_ #_ #o0 #k #t_o #_ r0 ho _ _ ->
    check_weaken sg g g' r0 (KRow EType);
    check_weaken sg g g' t KType;
    TO_Field #sg #g' #om #o0 #k #t_o #t r0 (occ_typing_ren_tm' ho xi g') () ()

(* The stated theorems. *)

let occ_typing_ren_tm #sg #g #om #o #t h xi g' = occ_typing_ren_tm' h xi g'

let typing_ren_tm #sg #ln #g #d #e #t #r h xi g' = typing_ren_tm' h xi g'

let exps_typing_ren_tm #sg #ln #g #d #r #es #ts h xi g' = exps_typing_ren_tm' h xi g'

let chain_typing_ren_tm #sg #ln #g #d #r #e h xi g' = chain_typing_ren_tm' h xi g'

let binds_typing_ren_tm #sg #ln #g #bs h xi g' = binds_typing_ren_tm' h xi g'

let cells_typing_ren_tm #sg #ln #g #cells #lay h xi g' = cells_typing_ren_tm' h xi g'

let match_typing_ren_tm #sg #ln #g #d #r #th #om h xi g' = match_typing_ren_tm' h xi g'

let dt_typing_ren_tm #sg #ln #g #d #om #dt #t #r h xi g' = dt_typing_ren_tm' h xi g'

let ctor_brs_typing_ren_tm #sg #ln #g #d #om #o #ks #ss #cs #bs #t #r h xi g' =
  ctor_brs_typing_ren_tm' h xi g'

let lit_brs_typing_ren_tm #sg #ln #g #d #om #lt #bs #t #r h xi g' =
  lit_brs_typing_ren_tm' h xi g'

let key_brs_typing_ren_tm #sg #ln #g #d #om #o #kts #bs #t #r h xi g' =
  key_brs_typing_ren_tm' h xi g'

let clauses_typing_ren_tm #sg #ln #g #ei #ts #r #b #cs h xi g' = clauses_typing_ren_tm' h xi g'
