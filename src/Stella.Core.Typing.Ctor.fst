(* Proof structure.

   `chain_typing_domains` is by induction on the chain judgement: a type or
   constraint argument adds neither a domain nor a value argument, and a
   value argument adds its domain and itself
   (`Stella.Core.Spine.Lemmas.chain_domains_apply_arg`), typed by the
   premise of `TS_Val`. The saturated case reads the domains as the fields
   by `Stella.Core.Spine.Lemmas.ctor_chain_saturated`.

   At a data type, a chain is normalized (`chain_normal`). The instance of
   a non-saturated remainder is a `forall`, a constrained type or a
   function type, none equal to a data type, so the remainder is saturated
   and its instance is `T [[κ̄]] σ̄` for the chain's own arguments; the
   inversion of type equality on applications relates them to those of the
   occurrence. The fields are compared through the instantiated scheme
   `forall K̄. F̄ -> R` (`ctor_fields_inst`): at `|σ̄| = |K̄|` they are
   `θ(F̄)` for the substitution `θ` that conses `σ̄`, which pointwise equal
   `σ̄` make pointwise equal; at fewer arguments there are none. *)
module Stella.Core.Typing.Ctor
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Spine.Wf
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Chain
open Stella.Core.Typing.Regularity
open Stella.Core.Typing.Wf
module L = FStar.List.Tot

let rec exps_typing_length #sg #ln #g #d #r #es #ts h =
  match h with
  | TE_Nil _ -> ()
  | TE_Cons _ h' -> exps_typing_length h'

let rec exps_typing_snoc #sg #ln #g #d #r #es #ts #e #t h h1 =
  match h with
  | TE_Nil hr -> TE_Cons h1 (TE_Nil hr)
  | TE_Cons h0 h' -> TE_Cons h0 (exps_typing_snoc h' h1)

let rec exps_typing_nth #sg #ln #g #d #r #es #ts h j e t =
  match h with
  | TE_Cons h0 h' -> if j = 0 then h0 else exps_typing_nth h' (j - 1) e t

(* The indices of a derivation, read up to equality. *)
let cast_exps (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts)
  (es': list exp{es' == es}) (ts': list typ{ts' == ts})
  : exps_typing sg ln g d r es' ts' =
  h

let rec chain_typing_domains #sg #ln #g #d #r #e hc =
  match hc with
  | TS_Head _ _ hr -> TE_Nil hr
  | TS_Ty #_ #_ #_ #_ #_ #e0 #s h0 _ _ ->
    chain_domains_apply_arg sg e0 (STy s);
    L.append_l_nil (chain_domains sg e0);
    L.append_l_nil (chain_value_args e0);
    cast_exps (chain_typing_domains h0) (chain_value_args e) (chain_domains sg e)
  | TS_Constr #_ #_ #_ #_ #_ #e0 h0 _ _ ->
    chain_domains_apply_arg sg e0 SConstr;
    L.append_l_nil (chain_domains sg e0);
    L.append_l_nil (chain_value_args e0);
    cast_exps (chain_typing_domains h0) (chain_value_args e) (chain_domains sg e)
  | TS_Val #_ #_ #_ #_ #_ #e0 #v #t #th #t1 h0 _ hv ->
    chain_domains_apply_arg sg e0 (SVal v);
    cast_exps (exps_typing_snoc (chain_typing_domains h0) hv) (chain_value_args e)
      (chain_domains sg e)

let ctor_chain_fields_typing #sg #ln #g #d #r #e hc c ks args ci t th fs =
  ctor_chain_saturated sg e c ks args ci t th;
  cast_exps (chain_typing_domains hc) (value_args args) fs

let ctor_chain_fields sg e c ks args ci t th = ctor_chain_saturated sg e c ks args ci t th

(* Lists up to type equality. *)

let rec exps_typing_conv #sg #ln #g #d #r #es #ts h ts'
  : Pure (exps_typing sg ln g d r es ts')
         (requires tys_eq ts ts' /\ tys_ok sg g ts' /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TE_Nil sq -> TE_Nil sq
  | TE_Cons #_ #_ #_ #_ #_ #_ #_ #t0 #ts0 h1 h2 ->
    let t1 :: ts1 = ts' in
    ty_eq_refl r;
    let h1' : typing sg ln g d _ t1 r = T_Conv h1 () () in
    TE_Cons h1' (exps_typing_conv h2 ts1)

(* Saturation at a data type. *)

let data_not_function (sg: sig) (tq: qname) (cs: list qname)
  : Lemma (requires prim_wf sg /\ has_class sg tq (TcData cs)) (ensures tq =!= prim_function) = ()

let saturated_of_data sg s th tq ks ss cs =
  data_not_function sg tq cs;
  ty_eq_sym (sub_ty th s) (tapps (TCon tq ks) ss);
  match s with
  | TForall _ _ | TConstr _ _ -> ty_eq_tapps_binder tq ks ss (sub_ty th s)
  | _ ->
    match as_function sg s with
    | None -> ()
    | Some (a1, r1, b1) ->
      as_function_sub sg th s a1 r1 b1;
      as_function_t_fun sg (sub_ty th s) (sub_ty th a1) (sub_ty th r1) (sub_ty th b1);
      assert_norm (t_fun (sub_ty th a1) (sub_ty th r1) (sub_ty th b1) ==
                   tapps (TCon prim_function []) [sub_ty th a1; sub_ty th r1; sub_ty th b1]);
      ty_eq_tapps_inv tq prim_function ks [] ss [sub_ty th a1; sub_ty th r1; sub_ty th b1]

(* The instantiated constructor scheme. *)

let rec cons_all (ss: list typ) (th: tsub) : Tot tsub (decreases ss) =
  match ss with
  | [] -> th
  | s :: ss -> cons_all ss (scons s th)

let rec drop_n (#a: Type) (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then l else match l with [] -> [] | _ :: l -> drop_n (n - 1) l

let rec drop_n_length (#a: Type) (n: nat) (l: list a)
  : Lemma (requires n <= L.length l) (ensures L.length (drop_n n l) == L.length l - n)
          (decreases n) =
  if n = 0 then () else drop_n_length (n - 1) (L.tl l)

let rec drop_n_all (#a: Type) (l: list a)
  : Lemma (ensures drop_n (L.length l) l == []) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l' -> drop_n_all l'

let rec kforalls (ks: list kind) (ps: list kind) (t: typ)
  : Lemma (ensures kinst_ty ks (foralls ps t) == foralls (kinst_kinds ks ps) (kinst_ty ks t))
          (decreases ps) =
  match ps with
  | [] -> ()
  | _ :: ps' -> kforalls ks ps' t

let rec kpure_arrows (ks: list kind) (fs: list typ) (t: typ)
  : Lemma (ensures kinst_ty ks (pure_arrows fs t) == pure_arrows (kinst_tys ks fs) (kinst_ty ks t))
          (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs' ->
    kpure_arrows ks fs' t;
    let h = TCon prim_function [] in
    let x = pure_arrows fs' t in
    assert (kinst_ty ks h == h);
    assert (kinst_ty ks (TApp h f) == TApp h (kinst_ty ks f));
    assert (kinst_ty ks (TApp (TApp h f) TRowEmpty) == TApp (TApp h (kinst_ty ks f)) TRowEmpty);
    assert (kinst_ty ks (TApp (TApp (TApp h f) TRowEmpty) x) ==
            TApp (TApp (TApp h (kinst_ty ks f)) TRowEmpty) (kinst_ty ks x))

let rec ktapps (ks: list kind) (h: typ) (ts: list typ)
  : Lemma (ensures kinst_ty ks (tapps h ts) == tapps (kinst_ty ks h) (kinst_tys ks ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> ktapps ks (TApp h t) ts'

let rec stapps (sigma: tsub) (h: typ) (ts: list typ)
  : Lemma (ensures sub_ty sigma (tapps h ts) == tapps (sub_ty sigma h) (L.map (sub_ty sigma) ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> stapps sigma (TApp h t) ts'

let rec spure_arrows (sigma: tsub) (fs: list typ) (t: typ)
  : Lemma (ensures sub_ty sigma (pure_arrows fs t) == pure_arrows (L.map (sub_ty sigma) fs) (sub_ty sigma t))
          (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs' ->
    spure_arrows sigma fs' t;
    let h = TCon prim_function [] in
    let x = pure_arrows fs' t in
    assert (sub_ty sigma h == h);
    assert (sub_ty sigma (TApp h f) == TApp h (sub_ty sigma f));
    assert (sub_ty sigma (TApp (TApp h f) TRowEmpty) == TApp (TApp h (sub_ty sigma f)) TRowEmpty);
    assert (sub_ty sigma (TApp (TApp (TApp h f) TRowEmpty) x) ==
            TApp (TApp (TApp h (sub_ty sigma f)) TRowEmpty) (sub_ty sigma x))

let rec fun_args_arrows (sg: sig) (fs: list typ) (t: typ)
  : Lemma (requires prim_wf sg) (ensures fun_args sg (pure_arrows fs t) == L.append fs (fun_args sg t))
          (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs' -> fun_args_arrows sg fs' t

let rec head_tapps (h: typ) (ts: list typ)
  : Lemma (requires TCon? h \/ TApp? h)
          (ensures (TCon? (tapps h ts) \/ TApp? (tapps h ts)) /\ ty_head (tapps h ts) == ty_head h)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> head_tapps (TApp h t) ts'

let headed_no_args (sg: sig) (t: typ) (q: qname)
  : Lemma (requires (TCon? t \/ TApp? t) /\ ty_head t == Some q /\ not (is_function_tycon sg q))
          (ensures fun_args sg t == []) =
  match t with
  | TApp (TApp (TApp h a) b) _ ->
    assert (ty_head t == ty_head (TApp (TApp h a) b));
    assert (ty_head (TApp (TApp h a) b) == ty_head (TApp h a));
    assert (ty_head (TApp h a) == ty_head h)
  | _ -> ()

let rec inst_foralls_gen (kps: list kind) (b: typ) (th: tsub) (ss: list typ)
  : Lemma (requires TCon? b \/ TApp? b)
          (ensures inst_foralls (sub_ty th (foralls kps b)) ss ==
                   (if L.length ss <= L.length kps
                    then Some (sub_ty (cons_all ss th) (foralls (drop_n (L.length ss) kps) b))
                    else None))
          (decreases kps) =
  match ss with
  | [] -> ()
  | s :: ss' ->
    match kps with
    | [] -> ()
    | _ :: kps' ->
      cursor_instance_forall s th (foralls kps' b);
      inst_foralls_gen kps' b (scons s th) ss'

(* At fewer type arguments than binders, the instance is a `forall`. *)
let fewer_args (sg: sig) (kps: list kind) (b: typ) (th: tsub) (n: nat)
  : Lemma (requires n < L.length kps) (ensures fun_args sg (sub_ty th (foralls (drop_n n kps) b)) == []) =
  drop_n_length n kps;
  match drop_n n kps with
  | _ :: _ -> ()

(* The parts of a constructor scheme instantiated at `ks`. *)
let ctor_kps (sg: sig) (ci: ctor_info) (ks: list kind) : list kind =
  match sg.tycons ci.ct_owner with
  | Some ti -> kinst_kinds ks (arg_kinds ti.tc_kind)
  | None -> []

let ctor_kfs (sg: sig) (ci: ctor_info) (ks: list kind) : list typ =
  match sg.tycons ci.ct_owner with
  | Some ti -> kinst_tys ks (ctor_decl_fields ti ci.ct_ty)
  | None -> []

(* The result `R` of the instantiated scheme `forall K̄. F̄ -> R`. *)
let ctor_res (sg: sig) (ci: ctor_info) (ks: list kind) : typ =
  match sg.tycons ci.ct_owner with
  | Some ti ->
    tapps (TCon ci.ct_owner (kinst_kinds ks (kind_vars ti.tc_nk)))
      (kinst_tys ks (type_vars (L.length (arg_kinds ti.tc_kind))))
  | None -> TRowEmpty

let no_fun_args (sg: sig) (t: typ) : prop = forall (th: tsub). fun_args sg (sub_ty th t) == []

let ctor_scheme_shape (sg: sig) (c: qname) (ci: ctor_info) (ks: list kind)
  : Lemma (requires sig_ok sg /\ sg.ctors c == Some ci)
          (ensures kinst_ty ks ci.ct_ty ==
                   foralls (ctor_kps sg ci ks) (pure_arrows (ctor_kfs sg ci ks) (ctor_res sg ci ks)) /\
                   (TCon? (ctor_res sg ci ks) \/ TApp? (ctor_res sg ci ks)) /\
                   no_fun_args sg (ctor_res sg ci ks)) =
  let Some ti = sg.tycons ci.ct_owner in
  assert (ctor_ok sg c ci);
  let owner = ci.ct_owner in
  let fs0 = ctor_decl_fields ti ci.ct_ty in
  let ps = arg_kinds ti.tc_kind in
  let n = L.length ps in
  let kv = kinst_kinds ks (kind_vars ti.tc_nk) in
  let tv = kinst_tys ks (type_vars n) in
  let res0 = tapps (TCon owner (kind_vars ti.tc_nk)) (type_vars n) in
  kforalls ks ps (pure_arrows fs0 res0);
  kpure_arrows ks fs0 res0;
  ktapps ks (TCon owner (kind_vars ti.tc_nk)) (type_vars n);
  head_tapps (TCon owner kv) tv;
  assert (not (is_function_tycon sg owner));
  introduce forall (th: tsub). fun_args sg (sub_ty th (tapps (TCon owner kv) tv)) == []
  with begin
    stapps th (TCon owner kv) tv;
    head_tapps (TCon owner kv) (L.map (sub_ty th) tv);
    headed_no_args sg (sub_ty th (tapps (TCon owner kv) tv)) owner
  end

let pure_arrows_head (fs: list typ) (res: typ)
  : Lemma (requires TCon? res \/ TApp? res) (ensures TCon? (pure_arrows fs res) \/ TApp? (pure_arrows fs res)) =
  match fs with
  | [] -> ()
  | _ :: _ -> ()

(* The instances of `forall K̄. F̄ -> R`, by the number of type arguments. *)
let fields_of_shape (sg: sig) (kps: list kind) (kfs: list typ) (res: typ) (ss: list typ)
  : Lemma (requires prim_wf sg /\ (TCon? res \/ TApp? res) /\ no_fun_args sg res)
          (ensures (match inst_foralls (foralls kps (pure_arrows kfs res)) ss with
                    | Some t -> Some (fun_args sg t)
                    | None -> None) ==
                   (if L.length ss = L.length kps
                    then Some (L.map (sub_ty (cons_all ss tvar)) kfs)
                    else if L.length ss < L.length kps then Some []
                    else None)) =
  let b = pure_arrows kfs res in
  let th = cons_all ss tvar in
  pure_arrows_head kfs res;
  sub_ty_tvar (foralls kps b);
  inst_foralls_gen kps b tvar ss;
  if L.length ss = L.length kps then begin
    drop_n_all kps;
    spure_arrows th kfs res;
    fun_args_arrows sg (L.map (sub_ty th) kfs) (sub_ty th res);
    L.append_l_nil (L.map (sub_ty th) kfs)
  end
  else if L.length ss < L.length kps then fewer_args sg kps b th (L.length ss)

let ctor_fields_inst (sg: sig) (c: qname) (ci: ctor_info) (ks: list kind) (ss: list typ)
  : Lemma (requires sig_ok sg /\ sg.ctors c == Some ci)
          (ensures ctor_fields sg c ks ss ==
                   (if L.length ss = L.length (ctor_kps sg ci ks)
                    then Some (L.map (sub_ty (cons_all ss tvar)) (ctor_kfs sg ci ks))
                    else if L.length ss < L.length (ctor_kps sg ci ks) then Some []
                    else None)) =
  ctor_scheme_shape sg c ci ks;
  fields_of_shape sg (ctor_kps sg ci ks) (ctor_kfs sg ci ks) (ctor_res sg ci ks) ss

(* Fields at pointwise equal arguments. *)

let rec tys_eq_length (ts ts': list typ)
  : Lemma (requires tys_eq ts ts') (ensures L.length ts == L.length ts') (decreases ts) =
  match ts, ts' with
  | [], [] -> ()
  | _ :: ts1, _ :: ts1' -> tys_eq_length ts1 ts1'

let rec cons_all_eq (ss ss': list typ) (th th': tsub) (i: nat)
  : Lemma (requires tys_eq ss ss' /\ (forall (j: nat). ty_eq (th j) (th' j)))
          (ensures ty_eq (cons_all ss th i) (cons_all ss' th' i)) (decreases ss) =
  match ss, ss' with
  | [], [] -> ()
  | s1 :: ss1, s1' :: ss1' ->
    introduce forall (j: nat). ty_eq (scons s1 th j) (scons s1' th' j)
    with (if j = 0 then () else ());
    cons_all_eq ss1 ss1' (scons s1 th) (scons s1' th') i

let rec map_sub_tys_eq (th th': tsub) (fs: list typ)
  : Lemma (requires forall (i: nat). ty_eq (th i) (th' i))
          (ensures tys_eq (L.map (sub_ty th) fs) (L.map (sub_ty th') fs)) (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs1 -> ty_eq_sub_pointwise th th' f; map_sub_tys_eq th th' fs1

let ctor_fields_tys_eq sg c ks ss ss' =
  let Some ci = sg.ctors c in
  tys_eq_length ss ss';
  ctor_fields_inst sg c ci ks ss;
  ctor_fields_inst sg c ci ks ss';
  if L.length ss = L.length (ctor_kps sg ci ks) then begin
    let th = cons_all ss tvar in
    let th' = cons_all ss' tvar in
    introduce forall (i: nat). ty_eq (th i) (th' i)
    with begin
      FStar.Classical.forall_intro (fun (j: nat) -> ty_eq_refl (tvar j));
      cons_all_eq ss ss' tvar tvar i
    end;
    map_sub_tys_eq th th' (ctor_kfs sg ci ks)
  end

(* The value at a data type. *)

let ctor_value_fields_typing #sg #ln #g #d #v #t_o #r h c ks args tq ks' ss' cs fs' =
  let hc = chain_normal h in
  let Some (s, th) = chain_cursor sg v in
  let ts = tapps (TCon tq ks') ss' in
  ty_eq_sym t_o (sub_ty th s);
  ty_eq_trans (sub_ty th s) t_o ts;
  saturated_of_data sg s th tq ks' ss' cs;
  let Some ci = sg.ctors c in
  ctor_chain_saturated sg v c ks args ci s th;
  ty_eq_tapps_inv ci.ct_owner tq ks ks' (ty_args args) ss';
  ctor_fields_tys_eq sg c ks (ty_args args) ss';
  ctor_fields_ok sg g tq ks' ss' cs c fs';
  chain_typing_args_ok hc;
  let hf = ctor_chain_fields_typing hc c ks args ci s th (chain_domains sg v) in
  tys_eq_length (chain_domains sg v) fs';
  exps_typing_conv hf fs'
