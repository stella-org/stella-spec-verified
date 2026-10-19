(* Proof structure.

   Context extensions: each component of `wf_ctx` is carried over
   separately. A term binder, an assumption and a region extend the context
   (`ctx_ext_*`), so the stored types keep their kinds by weakening; a type
   binder shifts them (`check_shift`).

   `perform`: the operation's types are kinded in the declaration context
   `·, ā : κ̄, b̄ : κ̄'` with no kind variable. Kind instantiation at the
   empty vector moves them to the kind variables of `g`, and the two
   instantiations of `op_inst` compose into one substitution by the list
   `rev σ̄ @ rev τ̄`, which is `sub_ok` from that context into `g`
   (design §3.1).

   `switchCtor`: the instance `T [[κ̄]] σ̄` kinds each `σ_i` at the `i`-th
   parameter kind of `T`. The constructor's scheme binds those kinds first
   (`ctor_ok`, which `T` listing it implies), so instantiating them one
   at a time stays kinded (`check_subst1`), and the argument types of the
   function arrows of a type of kind `Type` have kind `Type`. *)
module Stella.Core.Typing.Wf
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Spine
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

(* The lists of `wf_ctx`. *)

let rec tys_ok_nth sg g ts i t =
  match ts with
  | _ :: ts' -> if i = 0 then () else tys_ok_nth sg g ts' (i - 1) t

let rec layout_ok_assoc sg g l k t =
  match l with
  | (k', _) :: l' -> if k = k' then () else layout_ok_assoc sg g l' k t

let rec regions_ok_assoc sg g rs a l =
  match rs with
  | (a', _) :: rs' -> if a = a' then () else regions_ok_assoc sg g rs' a l

let rec layout_row_ok sg g l =
  match l with
  | [] -> ()
  | (_, _) :: l' -> layout_row_ok sg g l'

let rec tys_ok_weaken sg g g' ts =
  match ts with
  | [] -> ()
  | t :: ts' -> check_weaken sg g g' t KType; tys_ok_weaken sg g g' ts'

let rec layout_ok_weaken sg g g' l =
  match l with
  | [] -> ()
  | (_, t) :: l' -> check_weaken sg g g' t KType; layout_ok_weaken sg g g' l'

let rec regions_ok_weaken sg g g' rs =
  match rs with
  | [] -> ()
  | (_, l) :: rs' -> layout_ok_weaken sg g g' l; regions_ok_weaken sg g g' rs'

(* Extending a well-formed context. *)

(* An extension that adds hypotheses alone keeps `wf_ctx` once they are
   well formed. *)
let wf_ctx_ext (sg: sig) (g g': ctx)
  : Lemma (requires wf_ctx sg g /\ ctx_ext g g' /\ g'.vars == g.vars /\ g'.regions == g.regions /\
                    wf_hyps sg g')
          (ensures wf_ctx sg g') =
  tys_ok_weaken sg g g' g.vars;
  regions_ok_weaken sg g g' g.regions

let wf_ctx_push_var sg g t =
  let g' = push_var g t in
  ctx_ext_push_var g t;
  constrs_ok_weaken sg g g' (hyps g);
  check_weaken sg g g' t KType;
  tys_ok_weaken sg g g' g.vars;
  regions_ok_weaken sg g g' g.regions

let rec wf_ctx_push_vars (sg: sig) (g: ctx) (ts: list typ)
  : Lemma (requires wf_ctx sg g /\ tys_ok sg g ts) (ensures wf_ctx sg (push_vars g ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' ->
    wf_ctx_push_var sg g t;
    ctx_ext_push_var g t;
    tys_ok_weaken sg g (push_var g t) ts';
    wf_ctx_push_vars sg (push_var g t) ts'

let rec tys_ok_shift (sg: sig) (g: ctx) (k: kind) (ts: list typ)
  : Lemma (requires tys_ok sg g ts)
          (ensures tys_ok sg (push_tvar g k) (L.map (ren_ty (shift 1)) ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> check_shift sg g k t KType; tys_ok_shift sg g k ts'

let rec layout_ok_shift (sg: sig) (g: ctx) (k: kind) (l: layout)
  : Lemma (requires layout_ok sg g l)
          (ensures layout_ok sg (push_tvar g k) (ren_layout (shift 1) l)) (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l' -> check_shift sg g k t KType; layout_ok_shift sg g k l'

let rec regions_ok_shift (sg: sig) (g: ctx) (k: kind) (rs: list (atom & layout))
  : Lemma (requires regions_ok sg g rs)
          (ensures regions_ok sg (push_tvar g k) (L.map (ren_region (shift 1)) rs)) (decreases rs) =
  match rs with
  | [] -> ()
  | (_, l) :: rs' -> layout_ok_shift sg g k l; regions_ok_shift sg g k rs'

let wf_ctx_push_tvar sg g k =
  tvars_wf_push_tvar g k;
  wf_hyps_push_tvar sg g k;
  tys_ok_shift sg g k g.vars;
  regions_ok_shift sg g k g.regions

let rec wf_ctx_push_tvars (sg: sig) (g: ctx) (ks: list kind)
  : Lemma (requires wf_ctx sg g /\ qkinds_wf g.nk ks) (ensures wf_ctx sg (push_tvars g ks))
          (decreases ks) =
  match ks with
  | [] -> ()
  | k :: ks' -> wf_ctx_push_tvar sg g k; wf_ctx_push_tvars sg (push_tvar g k) ks'

let rec ops_ok_assoc (sg: sig) (params: list kind) (ops: list (opname & op_sig)) (op: opname)
  (os: op_sig)
  : Lemma (requires ops_ok sg params ops /\ L.assoc op ops == Some os) (ensures op_ok sg params os)
          (decreases ops) =
  match ops with
  | (op', _) :: ops' -> if op = op' then () else ops_ok_assoc sg params ops' op os

let op_ok_of (sg: sig) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  : Lemma (requires effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os)
          (ensures effect_ok sg ei /\ op_ok sg ei.eff_params os) =
  assert (match sg.effects q with Some ei -> effect_ok sg ei | None -> True);
  ops_ok_assoc sg ei.eff_params ei.eff_ops op os

let wf_ctx_clause_binders sg g q ei op os =
  op_ok_of sg q ei op os;
  qkinds_wf_mono 0 g.nk os.binders;
  wf_ctx_push_tvars sg g os.binders

let wf_ctx_add_assump sg g c =
  ctx_ext_add_assump g c;
  wf_hyps_add_assump sg g c;
  wf_ctx_ext sg g (add_assump g c)

let wf_ctx_enter_region sg g a l =
  let g' = enter_region g a l in
  ctx_ext_enter_region g a l;
  wf_hyps_enter_region sg g a l;
  tys_ok_weaken sg g g' g.vars;
  layout_ok_weaken sg g g' l;
  regions_ok_weaken sg g g' g.regions

(* `Ω`. *)

let rec octx_ok_assoc sg g om o t =
  match om with
  | (o', _) :: om' -> if o = o' then () else octx_ok_assoc sg g om' o t

let rec octx_ok_weaken sg g g' om =
  match om with
  | [] -> ()
  | (_, t) :: om' -> check_weaken sg g g' t KType; octx_ok_weaken sg g g' om'

let rec octx_ok_append sg g om1 om2 =
  match om1 with
  | [] -> ()
  | _ :: om1' -> octx_ok_append sg g om1' om2

let occ_typing_regular #sg #g #om #o #t h =
  match h with
  | TO_Lookup _ -> octx_ok_assoc sg g om o t
  | TO_Field _ _ _ _ -> ()

let rec octx_ok_scrut_occs (sg: sig) (g: ctx) (i: nat) (ts: list typ)
  : Lemma (requires tys_ok sg g ts) (ensures octx_ok sg g (scrut_occs i ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts' -> octx_ok_scrut_occs sg g (i + 1) ts'

let octx_ok_key_branch sg g om o k pt = ()

let octx_ok_key_default sg g om o vr' = check_t_variant sg g vr'

(* Globals. *)

let global_type_ok (sg: sig) (q: qname) (n: nat) (t: typ)
  : Lemma (requires sig_wf sg /\ global_type sg q == Some (n, t)) (ensures scheme_ok sg n t) =
  assert (match sg.ctors q with Some ci -> scheme_ok sg ci.ct_nk ci.ct_ty | None -> True);
  assert (match sg.foreigns q with Some fi -> scheme_ok sg fi.fr_nk fi.fr_ty | None -> True);
  assert (match sg.values q with Some vi -> scheme_ok sg vi.vl_nk vi.vl_ty | None -> True)

let check_global_inst sg g q ks n t =
  global_type_ok sg q n t;
  scheme_inst sg g n t ks

(* `perform`. *)

(* The context with `n` kind variables and the type variables `tv`
   alone. *)
let tvar_ctx (n: nat) (tv: list kind) : ctx = { decl_ctx n with tvars = tv }

let rec push_tvars_tvar_ctx (n: nat) (tv ks: list kind)
  : Lemma (ensures push_tvars (tvar_ctx n tv) ks == tvar_ctx n (L.rev_acc ks tv)) (decreases ks) =
  match ks with
  | [] -> ()
  | k :: ks' ->
    assert (push_tvar (tvar_ctx n tv) k == tvar_ctx n (k :: tv));
    push_tvars_tvar_ctx n (k :: tv) ks'

(* The declaration context of an operation's types. *)
let op_ctx (n: nat) (params binders: list kind) : ctx =
  tvar_ctx n (L.rev_acc binders (L.rev_acc params []))

let op_ctx_push (params binders: list kind)
  : Lemma (push_tvars (push_tvars (decl_ctx 0) params) binders == op_ctx 0 params binders) =
  assert (decl_ctx 0 == tvar_ctx 0 []);
  push_tvars_tvar_ctx 0 [] params;
  push_tvars_tvar_ctx 0 (L.rev_acc params []) binders

(* Instantiating with no kinds moves a type to more kind variables. *)
let check_tvar_ctx_nk (sg: sig) (n: nat) (tv: list kind) (t: typ)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ check sg (tvar_ctx 0 tv) t KType)
          (ensures check sg (tvar_ctx n tv) t KType) =
  check_kinst sg [] n (tvar_ctx 0 tv) t KType;
  kinst_kinds_nil tv;
  kinst_ty_nil t;
  assert (kinst_ctx [] n (tvar_ctx 0 tv) == tvar_ctx n tv)

let rec check_tys_rev_acc (sg: sig) (g: ctx) (xs ys: list typ) (ks ls: list kind)
  : Lemma (requires check_tys sg g xs ks /\ check_tys sg g ys ls)
          (ensures check_tys sg g (L.rev_acc xs ys) (L.rev_acc ks ls)) (decreases xs) =
  match xs, ks with
  | [], [] -> ()
  | x :: xs', k :: ks' -> check_tys_rev_acc sg g xs' (x :: ys) ks' (k :: ls)

let rec check_tys_length (sg: sig) (g: ctx) (xs: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g xs ks) (ensures L.length xs == L.length ks) (decreases xs) =
  match xs, ks with
  | [], [] -> ()
  | _ :: xs', _ :: ks' -> check_tys_length sg g xs' ks'

let list_tsub_cons (x: typ) (l: list typ) (i: nat)
  : Lemma (list_tsub (x :: l) i == (if i = 0 then x else list_tsub l (i - 1))) = ()

let rec check_tys_list_tsub (sg: sig) (g: ctx) (xs: list typ) (ks: list kind) (i: nat) (k: kind)
  : Lemma (requires check_tys sg g xs ks /\ L.nth ks i == Some k)
          (ensures check sg g (list_tsub xs i) k) (decreases xs) =
  match xs, ks with
  | x :: xs', _ :: ks' ->
    list_tsub_cons x xs' i;
    if i = 0 then () else check_tys_list_tsub sg g xs' ks' (i - 1) k

let rec list_tsub_append (a b: list typ) (i: nat)
  : Lemma (ensures list_tsub (L.append a b) i ==
                   (if i < L.length a then list_tsub a i else list_tsub b (i - L.length a)))
          (decreases a) =
  match a with
  | [] -> ()
  | x :: a' ->
    list_tsub_cons x (L.append a' b) i;
    list_tsub_cons x a' i;
    if i = 0 then () else list_tsub_append a' b (i - 1)

let rev_acc_append (l acc: list typ) : Lemma (L.rev_acc l acc == L.append (L.rev l) acc) =
  LP.rev_acc_rev' l acc;
  LP.rev_rev' l

(* The two instantiations of `op_inst`, at one index. *)
let op_inst_at (a b: list typ) (i: nat)
  : Lemma (sub_ty (upn_tsub 0 (list_tsub a)) (upn_tsub (L.length a) (list_tsub b) i) ==
           list_tsub (L.append a b) i) =
  let m = L.length a in
  let tau = upn_tsub 0 (list_tsub a) in
  list_tsub_append a b i;
  introduce forall (j: nat). tau j == list_tsub a j
  with ren_ty_shift0 (list_tsub a j);
  if i < m then ()
  else begin
    let x = list_tsub b (i - m) in
    introduce forall (j: nat). tvar j == tau (shift m j)
    with ren_ty_shift0 (list_tsub a (shift m j));
    sub_ren_ty tau (shift m) tvar x;
    sub_ty_tvar x
  end

let op_inst_sub (ts ss: list typ) (t: typ)
  : Lemma (op_inst ts ss t == sub_ty (list_tsub (L.append (L.rev ss) (L.rev ts))) t) =
  let a = L.rev ss in
  let b = L.rev ts in
  LP.rev_length ss;
  introduce forall (i: nat).
    list_tsub (L.append a b) i ==
    sub_ty (upn_tsub 0 (list_tsub a)) (upn_tsub (L.length a) (list_tsub b) i)
  with op_inst_at a b i;
  sub_sub_ty (upn_tsub 0 (list_tsub a)) (upn_tsub (L.length a) (list_tsub b))
    (list_tsub (L.append a b)) t

let check_op_type (sg: sig) (g: ctx) (params binders: list kind) (ts ss: list typ) (t: typ)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ check sg (op_ctx 0 params binders) t KType /\
                    check_tys sg g ts params /\ check_tys sg g ss binders)
          (ensures check sg g (op_inst ts ss t) KType) =
  let tv = L.rev_acc binders (L.rev_acc params []) in
  let xs = L.rev_acc ss (L.rev_acc ts []) in
  let sigma = list_tsub xs in
  check_tvar_ctx_nk sg g.nk tv t;
  check_tys_rev_acc sg g ts [] params [];
  check_tys_rev_acc sg g ss (L.rev_acc ts []) binders (L.rev_acc params []);
  introduce forall (i: nat).
    (match L.nth tv i with Some k -> check sg g (sigma i) k | None -> True)
  with (match L.nth tv i with
        | Some k -> check_tys_list_tsub sg g xs tv i k
        | None -> ());
  assert (sub_ok sg sigma (tvar_ctx g.nk tv) g);
  check_sub sg sigma (tvar_ctx g.nk tv) g t KType;
  rev_acc_append ss (L.rev_acc ts []);
  op_inst_sub ts ss t

let check_op_inst sg g q ei op os ts ss =
  op_ok_of sg q ei op os;
  op_ctx_push ei.eff_params os.binders;
  check_op_type sg g ei.eff_params os.binders ts ss os.arg;
  check_op_type sg g ei.eff_params os.binders ts ss os.res

(* `switchCtor`. *)

(* The kind of `h σ̄`, `h` of kind `k`. *)
let rec spine_kind (sg: sig) (g: ctx) (k: kind) (ss: list typ) : Tot (option kind) (decreases ss) =
  match ss with
  | [] -> Some k
  | s :: ss' ->
    (match k with
     | KArrow k1 k2 -> if check sg g s k1 then spine_kind sg g k2 ss' else None
     | _ -> None)

let rec synth_tapps (sg: sig) (g: ctx) (h: typ) (ss: list typ)
  : Lemma (ensures synth_kind sg g (tapps h ss) ==
                   (match synth_kind sg g h with Some k -> spine_kind sg g k ss | None -> None))
          (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' -> synth_tapps sg g (TApp h s) ss'

let rec tapps_app (h: typ) (ss: list typ)
  : Lemma (requires TCon? h \/ TApp? h) (ensures TCon? (tapps h ss) \/ TApp? (tapps h ss))
          (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' -> tapps_app (TApp h s) ss'

let rec arg_kinds_kinst (ks: list kind) (k: kind)
  : Lemma (requires result k = KType)
          (ensures arg_kinds (kinst_kind ks k) == kinst_kinds ks (arg_kinds k)) (decreases k) =
  match k with
  | KArrow _ k2 -> arg_kinds_kinst ks k2
  | _ -> ()

(* `σ` begins with the binders `forall (a1 : κ1) … (an : κn)`, `kl` being
   `κ̄`. *)
let rec binds_kinds (kl: list kind) (t: typ) : Tot bool (decreases kl) =
  match kl with
  | [] -> true
  | k :: kl ->
    (match t with
     | TForall k' t' -> k' = k && binds_kinds kl t'
     | _ -> false)

let rec binds_kinds_foralls (kl: list kind) (t: typ)
  : Lemma (ensures binds_kinds kl (foralls kl t)) (decreases kl) =
  match kl with
  | [] -> ()
  | _ :: kl' -> binds_kinds_foralls kl' t

let rec binds_kinds_kinst (ks: list kind) (kl: list kind) (t: typ)
  : Lemma (requires binds_kinds kl t) (ensures binds_kinds (kinst_kinds ks kl) (kinst_ty ks t))
          (decreases kl) =
  match kl, t with
  | [], _ -> ()
  | _ :: kl', TForall _ t' -> binds_kinds_kinst ks kl' t'

let rec binds_kinds_sub (kl: list kind) (sigma: tsub) (t: typ)
  : Lemma (requires binds_kinds kl t) (ensures binds_kinds kl (sub_ty sigma t)) (decreases kl) =
  match kl, t with
  | [], _ -> ()
  | _ :: kl', TForall _ t' -> binds_kinds_sub kl' (up_tsub sigma) t'

(* Instantiating the leading binders of a type of kind `Type`, which bind
   the argument kinds of `k`, at arguments kinded as `σ̄` in `h σ̄`, `h` of
   kind `k`. *)
let rec inst_foralls_check (sg: sig) (g: ctx) (t: typ) (k: kind) (ss: list typ) (t': typ)
  : Lemma (requires check sg g t KType /\ Some? (spine_kind sg g k ss) /\
                    binds_kinds (arg_kinds k) t /\ inst_foralls t ss == Some t')
          (ensures check sg g t' KType) (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' ->
    let KArrow k1 k2 = k in
    let TForall _ b = t in
    check_subst1 sg g k1 s b KType;
    binds_kinds_sub (arg_kinds k2) (scons s tvar) b;
    inst_foralls_check sg g (subst1_ty s b) k2 ss' t'

(* The argument types of the function arrows of a type of kind `Type`. *)
let rec fun_args_ok (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires prim_wf sg /\ check sg g t KType) (ensures tys_ok sg g (fun_args sg t))
          (decreases t) =
  match t with
  | TApp (TApp (TApp (TCon q []) t1) r) t2 ->
    if is_function_tycon sg q then begin
      assert ((match sg.tycons q with
               | Some ti -> ti.tc_class = TcIntrinsic ClsFunction
               | None -> false) ==> q == prim_function);
      check_t_fun sg g t1 r t2;
      fun_args_ok sg g t2
    end
  | _ -> ()

(* What the instance `T [[κ̄]] σ̄` of kind `Type` says of `κ̄` and `σ̄`. *)
let tapps_con_kind (sg: sig) (g: ctx) (tq: qname) (ks: list kind) (ss: list typ)
  : Lemma (requires check sg g (tapps (TCon tq ks) ss) KType)
          (ensures Some? (sg.tycons tq) /\
                   (let ti = Some?.v (sg.tycons tq) in
                    L.length ks == ti.tc_nk /\ qkinds_wf g.nk ks /\
                    Some? (spine_kind sg g (kinst_kind ks ti.tc_kind) ss))) =
  tapps_app (TCon tq ks) ss;
  synth_tapps sg g (TCon tq ks) ss

(* What `Σ` says of a constructor `c` of the data type `tq`: it is owned
   by `tq`, so its scheme is `tq`'s constructor scheme. *)
let ctor_of_listed (sg: sig) (tq: qname) (cs: list qname) (c: qname)
  : Lemma (requires sig_ok sg /\ has_class sg tq (TcData cs) /\ L.mem c cs)
          (ensures Some? (sg.ctors c) /\
                   (let ti = Some?.v (sg.tycons tq) in
                    let ci = Some?.v (sg.ctors c) in
                    tycon_ok ti /\ scheme_ok sg ci.ct_nk ci.ct_ty /\ ci.ct_nk = ti.tc_nk /\
                    binds_kinds (arg_kinds ti.tc_kind) ci.ct_ty)) =
  let Some ti = sg.tycons tq in
  assert (tycon_ok ti);
  ctor_of_data sg tq ti cs c;
  let Some ci = sg.ctors c in
  assert (scheme_ok sg ci.ct_nk ci.ct_ty);
  assert (ctor_ok sg c ci);
  binds_kinds_foralls (arg_kinds ti.tc_kind)
    (pure_arrows (ctor_decl_fields ti ci.ct_ty)
       (tapps (TCon tq (kind_vars ti.tc_nk)) (type_vars (L.length (arg_kinds ti.tc_kind)))))

let ctor_fields_ok sg g tq ks ss cs c fs =
  tapps_con_kind sg g tq ks ss;
  ctor_of_listed sg tq cs c;
  let ti = Some?.v (sg.tycons tq) in
  let ci = Some?.v (sg.ctors c) in
  let k = kinst_kind ks ti.tc_kind in
  let t0 = kinst_ty ks ci.ct_ty in
  scheme_inst sg g ci.ct_nk ci.ct_ty ks;
  arg_kinds_kinst ks ti.tc_kind;
  binds_kinds_kinst ks (arg_kinds ti.tc_kind) ci.ct_ty;
  let t = Some?.v (inst_foralls t0 ss) in
  inst_foralls_check sg g t0 k ss t;
  fun_args_ok sg g t

let rec octx_ok_field_occs (sg: sig) (g: ctx) (o: occ) (c: qname) (j: nat) (fs: list typ)
  : Lemma (requires tys_ok sg g fs) (ensures octx_ok sg g (field_occs o c j fs)) (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs' -> octx_ok_field_occs sg g o c (j + 1) fs'

let octx_ok_ctor_branch sg g om o tq ks ss cs c fs =
  ctor_fields_ok sg g tq ks ss cs c fs;
  octx_ok_field_occs sg g o c 0 fs;
  octx_ok_append sg g (field_occs o c 0 fs) om
