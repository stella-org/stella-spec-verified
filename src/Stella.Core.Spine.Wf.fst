(* Proof structure.

   Purity: `spine_pure` reads a type along the path the cursor walks, the
   bodies of `forall` and of constraint arrows and the results of arrows,
   and requires every arrow on it to be pure. A constructor scheme has it,
   since its arrows are written `-{()}->` and its result is headed by a data
   type, and a foreign's type has it by `arrows_pure`, the function type
   constructor being `Prim.Function` alone. Kind instantiation and every
   cursor step keep it.

   Regularity: the invariant is the conclusion itself, that the instance
   `θ(σ)` of the current remainder is kinded. A `[τ]` step instantiates the
   bound variable (`check_subst1`, `cursor_instance_forall`), a `[•]` step
   discharges the constraint by cut (`check_cut`), and a value step reads
   the result of a kinded function type. *)
module Stella.Core.Spine.Wf
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
module L = FStar.List.Tot

(* Function types. *)

let function_tycon_prim (sg: sig) (q: qname)
  : Lemma (requires prim_wf sg /\ is_function_tycon sg q) (ensures q == prim_function) =
  assert ((match sg.tycons q with
           | Some ti -> ti.tc_class = TcIntrinsic ClsFunction
           | None -> false) ==> q == prim_function)

let as_function_t_fun sg t t1 r t2 =
  let TApp (TApp (TApp (TCon q []) _) _) _ = t in
  function_tycon_prim sg q

let check_as_function sg g t t1 r t2 =
  as_function_t_fun sg t t1 r t2;
  check_t_fun sg g t1 r t2

(* Purity. *)

let rec spine_pure (sg: sig) (t: typ) : Tot bool (decreases t) =
  match t with
  | TForall _ b | TConstr _ b -> spine_pure sg b
  | TApp (TApp (TApp (TCon q []) _) r) t2 ->
    not (is_function_tycon sg q) || (ty_eq r TRowEmpty && spine_pure sg t2)
  | _ -> true

let spine_pure_arrow (sg: sig) (t t1 r t2: typ)
  : Lemma (requires spine_pure sg t /\ as_function sg t == Some (t1, r, t2))
          (ensures ty_eq r TRowEmpty) =
  ()

(* `kinst_ty` is unfolded one application node at a time. *)
let rec spine_pure_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (requires spine_pure sg t) (ensures spine_pure sg (kinst_ty ks t)) (decreases t) =
  match t with
  | TForall _ b | TConstr _ b -> spine_pure_kinst sg ks b
  | TApp f t2 ->
    assert (kinst_ty ks t == TApp (kinst_ty ks f) (kinst_ty ks t2));
    (match f with
     | TApp g r ->
       assert (kinst_ty ks f == TApp (kinst_ty ks g) (kinst_ty ks r));
       (match g with
        | TApp h t1 ->
          assert (kinst_ty ks g == TApp (kinst_ty ks h) (kinst_ty ks t1));
          (match h with
           | TCon q [] ->
             if is_function_tycon sg q then begin
               ty_eq_kinst ks r TRowEmpty;
               spine_pure_kinst sg ks t2
             end
           | _ -> ())
        | _ -> ())
     | _ -> ())
  | _ -> ()

let spine_pure_step (sg: sig) (t: typ) (th: tsub) (a: spine_arg) (t': typ) (th': tsub)
  : Lemma (requires spine_pure sg t /\ cursor_step sg t th a == Some (t', th'))
          (ensures spine_pure sg t') =
  ()

let rec spine_pure_cursor (sg: sig) (t: typ) (th: tsub) (args: list spine_arg) (t': typ)
  (th': tsub)
  : Lemma (requires spine_pure sg t /\ cursor sg t th args == Some (t', th'))
          (ensures spine_pure sg t') (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    let Some (t1, th1) = cursor_step sg t th a in
    spine_pure_step sg t th a t1 th1;
    spine_pure_cursor sg t1 th1 args' t' th'

let rec spine_pure_foralls (sg: sig) (ks: list kind) (t: typ)
  : Lemma (requires spine_pure sg t) (ensures spine_pure sg (foralls ks t)) (decreases ks) =
  match ks with
  | [] -> ()
  | _ :: ks' -> spine_pure_foralls sg ks' t

let rec spine_pure_pure_arrows (sg: sig) (fs: list typ) (t: typ)
  : Lemma (requires spine_pure sg t) (ensures spine_pure sg (pure_arrows fs t)) (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs' -> ty_eq_refl TRowEmpty; spine_pure_pure_arrows sg fs' t

let rec tapps_head (h: typ) (ts: list typ)
  : Lemma (requires TCon? h \/ TApp? h)
          (ensures (TCon? (tapps h ts) \/ TApp? (tapps h ts)) /\ ty_head (tapps h ts) == ty_head h)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> tapps_head (TApp h t) ts'

(* A type headed by a constructor other than a function type constructor
   is no arrow. *)
let spine_pure_headed (sg: sig) (t: typ) (q: qname)
  : Lemma (requires (TCon? t \/ TApp? t) /\ ty_head t == Some q /\ not (is_function_tycon sg q))
          (ensures spine_pure sg t) =
  match t with
  | TApp (TApp (TApp h a) b) _ ->
    assert (ty_head t == ty_head (TApp (TApp h a) b));
    assert (ty_head (TApp (TApp h a) b) == ty_head (TApp h a));
    assert (ty_head (TApp h a) == ty_head h)
  | _ -> ()

let ctor_spine_pure (sg: sig) (c: qname) (ci: ctor_info)
  : Lemma (requires ctor_ok sg c ci) (ensures spine_pure sg ci.ct_ty) =
  let Some ti = sg.tycons ci.ct_owner in
  let ps = arg_kinds ti.tc_kind in
  let res = tapps (TCon ci.ct_owner (kind_vars ti.tc_nk)) (type_vars (L.length ps)) in
  tapps_head (TCon ci.ct_owner (kind_vars ti.tc_nk)) (type_vars (L.length ps));
  spine_pure_headed sg res ci.ct_owner;
  spine_pure_pure_arrows sg (ctor_decl_fields ti ci.ct_ty) res;
  spine_pure_foralls sg ps (pure_arrows (ctor_decl_fields ti ci.ct_ty) res)

let rec foreign_spine_pure (sg: sig) (t: typ)
  : Lemma (requires prim_wf sg /\ arrows_pure t) (ensures spine_pure sg t) (decreases t) =
  match t with
  | TForall _ b | TConstr _ b -> foreign_spine_pure sg b
  | TApp (TApp (TApp (TCon q []) _) r) t2 ->
    if is_function_tycon sg q then begin
      function_tycon_prim sg q;
      foreign_spine_pure sg t2
    end
  | _ -> ()

let global_spine_pure (sg: sig) (q: qname) (c: global_class) (nk: nat) (t: typ)
  : Lemma (requires sig_ok sg /\ global_scheme sg q == Some (c, nk, t)) (ensures spine_pure sg t) =
  match sg.ctors q, sg.foreigns q with
  | Some ci, _ -> assert (ctor_ok sg q ci); ctor_spine_pure sg q ci
  | None, Some fi -> assert (arrows_pure fi.fr_ty); foreign_spine_pure sg fi.fr_ty

let cursor_arrow_pure sg q ks args t th t1 r t2 =
  let Some (c, nk, t0) = global_scheme sg q in
  global_spine_pure sg q c nk t0;
  spine_pure_kinst sg ks t0;
  spine_pure_cursor sg (kinst_ty ks t0) tvar args t th;
  spine_pure_arrow sg t t1 r t2;
  ty_eq_sub th r TRowEmpty

(* Well-formed arguments. *)

let rec cursor_args_ok_snoc sg g t th args a =
  match args with
  | [] -> ()
  | b :: args' ->
    match cursor_step sg t th b with
    | Some (t1, th1) -> cursor_args_ok_snoc sg g t1 th1 args' a
    | None -> ()

let spine_args_ok_snoc sg g q ks args a =
  match global_scheme sg q with
  | Some (_, nk, t) -> cursor_args_ok_snoc sg g (kinst_ty ks t) tvar args a
  | None -> ()

(* Regularity. *)

let global_scheme_ok (sg: sig) (q: qname) (c: global_class) (nk: nat) (t: typ)
  : Lemma (requires sig_wf sg /\ global_scheme sg q == Some (c, nk, t)) (ensures scheme_ok sg nk t) =
  match sg.ctors q, sg.foreigns q with
  | Some ci, _ -> assert (scheme_ok sg ci.ct_nk ci.ct_ty)
  | None, Some fi -> assert (scheme_ok sg fi.fr_nk fi.fr_ty)

let spine_cursor_nil_regular sg g q ks =
  let Some (c, nk, t) = global_scheme sg q in
  global_scheme_ok sg q c nk t;
  scheme_inst sg g nk t ks;
  sub_ty_tvar (kinst_ty ks t)

let cursor_step_regular sg g t th a t' th' =
  match a, t with
  | STy s, TForall k body ->
    check_forall sg g k (sub_ty (up_tsub th) body);
    check_subst1 sg g k s (sub_ty (up_tsub th) body) KType;
    cursor_instance_forall s th body
  | SConstr, TConstr c body ->
    let c' = sub_constr th c in
    check_constr sg g c' (sub_ty th body);
    add_assump_assumps g c';
    check_cut sg g [c'] (sub_ty th body) KType
  | SVal _, _ ->
    let Some (t1, r, t2) = as_function sg t in
    as_function_sub sg th t t1 r t2;
    check_as_function sg g (sub_ty th t) (sub_ty th t1) (sub_ty th r) (sub_ty th t2)

let rec cursor_regular sg g t th args t' th' =
  match args with
  | [] -> ()
  | a :: args' ->
    let Some (t1, th1) = cursor_step sg t th a in
    cursor_step_regular sg g t th a t1 th1;
    cursor_regular sg g t1 th1 args' t' th'

let spine_cursor_regular sg g q ks args t th =
  spine_cursor_nil_regular sg g q ks;
  let Some (_, _, t0) = global_scheme sg q in
  cursor_regular sg g (kinst_ty ks t0) tvar args t th

let spine_cursor_fun_regular sg g q ks args t th t1 r t2 =
  spine_cursor_regular sg g q ks args t th;
  as_function_sub sg th t t1 r t2;
  check_as_function sg g (sub_ty th t) (sub_ty th t1) (sub_ty th r) (sub_ty th t2);
  cursor_arrow_pure sg q ks args t th t1 r t2

(* Chains under type substitution. *)

let rec ty_args_count (args: list spine_arg) : Tot nat (decreases args) =
  match args with
  | [] -> 0
  | STy _ :: args -> 1 + ty_args_count args
  | _ :: args -> ty_args_count args

(* `θ` followed by `σ`. *)
let tsub_then (sigma th: tsub) (i: nat) : typ = sub_ty sigma (th i)

let rec cursor_sub_args (sg: sig) (sigma: tsub) (n: nat) (t: typ) (th th': tsub)
  (args: list spine_arg)
  : Lemma (requires tvs_below n t /\ (forall (i: nat). i < n ==> th' i == sub_ty sigma (th i)) /\
                    Some? (cursor sg t th args))
          (ensures (let Some (t1, th1) = cursor sg t th args in
                    match cursor sg t th' (L.map (sub_arg sigma) args) with
                    | Some (t1', th1') ->
                      t1' == t1 /\ tvs_below (n + ty_args_count args) t1 /\
                      (forall (i: nat). i < n + ty_args_count args ==> th1' i == sub_ty sigma (th1 i))
                    | None -> False))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    match a, t with
    | STy s, TForall _ body ->
      introduce forall (i: nat). i < n + 1 ==> scons (sub_ty sigma s) th' i == sub_ty sigma (scons s th i)
      with introduce _ ==> _
      with (if i = 0 then () else assert (th' (i - 1) == sub_ty sigma (th (i - 1))));
      cursor_sub_args sg sigma (n + 1) body (scons s th) (scons (sub_ty sigma s) th') args'
    | SConstr, TConstr _ body -> cursor_sub_args sg sigma n body th th' args'
    | SVal _, _ ->
      let Some (_, _, t2) = as_function sg t in
      cursor_sub_args sg sigma n t2 th th' args'

let inst_sub (n: nat) (sigma th th': tsub) (u: typ)
  : Lemma (requires tvs_below n u /\ (forall (i: nat). i < n ==> th' i == sub_ty sigma (th i)))
          (ensures sub_ty th' u == sub_ty sigma (sub_ty th u)) =
  sub_sub_ty sigma th (tsub_then sigma th) u;
  sub_tvs_ext n th' (tsub_then sigma th) u

let chain_cursor_sub_ty sg sigma e t th =
  decompose_sub_ty_exp sigma e;
  let Some (q, ks, args) = decompose_global_app e in
  let Some (c, nk, t0) = global_scheme sg q in
  global_scheme_ok sg q c nk t0;
  check_tvs_below sg (decl_ctx nk) t0 KType;
  kinst_tvs_below ks 0 t0;
  cursor_sub_args sg sigma 0 (kinst_ty ks t0) tvar tvar args;
  let m = ty_args_count args in
  let Some (_, th') = cursor sg (kinst_ty ks t0) tvar (L.map (sub_arg sigma) args) in
  inst_sub m sigma th th' t;
  introduce forall (t1 r t2: typ). as_function sg t == Some (t1, r, t2) ==>
    sub_ty th' t1 == sub_ty sigma (sub_ty th t1) /\
    sub_ty th' r == sub_ty sigma (sub_ty th r) /\
    sub_ty th' t2 == sub_ty sigma (sub_ty th t2)
  with introduce _ ==> _
  with begin
    let TApp (TApp (TApp f _) _) _ = t in
    assert (tvs_below m (TApp (TApp f t1) r) /\ tvs_below m t2);
    assert (tvs_below m (TApp f t1) /\ tvs_below m r);
    inst_sub m sigma th th' t1;
    inst_sub m sigma th th' r;
    inst_sub m sigma th th' t2
  end;
  introduce forall (c: constr) (b: typ). t == TConstr c b ==>
    sub_constr th' c == sub_constr sigma (sub_constr th c)
  with introduce _ ==> _
  with begin
    (* `TConstr c ()` carries `c` alone. *)
    let u = TConstr c TRowEmpty in
    assert (tvs_below_constr m c);
    assert (tvs_below m u);
    inst_sub m sigma th th' u;
    assert (sub_ty th' u == TConstr (sub_constr th' c) TRowEmpty);
    assert (sub_ty sigma (sub_ty th u) == TConstr (sub_constr sigma (sub_constr th c)) TRowEmpty)
  end
