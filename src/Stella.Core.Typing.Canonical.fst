(* Proof structure.

   The head of a type is read off its canonical form (`chead`), and its
   class off `Σ` (`head_class`); both depend on the type only through
   `canon`, so a conversion keeps them. `value_shape` computes, by
   recursion on the derivation of a value, a fact about its type per form
   (`vshape`): the class of its head, or the binder its canonical form
   starts with; for a variant value also its view, which a `weaken` keeps
   from its operand. A chain is normalized (`Stella.Core.Typing.Chain`) and
   classified by its cursor remainder (`chain_shape`): a `forall`, a
   constrained type, a function type (`t_fun`, by `class_unique`), or, for
   a constructor, a saturated remainder whose instance is headed by the
   constructor's owner, a data type.

   Each canonical form compares the class of the given type with the one
   `vshape` gives (`shape_*`). The record field recurses on the record
   value, keeping the entries of the row it reads within those of the
   original row, whose sharpness gives the payload at the hit. *)
module Stella.Core.Typing.Canonical
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Rows.Split
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Sharp
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Spine.Wf
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Regularity
open Stella.Core.Typing.Inversion
open Stella.Core.Typing.Chain
open Stella.Core.Typing.Ctor
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module V = Stella.Core.Value

(* Constructors and their owners. *)

let ctor_owner_listed sg c ci cs = assert (ctor_ok sg c ci)

(* Heads of canonical types. *)

let rec chead (c: ctyp) : Tot (option qname) (decreases c) =
  match c with
  | CCon q _ -> Some q
  | CApp f _ -> chead f
  | _ -> None

let head_class (sg: sig) (t: typ) : option tycon_class =
  match chead (canon t) with
  | Some q -> (match sg.tycons q with Some ti -> Some ti.tc_class | None -> None)
  | None -> None

let rec chead_ty_head (t: typ)
  : Lemma (requires Some? (ty_head t)) (ensures chead (canon t) == ty_head t) (decreases t) =
  match t with
  | TCon _ _ -> ()
  | TApp f _ -> chead_ty_head f

let rec chead_tapps (h: typ) (ss: list typ)
  : Lemma (ensures chead (canon (tapps h ss)) == chead (canon h)) (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' -> chead_tapps (TApp h s) ss'

let rec ty_head_tapps (h: typ) (ss: list typ)
  : Lemma (ensures ty_head (tapps h ss) == ty_head h) (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' -> ty_head_tapps (TApp h s) ss'

let chead_t_fun (a rho b: typ) : Lemma (chead (canon (t_fun a rho b)) == Some prim_function) =
  assert_norm (chead (canon (t_fun a rho b)) == Some prim_function)

let class_fun (sg: sig) (a rho b: typ)
  : Lemma (requires prim_wf sg)
          (ensures head_class sg (t_fun a rho b) == Some (TcIntrinsic ClsFunction)) =
  chead_t_fun a rho b

let class_record (sg: sig) (rr: typ)
  : Lemma (requires prim_wf sg) (ensures head_class sg (t_record rr) == Some (TcIntrinsic ClsRecord)) =
  ()

let class_variant (sg: sig) (rr: typ)
  : Lemma (requires prim_wf sg)
          (ensures head_class sg (t_variant rr) == Some (TcIntrinsic ClsVariant)) =
  ()

let class_lit (sg: sig) (c: lit)
  : Lemma (requires prim_wf sg)
          (ensures head_class sg (lit_type c) == Some (TcIntrinsic ClsLiteral)) =
  match c with
  | LInt _ | LNumber _ | LString _ | LChar _ | LBool _ -> ()

let class_tapps (sg: sig) (q: qname) (ks: list kind) (ss: list typ) (c: tycon_class)
  : Lemma (requires has_class sg q c) (ensures head_class sg (tapps (TCon q ks) ss) == Some c) =
  chead_tapps (TCon q ks) ss

let class_opaque (sg: sig) (t: typ)
  : Lemma (requires opaque_type sg t) (ensures head_class sg t == Some (TcIntrinsic ClsOpaque)) =
  chead_ty_head t

(* The opaque class. *)

let prim_not_opaque sg a rho b rr =
  assert_norm (ty_head (t_fun a rho b) == Some prim_function)

let data_not_opaque sg tq ks ss cs = ty_head_tapps (TCon tq ks) ss

(* The shape of the type of a value. *)

(** A chain at its cursor remainder `s`: a `forall`, a constrained type,
    a function type, or the saturated remainder of a constructor, whose
    instance is headed by a data type. *)
let chain_shape (sg: sig) (v: exp) (t: typ) : prop =
  match chain_cursor sg v with
  | Some (s, th) ->
    ty_eq t (sub_ty th s) /\
    ((TForall? s /\ CForall? (canon t)) \/
     (TConstr? s /\ CConstr? (canon t)) \/
     (Some? (as_function sg s) /\ head_class sg t == Some (TcIntrinsic ClsFunction)) \/
     (saturated sg s /\ Some? (ctor_head sg v) /\ Some? (head_class sg t) /\
      TcData? (Some?.v (head_class sg t))))
  | None -> False

let vshape (sg: sig) (v: exp) (t: typ) : prop =
  match v with
  | ELit c -> ty_eq t (lit_type c) /\ head_class sg t == Some (TcIntrinsic ClsLiteral)
  | ELam _ _ _ | EOpenEff _ _ -> head_class sg t == Some (TcIntrinsic ClsFunction)
  | ETyLam _ _ -> CForall? (canon t)
  | ECLam _ _ -> CConstr? (canon t)
  | ERecEmpty | EExtend _ _ _ -> head_class sg t == Some (TcIntrinsic ClsRecord)
  | EInject _ _ _ | EWeaken _ _ _ ->
    head_class sg t == Some (TcIntrinsic ClsVariant) /\ Some? (variant_view v)
  | EOpaque _ _ -> head_class sg t == Some (TcIntrinsic ClsOpaque)
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> chain_shape sg v t
  | _ -> False

let is_chain_form (v: exp) : bool = EGlobal? v || EApp? v || ETyApp? v || ECApp? v

let value_chain_form (sg: sig) (v: exp)
  : Lemma (requires V.is_value sg v /\ is_chain_form v)
          (ensures V.value_head sg v /\ Some? (decompose_global_app v)) = ()

(* A remainder that is a function type is `t_fun` under every
   substitution. *)
let fun_remainder (sg: sig) (s: typ) (th: tsub) (t: typ)
  : Lemma (requires prim_wf sg /\ Some? (as_function sg s) /\ ty_eq t (sub_ty th s))
          (ensures head_class sg t == Some (TcIntrinsic ClsFunction)) =
  let Some (a, rho, b) = as_function sg s in
  as_function_sub sg th s a rho b;
  as_function_t_fun sg (sub_ty th s) (sub_ty th a) (sub_ty th rho) (sub_ty th b);
  class_fun sg (sub_ty th a) (sub_ty th rho) (sub_ty th b)

(* A saturated constructor remainder is an instance of the owner. *)
let ctor_remainder (sg: sig) (v: exp) (s: typ) (th: tsub) (t: typ)
  : Lemma (requires sig_ok sg /\ chain_cursor sg v == Some (s, th) /\ saturated sg s /\
                    is_ctor sg (let Some (q, _, _) = decompose_global_app v in q) /\
                    Some? (decompose_global_app v) /\ ty_eq t (sub_ty th s))
          (ensures Some? (ctor_head sg v) /\ Some? (head_class sg t) /\
                   TcData? (Some?.v (head_class sg t))) =
  let Some (c, ks, args) = decompose_global_app v in
  let Some ci = sg.ctors c in
  ctor_chain_saturated sg v c ks args ci s th;
  assert (ctor_ok sg c ci);
  chead_tapps (TCon ci.ct_owner ks) (ty_args args)

(* A substitution keeps the binder a type starts with. *)
let canon_sub_binder (th: tsub) (s: typ)
  : Lemma (requires TForall? s \/ TConstr? s)
          (ensures (TForall? s ==> CForall? (canon (sub_ty th s))) /\
                   (TConstr? s ==> CConstr? (canon (sub_ty th s)))) = ()

let chain_shape_lemma (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ is_chain_form v) (ensures chain_shape sg v t) =
  value_chain_form sg v;
  value_chain_normalizes sg v;
  let _ = chain_normal h in
  let Some (s, th) = chain_cursor sg v in
  match s with
  | TForall k b -> canon_sub_binder th s
  | TConstr c b -> canon_sub_binder th s
  | _ ->
    if Some? (as_function sg s) then fun_remainder sg s th t
    else ctor_remainder sg v s th t

(* A variant value's operand under `weaken` has a view. *)
let shape_view (sg: sig) (v: exp) (t: typ)
  : Lemma (requires prim_wf sg /\ vshape sg v t /\ head_class sg t == Some (TcIntrinsic ClsVariant))
          (ensures Some? (variant_view v)) = ()

(* `sig_ok`, hidden from the cases that do not read it. *)
[@@"opaque_to_smt"]
let sig_ok_h (sg: sig) : prop = sig_ok sg

let hide_sig_ok (sg: sig) : Lemma (requires sig_ok sg) (ensures sig_ok_h sg /\ prim_wf sg) =
  reveal_opaque (`%sig_ok_h) (sig_ok_h sg)

let chain_shape_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r)
  : Lemma (requires sig_ok_h sg /\ V.is_value sg v /\ is_chain_form v) (ensures chain_shape sg v t) =
  reveal_opaque (`%sig_ok_h) (sig_ok_h sg);
  chain_shape_lemma h

let rec value_shape_go (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r)
  : Lemma (requires sig_ok_h sg /\ prim_wf sg /\ V.is_value sg v) (ensures vshape sg v t)
          (decreases h) =
  if is_chain_form v then chain_shape_h h
  else match h with
  | T_Conv h1 _ _ -> value_shape_go h1
  | T_Lit #_ #_ #_ #_ #c _ -> class_lit sg c
  | T_Lam #_ #_ #_ #_ #t1 #r' #_ #t2 _ _ _ -> class_fun sg t1 r' t2
  | T_OpenEff #_ #_ #_ #_ #r' #_ #t1 #r1 #t2 _ _ -> class_fun sg t1 (TRowUnion r1 r') t2
  | T_TyLam _ _ _ _ -> ()
  | T_CLam _ _ _ _ -> ()
  | T_RecEmpty _ -> class_record sg TRowEmpty
  | T_Extend #_ #_ #_ #_ #k #_ #_ #t1 #r0 _ _ _ -> class_record sg (TRowExt (EntTy k t1) r0)
  | T_Inject #_ #_ #_ #_ #k #r0 #_ #t1 _ _ _ -> class_variant sg (TRowExt (EntTy k t1) r0)
  | T_Weaken #_ #_ #_ #_ #k #t1 #e1 #r0 h1 _ _ ->
    value_shape_go h1;
    class_variant sg r0;
    shape_view sg e1 (t_variant r0);
    class_variant sg (TRowExt (EntTy k t1) r0)
  | T_VariantValue vr0 vr _ _ _ _ -> class_variant sg vr
  | T_Opaque _ _ -> class_opaque sg t
  | _ -> ()

let value_shape (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r)
  : Lemma (requires sig_ok sg /\ V.is_value sg v) (ensures vshape sg v t) =
  hide_sig_ok sg;
  value_shape_go h

(* Comparing classes. *)

let shape_fun (sg: sig) (v: exp) (t: typ)
  : Lemma (requires prim_wf sg /\ V.is_value sg v /\ vshape sg v t /\
                    head_class sg t == Some (TcIntrinsic ClsFunction))
          (ensures ELam? v \/ EOpenEff? v \/
                   (V.value_head sg v /\
                    (match chain_cursor sg v with
                     | Some (s, th) -> Some? (as_function sg s) /\ ty_eq t (sub_ty th s)
                     | None -> False))) =
  if is_chain_form v then value_chain_form sg v

let shape_binder (sg: sig) (v: exp) (t: typ)
  : Lemma (requires V.is_value sg v /\ vshape sg v t /\
                    (CForall? (canon t) \/ CConstr? (canon t)))
          (ensures (CForall? (canon t) ==>
                    ETyLam? v \/
                    (V.value_head sg v /\
                     (match chain_cursor sg v with
                      | Some (s, th) -> TForall? s /\ ty_eq t (sub_ty th s)
                      | None -> False))) /\
                   (CConstr? (canon t) ==>
                    ECLam? v \/
                    (V.value_head sg v /\
                     (match chain_cursor sg v with
                      | Some (s, th) -> TConstr? s /\ ty_eq t (sub_ty th s)
                      | None -> False)))) =
  if is_chain_form v then value_chain_form sg v

(* Abstractions. *)

let canonical_fun #sg #ln #g #d #v #t #r h a rho b =
  value_shape h;
  class_fun sg a rho b;
  shape_fun sg v t

let canonical_forall #sg #ln #g #d #v #t #r h k s0 =
  value_shape h;
  shape_binder sg v t

let canonical_constr #sg #ln #g #d #v #t #r h c s0 =
  value_shape h;
  shape_binder sg v t

(* Records. *)

let shape_record (sg: sig) (v: exp) (t: typ)
  : Lemma (requires prim_wf sg /\ V.is_value sg v /\ vshape sg v t /\
                    head_class sg t == Some (TcIntrinsic ClsRecord))
          (ensures v == ERecEmpty \/ EExtend? v) =
  if is_chain_form v then value_chain_form sg v

let canonical_record #sg #ln #g #d #v #t #r h rr =
  value_shape h;
  class_record sg rr;
  shape_record sg v t

(** The entries of a row `rr` the recursion has reached, all entries of the
    original row `rr0`. *)
let entries_within (rr rr0: typ) : prop =
  forall (e: centry). L.mem e (row_entries (canon rr)) ==> L.mem e (row_entries (canon rr0))

let entries_within_ext (k: key) (t1 r0 rr rr0: typ)
  : Lemma (requires ty_eq rr (TRowExt (EntTy k t1) r0) /\ entries_within rr rr0)
          (ensures entries_within r0 rr0 /\ L.mem (k, PTy (canon t1)) (row_entries (canon rr0))) =
  FStar.Classical.forall_intro (mem_entries_ext (EntTy k t1) r0)

let entry_miss (k k': key) (pt t1 r0 rr: typ)
  : Lemma (requires ty_eq rr (TRowExt (EntTy k' t1) r0) /\ k' <> k /\
                    L.mem (k, PTy (canon pt)) (row_entries (canon rr)))
          (ensures L.mem (k, PTy (canon pt)) (row_entries (canon r0))) =
  mem_entries_ext (EntTy k' t1) r0 (k, PTy (canon pt))

let entry_hit (sg: sig) (g: ctx) (k: key) (pt t1 rr0: typ)
  : Lemma (requires check sg g rr0 (KRow EType) /\ not (inconsistent (hyps g)) /\
                    L.mem (k, PTy (canon pt)) (row_entries (canon rr0)) /\
                    L.mem (k, PTy (canon t1)) (row_entries (canon rr0)))
          (ensures ty_eq t1 pt) =
  check_sharp sg g rr0 EType

let extend_values (sg: sig) (k k': key) (v1 v2: exp)
  : Lemma (requires V.is_value sg (EExtend k' v1 v2))
          (ensures V.is_value sg v1 /\ V.is_value sg v2 /\
                   record_field k (EExtend k' v1 v2) ==
                   (if k' = k then Some v1 else record_field k v2)) = ()

let rec record_field_go (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (rr0 rr: typ) (k: key) (pt: typ)
  : Pure (w: exp & typing sg ln g [] w pt r)
         (requires sig_ok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\ V.is_value sg v /\
                   ty_eq t (t_record rr) /\ check sg g rr0 (KRow EType) /\ check sg g pt KType /\
                   entries_within rr rr0 /\
                   L.mem (k, PTy (canon pt)) (row_entries (canon rr0)) /\
                   L.mem (k, PTy (canon pt)) (row_entries (canon rr)))
         (ensures fun (| w, _ |) -> record_field k v == Some w /\ V.is_value sg w)
         (decreases v) =
  canonical_record h rr;
  match v with
  | ERecEmpty ->
    let h0 : typing sg ln g d ERecEmpty t r = h in
    inv_rec_empty h0 rr; false_elim ()
  | EExtend k' v1 v2 ->
    let h0 : typing sg ln g d (EExtend k' v1 v2) t r = h in
    let p = inv_extend h0 rr in
    extend_values sg k k' v1 v2;
    entries_within_ext k' p.ext_ty p.ext_rest rr rr0;
    if k' = k then begin
      entry_hit sg g k pt p.ext_ty rr0;
      typing_regular h;
      (| v1, T_Conv p.ext_head () () |)
    end
    else begin
      entry_miss k k' pt p.ext_ty p.ext_rest rr;
      record_field_go p.ext_tail rr0 p.ext_rest k pt
    end

let canonical_record_field #sg #ln #g #d #v #t #r h rr k pt =
  record_field_go h rr rr k pt

(* Variants. *)

let canonical_variant #sg #ln #g #d #v #t #r h rr =
  value_shape h;
  class_variant sg rr

let canonical_variant_empty #sg #ln #g #d #v #t #r h rr =
  canonical_variant h rr;
  let Some (k, w) = variant_view v in
  let _ = inv_variant h k w rr in
  ()

(* Literals. *)

let shape_lit (sg: sig) (v: exp) (t: typ) (lq: qname)
  : Lemma (requires prim_wf sg /\ V.is_value sg v /\ vshape sg v t /\ ty_eq t (TCon lq []) /\
                    head_class sg t == Some (TcIntrinsic ClsLiteral))
          (ensures (match v with
                    | ELit c -> ty_eq (lit_type c) (TCon lq []) /\ lit_of v == Some c
                    | _ -> False)) =
  if is_chain_form v then value_chain_form sg v

let canonical_lit #sg #ln #g #d #v #t #r h lq =
  value_shape h;
  class_tapps sg lq [] [] (TcIntrinsic ClsLiteral);
  shape_lit sg v t lq

let canonical_bool #sg #ln #g #d #v #t #r h =
  canonical_lit h prim_boolean

(* Data types. *)

let ctor_head_ctors (sg: sig) (v: exp)
  : Lemma (requires Some? (ctor_head sg v))
          (ensures (match decompose_global_app v with
                    | Some (c, _, _) -> ctor_head sg v == Some c /\ is_ctor sg c /\ Some? (sg.ctors c)
                    | None -> False)) = ()

let data_chain (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (tq: qname) (ks: list kind) (ss: list typ) (cs: list qname)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ is_chain_form v /\
                    ty_eq t (tapps (TCon tq ks) ss) /\ has_class sg tq (TcData cs) /\
                    Some? (ctor_head sg v))
          (ensures (match ctor_head sg v, decompose_global_app v with
                    | Some c, Some (c', ks', _) ->
                      c' == c /\ ks' == ks /\ is_ctor sg c /\ L.mem c cs /\
                      Some? (ctor_fields sg c ks ss)
                    | _ -> False)) =
  value_chain_form sg v;
  value_chain_normalizes sg v;
  let _ = chain_normal h in
  let Some (s, th) = chain_cursor sg v in
  ctor_head_ctors sg v;
  let Some (c, ks0, args) = decompose_global_app v in
  ty_eq_sym t (sub_ty th s);
  ty_eq_trans (sub_ty th s) t (tapps (TCon tq ks) ss);
  saturated_of_data sg s th tq ks ss cs;
  let Some ci = sg.ctors c in
  ctor_chain_saturated sg v c ks0 args ci s th;
  ty_eq_tapps_inv ci.ct_owner tq ks0 ks (ty_args args) ss;
  ctor_fields_tys_eq sg c ks0 (ty_args args) ss;
  ctor_owner_listed sg c ci cs

let shape_data (sg: sig) (v: exp) (t: typ) (cs: list qname)
  : Lemma (requires prim_wf sg /\ V.is_value sg v /\ vshape sg v t /\
                    head_class sg t == Some (TcData cs))
          (ensures is_chain_form v /\ Some? (ctor_head sg v)) =
  if is_chain_form v then value_chain_form sg v

let canonical_data #sg #ln #g #d #v #t #r h tq ks ss cs =
  value_shape h;
  class_tapps sg tq ks ss (TcData cs);
  shape_data sg v t cs;
  data_chain h tq ks ss cs

(* Opaque types. *)

let shape_opaque (sg: sig) (v: exp) (t: typ)
  : Lemma (requires prim_wf sg /\ V.is_value sg v /\ vshape sg v t /\
                    head_class sg t == Some (TcIntrinsic ClsOpaque))
          (ensures EOpaque? v) =
  if is_chain_form v then value_chain_form sg v

let canonical_opaque #sg #ln #g #d #v #t #r h t' =
  value_shape h;
  class_opaque sg t';
  shape_opaque sg v t
