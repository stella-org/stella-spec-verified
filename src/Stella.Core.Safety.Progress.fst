(* Proof structure.

   The induction is on the term (`prog`, `decreases e`), not on the
   derivation: the hole's derivation that `plug1_typing` gives may be
   rebuilt (a chain prefix retyped by `T_Chain`, conversions stripped), so
   it is no subderivation. The induction hypothesis is passed to the
   helpers as a function on the subterms of `e` (`ih_t`).

   The premises on `Σ`, `Γ_R`, `Γ_N` and `G` are hidden behind the opaque
   `env_ok` (`Stella.Core.Safety.Hidden`), and those on the term behind the
   opaque `term_ok`: the quantifiers of `sig_ok`, `genv_ok` and `pre_ok`
   stay out of every query but the few that reveal them. A lemma of
   `Typing.Plug` or `Typing.Occ` is called through its wrapper in
   `Safety.Hidden` (`*_h`), which asks for the hidden `sok` that
   `env_ok_sok` gives. A lemma of `Typing.Canonical`, and condition (3) of
   `genv_ok`, are called through a wrapper here (`w_*`) that reveals
   `env_ok`. `term_ok` is read by `term_ok_*`.

   Each form has one helper (`prog_*`). A subterm in an evaluation
   position that is no value is split off by `plug1_typing` and its
   outcome lifted through the frame (`lift_frame`): a step by `S_Ctx` or
   `S_CtxFault`; a jump is impossible, the hole standing under `Δ = []`;
   a `perform` is one in a context one frame longer (`lift_perform`),
   the frame being no `handle`. The continuation of `letjoin` is one
   exception (`prog_letjoin`): its hole stands under the `letjoin`'s
   join point, so a jump to it takes the join rule, the arity coming from
   the `jump`'s typing through `tl_typing` (`join_arity`), and a jump
   past it is one frame longer. `handle` is the other
   (`prog_handle`): a `perform` of its key takes the rule of its clause,
   which `Stella.Core.Safety.Progress.Eff.handled_perform_redex` builds
   (`w_handled`), and one of another key is lifted. A `perform` with a
   value argument is itself the outcome (`prog_perform`), and at the root
   it is refuted by the row `()` (`progress_top`).
   When every evaluation subterm is a value, the redex is read off the
   canonical forms, and the stuck shapes are refuted by recursion on the
   derivation through its conversions (`*_stuck`). A chain extended by a
   value argument, a type or `[•]` its cursor accepts is a value or a
   foreign redex (`chain_extend_value_or_redex`); a foreign redex steps
   by the adapter's outcome, which condition (3) of `genv_ok` gives
   (`prog_foreign`). *)
module Stella.Core.Safety.Progress
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Closed
open Stella.Core.Typing.Inversion
open Stella.Core.Typing.ValueForm
open Stella.Core.Typing.Plug
open Stella.Core.Typing.Canonical
open Stella.Core.Typing.Occ
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Safety.Hidden
open Stella.Core.Safety.Progress.Eff
module L = FStar.List.Tot
module V = Stella.Core.Value
module TC = Stella.Core.Typing.Ctor

(* * The premises on the term, hidden *)

[@@"opaque_to_smt"]
let term_ok (sg: sig) (gi: genv) (e: exp) : prop =
  stage6_frag e /\ covers sg gi e /\ pre_ok sg gi e

let term_ok_intro (sg: sig) (gi: genv) (e: exp)
  : Lemma (requires stage6_frag e /\ covers sg gi e /\ pre_ok sg gi e) (ensures term_ok sg gi e) =
  reveal_opaque (`%term_ok) (term_ok sg gi e)

let term_ok_frag (sg: sig) (gi: genv) (e: exp)
  : Lemma (requires term_ok sg gi e) (ensures stage6_frag e) =
  reveal_opaque (`%term_ok) (term_ok sg gi e)

let term_ok_covers (sg: sig) (gi: genv) (e: exp)
  : Lemma (requires term_ok sg gi e) (ensures covers sg gi e) =
  reveal_opaque (`%term_ok) (term_ok sg gi e)

let term_ok_root (sg: sig) (gi: genv) (e: exp)
  : Lemma (requires term_ok sg gi e /\ V.foreign_redex sg e) (ensures foreign_pre_ok gi e) =
  reveal_opaque (`%term_ok) (term_ok sg gi e);
  pre_ok_root sg gi e

let term_ok_plug1 (sg: sig) (gi: genv) (f: frame) (e: exp)
  : Lemma (requires frame_ok sg f /\ term_ok sg gi (plug1 f e)) (ensures term_ok sg gi e) =
  reveal_opaque (`%term_ok) (term_ok sg gi (plug1 f e));
  stage6_frag_plug1 f e;
  covers_plug1 sg gi f e;
  pre_ok_plug1 sg gi f e;
  reveal_opaque (`%term_ok) (term_ok sg gi e)

(* * The induction hypothesis *)

let ih_t (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout)) (ra: list atom) (st: store)
  (e: exp) : Type =
  e0: exp{e0 << e} -> d0: jctx -> t0: typ -> r0: typ ->
  h0: typing sg ln (closed_ctx rs) d0 e0 t0 r0 ->
  Pure (pin sg gi ra st d0 e0) (requires env_ok sg gi ln rs /\ term_ok sg gi e0)
       (ensures fun _ -> True)

(* * Rewriting indices *)

let coerce_step (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e1: exp) (e2: exp)
  (#ra': list atom) (#st': store) (#c1: config) (c2: config) (s: step sg gi ra st e1 ra' st' c1)
  : Pure (step sg gi ra st e2 ra' st' c2) (requires e1 == e2 /\ c1 == c2) (ensures fun _ -> True) =
  coerce_eq () s

(* A head rule at the root. *)
let pi_head (#sg: sig) (#gi: genv) (ra: list atom) (st: store) (#d: jctx) (e: exp) (#e0: exp)
  (#c: config) (ph: pure_head sg gi e0 c)
  : Pure (pin sg gi ra st d e) (requires e0 == e) (ensures fun _ -> True) =
  PIStep ra st c (coerce_step e c (S_Pure #sg #gi #ra #st #e0 #c ph))

(* * Wrappers revealing the premises *)

let w_canonical_fun (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#v: exp) (#a #rho #b #r: typ) (h: typing sg ln (closed_ctx rs) d v (t_fun a rho b) r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg v)
          (ensures ELam? v \/ EOpenEff? v \/
                   (V.value_head sg v /\
                    (match chain_cursor sg v with
                     | Some (s, _) -> Some? (as_function sg s)
                     | None -> False))) =
  env_ok_elim sg gi ln rs;
  ty_eq_refl (t_fun a rho b);
  canonical_fun h a rho b

let w_canonical_forall (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#v: exp) (#k: kind) (#s0 #r: typ) (h: typing sg ln (closed_ctx rs) d v (TForall k s0) r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg v)
          (ensures ETyLam? v \/
                   (V.value_head sg v /\
                    (match chain_cursor sg v with
                     | Some (s, _) -> TForall? s
                     | None -> False))) =
  env_ok_elim sg gi ln rs;
  ty_eq_refl (TForall k s0);
  canonical_forall h k s0

let w_canonical_constr (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#v: exp) (#c: constr) (#s0 #r: typ) (h: typing sg ln (closed_ctx rs) d v (TConstr c s0) r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg v)
          (ensures ECLam? v \/
                   (V.value_head sg v /\
                    (match chain_cursor sg v with
                     | Some (s, _) -> TConstr? s
                     | None -> False))) =
  env_ok_elim sg gi ln rs;
  ty_eq_refl (TConstr c s0);
  canonical_constr h c s0

let w_canonical_record (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#v: exp) (#rr #r: typ) (h: typing sg ln (closed_ctx rs) d v (t_record rr) r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg v)
          (ensures v == ERecEmpty \/ EExtend? v) =
  env_ok_elim sg gi ln rs;
  ty_eq_refl (t_record rr);
  canonical_record h rr

let w_canonical_variant_empty (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#d: jctx) (#v: exp) (#r: typ) (h: typing sg ln (closed_ctx rs) d v (t_variant TRowEmpty) r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg v) (ensures False) =
  env_ok_elim sg gi ln rs;
  ty_eq_refl (t_variant TRowEmpty);
  ty_eq_refl TRowEmpty;
  canonical_variant_empty h TRowEmpty

let w_canonical_bool (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#v: exp) (#r: typ) (h: typing sg ln (closed_ctx rs) d v t_bool r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg v)
          (ensures v == bool_lit true \/ v == bool_lit false) =
  env_ok_elim sg gi ln rs;
  ty_eq_refl t_bool;
  canonical_bool h

let w_canonical_data (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#v: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d v t r)
  (tq: qname) (ks: list kind) (ss: list typ) (cs: list qname)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg v /\ ty_eq t (tapps (TCon tq ks) ss) /\
                    has_class sg tq (TcData cs))
          (ensures (match ctor_head sg v with
                    | Some c -> L.mem c cs
                    | None -> False)) =
  env_ok_elim sg gi ln rs;
  canonical_data h tq ks ss cs

(* The key a variant value carries, with an entry at it in the row of its
   type. *)
let w_variant_key (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#v: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d v t r) (vr: typ)
  : Pure (key & cpayload)
         (requires env_ok sg gi ln rs /\ V.is_value sg v /\ ty_eq t (t_variant vr))
         (ensures fun (k, p) -> carrier_key v == Some k /\ L.mem (k, p) (row_entries (canon vr))) =
  env_ok_elim sg gi ln rs;
  canonical_variant h vr;
  let Some (k, w) = variant_view v in
  let iv = inv_variant h k w vr in
  let _ = iv.var_facts in
  (k, PTy (canon iv.var_ty))

(* Condition (3) of `genv_ok` at a saturated foreign chain of the term,
   which is typed at its cursor instance. *)
let w_foreign_call (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d e t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.foreign_redex sg e)
          (ensures foreign_call_ok sg gi ln rs e /\
                   (match chain_cursor sg e with
                    | Some (s, th) -> typed sg ln (closed_ctx rs) e (sub_ty th s)
                    | None -> False)) =
  env_ok_elim sg gi ln rs;
  genv_ok_foreign sg ln rs gi e;
  env_ok_sok sg gi ln rs;
  let Some (s, th) = chain_cursor sg e in
  foreign_redex_typed_h h s th

(* * Lists *)

let rec nth_some_lt (#a: Type) (l: list a) (n: nat)
  : Lemma (requires Some? (L.nth l n)) (ensures n < L.length l) (decreases l) =
  match l with
  | _ :: l' -> if n = 0 then () else nth_some_lt l' (n - 1)

(* The first term of a list that is no value, with the values before it. *)
let rec split_nv (sg: sig) (es: list exp)
  : Pure (option (list exp & exp & list exp)) (requires True)
         (ensures fun o ->
           match o with
           | None -> L.for_all (V.is_value sg) es
           | Some (vs, e0, es') ->
             es == L.append vs (e0 :: es') /\ L.for_all (V.is_value sg) vs /\
             not (V.is_value sg e0) /\ e0 << es)
         (decreases es) =
  match es with
  | [] -> None
  | e :: rest ->
    if not (V.is_value sg e) then Some ([], e, rest)
    else
      (match split_nv sg rest with
       | None -> None
       | Some (vs, e0, es') -> Some (e :: vs, e0, es'))

(* * The head of a covered chain *)

let rec covers_head (sg: sig) (gi: genv) (e: exp)
  : Lemma (requires covers sg gi e /\ Some? (decompose_global_app e))
          (ensures (match decompose_global_app e with
                    | Some (q, _, _) -> covered_name sg gi q
                    | None -> True))
          (decreases e) =
  match e with
  | EApp f _ | ETyApp f _ | ECApp f -> covers_head sg gi f
  | _ -> ()

(* * Lifting through a frame *)

let lift_config (f: frame) (c: config) : config =
  match c with
  | CTerm e' -> CTerm (plug1 f e')
  | CFault phi -> CFault phi

let lift_step (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom)
  (#st': store) (#c: config) (f: frame) (s: step sg gi ra st e ra' st' c)
  : Pure (step sg gi ra st (plug1 f e) ra' st' (lift_config f c))
         (requires frame_ok sg f) (ensures fun _ -> True) =
  match c with
  | CTerm e' -> S_Ctx #sg #gi #ra #st #e #ra' #st' #e' f () s
  | CFault phi -> S_CtxFault #sg #gi #ra #st #e #ra' #st' #phi f () s

(* A `perform` in the hole of a frame other than a `handle` of its key is
   one in the context extended by the frame. *)
let lift_perform (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#d: jctx) (e: exp)
  (f: frame) (e0: exp) (fs: list frame) (k: key) (op: opname) (ss: list typ) (v: exp)
  : Pure (pin sg gi ra st d e)
         (requires e == plug1 f e0 /\ e0 == plug fs (EPerform k op ss v) /\ ev_k k fs /\
                   frames_ok sg fs /\ V.is_value sg v /\ frame_ok sg f /\ not_handle_of k f)
         (ensures fun _ -> True) =
  plug_snoc fs f (EPerform k op ss v);
  L.for_all_append (not_handle_of k) fs [f];
  L.for_all_append (frame_ok sg) fs [f];
  PIPerform (L.append fs [f]) k op ss v ()

(* The outcome of the hole of a frame other than a `letjoin` continuation
   or a `handle`: its hole stands under `Δ = []`, so it is no jump, and
   a `perform` there is one of the frame. *)
let lift_frame (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (e: exp) (h: typing sg ln (closed_ctx rs) d e t r)
  (f: frame) (e0: exp) (ih: ih_t sg gi ln rs ra st e)
  : Pure (pin sg gi ra st d e)
         (requires env_ok sg gi ln rs /\ term_ok sg gi e /\ e == plug1 f e0 /\ e0 << e /\
                   frame_ok sg f /\ not (V.is_value sg e0) /\ not (FLetJoin? f) /\
                   not (FHandle? f))
         (ensures fun _ -> True) =
  let h1 = retm h (plug1 f e0) in
  env_ok_sok sg gi ln rs;
  let p = plug1_typing_h h1 in
  let _ = p.hole_ctx in
  term_ok_plug1 sg gi f e0;
  match ih e0 p.hd p.ht p.hr p.hole with
  | PIValue _ -> false_elim ()
  | PIStep ra' st' c s ->
    PIStep ra' st' (lift_config f c) (coerce_step e (lift_config f c) (lift_step f s))
  | PIJump _ _ _ _ -> false_elim ()
  | PIPerform fs k op ss v _ -> lift_perform e f e0 fs k op ss v

(* * Foreign redexes *)

let prog_foreign (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#e: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d e t r)
  : Pure (pin sg gi ra st d e)
         (requires env_ok sg gi ln rs /\ term_ok sg gi e /\ V.foreign_redex sg e)
         (ensures fun _ -> True) =
  term_ok_covers sg gi e;
  term_ok_root sg gi e;
  let Some (q, ks, args) = decompose_global_app e in
  covers_head sg gi e;
  let Some fe = gi.gforeign q in
  w_foreign_call gi h;
  match fe.fe_adapt (chain_instance e) (value_args args) with
  | Some o ->
    PIStep ra st (foreign_config o)
      (S_Pure (PH_Foreign #sg #gi #e #q #ks #args #fe #o () () () ()))
  | None -> false_elim ()

(* * Variables and globals *)

let rec var_untyped (#sg: sig) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx) (#i: nat)
  (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (EVar i) t r)
  : Lemma (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    var_untyped #sg #ln #rs #d #i #t1' #r1' h'
  | _ -> ()

(* A global that is no top-level value is typed only as a constructor or a
   foreign, so its cursor is defined. *)
let rec global_cursor (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#q: qname) (#ks: list kind)
  (#t #r: typ) (h: typing sg ln g d (EGlobal q ks) t r)
  : Lemma (requires value_scheme sg q == None) (ensures Some? (chain_cursor sg (EGlobal q ks)))
          (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    global_cursor #sg #ln #g #d #q #ks #t1' #r1' h'
  | T_Global _ _ _ -> chain_cursor_global sg q ks
  | _ -> ()

let prog_global (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (q: qname) (ks: list kind)
  (h: typing sg ln (closed_ctx rs) d (EGlobal q ks) t r)
  : Pure (pin sg gi ra st d (EGlobal q ks))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EGlobal q ks))
         (ensures fun _ -> True) =
  if V.is_value sg (EGlobal q ks) then PIValue ()
  else
    match value_scheme sg q with
    | Some vi ->
      inv_global h vi;
      term_ok_covers sg gi (EGlobal q ks);
      covers_head sg gi (EGlobal q ks);
      let Some v = gi.gvals q in
      pi_head ra st (EGlobal q ks) (PH_Unfold #sg #gi #q #ks #vi #v () ())
    | None ->
      global_cursor h;
      V.chain_value_or_redex sg (EGlobal q ks);
      prog_foreign ra st h

(* * Abstractions and applications *)

let rec tylam_value (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: kind) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d (ETyLam k v) t r)
  : Lemma (ensures V.is_value sg (ETyLam k v)) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    tylam_value #sg #ln #g #d #k #v #t1' #r1' h'
  | T_TyLam _ _ _ _ -> value_form_is_value sg v
  | _ -> ()

let rec clam_value (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#c: constr) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d (ECLam c v) t r)
  : Lemma (ensures V.is_value sg (ECLam c v)) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    clam_value #sg #ln #g #d #c #v #t1' #r1' h'
  | T_CLam _ _ _ _ -> value_form_is_value sg v
  | _ -> ()

let rec app_stuck (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e1 #e2: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (EApp e1 e2) t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg e1 /\ V.is_value sg e2 /\
                    not (V.is_value sg (EApp e1 e2)) /\ not (V.foreign_redex sg (EApp e1 e2)) /\
                    not (ELam? e1) /\ not (EOpenEff? e1))
          (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    app_stuck #sg gi #ln #rs #d #e1 #e2 #t1' #r1' h'
  | T_App h1 _ ->
    w_canonical_fun gi #ln #rs h1;
    V.chain_extend_value_or_redex sg e1 (SVal e2)
  | T_Chain _ _ -> V.chain_prefix_value_or_redex sg e1 (SVal e2)
  | _ -> ()

let prog_app (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (e1 e2: exp)
  (h: typing sg ln (closed_ctx rs) d (EApp e1 e2) t r) (ih: ih_t sg gi ln rs ra st (EApp e1 e2))
  : Pure (pin sg gi ra st d (EApp e1 e2))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EApp e1 e2)) (ensures fun _ -> True) =
  if not (V.is_value sg e2) then lift_frame ra st (EApp e1 e2) h (FAppArg e1) e2 ih
  else if not (V.is_value sg e1) then lift_frame ra st (EApp e1 e2) h (FAppFun e2) e1 ih
  else if V.is_value sg (EApp e1 e2) then PIValue ()
  else if V.foreign_redex sg (EApp e1 e2) then prog_foreign ra st h
  else
    match e1 with
    | ELam t1 r1 body ->
      pi_head ra st (EApp e1 e2) (PH_Beta #sg #gi #t1 #r1 #body #e2 ())
    | EOpenEff r1 v ->
      pi_head ra st (EApp e1 e2) (PH_OpenEffApp #sg #gi #r1 #v #e2 ())
    | _ -> app_stuck gi h; false_elim ()

let rec tyapp_stuck (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e0: exp) (#s: typ) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (ETyApp e0 s) t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg e0 /\
                    not (V.is_value sg (ETyApp e0 s)) /\ not (V.foreign_redex sg (ETyApp e0 s)) /\
                    not (ETyLam? e0))
          (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    tyapp_stuck #sg gi #ln #rs #d #e0 #s #t1' #r1' h'
  | T_TyApp h1 _ ->
    w_canonical_forall gi #ln #rs h1;
    V.chain_extend_value_or_redex sg e0 (STy s)
  | T_Chain _ _ -> V.chain_prefix_value_or_redex sg e0 (STy s)
  | _ -> ()

let prog_tyapp (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (e0: exp) (s: typ)
  (h: typing sg ln (closed_ctx rs) d (ETyApp e0 s) t r) (ih: ih_t sg gi ln rs ra st (ETyApp e0 s))
  : Pure (pin sg gi ra st d (ETyApp e0 s))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (ETyApp e0 s)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (ETyApp e0 s) h (FTyApp s) e0 ih
  else if V.is_value sg (ETyApp e0 s) then PIValue ()
  else if V.foreign_redex sg (ETyApp e0 s) then prog_foreign ra st h
  else
    match e0 with
    | ETyLam k v -> pi_head ra st (ETyApp e0 s) (PH_TyBeta #sg #gi #k #v #s ())
    | _ -> tyapp_stuck gi h; false_elim ()

let rec capp_stuck (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e0: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (ECApp e0) t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg e0 /\
                    not (V.is_value sg (ECApp e0)) /\ not (V.foreign_redex sg (ECApp e0)) /\
                    not (ECLam? e0))
          (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    capp_stuck #sg gi #ln #rs #d #e0 #t1' #r1' h'
  | T_CApp h1 _ ->
    w_canonical_constr gi #ln #rs h1;
    V.chain_extend_value_or_redex sg e0 SConstr
  | T_Chain _ _ -> V.chain_prefix_value_or_redex sg e0 SConstr
  | _ -> ()

let prog_capp (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (ECApp e0) t r) (ih: ih_t sg gi ln rs ra st (ECApp e0))
  : Pure (pin sg gi ra st d (ECApp e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (ECApp e0)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (ECApp e0) h FCApp e0 ih
  else if V.is_value sg (ECApp e0) then PIValue ()
  else if V.foreign_redex sg (ECApp e0) then prog_foreign ra st h
  else
    match e0 with
    | ECLam c v -> pi_head ra st (ECApp e0) (PH_CBeta #sg #gi #c #v ())
    | _ -> capp_stuck gi h; false_elim ()

let prog_let (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (t1: typ) (e1 e2: exp)
  (h: typing sg ln (closed_ctx rs) d (ELet t1 e1 e2) t r)
  (ih: ih_t sg gi ln rs ra st (ELet t1 e1 e2))
  : Pure (pin sg gi ra st d (ELet t1 e1 e2))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (ELet t1 e1 e2)) (ensures fun _ -> True) =
  if not (V.is_value sg e1) then lift_frame ra st (ELet t1 e1 e2) h (FLet t1 e2) e1 ih
  else pi_head ra st (ELet t1 e1 e2) (PH_Let #sg #gi #t1 #e1 #e2 ())

(* * `case` and `jump` *)

let prog_case (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (es: list exp) (dt: dtree)
  (h: typing sg ln (closed_ctx rs) d (ECase es dt) t r) (ih: ih_t sg gi ln rs ra st (ECase es dt))
  : Pure (pin sg gi ra st d (ECase es dt))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (ECase es dt)) (ensures fun _ -> True) =
  match split_nv sg es with
  | Some (vs, e0, es') -> lift_frame ra st (ECase es dt) h (FCase vs es' dt) e0 ih
  | None -> pi_head ra st (ECase es dt) (PH_Case #sg #gi #es #dt ())

let prog_jump (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (n: nat) (es: list exp)
  (h: typing sg ln (closed_ctx rs) d (EJump n es) t r) (ih: ih_t sg gi ln rs ra st (EJump n es))
  : Pure (pin sg gi ra st d (EJump n es))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EJump n es)) (ensures fun _ -> True) =
  match split_nv sg es with
  | Some (vs, e0, es') -> lift_frame ra st (EJump n es) h (FJump n vs es') e0 ih
  | None ->
    let j = inv_jump h in
    let _ = j.j_facts in
    nth_some_lt d n;
    PIJump [] n es ()

(* * Join points *)

(* A jump to the join point of a `letjoin` through its tail context has the
   join point's arity. *)
let join_arity (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#hd: jctx)
  (#e2: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) hd e2 t r)
  (fs: list frame) (n: nat) (vs: list exp) (ts: list typ) (t1 r1: typ) (d: jctx)
  : Lemma (requires env_ok sg gi ln rs /\ e2 == plug fs (EJump n vs) /\ tl_frames fs /\
                    n == L.length fs /\ hd == (ts, t1, r1) :: d)
          (ensures L.length vs == L.length ts) =
  let h' = retm h (plug fs (EJump n vs)) in
  env_ok_sok sg gi ln rs;
  let p = tl_typing_h h' in
  let _ = p.tl_pre in
  let j = inv_jump p.tl_hole in
  let _ = j.j_facts in
  nth_append p.pre hd n;
  TC.exps_typing_length j.j_args

let prog_letjoin (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (ts: list typ) (t1: typ) (e1 e2: exp)
  (h: typing sg ln (closed_ctx rs) d (ELetJoin ts t1 e1 e2) t r)
  (ih: ih_t sg gi ln rs ra st (ELetJoin ts t1 e1 e2))
  : Pure (pin sg gi ra st d (ELetJoin ts t1 e1 e2))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (ELetJoin ts t1 e1 e2))
         (ensures fun _ -> True) =
  let e = ELetJoin ts t1 e1 e2 in
  if V.is_value sg e2 then pi_head ra st e (PH_JoinValue #sg #gi #ts #t1 #e1 #e2 ())
  else begin
    let f = FLetJoin ts t1 e1 in
    env_ok_sok sg gi ln rs;
    let p = plug1_typing_h #sg #ln #(closed_ctx rs) #d #f #e2 h in
    let _ = p.hole_ctx in
    term_ok_plug1 sg gi f e2;
    match ih e2 p.hd p.ht p.hr p.hole with
    | PIValue _ -> false_elim ()
    | PIStep ra' st' c s -> PIStep ra' st' (lift_config f c) (lift_step f s)
    | PIJump fs n vs _ ->
      if n = L.length fs then begin
        join_arity #sg gi #ln #rs p.hole fs n vs ts t1 p.hr d;
        pi_head ra st e (PH_Join #sg #gi #ts #t1 #e1 #fs #n #vs () ())
      end else begin
        plug_snoc fs f (EJump n vs);
        tl_frames_snoc fs f;
        PIJump (L.append fs [f]) n vs ()
      end
    | PIPerform fs k op ss v _ -> lift_perform e f e2 fs k op ss v
  end

(* * Records *)

(* A record value of a type holding the key `k` is an `extend`: `{}` has
   the empty row, which holds no key. *)
let record_ext_extend (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#v: exp) (#r: typ) (k: key) (t0 r0: typ)
  (h: typing sg ln (closed_ctx rs) d v (t_record (TRowExt (EntTy k t0) r0)) r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg v) (ensures EExtend? v) =
  w_canonical_record gi h;
  match v with
  | ERecEmpty ->
    inv_rec_empty h (TRowExt (EntTy k t0) r0);
    mem_known_keys_ext k (EntTy k t0) r0;
    known_keys_empty ()
  | _ -> ()

let prog_extend (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (k: key) (e1 e2: exp)
  (h: typing sg ln (closed_ctx rs) d (EExtend k e1 e2) t r)
  (ih: ih_t sg gi ln rs ra st (EExtend k e1 e2))
  : Pure (pin sg gi ra st d (EExtend k e1 e2))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EExtend k e1 e2)) (ensures fun _ -> True) =
  if not (V.is_value sg e1) then lift_frame ra st (EExtend k e1 e2) h (FExtendL k e2) e1 ih
  else if not (V.is_value sg e2) then lift_frame ra st (EExtend k e1 e2) h (FExtendR k e1) e2 ih
  else PIValue ()

let rec select_stuck (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#k: key) (#e0: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (ESelect k e0) t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg e0 /\ not (EExtend? e0))
          (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    select_stuck #sg gi #ln #rs #d #k #e0 #t1' #r1' h'
  | T_Select #_ #_ #_ #_ #_ #_ #t0 #r0 h1 _ -> record_ext_extend gi #ln #rs k t0 r0 h1
  | _ -> ()

let prog_select (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (k: key) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (ESelect k e0) t r) (ih: ih_t sg gi ln rs ra st (ESelect k e0))
  : Pure (pin sg gi ra st d (ESelect k e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (ESelect k e0)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (ESelect k e0) h (FSelect k) e0 ih
  else
    match e0 with
    | EExtend k' v1 v2 ->
      if k' = k then pi_head ra st (ESelect k e0) (PH_SelectHit #sg #gi #k #v1 #v2 ())
      else pi_head ra st (ESelect k e0) (PH_SelectMiss #sg #gi #k #k' #v1 #v2 () ())
    | _ -> select_stuck gi h; false_elim ()

let rec restrict_stuck (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#k: key) (#e0: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (ERestrict k e0) t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg e0 /\ not (EExtend? e0))
          (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    restrict_stuck #sg gi #ln #rs #d #k #e0 #t1' #r1' h'
  | T_Restrict #_ #_ #_ #_ #_ #_ #t0 #r0 h1 _ -> record_ext_extend gi #ln #rs k t0 r0 h1
  | _ -> ()

let prog_restrict (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (k: key) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (ERestrict k e0) t r)
  (ih: ih_t sg gi ln rs ra st (ERestrict k e0))
  : Pure (pin sg gi ra st d (ERestrict k e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (ERestrict k e0)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (ERestrict k e0) h (FRestrict k) e0 ih
  else
    match e0 with
    | EExtend k' v1 v2 ->
      if k' = k then pi_head ra st (ERestrict k e0) (PH_RestrictHit #sg #gi #k #v1 #v2 ())
      else pi_head ra st (ERestrict k e0) (PH_RestrictMiss #sg #gi #k #k' #v1 #v2 () ())
    | _ -> restrict_stuck gi h; false_elim ()

let rec update_stuck (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#k: key) (#e1 #e2: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (EUpdate k e1 e2) t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg e1 /\ not (EExtend? e1))
          (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    update_stuck #sg gi #ln #rs #d #k #e1 #e2 #t1' #r1' h'
  | T_Update #_ #_ #_ #_ #_ #_ #_ #t0 #_ #r0 h1 _ _ -> record_ext_extend gi #ln #rs k t0 r0 h1
  | _ -> ()

let prog_update (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (k: key) (e1 e2: exp)
  (h: typing sg ln (closed_ctx rs) d (EUpdate k e1 e2) t r)
  (ih: ih_t sg gi ln rs ra st (EUpdate k e1 e2))
  : Pure (pin sg gi ra st d (EUpdate k e1 e2))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EUpdate k e1 e2)) (ensures fun _ -> True) =
  let e = EUpdate k e1 e2 in
  if not (V.is_value sg e1) then lift_frame ra st e h (FUpdateL k e2) e1 ih
  else if not (V.is_value sg e2) then lift_frame ra st e h (FUpdateR k e1) e2 ih
  else
    match e1 with
    | EExtend k' v1 v2 ->
      if k' = k then pi_head ra st e (PH_UpdateHit #sg #gi #k #v1 #v2 #e2 ())
      else pi_head ra st e (PH_UpdateMiss #sg #gi #k #k' #v1 #v2 #e2 () ())
    | _ -> update_stuck gi h; false_elim ()

let rec merge_stuck (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e1 #e2: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (EMerge e1 e2) t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg e1 /\ e1 =!= ERecEmpty /\ not (EExtend? e1))
          (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    merge_stuck #sg gi #ln #rs #d #e1 #e2 #t1' #r1' h'
  | T_Merge h1 _ _ -> w_canonical_record gi #ln #rs h1
  | _ -> ()

let prog_merge (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (e1 e2: exp)
  (h: typing sg ln (closed_ctx rs) d (EMerge e1 e2) t r) (ih: ih_t sg gi ln rs ra st (EMerge e1 e2))
  : Pure (pin sg gi ra st d (EMerge e1 e2))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EMerge e1 e2)) (ensures fun _ -> True) =
  let e = EMerge e1 e2 in
  if not (V.is_value sg e1) then lift_frame ra st e h (FMergeL e2) e1 ih
  else if not (V.is_value sg e2) then lift_frame ra st e h (FMergeR e1) e2 ih
  else
    match e1 with
    | ERecEmpty -> pi_head ra st e (PH_MergeEmpty #sg #gi #e2 ())
    | EExtend k v1 v2 -> pi_head ra st e (PH_MergeExtend #sg #gi #k #v1 #v2 #e2 ())
    | _ -> merge_stuck gi h; false_elim ()

(* * Variants and `openEff` *)

let prog_inject (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (k: key) (r0: typ) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (EInject k r0 e0) t r)
  (ih: ih_t sg gi ln rs ra st (EInject k r0 e0))
  : Pure (pin sg gi ra st d (EInject k r0 e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EInject k r0 e0)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (EInject k r0 e0) h (FInject k r0) e0 ih
  else PIValue ()

let prog_weaken (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (k: key) (t1: typ) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (EWeaken k t1 e0) t r)
  (ih: ih_t sg gi ln rs ra st (EWeaken k t1 e0))
  : Pure (pin sg gi ra st d (EWeaken k t1 e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EWeaken k t1 e0)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (EWeaken k t1 e0) h (FWeaken k t1) e0 ih
  else PIValue ()

let rec absurd_stuck (#sg: sig) (gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#t1: typ) (#e0: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (EAbsurd t1 e0) t r)
  : Lemma (requires env_ok sg gi ln rs /\ V.is_value sg e0) (ensures False) (decreases h) =
  match h with
  | T_Conv #_ #_ #_ #_ #_ #t1' #r1' #_ #_ h' _ _ ->
    absurd_stuck #sg gi #ln #rs #d #t1 #e0 #t1' #r1' h'
  | T_Absurd h1 _ -> w_canonical_variant_empty gi #ln #rs h1
  | _ -> ()

let prog_absurd (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (t1: typ) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (EAbsurd t1 e0) t r)
  (ih: ih_t sg gi ln rs ra st (EAbsurd t1 e0))
  : Pure (pin sg gi ra st d (EAbsurd t1 e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EAbsurd t1 e0)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (EAbsurd t1 e0) h (FAbsurd t1) e0 ih
  else (absurd_stuck gi h; false_elim ())

let prog_openeff (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (r1: typ) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (EOpenEff r1 e0) t r)
  (ih: ih_t sg gi ln rs ra st (EOpenEff r1 e0))
  : Pure (pin sg gi ra st d (EOpenEff r1 e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EOpenEff r1 e0)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (EOpenEff r1 e0) h (FOpenEff r1) e0 ih
  else PIValue ()

let prog_openeffc (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (r1: typ) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (EOpenEffC r1 e0) t r)
  (ih: ih_t sg gi ln rs ra st (EOpenEffC r1 e0))
  : Pure (pin sg gi ra st d (EOpenEffC r1 e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EOpenEffC r1 e0)) (ensures fun _ -> True) =
  if not (V.is_value sg e0) then lift_frame ra st (EOpenEffC r1 e0) h (FOpenEffC r1) e0 ih
  else pi_head ra st (EOpenEffC r1 e0) (PH_OpenEffC #sg #gi #r1 #e0 ())

(* * `match` *)

let prog_bind (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (th: list exp) (o: occ) (dt: dtree)
  (#om: octx) (#t' #r': typ) (hm: match_typing sg ln (closed_ctx rs) [] r' th om)
  (hdt: dt_typing sg ln (closed_ctx rs) d om (DBind o dt) t' r')
  : Pure (pin sg gi ra st d (EMatch th (DBind o dt)))
         (requires env_ok sg gi ln rs /\ L.for_all (V.is_value sg) th) (ensures fun _ -> True) =
  match hdt with
  | TD_Bind ho _ ->
    env_ok_sok sg gi ln rs;
    let (| v, _ |) = occ_sound_h hm ho in
    pi_head ra st (EMatch th (DBind o dt)) (PH_Bind #sg #gi #th #o #dt #v ())

let prog_guard (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (th: list exp) (e1: exp) (dt1 dt2: dtree)
  (h: typing sg ln (closed_ctx rs) d (EMatch th (DGuard e1 dt1 dt2)) t r)
  (#om: octx) (#t' #r': typ) (hdt: dt_typing sg ln (closed_ctx rs) d om (DGuard e1 dt1 dt2) t' r')
  (ih: ih_t sg gi ln rs ra st (EMatch th (DGuard e1 dt1 dt2)))
  : Pure (pin sg gi ra st d (EMatch th (DGuard e1 dt1 dt2)))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EMatch th (DGuard e1 dt1 dt2)) /\
                   L.for_all (V.is_value sg) th)
         (ensures fun _ -> True) =
  let e = EMatch th (DGuard e1 dt1 dt2) in
  if not (V.is_value sg e1) then lift_frame ra st e h (FGuard th dt1 dt2) e1 ih
  else
    match hdt with
    | TD_Guard he _ _ ->
      w_canonical_bool gi #ln #rs he;
      if e1 = bool_lit true then pi_head ra st e (PH_GuardTrue #sg #gi #th #dt1 #dt2)
      else pi_head ra st e (PH_GuardFalse #sg #gi #th #dt1 #dt2)

let prog_switch_ctor (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (ra: list atom) (st: store) (#d: jctx) (th: list exp) (o: occ) (bs: list (qname & dtree))
  (df: option dtree) (#om: octx) (#t' #r': typ) (hm: match_typing sg ln (closed_ctx rs) [] r' th om)
  (hdt: dt_typing sg ln (closed_ctx rs) d om (DSwitchCtor o bs df) t' r')
  : Pure (pin sg gi ra st d (EMatch th (DSwitchCtor o bs df)))
         (requires env_ok sg gi ln rs /\ L.for_all (V.is_value sg) th) (ensures fun _ -> True) =
  let e = EMatch th (DSwitchCtor o bs df) in
  match hdt with
  | TD_SwitchCtor tq ks ss cs ho _ _ _ _ ->
    env_ok_sok sg gi ln rs;
    let (| v, hv |) = occ_sound_h hm ho in
    (match branch (ctor_head sg v) bs with
     | Some dt -> pi_head ra st e (PH_SwitchCtor #sg #gi #th #o #bs #df #v #dt ())
     | None ->
       w_canonical_data gi hv tq ks ss cs;
       let Some c = ctor_head sg v in
       ctor_brs_exhaustive cs bs c;
       false_elim ())
  | TD_SwitchCtorDef #_ #_ #_ #_ #_ #_ #_ #df0 _ _ _ _ ho _ _ _ _ _ ->
    env_ok_sok sg gi ln rs;
    let (| v, _ |) = occ_sound_h hm ho in
    (match branch (ctor_head sg v) bs with
     | Some dt -> pi_head ra st e (PH_SwitchCtor #sg #gi #th #o #bs #df #v #dt ())
     | None -> pi_head ra st e (PH_SwitchCtorDef #sg #gi #th #o #bs #df0 #v ()))

let prog_switch_lit (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (ra: list atom) (st: store) (#d: jctx) (th: list exp) (o: occ) (bs: list (lit & dtree))
  (dt0: dtree) (#om: octx) (#t' #r': typ) (hm: match_typing sg ln (closed_ctx rs) [] r' th om)
  (hdt: dt_typing sg ln (closed_ctx rs) d om (DSwitchLit o bs dt0) t' r')
  : Pure (pin sg gi ra st d (EMatch th (DSwitchLit o bs dt0)))
         (requires env_ok sg gi ln rs /\ L.for_all (V.is_value sg) th) (ensures fun _ -> True) =
  let e = EMatch th (DSwitchLit o bs dt0) in
  match hdt with
  | TD_SwitchLit _ ho _ _ _ _ ->
    env_ok_sok sg gi ln rs;
    let (| v, _ |) = occ_sound_h hm ho in
    (match branch (lit_of v) bs with
     | Some dt -> pi_head ra st e (PH_SwitchLit #sg #gi #th #o #bs #dt0 #v #dt ())
     | None -> pi_head ra st e (PH_SwitchLitDef #sg #gi #th #o #bs #dt0 #v ()))

let prog_switch_key (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (ra: list atom) (st: store) (#d: jctx) (th: list exp) (o: occ) (bs: list (key & dtree))
  (df: option dtree) (#om: octx) (#t' #r': typ) (hm: match_typing sg ln (closed_ctx rs) [] r' th om)
  (hdt: dt_typing sg ln (closed_ctx rs) d om (DSwitchKey o bs df) t' r')
  : Pure (pin sg gi ra st d (EMatch th (DSwitchKey o bs df)))
         (requires env_ok sg gi ln rs /\ L.for_all (V.is_value sg) th) (ensures fun _ -> True) =
  let e = EMatch th (DSwitchKey o bs df) in
  match hdt with
  | TD_SwitchKey vr _ ho _ _ _ hbs ->
    env_ok_sok sg gi ln rs;
    let (| v, hv |) = occ_sound_h hm ho in
    (match branch (carrier_key v) bs with
     | Some dt -> pi_head ra st e (PH_SwitchKey #sg #gi #th #o #bs #df #v #dt ())
     | None ->
       let (k, p) = w_variant_key gi hv vr in
       key_brs_exhaustive hbs vr k p;
       false_elim ())
  | TD_SwitchKeyDef #_ #_ #_ #_ #_ #_ #_ #df0 _ _ _ ho _ _ _ _ _ ->
    env_ok_sok sg gi ln rs;
    let (| v, _ |) = occ_sound_h hm ho in
    (match branch (carrier_key v) bs with
     | Some dt -> pi_head ra st e (PH_SwitchKey #sg #gi #th #o #bs #df #v #dt ())
     | None -> pi_head ra st e (PH_SwitchKeyDef #sg #gi #th #o #bs #df0 #v ()))

let prog_match (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (th: list exp) (dt: dtree)
  (h: typing sg ln (closed_ctx rs) d (EMatch th dt) t r) (ih: ih_t sg gi ln rs ra st (EMatch th dt))
  : Pure (pin sg gi ra st d (EMatch th dt))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EMatch th dt)) (ensures fun _ -> True) =
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match _ _ _ hm hdt ->
    (match dt with
     | DLeaf e1 -> pi_head ra st (EMatch th dt) (PH_Leaf #sg #gi #th #e1)
     | DBind o dt' -> prog_bind #sg #gi #ln #rs ra st th o dt' hm hdt
     | DGuard e1 dt1 dt2 -> prog_guard #sg #gi #ln #rs ra st th e1 dt1 dt2 h hdt ih
     | DSwitchCtor o bs df -> prog_switch_ctor #sg #gi #ln #rs ra st th o bs df hm hdt
     | DSwitchLit o bs dt0 -> prog_switch_lit #sg #gi #ln #rs ra st th o bs dt0 hm hdt
     | DSwitchKey o bs df -> prog_switch_key #sg #gi #ln #rs ra st th o bs df hm hdt)
  | _ -> false_elim ()

(* * Operations and handlers *)

(* An effect rule at the root. *)
let pi_eff (#sg: sig) (#gi: genv) (ra: list atom) (st: store) (#d: jctx) (e: exp) (#e0: exp)
  (#c: config) (eh: eff_head sg gi e0 c)
  : Pure (pin sg gi ra st d e) (requires e0 == e) (ensures fun _ -> True) =
  PIStep ra st c (coerce_step e c (S_Eff #sg #gi #ra #st #e0 #c eh))

(* `Stella.Core.Safety.Progress.Eff.handled_perform_redex`, revealing the
   premises. *)
let w_handled (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#fs: list frame) (#k: key) (#op: opname) (#ss: list typ) (#v: exp) (#hd: handler)
  (#t #r: typ) (h: typing sg ln (closed_ctx rs) d (EHandle (plug fs (EPerform k op ss v)) hd) t r)
  : Pure (c: config & eff_head sg gi (EHandle (plug fs (EPerform k op ss v)) hd) c)
         (requires env_ok sg gi ln rs /\ frames_ok sg fs /\ ev_k k fs /\ V.is_value sg v /\
                   handler_key hd == k)
         (ensures fun _ -> True) =
  env_ok_elim sg gi ln rs;
  handled_perform_redex #sg #gi #ln #rs #d #fs #k #op #ss #v #hd #t #r h

let prog_perform (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (k: key) (op: opname) (ss: list typ) (e0: exp)
  (h: typing sg ln (closed_ctx rs) d (EPerform k op ss e0) t r)
  (ih: ih_t sg gi ln rs ra st (EPerform k op ss e0))
  : Pure (pin sg gi ra st d (EPerform k op ss e0))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EPerform k op ss e0))
         (ensures fun _ -> True) =
  if not (V.is_value sg e0) then
    lift_frame ra st (EPerform k op ss e0) h (FPerform k op ss) e0 ih
  else PIPerform [] k op ss e0 ()

let prog_handle (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#t #r: typ) (e0: exp) (hd: handler)
  (h: typing sg ln (closed_ctx rs) d (EHandle e0 hd) t r)
  (ih: ih_t sg gi ln rs ra st (EHandle e0 hd))
  : Pure (pin sg gi ra st d (EHandle e0 hd))
         (requires env_ok sg gi ln rs /\ term_ok sg gi (EHandle e0 hd))
         (ensures fun _ -> True) =
  let e = EHandle e0 hd in
  if V.is_value sg e0 then pi_eff ra st e (EH_Return #sg #gi #e0 #hd ())
  else begin
    let f = FHandle hd in
    env_ok_sok sg gi ln rs;
    let p = plug1_typing_h #sg #ln #(closed_ctx rs) #d #f #e0 h in
    let _ = p.hole_ctx in
    term_ok_plug1 sg gi f e0;
    match ih e0 p.hd p.ht p.hr p.hole with
    | PIValue _ -> false_elim ()
    | PIStep ra' st' c s -> PIStep ra' st' (lift_config f c) (lift_step f s)
    | PIJump _ _ _ _ -> false_elim ()
    | PIPerform fs k op ss v _ ->
      if k = handler_key hd then begin
        let (| c, eh |) =
          w_handled #sg #gi #ln #rs #d #fs #k #op #ss #v #hd #t #r
            (retm h (EHandle (plug fs (EPerform k op ss v)) hd)) in
        pi_eff ra st e eh
      end
      else lift_perform e f e0 fs k op ss v
  end

(* * The induction *)

let rec prog (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (ra: list atom)
  (st: store) (#d: jctx) (#e: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d e t r)
  : Pure (pin sg gi ra st d e) (requires env_ok sg gi ln rs /\ term_ok sg gi e)
         (ensures fun _ -> True) (decreases e) =
  let ih : ih_t sg gi ln rs ra st e =
    fun (e0: exp{e0 << e}) (d0: jctx) (t0 r0: typ) (h0: typing sg ln (closed_ctx rs) d0 e0 t0 r0) ->
      prog #sg #gi #ln #rs ra st #d0 #e0 #t0 #r0 h0 in
  match e with
  | EVar i -> var_untyped #sg #ln #rs #d #i #t #r h; false_elim ()
  | EGlobal q ks -> prog_global ra st q ks h
  | ELit _ | ELam _ _ _ | ERecEmpty | EOpaque _ _ -> PIValue ()
  | EApp e1 e2 -> prog_app ra st e1 e2 h ih
  | ETyLam k v -> tylam_value #sg #ln #(closed_ctx rs) #d #k #v #t #r h; PIValue ()
  | ETyApp e0 s -> prog_tyapp ra st e0 s h ih
  | ECLam c v -> clam_value #sg #ln #(closed_ctx rs) #d #c #v #t #r h; PIValue ()
  | ECApp e0 -> prog_capp ra st e0 h ih
  | ELet t1 e1 e2 -> prog_let ra st t1 e1 e2 h ih
  | ECase es dt -> prog_case ra st es dt h ih
  | ELetJoin ts t1 e1 e2 -> prog_letjoin ra st ts t1 e1 e2 h ih
  | EJump n es -> prog_jump ra st n es h ih
  | EExtend k e1 e2 -> prog_extend ra st k e1 e2 h ih
  | ESelect k e0 -> prog_select ra st k e0 h ih
  | ERestrict k e0 -> prog_restrict ra st k e0 h ih
  | EUpdate k e1 e2 -> prog_update ra st k e1 e2 h ih
  | EMerge e1 e2 -> prog_merge ra st e1 e2 h ih
  | EInject k r0 e0 -> prog_inject ra st k r0 e0 h ih
  | EWeaken k t1 e0 -> prog_weaken ra st k t1 e0 h ih
  | EAbsurd t1 e0 -> prog_absurd ra st t1 e0 h ih
  | EOpenEff r1 e0 -> prog_openeff ra st r1 e0 h ih
  | EOpenEffC r1 e0 -> prog_openeffc ra st r1 e0 h ih
  | EMatch th dt -> prog_match ra st th dt h ih
  | EPerform k op ss e0 -> prog_perform ra st k op ss e0 h ih
  | EHandle e0 hd -> prog_handle ra st e0 hd h ih
  | ERegion _ _ _ | ERegionOpen _ _ _
  | EReadCell _ _ | EWriteCell _ _ _ | ELetRec _ _ | EForce _ | EFill _ _ ->
    term_ok_frag sg gi e; false_elim ()

(* * The statements *)

let progress_in #sg #gi #ln #rs #d #e #t #r h ra st =
  env_ok_intro sg gi ln rs;
  term_ok_intro sg gi e;
  prog #sg #gi #ln #rs ra st #d #e #t #r h

let progress_top #sg #gi #ln #rs #e #t h ra st =
  match progress_in #sg #gi #ln #rs #[] #e #t #TRowEmpty h ra st with
  | PIValue sq -> PValue sq
  | PIStep ra' st' c s -> PStep ra' st' c s
  | PIJump _ _ _ _ -> false_elim ()
  | PIPerform fs k op ss v _ ->
    rctx_ok_wf_ctx sg rs;
    unhandled_perform_untypable h;
    false_elim ()
