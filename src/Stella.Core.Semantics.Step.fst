(* A redex of a pure head rule is no value: its head is an elimination
   form, a run-time form that is no value, a global with a body, or a
   saturated foreign chain (`Stella.Core.Value.foreign_redex_not_value`).

   The context lemmas are inductions on the list of frames. A frame's hole
   is a direct subterm of the plugged term, or an element of one of its
   lists, so a property holding at every node of the plugged term holds at
   every node of the hole. *)
module Stella.Core.Semantics.Step
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Erase
open Stella.Core.Typing.Aux
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

let value_no_pure_head #sg #gi #e #c h =
  match h with
  | PH_Foreign _ _ _ _ -> V.foreign_redex_not_value sg e
  | _ -> ()

let rec step_plug #sg #gi #ra #st #e #ra' #st' #e' fs h
  : Pure (step sg gi ra st (plug fs e) ra' st' (CTerm (plug fs e')))
         (requires frames_ok sg fs) (ensures fun _ -> True) (decreases fs) =
  match fs with
  | [] -> h
  | f :: fs' -> step_plug fs' (S_Ctx f () h)

let rec step_plug_fault #sg #gi #ra #st #e #ra' #st' #phi fs h
  : Pure (step sg gi ra st (plug fs e) ra' st' (CFault phi))
         (requires frames_ok sg fs) (ensures fun _ -> True) (decreases fs) =
  match fs with
  | [] -> h
  | f :: fs' -> step_plug_fault fs' (S_CtxFault f () h)

let rec exp_all_exps_mid (p: exp -> bool) (vs: list exp) (e: exp) (es: list exp)
  : Lemma (requires exp_all_exps p (L.append vs (e :: es))) (ensures exp_all p e)
          (decreases vs) =
  match vs with
  | [] -> ()
  | _ :: vs' -> exp_all_exps_mid p vs' e es

let exp_all_plug1 (p: exp -> bool) (f: frame) (e: exp)
  : Lemma (requires exp_all p (plug1 f e)) (ensures exp_all p e) =
  match f with
  | FCase vs es _ | FJump _ vs es | FRegion _ vs es _ -> exp_all_exps_mid p vs e es
  | _ -> ()

let stage5_frag_plug1 f e = exp_all_plug1 stage5_node f e

let covers_plug1 sg gi f e = exp_all_plug1 (covered sg gi) f e

let pre_ok_plug1 sg gi f e =
  introduce forall (fs: list frame) (r: exp).
      (frames_ok sg fs /\ e == plug fs r /\ V.foreign_redex sg r) ==> foreign_pre_ok gi r
  with introduce _ ==> _
  with (
    plug_snoc fs f r;
    LP.for_all_append (frame_ok sg) fs [f];
    assert (frames_ok sg (L.append fs [f]));
    assert (plug1 f e == plug (L.append fs [f]) r)
  )

let pre_ok_root sg gi e = assert (plug [] e == e)

(* * Introducing preconditions

   A non-empty context is an inner context inside its outermost frame
   (`plug_snoc`), so a decomposition of `e` other than the root one is a
   decomposition of the hole of a frame `e` is plugged from. *)

let rec split_last (fs: list frame{Cons? fs})
  : Tot (r: (list frame & frame){fs == L.append (fst r) [snd r]}) (decreases fs) =
  match fs with
  | [f] -> ([], f)
  | f :: fs' -> let (init, last) = split_last fs' in (f :: init, last)

let pre_ok_intro sg gi e =
  introduce forall (fs: list frame) (r: exp).
      (frames_ok sg fs /\ e == plug fs r /\ V.foreign_redex sg r) ==> foreign_pre_ok gi r
  with introduce _ ==> _
  with (
    match fs with
    | [] -> ()
    | _ ->
      let (init, f) = split_last fs in
      plug_snoc init f r;
      LP.for_all_append (frame_ok sg) init [f];
      assert (frame_ok sg f /\ plug1 f (plug init r) == e);
      assert (pre_ok sg gi (plug init r));
      assert (frames_ok sg init)
  )

(* The hole of a frame a value is plugged from holds a value, and so does
   every hole of a context. *)
let hole_value (sg: sig) (f: frame) (x: exp)
  : Lemma (requires V.is_value sg (plug1 f x)) (ensures V.is_value sg x) =
  if not (V.is_value sg x) then plug1_not_value sg f x

let rec plug_value_hole (sg: sig) (fs: list frame) (r: exp)
  : Lemma (requires V.is_value sg (plug fs r)) (ensures V.is_value sg r) (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs' -> plug_value_hole sg fs' (plug1 f r); hole_value sg f r

let value_pre_ok sg gi v =
  introduce forall (fs: list frame) (r: exp).
      (frames_ok sg fs /\ v == plug fs r /\ V.foreign_redex sg r) ==> foreign_pre_ok gi r
  with introduce _ ==> _
  with (plug_value_hole sg fs r; V.foreign_redex_not_value sg r)

(* * Values and faults *)

let rec value_no_step #sg #gi #ra #st #e #ra' #st' #c h
  : Lemma (requires V.is_value sg e) (ensures False) (decreases h) =
  match h with
  | S_Pure ph -> value_no_pure_head ph
  | S_Ctx #_ #_ #_ #_ #x #_ #_ #_ f _ h' -> hole_value sg f x; value_no_step h'
  | S_CtxFault #_ #_ #_ #_ #x #_ #_ #_ f _ h' -> hole_value sg f x; value_no_step h'

(* A fault at the root is the outcome of a foreign: every other head rule
   steps to a term. *)
let pure_head_fault (#sg: sig) (#gi: genv) (#e: exp) (#c: config) (ph: pure_head sg gi e c)
  : Lemma (requires CFault? c) (ensures exists (a: abi_fault). c == CFault (FAbi a) /\ foreign_faults sg gi e a) =
  match ph with
  | PH_Foreign #_ #_ #_ #q #ks #args #fe #o _ _ _ _ ->
    (match o with
     | FOFault a -> assert (c == CFault (FAbi a) /\ foreign_faults sg gi e a)
     | FOVal _ -> ())
  | _ -> ()

let rec fault_site (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#phi: fault) (h: step sg gi ra st e ra' st' (CFault phi))
  : Lemma (ensures ra' == ra /\ st' == st /\
                   (exists (fs: list frame) (r: exp) (a: abi_fault).
                      phi == FAbi a /\ frames_ok sg fs /\ e == plug fs r /\
                      foreign_faults sg gi r a))
          (decreases h) =
  match h with
  | S_Pure ph ->
    pure_head_fault ph;
    eliminate exists (a: abi_fault). CFault phi == CFault (FAbi a) /\ foreign_faults sg gi e a
    with (
      assert (plug [] e == e);
      introduce exists (fs: list frame) (r: exp) (a: abi_fault).
          phi == FAbi a /\ frames_ok sg fs /\ e == plug fs r /\ foreign_faults sg gi r a
      with [] e a and ()
    )
  | S_CtxFault #_ #_ #_ #_ #x #_ #_ #_ f _ h' ->
    fault_site h';
    eliminate exists (fs: list frame) (r: exp) (a: abi_fault).
        phi == FAbi a /\ frames_ok sg fs /\ x == plug fs r /\ foreign_faults sg gi r a
    with (
      plug_snoc fs f r;
      LP.for_all_append (frame_ok sg) fs [f];
      introduce exists (fs': list frame) (r: exp) (a: abi_fault).
          phi == FAbi a /\ frames_ok sg fs' /\ e == plug fs' r /\ foreign_faults sg gi r a
      with (L.append fs [f]) r a and ()
    )

let step_fault_shape #sg #gi #ra #st #e #ra' #st' #phi h = fault_site h

(* A pure head rule keeps `R` and `N`, and a frame passes them on. *)
let rec term_site (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#e': exp) (h: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (ensures ra' == ra /\ st' == st) (decreases h) =
  match h with
  | S_Pure _ -> ()
  | S_Ctx _ _ h' -> term_site h'

let step_term_shape #sg #gi #ra #st #e #ra' #st' #e' h = term_site h
