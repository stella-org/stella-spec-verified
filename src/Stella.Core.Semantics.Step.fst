(* A redex of a pure or effect head rule is no value: its head is an
   elimination form, a `handle`, a run-time form that is no value, a global with a body, or a
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
open Stella.Core.Semantics.Ctx.Ren
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

let value_no_pure_head #sg #gi #e #c h =
  match h with
  | PH_Foreign _ _ _ _ -> V.foreign_redex_not_value sg e
  | _ -> ()

(* An effect rule rewrites a `handle`, which is no value. *)

let rec clause_of_mem (op: opname) (cs: list clause) (c: clause)
  : Lemma (requires clause_of op cs == Some c) (ensures clause_op c == op /\ L.memP c cs)
          (decreases cs) =
  match cs with
  | c0 :: cs0 -> if clause_op c0 = op then () else clause_of_mem op cs0 c

let eff_step_shape #sg #gi #e #c h =
  match h with
  | EH_Return _ -> ()
  | EH_Full _ _ _ _ _ -> ()
  | EH_Fast _ _ _ _ -> ()

let value_no_eff_head #sg #gi #e #c h = eff_step_shape h

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

(* * Fragments

   `stage5_node` implies `stage6_node`, so `exp_all` of the first implies
   `exp_all` of the second, node by node. *)

let stage5_node_stage6 (e: exp) : Lemma (requires stage5_node e) (ensures stage6_node e) = ()

let rec s56_exp (e: exp)
  : Lemma (requires exp_all stage5_node e) (ensures exp_all stage6_node e) (decreases e) =
  stage5_node_stage6 e;
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> s56_exp b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> s56_exp e1; s56_exp e2
  | ELetRec bs b -> s56_binds bs; s56_exp b
  | ECase es dt -> s56_exps es; s56_dt dt
  | EMatch th dt -> s56_exps th; s56_dt dt
  | EJump _ es -> s56_exps es
  | EHandle b h -> s56_exp b; s56_exp h.h_ret; s56_cls h.h_clauses
  | ERegion _ es b -> s56_exps es; s56_exp b
  | ERegionOpen _ th b -> s56_cells th; s56_exp b

and s56_exps (es: list exp)
  : Lemma (requires exp_all_exps stage5_node es) (ensures exp_all_exps stage6_node es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> s56_exp e; s56_exps es

and s56_binds (bs: list (typ & exp))
  : Lemma (requires exp_all_binds stage5_node bs) (ensures exp_all_binds stage6_node bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> s56_exp e; s56_binds bs

and s56_cells (th: list (key & exp))
  : Lemma (requires exp_all_cells stage5_node th) (ensures exp_all_cells stage6_node th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> s56_exp e; s56_cells th

and s56_dt (dt: dtree)
  : Lemma (requires exp_all_dt stage5_node dt) (ensures exp_all_dt stage6_node dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> s56_exp e
  | DBind _ dt -> s56_dt dt
  | DSwitchCtor _ bs df -> s56_brs bs; s56_odt df
  | DSwitchLit _ bs df -> s56_brs bs; s56_dt df
  | DSwitchKey _ bs df -> s56_brs bs; s56_odt df
  | DGuard e dt1 dt2 -> s56_exp e; s56_dt dt1; s56_dt dt2

and s56_odt (df: option dtree)
  : Lemma (requires exp_all_odt stage5_node df) (ensures exp_all_odt stage6_node df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> s56_dt dt

and s56_brs (#lb: eqtype) (bs: list (lb & dtree))
  : Lemma (requires exp_all_brs stage5_node bs) (ensures exp_all_brs stage6_node bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> s56_dt dt; s56_brs bs

and s56_cls (cs: list clause)
  : Lemma (requires exp_all_cls stage5_node cs) (ensures exp_all_cls stage6_node cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> s56_exp b; s56_cls cs
  | CFast _ _ _ b :: cs -> s56_exp b; s56_cls cs

let stage5_frag_stage6 e = s56_exp e

let stage5_no_eff #sg #gi #e #c h = eff_step_shape h

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

let stage6_frag_plug1 f e = exp_all_plug1 stage6_node f e

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
  | S_Eff eh -> value_no_eff_head eh
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
  | S_Eff eh -> eff_step_shape eh
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

(* A pure or effect head rule keeps `R` and `N`, and a frame passes them on. *)
let rec term_site (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#e': exp) (h: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (ensures ra' == ra /\ st' == st) (decreases h) =
  match h with
  | S_Pure _ -> ()
  | S_Eff _ -> ()
  | S_Ctx _ _ h' -> term_site h'

let step_term_shape #sg #gi #ra #st #e #ra' #st' #e' h = term_site h
