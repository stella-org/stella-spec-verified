(* Proof structure.

   Spines: `decompose_global_app` of a frame of a chain is that of its
   function part with one more argument, and `None` for every other
   frame. A hole of a chain sits in its function part or at a value
   argument, which `spine_like` ignores, so the relation goes through
   every frame. The cursor reads a value argument through
   its position only (`cursor_step`), so it is the same on `L.map
   arg_shape` of the arguments (`cursor_shape`).

   Plugging: by induction on the list of frames, outermost last, as
   `plug (f :: fs) e = plug fs (plug1 f e)`: the outer frames `fs` are
   split first, around `plug1 f e`, which is no value
   (`Stella.Core.Semantics.Ctx.plug1_not_value`), and their hole is split
   at `f` by `plug1_typing`. Putting back goes the other way, each frame
   keeping the spine. The effect entries of key `k` go from the hole of `f`
   to the hole of `fs` (`hole_row_eff`), then out to the whole term.

   Rows: an entry of an extension is the element added or one of the row
   extended, and an entry of a part of a union is one of the union
   (`Stella.Core.Rows.Split`). The element a `handle` of another key adds
   has another key (`canon_ent_key`), and a region element has a payload
   that is no effect's.

   The handled entry: the `perform`'s entry is, through the `Ev_k`, an entry
   of the handled computation's row `( E τ̄ | ρ )`, which also has the
   handler's own entry at the same key; sharpness makes the two payloads
   one.

   Resuming: the redex's derivation is weakened past the new binder
   (`typing_weaken_var`), which renames the term by `↑1`, as `resume`
   renames the context and the handler (`ren_tm_plug`, `ren_tm_handle`).
   The weakened derivation is split again, and the `perform` in its hole is
   inverted again, its type being the instance of the operation's result
   type at arguments equal to the handler's (`handled_entry`,
   `op_inst_canon`); the variable `y : τ'` has that type. *)
module Stella.Core.Typing.Eff
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
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Sharp
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Prim
open Stella.Core.Typing
open Stella.Core.Typing.Wf
open Stella.Core.Typing.Inversion
open Stella.Core.Typing.Regularity
open Stella.Core.Typing.Weaken
open Stella.Core.Typing.Subst.Tys
open Stella.Core.Typing.Plug
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Ctx.Ren
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* * Spines *)

let spine_like_atoms a b = ()

let plug1_nonchain (f: frame) (a: exp)
  : Lemma (requires ~(FAppArg? f) /\ ~(FAppFun? f) /\ ~(FTyApp? f) /\ ~(FCApp? f))
          (ensures decompose_global_app (plug1 f a) == None) =
  match f with
  | FOpenEff _ -> () | FOpenEffC _ -> () | FExtendL _ _ -> () | FExtendR _ _ -> ()
  | FUpdateL _ _ -> () | FUpdateR _ _ -> () | FMergeL _ -> () | FMergeR _ -> ()
  | FSelect _ -> () | FRestrict _ -> () | FInject _ _ -> () | FWeaken _ _ -> ()
  | FAbsurd _ -> () | FLet _ _ -> () | FCase _ _ _ -> () | FGuard _ _ _ -> ()
  | FLetJoin _ _ _ -> () | FJump _ _ _ -> () | FPerform _ _ _ -> () | FHandle _ -> ()
  | FRegion _ _ _ _ -> () | FRegionOpen _ _ -> () | FWriteCell _ _ -> () | FFill _ -> ()

let spine_like_plug1 f a b =
  match f with
  | FAppArg fn ->
    (match decompose_global_app fn with
     | Some (_, _, args) ->
       LP.map_append arg_shape args [SVal a];
       LP.map_append arg_shape args [SVal b]
     | None -> ())
  | FAppFun v ->
    (match decompose_global_app a, decompose_global_app b with
     | Some (_, _, args), Some (_, _, args') ->
       LP.map_append arg_shape args [SVal v];
       LP.map_append arg_shape args' [SVal v]
     | _ -> ())
  | FTyApp t ->
    (match decompose_global_app a, decompose_global_app b with
     | Some (_, _, args), Some (_, _, args') ->
       LP.map_append arg_shape args [STy t];
       LP.map_append arg_shape args' [STy t]
     | _ -> ())
  | FCApp ->
    (match decompose_global_app a, decompose_global_app b with
     | Some (_, _, args), Some (_, _, args') ->
       LP.map_append arg_shape args [SConstr];
       LP.map_append arg_shape args' [SConstr]
     | _ -> ())
  | _ -> plug1_nonchain f a; plug1_nonchain f b

let rec cursor_shape (sg: sig) (t: typ) (th: tsub) (args: list spine_arg)
  : Lemma (ensures cursor sg t th args == cursor sg t th (L.map arg_shape args)) (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    assert (cursor_step sg t th a == cursor_step sg t th (arg_shape a));
    match cursor_step sg t th a with
    | Some (t', th') -> cursor_shape sg t' th' args'
    | None -> ()

let spine_like_cursor sg a b =
  match decompose_global_app a, decompose_global_app b with
  | Some (q, ks, args), Some (_, _, args') ->
    (match global_scheme sg q with
     | Some (_, nk, t) ->
       cursor_shape sg (kinst_ty ks t) tvar args;
       cursor_shape sg (kinst_ty ks t) tvar args'
     | None -> ())
  | _ -> ()

(* * Rows *)

let empty_entries () : Lemma (row_entries (canon TRowEmpty) == []) =
  assert_norm (row_entries (canon TRowEmpty) == [])

let hole_row_eff f k r hr =
  match f with
  | FOpenEffC r' ->
    introduce forall (q: qname) (cs: list ctyp).
      L.mem (k, PEff q cs) (row_entries (canon hr)) ==> L.mem (k, PEff q cs) (row_entries (canon r))
    with mem_entries_union hr r' (k, PEff q cs)
  | FHandle h ->
    canon_ent_key h.h_ent;
    introduce forall (q: qname) (cs: list ctyp).
      L.mem (k, PEff q cs) (row_entries (canon hr)) ==> L.mem (k, PEff q cs) (row_entries (canon r))
    with mem_entries_ext h.h_ent r (k, PEff q cs)
  | FRegionOpen a _ ->
    introduce forall (q: qname) (cs: list ctyp).
      L.mem (k, PEff q cs) (row_entries (canon hr)) ==> L.mem (k, PEff q cs) (row_entries (canon r))
    with mem_entries_ext (EntRegion (RFree a)) r (k, PEff q cs)
  | FFill _ -> empty_entries ()
  | _ -> ()

(* * Plugging a context *)

let rec plug_go (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#fs: list frame) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d (plug fs e) t r)
  : Pure (plug_inv sg ln g d fs e t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ not (V.is_value sg e))
         (ensures fun _ -> True)
         (decreases fs) =
  match fs with
  | [] ->
    let fill (e': exp) (h': typing sg ln g d e' t r)
      : Pure (typing sg ln g d (plug fs e') t r) (requires spine_like e e') (ensures fun _ -> True) =
      h'
    in
    { p_d = d; p_t = t; p_r = r; p_hole = h; p_rows = (); p_fill = fill }
  | f :: fs' ->
    plug1_not_value sg f e;
    let h0 : typing sg ln g d (plug fs' (plug1 f e)) t r = h in
    let pi = plug_go #sg #ln #g #d #fs' #(plug1 f e) #t #r h0 in
    let p1 = plug1_typing #sg #ln #g #pi.p_d #f #e #pi.p_t #pi.p_r pi.p_hole in
    introduce forall (k: key). ev_k k fs ==> eff_entries_in k p1.hr r
    with introduce _ ==> _
    with begin
      assert (ev_k k fs');
      hole_row_eff f k pi.p_r p1.hr
    end;
    let fill (e': exp) (h': typing sg ln g p1.hd e' p1.ht p1.hr)
      : Pure (typing sg ln g d (plug fs e') t r) (requires spine_like e e') (ensures fun _ -> True) =
      spine_like_plug1 f e e';
      spine_like_cursor sg (plug1 f e) (plug1 f e');
      let h1 = p1.fill e' h' in
      pi.p_fill (plug1 f e') h1
    in
    { p_d = p1.hd; p_t = p1.ht; p_r = p1.hr; p_hole = p1.hole; p_rows = (); p_fill = fill }

let plug_typing #sg #ln #g #d #fs #e #t #r h = plug_go h

(* * `handle` and `perform` *)

let inv_handle #sg #ln #g #d #e #h #t #r hh =
  let s = strip_conv hh in
  match s.cf_h with
  | T_Handle #_ #_ #_ #_ #_ #_ #b #r0 #lbl #q #ts #ei _ _ _ _ he hret hcl ->
    { hi_b = b; hi_r = r0; hi_lbl = lbl; hi_q = q; hi_ts = ts; hi_ei = ei;
      hi_body = he; hi_ret = hret; hi_cls = hcl; hi_facts = () }
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let handle_typing #sg #ln #g #e #h #t #r hi d e' he =
  T_Handle #sg #ln #g #d #e' #h #hi.hi_b #hi.hi_r #hi.hi_lbl #hi.hi_q #hi.hi_ts #hi.hi_ei
    () () () () he hi.hi_ret hi.hi_cls

let inv_perform #sg #ln #g #d #k #op #ss #v #t #r h =
  let s = strip_conv h in
  match s.cf_h with
  | T_Perform #_ #_ #_ #_ #_ #_ #_ #_ #rr #q #ei #os ts _ _ _ hv ->
    { pf_q = q; pf_ts = ts; pf_ei = ei; pf_os = os; pf_r = rr; pf_arg = hv; pf_facts = () }
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let handled_entry sg g en r0 pr k lbl q q' ts ts' =
  let rr = TRowExt en r0 in
  let e1 : centry = (k, PEff q' (canon_tys ts')) in
  let e2 = canon_ent en in
  assert (L.mem e1 (row_entries (canon rr)));
  mem_entries_ext en r0 e2;
  canon_ent_key en;
  check_sharp sg g rr EEffect;
  assert (L.mem e2 (row_entries (canon rr)) /\ fst e1 == fst e2)

(* * Resuming *)

let perform_facts (sg: sig) (k: key) (op: opname) (ss: list typ) (v: exp)
  : Lemma (not (V.is_value sg (EPerform k op ss v)) /\
           None? (decompose_global_app (EPerform k op ss v)) /\
           None? (decompose_global_app (EVar 0))) =
  assert_norm (not (V.is_value sg (EPerform k op ss v)));
  assert_norm (None? (decompose_global_app (EPerform k op ss v)));
  assert_norm (None? (decompose_global_app (EVar 0)))

let perform_ren (xi: ren) (k: key) (op: opname) (ss: list typ) (v: exp)
  : Lemma (ren_tm xi (EPerform k op ss v) == EPerform k op ss (ren_tm xi v)) =
  ()

let resume_typing #sg #ln #g #fs #k #op #ss #v #hd #b #r0 h lbl q ts ei os tp d0 b' r' =
  let g1 = push_var g tp in
  let p = EPerform k op ss v in
  let p1 = EPerform k op ss (ren_tm (shift 1) v) in
  let fs1 = ren_frames (shift 1) fs in
  let hd1 = ren_handler (shift 1) hd in
  wf_ctx_push_var sg g tp;
  ctx_ext_push_var g tp;
  ren_tm_handle (shift 1) (plug fs p) hd;
  ren_tm_plug (shift 1) fs p;
  perform_ren (shift 1) k op ss v;
  perform_facts sg k op ss (ren_tm (shift 1) v);
  handler_key_ren (shift 1) hd;
  ev_k_ren k (shift 1) fs;
  let hw = typing_weaken_var h tp in
  let hw : typing sg ln g1 [] (EHandle (plug fs1 p1) hd1) b r0 = hw in
  let hi = inv_handle hw in
  let pi = plug_typing #sg #ln #g1 #[] #fs1 #p1 #hd1.h_ret_ty #(TRowExt hd1.h_ent hi.hi_r)
             hi.hi_body in
  let pf = inv_perform #sg #ln #g1 #pi.p_d #k #op #ss #(ren_tm (shift 1) v) #pi.p_t #pi.p_r
             pi.p_hole in
  assert (ev_k k fs1);
  assert (eff_entries_in k pi.p_r (TRowExt hd1.h_ent hi.hi_r));
  handled_entry sg g1 hd1.h_ent hi.hi_r pi.p_r k lbl q pf.pf_q ts pf.pf_ts;
  op_inst_canon ts pf.pf_ts ss os.res;
  typing_regular pi.p_hole;
  let hv : typing sg ln g1 pi.p_d (EVar 0) tp pi.p_r = T_Var () () in
  let hv : typing sg ln g1 pi.p_d (EVar 0) pi.p_t pi.p_r = T_Conv hv () () in
  spine_like_atoms p1 (EVar 0);
  let he = pi.p_fill (EVar 0) hv in
  let hh = handle_typing hi d0 (plug fs1 (EVar 0)) he in
  check_weaken sg g g1 b' KType;
  check_weaken sg g g1 r' (KRow EEffect);
  T_Conv hh () ()

(* * Clauses *)

let rec full_clause_typing #sg #ln #g #ei #ts #r #b #cs hc op nb s kt body =
  match hc with
  | TCL_Nil _ -> false_elim ()
  | TCL_Full #_ #_ #_ #_ #_ #_ #_ #op' #nb' #s' #kt' #body' #cs' #os _ _ _ hb hc' ->
    if op' = op then { fc_os = os; fc_body = hb; fc_facts = () }
    else full_clause_typing hc' op nb s kt body
  | TCL_Fast #_ #_ #_ #_ #_ #_ #_ #op' #nb' #s' #body' #cs' #os _ _ _ hc' ->
    if op' = op then false_elim () else full_clause_typing hc' op nb s kt body

let rec fast_clause_typing #sg #ln #g #ei #ts #r #b #cs hc op nb s body =
  match hc with
  | TCL_Nil _ -> false_elim ()
  | TCL_Full #_ #_ #_ #_ #_ #_ #_ #op' #nb' #s' #kt' #body' #cs' #os _ _ _ _ hc' ->
    if op' = op then false_elim () else fast_clause_typing hc' op nb s body
  | TCL_Fast #_ #_ #_ #_ #_ #_ #_ #op' #nb' #s' #body' #cs' #os _ _ hb hc' ->
    if op' = op then { sc_os = os; sc_body = hb; sc_facts = () }
    else fast_clause_typing hc' op nb s body
