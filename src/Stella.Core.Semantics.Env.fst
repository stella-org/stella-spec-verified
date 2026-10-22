(* Stability of conformance.

   (1) mentions no context. (2) weakens each definition: the declaration
   context `decl_rctx nk rs` has no hypothesis and no term variable, so it
   is extended in place by `decl_rctx nk rs'` as soon as the layouts of
   `rs` are kept (`typing_weaken_ext`), and `Γ_N` by `typing_lctx_ext`.
   (3) quantifies over extensions, and both `layouts_ext` and `lctx_incl`
   compose. *)
module Stella.Core.Semantics.Env
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding.Subst
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Weaken
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Kinst
module L = FStar.List.Tot
module V = Stella.Core.Value

let rec mem_map_fst_assoc (a: atom) (rs: list (atom & layout))
  : Lemma (requires L.mem a (L.map fst rs)) (ensures Some? (L.assoc a rs)) (decreases rs) =
  match rs with
  | (b, _) :: rs' -> if a = b then () else mem_map_fst_assoc a rs'

let rec assoc_mem_map_fst (a: atom) (rs: list (atom & layout))
  : Lemma (requires Some? (L.assoc a rs)) (ensures L.mem a (L.map fst rs)) (decreases rs) =
  match rs with
  | (b, _) :: rs' -> if a = b then () else assoc_mem_map_fst a rs'

let layouts_ext_regions (g1 g2 g1' g2': ctx)
  : Lemma (requires layouts_ext g1 g2 /\ g1'.regions == g1.regions /\ g2'.regions == g2.regions)
          (ensures layouts_ext g1' g2') = ()

let layouts_ext_trans (g1 g2 g3: ctx)
  : Lemma (requires layouts_ext g1 g2 /\ layouts_ext g2 g3) (ensures layouts_ext g1 g3) =
  introduce forall (a: atom).
      (match L.assoc a g1.regions with
       | Some l -> L.assoc a g3.regions == Some l
       | None -> True)
  with (match L.assoc a g1.regions with
        | Some l -> assert (L.assoc a g2.regions == Some l)
        | None -> ())

let lctx_incl_trans (ln1 ln2 ln3: lctx)
  : Lemma (requires lctx_incl ln1 ln2 /\ lctx_incl ln2 ln3) (ensures lctx_incl ln1 ln3) = ()

(* `decl_rctx nk rs'` extends `decl_rctx nk rs` in place. *)
let decl_rctx_weaker (nk: nat) (rs rs': list (atom & layout))
  : Lemma (requires layouts_ext (closed_ctx rs) (closed_ctx rs'))
          (ensures ctx_weaker (decl_rctx nk rs) (decl_rctx nk rs')) =
  let g = decl_rctx nk rs in
  let g' = decl_rctx nk rs' in
  layouts_ext_regions (closed_ctx rs) (closed_ctx rs') g g';
  assert (hyps g == []);
  introduce forall (a: atom). L.mem a (rdom g) ==> L.mem a (rdom g')
  with introduce _ ==> _
  with (
    mem_map_fst_assoc a rs;
    assert (L.assoc a g.regions == L.assoc a rs);
    assoc_mem_map_fst a rs'
  )

let typing_decl_ext (#sg: sig) (#ln: lctx) (#nk: nat) (#rs: list (atom & layout)) (#v: exp)
  (#t: typ) (h: typing sg ln (decl_rctx nk rs) [] v t TRowEmpty)
  (ln': lctx) (rs': list (atom & layout))
  : Pure (typing sg ln' (decl_rctx nk rs') [] v t TRowEmpty)
         (requires layouts_ext (closed_ctx rs) (closed_ctx rs') /\ lctx_incl ln ln')
         (ensures fun _ -> True) =
  decl_rctx_weaker nk rs rs';
  typing_lctx_ext (typing_weaken_ext h (decl_rctx nk rs')) ln'

let gval_typed_ext (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv)
  (ln': lctx) (rs': list (atom & layout)) (q: qname)
  : Lemma (requires gval_typed sg ln rs gi q /\
                    layouts_ext (closed_ctx rs) (closed_ctx rs') /\ lctx_incl ln ln')
          (ensures gval_typed sg ln' rs' gi q) =
  match sg.values q, gi.gvals q with
  | Some vi, Some v ->
    eliminate exists (h: typing sg ln (decl_rctx vi.vl_nk rs) [] v vi.vl_ty TRowEmpty). True
    with (
      introduce exists (h': typing sg ln' (decl_rctx vi.vl_nk rs') [] v vi.vl_ty TRowEmpty). True
      with (typing_decl_ext h ln' rs') and ()
    )
  | _ -> ()

let gvals_typed_ext (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv)
  (ln': lctx) (rs': list (atom & layout))
  : Lemma (requires gvals_typed sg ln rs gi /\
                    layouts_ext (closed_ctx rs) (closed_ctx rs') /\ lctx_incl ln ln')
          (ensures gvals_typed sg ln' rs' gi) =
  introduce forall (q: qname). gval_typed sg ln' rs' gi q
  with gval_typed_ext sg ln rs gi ln' rs' q

let gimpl_ok_ext (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv)
  (ln': lctx) (rs': list (atom & layout))
  : Lemma (requires gimpl_ok sg ln rs gi /\
                    layouts_ext (closed_ctx rs) (closed_ctx rs') /\ lctx_incl ln ln')
          (ensures gimpl_ok sg ln' rs' gi) =
  introduce forall (rs'': list (atom & layout)) (ln'': lctx) (e: exp).
      rt_ext sg ln' rs' ln'' rs'' ==> foreign_call_ok sg gi ln'' rs'' e
  with introduce _ ==> _
  with (
    layouts_ext_trans (closed_ctx rs) (closed_ctx rs') (closed_ctx rs'');
    lctx_incl_trans ln ln' ln'';
    assert (rt_ext sg ln rs ln'' rs'')
  )

let genv_ok_covered sg ln rs gi q v = ()

let genv_ok_gval sg ln rs gi q vi v = assert (gval_typed sg ln rs gi q)

let genv_ok_foreign sg ln rs gi e =
  assert (rt_ext sg ln rs ln rs)

let genv_ok_ext sg ln rs gi ln' rs' =
  gvals_typed_ext sg ln rs gi ln' rs';
  gimpl_ok_ext sg ln rs gi ln' rs'

let genv_ok_closed sg gi ln rs =
  assert (layouts_ext (closed_ctx []) (closed_ctx rs));
  assert (lctx_incl [] ln);
  genv_ok_ext sg [] [] gi ln rs
