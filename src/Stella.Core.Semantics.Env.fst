(* Stability of conformance.

   (1) mentions no context. (2) weakens each definition: the declaration
   context `decl_rctx nk rs` has no hypothesis and no term variable, so it
   is extended in place by `decl_rctx nk rs'` as soon as the layouts of
   `rs` are kept (`typing_weaken_ext`), and `Γ_N` by `typing_lctx_ext`.
   (3) quantifies over extensions, and both `layouts_ext` and `lctx_incl`
   compose.

   Coverage is read through `globals` by one induction over the mutual
   structure of terms. *)
module Stella.Core.Semantics.Env
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding.Subst
open Stella.Core.Spine
open Stella.Core.Spine.Lemmas
open Stella.Core.Erase
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Weaken
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Kinst
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* * Coverage through `globals`

   One induction over the mutual structure: each node contributes its own
   name, if it is a global, before those of its subterms, and both sides
   distribute over the concatenation (`for_all_append`). *)

let rec covers_globals_e (sg: sig) (gi: genv) (e: exp)
  : Lemma (ensures exp_all (covered sg gi) e == L.for_all (covered_name sg gi) (globals e))
          (decreases e) =
  let c = covered_name sg gi in
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b ->
    covers_globals_e sg gi b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    covers_globals_e sg gi e1; covers_globals_e sg gi e2;
    LP.for_all_append c (globals e1) (globals e2)
  | ELetRec bs b ->
    covers_globals_binds sg gi bs; covers_globals_e sg gi b;
    LP.for_all_append c (globals_binds bs) (globals b)
  | ECase es dt | EMatch es dt ->
    covers_globals_exps sg gi es; covers_globals_dt sg gi dt;
    LP.for_all_append c (globals_exps es) (globals_dt dt)
  | EJump _ es -> covers_globals_exps sg gi es
  | EHandle b h ->
    covers_globals_e sg gi b; covers_globals_e sg gi h.h_ret; covers_globals_cls sg gi h.h_clauses;
    LP.for_all_append c (globals h.h_ret) (globals_cls h.h_clauses);
    LP.for_all_append c (globals b) (L.append (globals h.h_ret) (globals_cls h.h_clauses))
  | ERegion _ es b ->
    covers_globals_exps sg gi es; covers_globals_e sg gi b;
    LP.for_all_append c (globals_exps es) (globals b)
  | ERegionOpen _ th b ->
    covers_globals_cells sg gi th; covers_globals_e sg gi b;
    LP.for_all_append c (globals_cells th) (globals b)

and covers_globals_exps (sg: sig) (gi: genv) (es: list exp)
  : Lemma (ensures exp_all_exps (covered sg gi) es ==
                   L.for_all (covered_name sg gi) (globals_exps es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' ->
    covers_globals_e sg gi e; covers_globals_exps sg gi es';
    LP.for_all_append (covered_name sg gi) (globals e) (globals_exps es')

and covers_globals_binds (sg: sig) (gi: genv) (bs: list (typ & exp))
  : Lemma (ensures exp_all_binds (covered sg gi) bs ==
                   L.for_all (covered_name sg gi) (globals_binds bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs' ->
    covers_globals_e sg gi e; covers_globals_binds sg gi bs';
    LP.for_all_append (covered_name sg gi) (globals e) (globals_binds bs')

and covers_globals_cells (sg: sig) (gi: genv) (th: list (key & exp))
  : Lemma (ensures exp_all_cells (covered sg gi) th ==
                   L.for_all (covered_name sg gi) (globals_cells th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th' ->
    covers_globals_e sg gi e; covers_globals_cells sg gi th';
    LP.for_all_append (covered_name sg gi) (globals e) (globals_cells th')

and covers_globals_dt (sg: sig) (gi: genv) (dt: dtree)
  : Lemma (ensures exp_all_dt (covered sg gi) dt == L.for_all (covered_name sg gi) (globals_dt dt))
          (decreases dt) =
  let c = covered_name sg gi in
  match dt with
  | DLeaf e -> covers_globals_e sg gi e
  | DBind _ dt' -> covers_globals_dt sg gi dt'
  | DSwitchCtor _ bs df ->
    covers_globals_brs sg gi bs; covers_globals_odt sg gi df;
    LP.for_all_append c (globals_brs bs) (globals_odt df)
  | DSwitchLit _ bs df ->
    covers_globals_brs sg gi bs; covers_globals_dt sg gi df;
    LP.for_all_append c (globals_brs bs) (globals_dt df)
  | DSwitchKey _ bs df ->
    covers_globals_brs sg gi bs; covers_globals_odt sg gi df;
    LP.for_all_append c (globals_brs bs) (globals_odt df)
  | DGuard e dt1 dt2 ->
    covers_globals_e sg gi e; covers_globals_dt sg gi dt1; covers_globals_dt sg gi dt2;
    LP.for_all_append c (globals_dt dt1) (globals_dt dt2);
    LP.for_all_append c (globals e) (L.append (globals_dt dt1) (globals_dt dt2))

and covers_globals_odt (sg: sig) (gi: genv) (df: option dtree)
  : Lemma (ensures exp_all_odt (covered sg gi) df ==
                   L.for_all (covered_name sg gi) (globals_odt df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> covers_globals_dt sg gi dt

and covers_globals_brs (#lb: eqtype) (sg: sig) (gi: genv) (bs: list (lb & dtree))
  : Lemma (ensures exp_all_brs (covered sg gi) bs ==
                   L.for_all (covered_name sg gi) (globals_brs bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' ->
    covers_globals_dt sg gi dt; covers_globals_brs sg gi bs';
    LP.for_all_append (covered_name sg gi) (globals_dt dt) (globals_brs bs')

and covers_globals_cls (sg: sig) (gi: genv) (cs: list clause)
  : Lemma (ensures exp_all_cls (covered sg gi) cs ==
                   L.for_all (covered_name sg gi) (globals_cls cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs' ->
    covers_globals_e sg gi b; covers_globals_cls sg gi cs';
    LP.for_all_append (covered_name sg gi) (globals b) (globals_cls cs')
  | CFast _ _ _ b :: cs' ->
    covers_globals_e sg gi b; covers_globals_cls sg gi cs';
    LP.for_all_append (covered_name sg gi) (globals b) (globals_cls cs')

let covers_globals sg gi e = covers_globals_e sg gi e

(* The names of covered terms are covered. *)
let rec covers_globals_list (sg: sig) (gi: genv) (vs: list exp)
  : Lemma (requires L.for_all (covers sg gi) vs)
          (ensures L.for_all (covered_name sg gi) (globals_exps vs)) (decreases vs) =
  match vs with
  | [] -> ()
  | v :: vs' ->
    covers_globals sg gi v; covers_globals_list sg gi vs';
    LP.for_all_append (covered_name sg gi) (globals v) (globals_exps vs')

let rec for_all_weaken (c d: qname -> bool) (l: list qname)
  : Lemma (requires L.for_all d l /\ (forall q. d q ==> c q))
          (ensures L.for_all c l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l' -> for_all_weaken c d l'

let covers_relative_covers sg gi vs v =
  let gs = globals_exps vs in
  covers_globals_list sg gi vs;
  L.for_all_mem (covered_name sg gi) gs;
  introduce forall (q: qname). L.mem q gs ==> covered_name sg gi q
  with introduce _ ==> _ with LP.mem_memP q gs;
  for_all_weaken (covered_name sg gi) (covered_or_in sg gi vs) (globals v);
  covers_globals sg gi v

let rec mem_globals_exps (q: qname) (v: exp) (vs: list exp)
  : Lemma (requires L.mem v vs /\ L.mem q (globals v)) (ensures L.mem q (globals_exps vs))
          (decreases vs) =
  match vs with
  | v' :: vs' ->
    LP.append_mem (globals v') (globals_exps vs') q;
    if v' = v then () else mem_globals_exps q v vs'

let rec for_all_intro_mem (f: qname -> bool) (l: list qname)
  : Lemma (requires forall q. L.mem q l ==> f q) (ensures L.for_all f l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l' -> for_all_intro_mem f l'

let covers_relative_self sg gi vs v =
  introduce forall (q: qname). L.mem q (globals v) ==> covered_or_in sg gi vs q
  with introduce _ ==> _ with mem_globals_exps q v vs;
  for_all_intro_mem (covered_or_in sg gi vs) (globals v)

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

let gforeign_ok_ext (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv)
  (ln': lctx) (rs': list (atom & layout))
  : Lemma (requires gforeign_ok sg ln rs gi /\
                    layouts_ext (closed_ctx rs) (closed_ctx rs') /\ lctx_incl ln ln')
          (ensures gforeign_ok sg ln' rs' gi) =
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
  gforeign_ok_ext sg ln rs gi ln' rs'

let genv_ok_closed sg gi ln rs =
  assert (layouts_ext (closed_ctx []) (closed_ctx rs));
  assert (lctx_incl [] ln);
  genv_ok_ext sg [] [] gi ln rs
