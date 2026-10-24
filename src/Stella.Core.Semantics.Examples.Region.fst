(* Each step is built from its rule, as in
   `Stella.Core.Semantics.Examples.Eff`. The premises are closed facts about
   `eff_sig`, the cells and the term, and the reduct the rule computes
   (opening, the cells, updating, renaming and plugging) equals the term
   written in the interface; both hold by normalization.

   That `shadowed` has no other step is by inversion of the step. No pure
   head rule, effect rule or opening applies at an open region frame or at
   a `readCell`. A context of the inner frame ending at a cell operation is
   empty (`plug_read_inv`), and one of the outer frame has the inner frame
   as its outermost frame, which is named `0` (`plug_open_not_ev_l`). *)
module Stella.Core.Semantics.Examples.Region
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Prim
open Stella.Core.Region
open Stella.Core.Spine
open Stella.Core.Sig.Examples
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Ctx.Ren
open Stella.Core.Semantics.Step
open Stella.Core.Semantics.Examples
open Stella.Core.Semantics.Examples.Eff
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

let retype (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#c: config)
  (e2: exp) (c2: config) (h: step eff_sig ex_genv ra st e ra' st' c)
  : Pure (step eff_sig ex_genv ra st e2 ra' st' c2) (requires e == e2 /\ c == c2)
         (ensures fun _ -> True) =
  h

let int_values () : Lemma (V.is_value eff_sig (lit_int 0l) /\ V.is_value eff_sig (lit_int 1l) /\
                            V.is_value eff_sig (lit_int 2l) /\ V.is_value eff_sig (lit_int 5l)) =
  assert_norm (V.is_value eff_sig (lit_int 0l) /\ V.is_value eff_sig (lit_int 1l) /\
               V.is_value eff_sig (lit_int 2l) /\ V.is_value eff_sig (lit_int 5l))

(* `( n ↦ v )` holds a value when `v` is one, and `n` reads it. *)
let cell_facts (v: exp)
  : Lemma (requires V.is_value eff_sig v)
          (ensures cells_values eff_sig (cell_n v) /\ L.assoc n_key (cell_n v) == Some v /\
                   frame_ok eff_sig (FRegionOpen 0 (cell_n v)) /\
                   frame_ok eff_sig (FRegionOpen 1 (cell_n v))) =
  assert_norm (L.assoc n_key (cell_n v) == Some v)

(* * Opening *)

let open_body : exp = EReadCell (RBound 0) n_key

let open_step =
  int_values ();
  assert_norm (L.for_all (V.is_value eff_sig) [lit_int 0l]);
  assert_norm (~(L.mem 1 [0]) /\ ~(L.mem 1 (frn_exp fresh_region)));
  let rh = RH_Open #eff_sig #ex_genv #[0] #[(n_key, t_int)] #[lit_int 0l] #open_body #1 () () in
  assert_norm (init_cells (L.map fst [(n_key, t_int)]) [lit_int 0l] == cell_n (lit_int 0l));
  assert_norm (open_region 1 open_body == read_n 1);
  retype fresh_region (CTerm (ERegionOpen 1 (cell_n (lit_int 0l)) (read_n 1)))
    (S_Region #_ #_ #[0] #[] rh)

(* * Exit *)

let exit_step =
  int_values ();
  let rh = RH_Exit #eff_sig #ex_genv #[] #0 #(cell_n (lit_int 0l)) #(lit_int 1l) () in
  S_Region #_ #_ #[] #[] rh

(* * Read and write *)

(* The read of `n` in the hole of `fs`, under `region⟨0⟩ ( n ↦ v )`. *)
let read_at (fs: list frame) (v: exp)
  : Pure (region_head eff_sig ex_genv [] (ERegionOpen 0 (cell_n v) (plug fs (read_n 0))) []
            (CTerm (ERegionOpen 0 (cell_n v) (plug fs v))))
         (requires frames_ok eff_sig fs /\ ev_l 0 fs /\ V.is_value eff_sig v)
         (ensures fun _ -> True) =
  cell_facts v;
  RH_Read #eff_sig #ex_genv #[] #0 #(cell_n v) #fs #n_key #v () ()

let read_step =
  int_values ();
  assert_norm (frames_ok eff_sig [] /\ ev_l 0 []);
  S_Region #_ #_ #[] #[] (read_at [] (lit_int 0l))

(* The write of `5` to `n` in the hole of `fs`, under `region⟨0⟩ ( n ↦ 0 )`. *)
let write_at (fs: list frame)
  : Pure (region_head eff_sig ex_genv [] (ERegionOpen 0 (cell_n (lit_int 0l)) (plug fs write_n5)) []
            (CTerm (ERegionOpen 0 (cell_n (lit_int 5l)) (plug fs unit_v))))
         (requires frames_ok eff_sig fs /\ ev_l 0 fs)
         (ensures fun _ -> True) =
  int_values ();
  cell_facts (lit_int 0l);
  assert_norm (cells_update (cell_n (lit_int 0l)) n_key (lit_int 5l) == cell_n (lit_int 5l));
  RH_Write #eff_sig #ex_genv #[] #0 #(cell_n (lit_int 0l)) #fs #n_key #(lit_int 5l) () ()

let write_step =
  assert_norm (frames_ok eff_sig [] /\ ev_l 0 []);
  S_Region #_ #_ #[] #[] (write_at [])

let read_let_step =
  int_values ();
  let fs = [FLet t_int (EVar 0)] in
  assert_norm (frames_ok eff_sig fs /\ ev_l 0 fs);
  retype (ERegionOpen 0 (cell_n (lit_int 0l)) read_let)
    (CTerm (ERegionOpen 0 (cell_n (lit_int 0l)) (ELet t_int (lit_int 0l) (EVar 0))))
    (S_Region #_ #_ #[] #[] (read_at fs (lit_int 0l)))

let write_let_step =
  let fs = [FLet t_unit (read_n 0)] in
  assert_norm (frames_ok eff_sig fs /\ ev_l 0 fs);
  retype (ERegionOpen 0 (cell_n (lit_int 0l)) write_let)
    (CTerm (ERegionOpen 0 (cell_n (lit_int 5l)) (ELet t_unit unit_v (read_n 0))))
    (S_Region #_ #_ #[] #[] (write_at fs))

(* * The innermost frame of a name *)

let inner : exp = ERegionOpen 0 (cell_n (lit_int 2l)) (read_n 0)

let inner_reduct : exp = ERegionOpen 0 (cell_n (lit_int 2l)) (lit_int 2l)

let shadowed_step =
  int_values ();
  cell_facts (lit_int 1l);
  assert_norm (frames_ok eff_sig [] /\ ev_l 0 []);
  let s = S_Region #_ #_ #[] #[] (read_at [] (lit_int 2l)) in
  retype shadowed (CTerm shadowed_reduct)
    (S_Ctx #_ #_ #[] #[] #inner #[] #[] #inner_reduct (FRegionOpen 0 (cell_n (lit_int 1l))) ()
       (retype inner (CTerm inner_reduct) s))

let shadowed_outer_excluded () =
  assert_norm (not (ev_l 0 [FRegionOpen 0 (cell_n (lit_int 2l))]))

(* ** Inversion *)

let plug1_not_read (f: frame) (x: exp) (r: region_ref) (k: key)
  : Lemma (~(plug1 f x == EReadCell r k)) = ()

let plug1_open_inv (f: frame) (x: exp) (a: atom) (th: list (key & exp)) (b: exp)
  : Lemma (requires plug1 f x == ERegionOpen a th b) (ensures f == FRegionOpen a th /\ x == b) = ()

(* A context whose plugged term is a `readCell` is empty. *)
let rec plug_read_inv (fs: list frame) (x: exp) (r: region_ref) (k: key)
  : Lemma (requires plug fs x == EReadCell r k) (ensures fs == [] /\ x == EReadCell r k)
          (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs' -> plug_read_inv fs' (plug1 f x) r k; plug1_not_read f x r k

let rec split_last (fs: list frame{Cons? fs})
  : Tot (r: (list frame & frame){fs == L.append (fst r) [snd r]}) (decreases fs) =
  match fs with
  | [f] -> ([], f)
  | f :: fs' -> let (init, last) = split_last fs' in (f :: init, last)

(* A context whose plugged term is an open region frame named `a`, and
   whose hole is not, has that frame as its outermost frame, so it is no
   `Ev_ℓ` for `a`. *)
let plug_open_not_ev_l (fs: list frame) (x: exp) (a: atom) (th: list (key & exp)) (b: exp)
  : Lemma (requires plug fs x == ERegionOpen a th b /\ not (ERegionOpen? x))
          (ensures not (ev_l a fs)) =
  match fs with
  | [] -> ()
  | _ ->
    let (init, f) = split_last fs in
    plug_snoc init f x;
    plug1_open_inv f (plug init x) a th b;
    LP.for_all_append (not_region_of a) init [f]

let pure_not_cell (#e: exp) (#c: config) (ph: pure_head eff_sig ex_genv e c)
  : Lemma (requires ERegionOpen? e \/ EReadCell? e) (ensures False) =
  match ph with
  | PH_Foreign _ _ _ _ -> ()
  | _ -> ()

let read_no_step (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store)
  (#c: config) (r: region_ref) (k: key) (s: step eff_sig ex_genv ra st e ra' st' c)
  : Lemma (requires e == EReadCell r k) (ensures False) =
  match s with
  | S_Pure ph -> pure_not_cell ph
  | S_Eff eh -> eff_step_shape eh
  | S_Region rh -> region_step_shape rh
  | S_Ctx #_ #_ #_ #_ #x #_ #_ #_ f _ _ -> plug1_not_read f x r k
  | S_CtxFault #_ #_ #_ #_ #x #_ #_ #_ f _ _ -> plug1_not_read f x r k

let inner_only (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store)
  (#c: config) (s: step eff_sig ex_genv ra st e ra' st' c)
  : Lemma (requires e == inner) (ensures c == CTerm inner_reduct) =
  match s with
  | S_Pure ph -> pure_not_cell ph
  | S_Eff eh -> eff_step_shape eh
  | S_Region rh ->
    (match rh with
     | RH_Open _ _ -> ()
     | RH_Exit _ -> assert_norm (not (V.is_value eff_sig (read_n 0)))
     | RH_Read #_ #_ #_ #a #th #fs #k #v _ _ ->
       plug_read_inv fs (EReadCell (RFree a) k) (RFree 0) n_key;
       assert_norm (L.assoc n_key (cell_n (lit_int 2l)) == Some (lit_int 2l))
     | RH_Write #_ #_ #_ #a #th #fs #k #v _ _ ->
       plug_read_inv fs (EWriteCell (RFree a) k v) (RFree 0) n_key)
  | S_Ctx #_ #_ #_ #_ #x #_ #_ #_ f _ s' ->
    plug1_open_inv f x 0 (cell_n (lit_int 2l)) (read_n 0);
    read_no_step (RFree 0) n_key s'
  | S_CtxFault #_ #_ #_ #_ #x #_ #_ #_ f _ s' ->
    plug1_open_inv f x 0 (cell_n (lit_int 2l)) (read_n 0);
    read_no_step (RFree 0) n_key s'

let shadowed_only_inner #ra #st #ra' #st' #c s =
  match s with
  | S_Pure ph -> pure_not_cell ph
  | S_Eff eh -> eff_step_shape eh
  | S_Region rh ->
    (match rh with
     | RH_Open _ _ -> ()
     | RH_Exit _ -> assert_norm (not (V.is_value eff_sig inner))
     | RH_Read #_ #_ #_ #a #th #fs #k #v _ _ ->
       plug_open_not_ev_l fs (EReadCell (RFree a) k) 0 (cell_n (lit_int 2l)) (read_n 0)
     | RH_Write #_ #_ #_ #a #th #fs #k #v _ _ ->
       plug_open_not_ev_l fs (EWriteCell (RFree a) k v) 0 (cell_n (lit_int 2l)) (read_n 0))
  | S_Ctx #_ #_ #_ #_ #x #_ #_ #_ f _ s' ->
    plug1_open_inv f x 0 (cell_n (lit_int 1l)) inner;
    inner_only s'
  | S_CtxFault #_ #_ #_ #_ #x #_ #_ #_ f _ s' ->
    plug1_open_inv f x 0 (cell_n (lit_int 1l)) inner;
    inner_only s'

(* * A frame of another name on the way *)

let crossing_region_ev_l () = assert_norm (ev_l 0 [FRegionOpen 1 (cell_n (lit_int 2l))])

let crossing_region_step =
  int_values ();
  cell_facts (lit_int 2l);
  crossing_region_ev_l ();
  let fs = [FRegionOpen 1 (cell_n (lit_int 2l))] in
  assert_norm (frames_ok eff_sig fs);
  retype crossing_region
    (CTerm (ERegionOpen 0 (cell_n (lit_int 1l)) (ERegionOpen 1 (cell_n (lit_int 2l)) (lit_int 1l))))
    (S_Region #_ #_ #[] #[] (read_at fs (lit_int 1l)))

(* * Regions and continuations *)

(* `log : String ->* Unit` *)
let log_os : op_sig = { binders = []; arg = t_string; res = t_unit }

let twice_body : exp = EApp (EVar 0) (EApp (EVar 0) unit_v)

(* The rule `full` for `perform Console.log "hi"` in the hole of `fs`,
   answered by `h_twice`. *)
let log_twice (fs: list frame)
  : Pure (eff_head eff_sig ex_genv (EHandle (plug fs log_hi) h_twice)
            (CTerm (full_reduct [] hi t_unit TRowEmpty fs h_twice twice_body)))
         (requires frames_ok eff_sig fs /\ ev_k console_key fs)
         (ensures fun _ -> True) =
  assert_norm (V.is_value eff_sig hi);
  assert_norm (eff_sig.effects console_q == Some console_info /\
               op_of console_info "log" == Some log_os);
  assert_norm (as_function eff_sig (sub_ty (binders_tsub []) log_kt) ==
               Some (t_unit, TRowEmpty, t_unit));
  assert_norm (h_twice.h_ent == console_ent /\ handler_key h_twice == console_key);
  assert_norm (clause_of "log" h_twice.h_clauses == Some (CFull "log" 0 t_string log_kt twice_body));
  EH_Full #eff_sig #ex_genv #fs #console_key #"log" #[] #hi #h_twice #None #console_q #[]
    #console_info #log_os #0 #t_string #log_kt #twice_body #t_unit #TRowEmpty #t_unit () () () () ()

let region_frame : frame = FRegionOpen 0 (cell_n (lit_int 1l))

let handler_outside_step =
  int_values ();
  cell_facts (lit_int 1l);
  let fs = [then_read; region_frame] in
  assert_norm (frames_ok eff_sig fs /\ ev_k console_key fs);
  assert_norm (full_reduct [] hi t_unit TRowEmpty fs h_twice twice_body ==
               EApp cont_outside (EApp cont_outside unit_v));
  retype handler_outside (CTerm (EApp cont_outside (EApp cont_outside unit_v)))
    (S_Eff #_ #_ #[] #[] (log_twice fs))

let handler_inside_step =
  int_values ();
  cell_facts (lit_int 1l);
  let fs = [then_read] in
  assert_norm (frames_ok eff_sig fs /\ ev_k console_key fs);
  assert_norm (full_reduct [] hi t_unit TRowEmpty fs h_twice twice_body ==
               EApp cont_inside (EApp cont_inside unit_v));
  let s = retype (EHandle log_then_read h_twice)
            (CTerm (EApp cont_inside (EApp cont_inside unit_v)))
            (S_Eff #_ #_ #[] #[] (log_twice fs)) in
  retype handler_inside (CTerm (in_region (EApp cont_inside (EApp cont_inside unit_v))))
    (S_Ctx region_frame () s)

let continuation_frames () =
  assert_norm (not (no_open_region cont_outside) /\ no_open_region cont_inside)
