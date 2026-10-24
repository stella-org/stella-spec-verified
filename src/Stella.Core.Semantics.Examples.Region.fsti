(**
 * Steps of the rules of regions and cells
 * (`Stella.Core.Semantics.Step.region_head`; spec 06 §Regions, §Cells,
 * §Evaluation contexts).
 *
 * The signature is `Stella.Core.Semantics.Examples.Eff.eff_sig` and the
 * environment `ex_genv`, which no rule here reads. The regions have one
 * cell `n : Int`.
 *
 *   - Opening: with `R = [0]`, `region [ℓ] ( n : Int ) @ ( 0 ) in readCell ℓ.n`
 *     allocates `1`, a name in neither `R` nor the term, and steps to
 *     `region⟨1⟩ ( n ↦ 0 ) in readCell 1.n` with `R' = [1; 0]`.
 *   - Exit: `region⟨0⟩ ( n ↦ 0 ) in 1  →  1`.
 *   - Read and write at the root of the frame:
 *     `region⟨0⟩ ( n ↦ 0 ) in readCell 0.n  →  region⟨0⟩ ( n ↦ 0 ) in 0` and
 *     `region⟨0⟩ ( n ↦ 0 ) in writeCell 0.n 5  →
 *     region⟨0⟩ ( n ↦ 5 ) in Prim.Unit`.
 *   - Read and write under a `let`, `Ev_ℓ = let x : τ = [] in e`: the hole
 *     is replaced, the `let` kept.
 *   - The innermost frame of a name: in
 *     `region⟨0⟩ ( n ↦ 1 ) in region⟨0⟩ ( n ↦ 2 ) in readCell 0.n` the
 *     read is a step under the outer frame, reading `2` from the inner
 *     one. It is the term's only step: the context from the outer frame to
 *     the `readCell` holds a frame named `0`, so it is no `Ev_ℓ`.
 *   - A frame of another name on the way: in
 *     `region⟨0⟩ ( n ↦ 1 ) in region⟨1⟩ ( n ↦ 2 ) in readCell 0.n` the read
 *     reaches the outer frame through `Ev_ℓ = region⟨1⟩ ( n ↦ 2 ) in []`,
 *     and reads `1`.
 *   - The two rows of the table of spec 06 §Cells, at the step of a
 *     `full` clause resuming twice, `h_twice`, on the body
 *     `let w : Unit = perform Console.log "hi" in readCell 0.n`:
 *       - the handler outside the region,
 *         `handle (region⟨0⟩ ( n ↦ 1 ) in body) with h_twice`: the region
 *         frame is in `Ev_k`, so the continuation
 *         `λ (y : Unit) / (). handle (region⟨0⟩ ( n ↦ 1 ) in let w = y in …) with h_twice`
 *         holds a copy of it, and each of its two applications runs under
 *         a copy of its own, its cells as they stood at the capture;
 *       - the handler inside the region,
 *         `region⟨0⟩ ( n ↦ 1 ) in handle body with h_twice`: the step is
 *         under the region frame, and the continuation
 *         `λ (y : Unit) / (). handle (let w = y in …) with h_twice` holds
 *         no region frame, so both applications run under the one frame.
 *)
module Stella.Core.Semantics.Examples.Region
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Prim
open Stella.Core.Sig.Examples
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Semantics.Examples
open Stella.Core.Semantics.Examples.Eff
module L = FStar.List.Tot

(** * Cells *)

(** The key `n` *)
let n_key : key = SymbolKey "n"

(** `( n ↦ v )` *)
let cell_n (v: exp) : list (key & exp) = [(n_key, v)]

(** `readCell a.n` *)
let read_n (a: atom) : exp = EReadCell (RFree a) n_key

(** * Opening *)

(** `region [ℓ] ( n : Int ) @ ( 0 ) in readCell ℓ.n` *)
let fresh_region : exp = ERegion [(n_key, t_int)] [lit_int 0l] (EReadCell (RBound 0) n_key)

val open_step :
  step eff_sig ex_genv [0] [] fresh_region [1; 0] []
    (CTerm (ERegionOpen 1 (cell_n (lit_int 0l)) (read_n 1)))

(** * Exit *)

val exit_step :
  step eff_sig ex_genv [] [] (ERegionOpen 0 (cell_n (lit_int 0l)) (lit_int 1l)) [] []
    (CTerm (lit_int 1l))

(** * Read and write at the root of the frame *)

val read_step :
  step eff_sig ex_genv [] [] (ERegionOpen 0 (cell_n (lit_int 0l)) (read_n 0)) [] []
    (CTerm (ERegionOpen 0 (cell_n (lit_int 0l)) (lit_int 0l)))

(** `writeCell 0.n 5` *)
let write_n5 : exp = EWriteCell (RFree 0) n_key (lit_int 5l)

val write_step :
  step eff_sig ex_genv [] [] (ERegionOpen 0 (cell_n (lit_int 0l)) write_n5) [] []
    (CTerm (ERegionOpen 0 (cell_n (lit_int 5l)) unit_v))

(** * Read and write under a `let` *)

(** `let x : Int = readCell 0.n in x` *)
let read_let : exp = ELet t_int (read_n 0) (EVar 0)

val read_let_step :
  step eff_sig ex_genv [] [] (ERegionOpen 0 (cell_n (lit_int 0l)) read_let) [] []
    (CTerm (ERegionOpen 0 (cell_n (lit_int 0l)) (ELet t_int (lit_int 0l) (EVar 0))))

(** `let u : Unit = writeCell 0.n 5 in readCell 0.n` *)
let write_let : exp = ELet t_unit write_n5 (read_n 0)

val write_let_step :
  step eff_sig ex_genv [] [] (ERegionOpen 0 (cell_n (lit_int 0l)) write_let) [] []
    (CTerm (ERegionOpen 0 (cell_n (lit_int 5l)) (ELet t_unit unit_v (read_n 0))))

(** * The innermost frame of a name *)

(** `region⟨0⟩ ( n ↦ 1 ) in region⟨0⟩ ( n ↦ 2 ) in readCell 0.n` *)
let shadowed : exp =
  ERegionOpen 0 (cell_n (lit_int 1l)) (ERegionOpen 0 (cell_n (lit_int 2l)) (read_n 0))

(** `region⟨0⟩ ( n ↦ 1 ) in region⟨0⟩ ( n ↦ 2 ) in 2` *)
let shadowed_reduct : exp =
  ERegionOpen 0 (cell_n (lit_int 1l)) (ERegionOpen 0 (cell_n (lit_int 2l)) (lit_int 2l))

val shadowed_step : step eff_sig ex_genv [] [] shadowed [] [] (CTerm shadowed_reduct)

(** The context from the outer frame to the `readCell` is no `Ev_ℓ`. *)
val shadowed_outer_excluded : unit
  -> Lemma (~(ev_l 0 [FRegionOpen 0 (cell_n (lit_int 2l))]))

(** Every step of `shadowed` reads the inner frame. *)
val shadowed_only_inner (#ra: list atom) (#st: store) (#ra': list atom) (#st': store)
  (#c: config) (s: step eff_sig ex_genv ra st shadowed ra' st' c)
  : Lemma (c == CTerm shadowed_reduct)

(** * A frame of another name on the way *)

(** `region⟨0⟩ ( n ↦ 1 ) in region⟨1⟩ ( n ↦ 2 ) in readCell 0.n` *)
let crossing_region : exp =
  ERegionOpen 0 (cell_n (lit_int 1l)) (ERegionOpen 1 (cell_n (lit_int 2l)) (read_n 0))

val crossing_region_ev_l : unit -> Lemma (ev_l 0 [FRegionOpen 1 (cell_n (lit_int 2l))])

val crossing_region_step :
  step eff_sig ex_genv [] [] crossing_region [] []
    (CTerm (ERegionOpen 0 (cell_n (lit_int 1l)) (ERegionOpen 1 (cell_n (lit_int 2l)) (lit_int 1l))))

(** * Regions and continuations (spec 06 §Cells) *)

(** `let w : Unit = [] in readCell 0.n` *)
let then_read : frame = FLet t_unit (read_n 0)

(** `let w : Unit = perform Console.log "hi" in readCell 0.n` *)
let log_then_read : exp = plug1 then_read log_hi

(** `region⟨0⟩ ( n ↦ 1 ) in e` *)
let in_region (e: exp) : exp = ERegionOpen 0 (cell_n (lit_int 1l)) e

(** ** The handler outside the region *)

let handler_outside : exp = EHandle (in_region log_then_read) h_twice

(** `λ (y : Unit) / (). handle (region⟨0⟩ ( n ↦ 1 ) in let w : Unit = y in readCell 0.n) with h_twice` *)
let cont_outside : exp =
  ELam t_unit TRowEmpty (EHandle (in_region (ELet t_unit (EVar 0) (read_n 0))) h_twice)

val handler_outside_step :
  step eff_sig ex_genv [] [] handler_outside [] []
    (CTerm (EApp cont_outside (EApp cont_outside unit_v)))

(** ** The handler inside the region *)

let handler_inside : exp = in_region (EHandle log_then_read h_twice)

(** `λ (y : Unit) / (). handle (let w : Unit = y in readCell 0.n) with h_twice` *)
let cont_inside : exp =
  ELam t_unit TRowEmpty (EHandle (ELet t_unit (EVar 0) (read_n 0)) h_twice)

val handler_inside_step :
  step eff_sig ex_genv [] [] handler_inside [] []
    (CTerm (in_region (EApp cont_inside (EApp cont_inside unit_v))))

(** `e` holds no open region frame. *)
let no_open_region (e: exp) : bool = exp_all (fun x -> not (ERegionOpen? x)) e

(** The continuation captured outside the region holds a copy of its frame,
    and the one captured inside holds none. *)
val continuation_frames : unit
  -> Lemma (not (no_open_region cont_outside) /\ no_open_region cont_inside)
