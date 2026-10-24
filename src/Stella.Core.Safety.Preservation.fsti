(**
 * Preservation (spec 06 §Properties; design §7).
 *
 * A closed run-time term `e` is typed in `closed_ctx rs`, the context of
 * the regions `rs = Γ_R` alone, under the store typing `ln = Γ_N`. When
 * `G ⊢ N; e → N'; e'` steps to a term, `e'` has the derivation's type, row
 * and `Δ` under a `Γ_R2` that extends `Γ_R`:
 *
 *     Γ_R; Γ_N; Δ ⊢ e : τ ! ρ   and   e → e'   give   Γ_R2; Γ_N; Δ ⊢ e' : τ ! ρ
 *
 * at the root or under any evaluation frame. Every region of `Γ_R` keeps
 * its layout in `Γ_R2` (`layouts_ext`), `Γ_R2` is well formed, `Γ_N` is
 * well formed under it, and `G` conforms at it (`rctx_after`). Opening a
 * region is the one rule that changes `Γ_R`: it adds the region with the
 * name it allocates and the layout the `region` writes.
 *
 * The hypotheses are the part of the premises of spec 06 §Properties
 * that does not concern the store: a well-formed `Σ` (`sig_ok`),
 * well-formed run-time contexts (`rctx_ok`, `lctx_ok`), and a global
 * environment that conforms at them (`genv_ok`), together with one fact
 * relating the names `R` allocated so far to `Γ_R`: every name of `Γ_R` is
 * in `R` (`rdom_in`). An opening allocates a name not in `R`, so not in
 * `Γ_R`, and the step keeps the fact, at the new `R`. The rest of the
 * spec's premises are left out, so the statement is stronger than the
 * spec's:
 *
 *   - the store typing `⊢ N : Γ_N`. None of these rules reads or writes
 *     the store or allocates a location, so none needs it, and `Γ_N` is the
 *     same on both sides of a step;
 *   - that the term respects the preconditions of the foreigns it calls
 *     (`Stella.Core.Semantics.Step.pre_ok`). The rule for a saturated
 *     foreign chain has the precondition of its call as a premise of its
 *     own, so a step that calls a foreign already has it.
 *
 * `Δ`, `τ` and `ρ` are arbitrary. A step under an evaluation frame is a
 * step of the frame's hole, which stands at a `Δ` and a row of its own
 * (`Stella.Core.Typing.Plug.plug1_typing`): under `letjoin` the hole has a
 * join point in front of `Δ`, under `openEffC` its row is the operand
 * row, under `handle` the row with the handled element, under an open
 * region the row with the region, and under `fill` the row `()`. At the
 * root of a program `Δ = []` and `ρ = ()` (`preservation_typed`).
 *
 * A rule of operations and handlers rewrites
 * `handle Ev_k[perform k.op [σ̄] v] with h` to the body of the clause for
 * `op` with `b̄ := σ̄` and `x := v`: a `full` clause's body with the
 * continuation for `k`, a `fast` clause's body bound by a `let` around
 * the handler reinstalled. The `perform` reads in its row an element of
 * key `k`, which through `Ev_k` is an element of the row of the handled
 * computation; that row is sharp, so the element is the handler's own,
 * and the `perform` is typed at the instance the clause is typed at
 * (`Stella.Core.Typing.Eff`). The continuation and the `let` rebuild the
 * `handle` around `Ev_k[y]`, typed as the redex was with `y` at the type
 * of the `perform`.
 *
 * A rule of regions and cells rewrites a `region` or an open region frame
 * `region⟨a⟩ θ in e` (`Stella.Core.Typing.Region`). The opening types the
 * body by the premise of `T_Region` at the name `a` it allocates, which is
 * in neither `Γ_R` nor the body. It types the initial values, which are
 * values and so have their types at `()`, as the cells against the
 * layout. `Γ_R2` is `(a, layout) :: Γ_R`, well formed since the layout is
 * kinded as a row with distinct keys. A value leaving its frame has its type at the outer
 * row, as a value has at every row. A read or a write stands in the hole
 * of an `Ev_ℓ` in the frame's body, and refers to the layout `Γ_R` gives
 * `a`, which is the frame's own: every frame named `a` is typed against
 * the one layout of `a`. The cell read has the type of its key, and the
 * value written that type at `()`, so the new cells are typed as the old
 * ones. The hole, filled with the cell or with `Prim.Unit`, keeps its
 * type.
 *
 * The reduct of each head rule is typed from the derivation of its redex
 * alone, except for two rules that read `G`. The unfolding of a top-level
 * value `M.x [[κ̄]]` takes the definition's derivation from condition (2)
 * of conformance, and a saturated foreign chain the derivation of the
 * adapter's value from condition (3). Conformance asserts that such a
 * derivation exists, so the derivation of the reduct is computed in the
 * `Ghost` effect: it is a proof object, and nothing runs it.
 *)
module Stella.Core.Safety.Preservation
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Runtime
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Step
module L = FStar.List.Tot

(** * The run-time contexts *)

(** Every region name of `Γ_R = rs` is among the names `R = ra` allocated
    so far. *)
let rdom_in (rs: list (atom & layout)) (ra: list atom) : prop =
  forall (a: atom). {:pattern L.mem a (L.map fst rs)} L.mem a (L.map fst rs) ==> L.mem a ra

(** With no name allocated, `Γ_R` is empty. *)
val rdom_in_nil (rs: list (atom & layout)) : Lemma (requires rdom_in rs []) (ensures rs == [])

(** `Γ_R2 = rs'` after a step from `Γ_R = rs` to the names `R' = ra'`:
    every region of `rs` with its layout is one of `rs'` (spec 06
    §Properties, `Γ_R2` extending `Γ_R`), `⊢ Γ_R2 ok`, `Γ_R2 ⊢ Γ_N ok`,
    `Σ; Γ_N ⊨ G` at `Γ_R2`, and every name of `rs'` is in `ra'`. *)
let rctx_after (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout)) (ra': list atom)
  (rs': list (atom & layout)) : prop =
  layouts_ext (closed_ctx rs) (closed_ctx rs') /\ rctx_ok sg rs' /\ lctx_ok sg rs' ln /\
  genv_ok sg ln rs' gi /\ rdom_in rs' ra'

(** The conclusion of preservation: a `Γ_R2 = rs'` after the step, and a
    derivation of the reduct `e'` under it at the `Δ`, the type and the
    row of the redex. *)
noeq type preserved (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout)) (ra': list atom)
  (d: jctx) (e': exp) (t r: typ) = {
  rs': list (atom & layout);
  ok: squash (rctx_after sg gi ln rs ra' rs');
  der: typing sg ln (closed_ctx rs') d e' t r;
}

(** * The theorems *)

(** A step to a term keeps the type, the row and the `Δ` of a derivation
    of a closed run-time term, under `Γ_R2` (spec 06 §Properties). *)
val preservation (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (#d: jctx) (#t #r: typ)
  (h: typing sg ln (closed_ctx rs) d e t r)
  (s: step sg gi ra st e ra' st' (CTerm e'))
  : Ghost (preserved sg gi ln rs ra' d e' t r)
          (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    rdom_in rs ra)
          (ensures fun _ -> True)

(** At the root of a program: a closed term typed at `τ`, under no join
    point and at the row `()`, steps to a term of the same type under
    `Γ_R2`. `Γ_N = ln` and `Γ_R = rs` occur in the hypotheses alone, so
    they are explicit. *)
val preservation_typed (#sg: sig) (#gi: genv) (ln: lctx) (rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (t: typ) (s: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    rdom_in rs ra /\ typed sg ln (closed_ctx rs) e t)
          (ensures exists (rs': list (atom & layout)).
                     rctx_after sg gi ln rs ra' rs' /\ typed sg ln (closed_ctx rs') e' t)
