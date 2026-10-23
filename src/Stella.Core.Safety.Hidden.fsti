(**
 * The premises of the safety proofs, hidden from SMT (design §7).
 *
 * `sig_ok` and conformance (`genv_ok`) are conjunctions of quantified
 * facts. The proofs of `Stella.Core.Safety.Preservation`,
 * `Stella.Core.Safety.Progress` and `Stella.Core.Safety.Covers` analyse
 * one case per rule, and each case is a query of its own. With those
 * facts in its context, every such query instantiates their quantifiers
 * anew, though a case uses them only through a few lemmas. So the proofs
 * carry the premises behind names that SMT does not unfold:
 *
 *   - `sok sg` is `sig_ok sg`;
 *   - `env_ok sg G Γ_N rs` is `sig_ok`, `rctx_ok`, `lctx_ok` and
 *     `genv_ok` at `Γ_R = rs` and `Γ_N`, together.
 *
 * Both are definitions marked `opaque_to_smt`: each equals what it names,
 * and its `_intro` and `_elim` lemmas convert between the two. A lemma
 * that asks `sig_ok` is called through a wrapper (`*_h`) that asks `sok`
 * instead and reveals it in a query of its own, which holds nothing else.
 *
 * The safety theorems state the premises themselves and introduce `sok`
 * or `env_ok` at the start of their proofs.
 *)
module Stella.Core.Safety.Hidden
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Plug
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * `sig_ok` *)

[@@"opaque_to_smt"]
let sok (sg: sig) : prop = sig_ok sg

val sok_intro (sg: sig) : Lemma (requires sig_ok sg) (ensures sok sg)

val sok_elim (sg: sig) : Lemma (requires sok sg) (ensures sig_ok sg)

(** * The premises on `Σ`, `Γ_R`, `Γ_N` and `G` *)

[@@"opaque_to_smt"]
let env_ok (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout)) : prop =
  sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi

val env_ok_intro (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout))
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi)
          (ensures env_ok sg gi ln rs)

(** The premises, and what they give of the context `closed_ctx rs` of a
    closed run-time term: it is well formed
    (`Stella.Core.Typing.Runtime.rctx_ok_wf_ctx`) and consistent. *)
val env_ok_elim (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout))
  : Lemma (requires env_ok sg gi ln rs)
          (ensures sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                   wf_ctx sg (closed_ctx rs) /\ not (inconsistent (hyps (closed_ctx rs))))

(** What the wrappers ask, with `sig_ok` still hidden. *)
val env_ok_sok (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout))
  : Lemma (requires env_ok sg gi ln rs)
          (ensures sok sg /\ wf_ctx sg (closed_ctx rs) /\ not (inconsistent (hyps (closed_ctx rs))))

(** * Rewriting the term of a derivation *)

(** A derivation of `e` read as one of a term equal to `e`. *)
val retm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (e2: exp)
  : Pure (typing sg ln g d e2 t r) (requires e == e2) (ensures fun _ -> True)

(** * Wrappers

    Each is the lemma it is named after, with `sok` in place of
    `sig_ok`. *)

(** `Stella.Core.Typing.Plug.plug1_typing`, at a hole that is no value. *)
val plug1_typing_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#f: frame) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d (plug1 f e) t r)
  : Pure (plug1_inv sg ln g d f e t r)
         (requires sok sg /\ wf_ctx sg g /\ not (V.is_value sg e))
         (ensures fun _ -> True)

(** `Stella.Core.Typing.Plug.tl_typing` *)
val tl_typing_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#fs: list frame) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d (plug fs e) t r)
  : Pure (tl_inv sg ln g d fs e t r)
         (requires sok sg /\ wf_ctx sg g /\ tl_frames fs)
         (ensures fun _ -> True)

(** `Stella.Core.Typing.Plug.foreign_redex_typed` *)
val foreign_redex_typed_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (s: typ) (th: tsub)
  : Lemma (requires sok sg /\ wf_ctx sg g /\ V.foreign_redex sg e /\
                    chain_cursor sg e == Some (s, th))
          (ensures typed sg ln g e (sub_ty th s) /\ ty_eq t (sub_ty th s))

(** `Stella.Core.Typing.Occ.occ_sound` *)
val occ_sound_h (#sg: sig) (#ln: lctx) (#g: ctx) (#r: typ) (#th: list exp) (#om: octx)
  (#o: occ) (#t_o: typ)
  (hm: match_typing sg ln g [] r th om) (ho: occ_typing sg g om o t_o)
  : Pure (v: exp & typing sg ln g [] v t_o r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   L.for_all (V.is_value sg) th)
         (ensures fun (| v, _ |) -> proj sg th o == Some v /\ V.is_value sg v)
