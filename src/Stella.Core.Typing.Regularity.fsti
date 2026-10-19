(**
 * Regularity: the type and the row of every derivation are well kinded
 * (spec 05; design §4.2, §4.4).
 *
 * In a well-formed context of a well-formed `Σ`, `sig_ok sg` and
 * `wf_ctx sg g`:
 *
 *   - `Γ; Δ ⊢ e : τ ! ρ` gives `Γ ⊢ τ : Type` and `Γ ⊢ ρ : Row Effect`;
 *   - `Γ; Δ; Ω ⊢ dt : τ ! ρ` gives the same, when every type of `Ω` has
 *     kind `Type` (`octx_ok`);
 *   - the list judgements kind their types and rows, `match_typing` its
 *     `Ω`, and each branch and clause judgement the type and the row it is
 *     indexed by;
 *   - the arguments of a typed chain are well formed against its cursor
 *     (`Stella.Core.Spine.Wf.spine_args_ok`), so the instance `θ(σ)` of
 *     its cursor is kinded, at the chain and at each prefix.
 *
 * `Δ` and `Γ_N` need no condition, since `jump` kinds the types it reads
 * and `force` kinds them in the closed context, which every context
 * weakens (`Stella.Core.Typing.Aux.Lemmas.check_closed_ctx`). Most rules
 * carry the kinding of what they conclude as a premise; the others read it
 * from their subderivations through the facts of
 * `Stella.Core.Kinding.Facts`, `Stella.Core.Spine.Wf` and
 * `Stella.Core.Typing.Wf`.
 *)
module Stella.Core.Typing.Regularity
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Subst
open Stella.Core.Spine
open Stella.Core.Spine.Wf
open Stella.Core.Kinding
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Wf
module L = FStar.List.Tot

(** The arguments of a chain `e` are well formed against its cursor. *)
let chain_args_ok (sg: sig) (g: ctx) (e: exp) : bool =
  match decompose_global_app e with
  | Some (q, ks, args) -> spine_args_ok sg g q ks args
  | None -> false

val typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d tl e t r)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g)
          (ensures check sg g t KType /\ check sg g r (KRow EEffect))

val chain_typing_args_ok (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e)
  : Lemma (chain_args_ok sg g e /\ check sg g r (KRow EEffect))

(** The instance of the cursor of a typed chain is kinded, at every node:
    each prefix of the chain is typed by a subderivation. *)
val chain_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e)
  : Lemma (requires sig_ok sg)
          (ensures check sg g r (KRow EEffect) /\
                   (match chain_cursor sg e with
                    | Some (t, th) -> check sg g (sub_ty th t) KType
                    | None -> False))

val exps_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d tl r es ts)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g)
          (ensures tys_ok sg g ts /\ check sg g r (KRow EEffect))

val binds_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs)
  : Lemma (tys_ok sg g (L.map fst bs))

(** The cells kind the types of their layout. They say nothing of its keys,
    which `wf_ctx` makes structural for a layout of `Γ`. *)
val cells_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g) (ensures tys_ok sg g (L.map snd lay))

val match_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g)
          (ensures octx_ok sg g om /\ check sg g r (KRow EEffect))

val dt_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d tl om dt t r)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g /\ octx_ok sg g om)
          (ensures check sg g t KType /\ check sg g r (KRow EEffect))

val ctor_brs_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ)
  (h: ctor_brs_typing sg ln g d tl om o ks ss cs bs t r)
  : Lemma (check sg g t KType /\ check sg g r (KRow EEffect))

val lit_brs_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d tl om lt bs t r)
  : Lemma (check sg g t KType /\ check sg g r (KRow EEffect))

val key_brs_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d tl om o kts bs t r)
  : Lemma (check sg g t KType /\ check sg g r (KRow EEffect))

val clauses_typing_regular (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause)
  (h: clauses_typing sg ln g ei ts r b cs)
  : Lemma (check sg g b KType /\ check sg g r (KRow EEffect))

(** The `Ω` of a `case`, `{ s_i ↦ τ_i }`, is well formed. *)
val case_octx_ok (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d tl r es ts)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g) (ensures octx_ok sg g (scrut_occs 0 ts))
