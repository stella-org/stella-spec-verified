(**
 * Join renaming and weakening of `Δ` (design §4.3; spec 04 §Join points).
 *
 * A join renaming `ξ` maps the join context `Δ` into `Δ'` when each join
 * point of `Δ` is found in `Δ'` at its image with the same signature
 * (`jren_ok`). Typing is preserved: `Γ; Δ ⊢ e : τ ! ρ` gives
 * `Γ; Δ' ⊢ ξ(e) : τ ! ρ`, with the same tail flag, and the same for every
 * judgement that carries `Δ`. Prepending a join point to `Δ` under
 * `ren_jp (shift 1)` is the weakening (`typing_weaken_jp`).
 *
 * The bodies that discard `Δ` mention no free join index
 * (`Stella.Core.Typing.Scope`), so the renaming fixes them and their
 * derivations stand as they are; so does every run-time value, which is how
 * the values of a `match` and a variant value retyped by `T_VariantValue`
 * are kept. The scope facts need a well-formed context (`wf_ctx`), whose
 * layouts have structural keys (`Stella.Core.Typing.Scope`).
 *)
module Stella.Core.Typing.Join
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Scope
module L = FStar.List.Tot
module V = Stella.Core.Value

(** `ξ` maps every join point of `Δ` to one of `Δ'` with the same parameter
    types, result type and row. *)
let jren_ok (xi: ren) (d d': jctx) : prop =
  forall (j: nat). j < L.length d ==> L.nth d' (xi j) == L.nth d j

(** Under a `letjoin`, the renaming is lifted past the new join point. *)
val jren_ok_up (xi: ren) (d d': jctx) (jt: list typ & typ & typ)
  : Lemma (requires jren_ok xi d d') (ensures jren_ok (up_ren xi) (jt :: d) (jt :: d'))

val jren_ok_shift (d: jctx) (jt: list typ & typ & typ)
  : Lemma (jren_ok (shift 1) d (jt :: d))

(** The value at an occurrence of run-time values is a value. *)
val proj_value (sg: sig) (th: list exp) (o: occ) (v: exp)
  : Lemma (requires L.for_all (V.is_value sg) th /\ proj sg th o == Some v)
          (ensures V.is_value sg v)

val typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d tl e t r) (xi: ren) (d': jctx)
  : Pure (typing sg ln g d' tl (ren_jp xi e) t r)
         (requires wf_ctx sg g /\ jren_ok xi d d')
         (ensures fun _ -> True)

val exps_typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d tl r es ts) (xi: ren) (d': jctx)
  : Pure (exps_typing sg ln g d' tl r (ren_jp_exps xi es) ts)
         (requires wf_ctx sg g /\ jren_ok xi d d')
         (ensures fun _ -> True)

val chain_typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (xi: ren) (d': jctx)
  : Pure (chain_typing sg ln g d' r (ren_jp xi e))
         (requires wf_ctx sg g /\ jren_ok xi d d')
         (ensures fun _ -> True)

(** The values of a `match` are fixed by the renaming. *)
val match_typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om) (xi: ren) (d': jctx)
  : Pure (match_typing sg ln g d' r th om)
         (requires wf_ctx sg g /\ jren_ok xi d d' /\ L.for_all (V.is_value sg) th)
         (ensures fun _ -> True)

val dt_typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d tl om dt t r) (xi: ren) (d': jctx)
  : Pure (dt_typing sg ln g d' tl om (ren_jp_dt xi dt) t r)
         (requires wf_ctx sg g /\ jren_ok xi d d')
         (ensures fun _ -> True)

(** Weakening: one more join point in front of `Δ`. *)
val typing_weaken_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d tl e t r) (jt: list typ & typ & typ)
  : Pure (typing sg ln g (jt :: d) tl (ren_jp (shift 1) e) t r)
         (requires wf_ctx sg g)
         (ensures fun _ -> True)
