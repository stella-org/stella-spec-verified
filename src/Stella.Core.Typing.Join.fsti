(**
 * Join renaming and weakening of `Δ` (design §4.3; spec 04 §Join points).
 *
 * A join renaming `ξ` maps the join context `Δ` into `Δ'` when each join
 * point of `Δ` is found in `Δ'` at its image with the same signature
 * (`jren_ok`). Typing is preserved: `Γ; Δ ⊢ e : τ ! ρ` gives
 * `Γ; Δ' ⊢ ξ(e) : τ ! ρ`, and the same for every judgement that carries
 * `Δ`. Prepending join points to `Δ` under `ren_jp (shift m)`, `m` their
 * number, is the weakening (`typing_weaken_jp`, `typing_weaken_jps`):
 * the hole of a tail context `Tl` under `letjoin j` has the join points
 * of `Tl` in front of the `Δ` of the `letjoin`. Appending join points
 * behind `Δ` changes nothing in the term (`typing_jp_append`), since every
 * join index it uses is below `|Δ|`; in particular a term typed under
 * `Δ = []` is typed, unchanged, under every `Δ` (`typing_jp_nil`).
 *
 * A non-tail subterm is typed under `Δ = []`, which `ξ` maps into `[]`,
 * so it is renamed there. The bodies behind a boundary (`λ`, `handle`,
 * `region`, …) mention no free join index
 * (`Stella.Core.Typing.Scope.typing_jp_scoped`), so the renaming fixes them
 * and their derivations stand as they are; so does every run-time value
 * (`Stella.Core.Typing.Scope.typing_value_ren_jp`), which is how the values
 * of a `match` and a variant value retyped by `T_VariantValue` are kept.
 * Join-point scoping holds in every context, so none of the theorems needs
 * a well-formed `Γ`.
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

(** The shift past a prefix `d0` maps `Δ` into `d0 @ Δ`. *)
val jren_ok_shift_prefix (d0 d: jctx)
  : Lemma (jren_ok (shift (L.length d0)) d (L.append d0 d))

(** The value at an occurrence of run-time values is a value. *)
val proj_value (sg: sig) (th: list exp) (o: occ) (v: exp)
  : Lemma (requires L.for_all (V.is_value sg) th /\ proj sg th o == Some v)
          (ensures V.is_value sg v)

val typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (xi: ren) (d': jctx)
  : Pure (typing sg ln g d' (ren_jp xi e) t r)
         (requires jren_ok xi d d')
         (ensures fun _ -> True)

val exps_typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d r es ts) (xi: ren) (d': jctx)
  : Pure (exps_typing sg ln g d' r (ren_jp_exps xi es) ts)
         (requires jren_ok xi d d')
         (ensures fun _ -> True)

val chain_typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (xi: ren) (d': jctx)
  : Pure (chain_typing sg ln g d' r (ren_jp xi e))
         (requires jren_ok xi d d')
         (ensures fun _ -> True)

(** The values of a `match` are fixed by the renaming. *)
val match_typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om) (xi: ren) (d': jctx)
  : Pure (match_typing sg ln g d' r th om)
         (requires jren_ok xi d d' /\ L.for_all (V.is_value sg) th)
         (ensures fun _ -> True)

val dt_typing_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d om dt t r) (xi: ren) (d': jctx)
  : Pure (dt_typing sg ln g d' om (ren_jp_dt xi dt) t r)
         (requires jren_ok xi d d')
         (ensures fun _ -> True)

(** Weakening: one more join point in front of `Δ`. *)
val typing_weaken_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (jt: list typ & typ & typ)
  : typing sg ln g (jt :: d) (ren_jp (shift 1) e) t r

(** Weakening by a prefix: the join points `d0` in front of `Δ`, the
    term shifted past them. *)
val typing_weaken_jps (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (d0: jctx)
  : typing sg ln g (L.append d0 d) (ren_jp (shift (L.length d0)) e) t r

(** Join points appended behind `Δ`: the term is unchanged. It is
    `jp_scoped |Δ|` (`Stella.Core.Typing.Scope.typing_jp_scoped`), so the
    identity renaming, which maps `Δ` into `Δ @ Δ'`, fixes it. *)
val typing_jp_append (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (d': jctx)
  : typing sg ln g (L.append d d') e t r

(** Weakening from no join point: a term typed under `Δ = []` is typed, as
    it is, under any `Δ` (`typing_jp_append` at `[]`). *)
val typing_jp_nil (#sg: sig) (#ln: lctx) (#g: ctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g [] e t r) (d: jctx)
  : typing sg ln g d e t r
