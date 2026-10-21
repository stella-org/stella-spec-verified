(**
 * Cut for the typing judgement (design §2.2 lemma 5): `Γ ⊨ C` and
 * `Γ, C ⊢ J` imply `Γ ⊢ J`.
 *
 * Assumptions that the hypotheses of `Γ` entail can be dropped. `Γ` and
 * `add_assumps Γ C̄` differ in their assumptions only, so `Γ` is reached
 * from `add_assumps Γ C̄` by the identity term renaming
 * (`Stella.Core.Typing.Weaken.typing_weaken_ext`): each hypothesis of
 * `add_assumps Γ C̄` is a member of `C̄`, entailed by assumption, or a
 * hypothesis of `Γ`, entailed by membership; the type variables, the
 * regions with their layouts, and the term variables are the same. The
 * identity term renaming fixes the term, and a term renaming changes no
 * type, so the conclusion has the same term, type, row, `Δ` and `Ω`.
 *
 * Cut is thus the hypothesis condition of a context morphism read as
 * entailment rather than membership (design §2.3). It needs no
 * well-formedness of `Σ` or of the context.
 *)
module Stella.Core.Typing.Cut
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Entail
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Weaken
module L = FStar.List.Tot

(** * The context morphism *)

(** `g` extends `add_assumps g cs` in place when `g` entails every member
    of `cs`. *)
val ctx_weaker_cut (g: ctx) (cs: list constr)
  : Lemma (requires forall (c: constr). L.mem c cs ==> entails (hyps g) c)
          (ensures ctx_weaker (add_assumps g cs) g)

(** * Terms *)

val typing_cut (#sg: sig) (#ln: lctx) (#g: ctx) (#c: constr) (#d: jctx) (#e: exp)
  (#t #r: typ)
  (h: typing sg ln (add_assump g c) d e t r)
  : Pure (typing sg ln g d e t r) (requires entails (hyps g) c) (ensures fun _ -> True)

val typing_cut_all (#sg: sig) (#ln: lctx) (#g: ctx) (#cs: list constr) (#d: jctx) (#e: exp)
  (#t #r: typ)
  (h: typing sg ln (add_assumps g cs) d e t r)
  : Pure (typing sg ln g d e t r)
         (requires forall (c: constr). L.mem c cs ==> entails (hyps g) c)
         (ensures fun _ -> True)

(** * Decision trees *)

val dt_typing_cut (#sg: sig) (#ln: lctx) (#g: ctx) (#c: constr) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln (add_assump g c) d om dt t r)
  : Pure (dt_typing sg ln g d om dt t r) (requires entails (hyps g) c) (ensures fun _ -> True)

val dt_typing_cut_all (#sg: sig) (#ln: lctx) (#g: ctx) (#cs: list constr) (#d: jctx)
  (#om: octx) (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln (add_assumps g cs) d om dt t r)
  : Pure (dt_typing sg ln g d om dt t r)
         (requires forall (c: constr). L.mem c cs ==> entails (hyps g) c)
         (ensures fun _ -> True)
