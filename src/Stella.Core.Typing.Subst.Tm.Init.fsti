(**
 * Initialization safety under a term substitution (spec 10; design §5).
 *
 * A term substitution under a `letrec` is lifted past the group's members,
 * `upn_esub |bs| σ`: it fixes every member and puts a substitute, shifted
 * past the members, where a variable bound outside the group stood. The
 * judgement of `Stella.Core.Init` reads such a variable as a local at
 * `ρ = ∅`. A substitute reads nothing of the group either, now or later,
 * when it has no free join index (`jps_below_exp 0`):
 *
 *   - it mentions no member, since every term variable it mentions is
 *     bound outside the group, at `ρ = ∅`;
 *   - every `jump` in it targets a `letjoin` within it, so it reads no join
 *     point of a right-hand side;
 *   - a local group has no global member.
 *
 * So the substituted group reads, before a right-hand side has a value,
 * only members the group reads there: a safe group stays safe. The
 * substitutes need not be values. A typed value under no join point has no
 * free join index (`Stella.Core.Typing.Scope`).
 *)
module Stella.Core.Typing.Subst.Tm.Init
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Scope
open Stella.Core.Init
module L = FStar.List.Tot

val init_safe_sub_tm (sg: sig) (sigma: esub) (bs: list (typ & exp))
  : Lemma (requires init_safe_letrec sg bs /\ (forall (i: nat). jps_below_exp 0 (sigma i)))
          (ensures init_safe_letrec sg (sub_tm_binds (upn_esub (L.length bs) sigma) bs))
