(**
 * Initialization safety is invariant under kind instantiation (spec 10;
 * design §5).
 *
 * The judgement of `Stella.Core.Init` reads no kind: it reads the shape of
 * a term, its term variables and join indices, and the declared scheme of
 * a chain's head (`Stella.Core.Spine.global_scheme`), which a kind
 * instantiation does not change. So a safe `letrec` group stays safe with
 * its kinds instantiated, as it does under a type substitution
 * (`Stella.Core.Init.Rename.init_safe_sub_ty`).
 *)
module Stella.Core.Typing.Kinst.Init
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Init
module L = FStar.List.Tot

val init_safe_kinst (sg: sig) (ks: list kind) (bs: list (typ & exp))
  : Lemma (requires init_safe_letrec sg bs) (ensures init_safe_letrec sg (kinst_binds ks bs))
