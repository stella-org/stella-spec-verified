(**
 * Initialization safety is invariant under the renamings and type
 * substitutions of a group (spec 10; design §5): a safe `letrec` group
 * stays safe under a type substitution (`init_safe_sub_ty`), a type
 * renaming (`init_safe_ren_ty`) and a term renaming (`init_safe_ren_tm`).
 *
 * The judgement of `Stella.Core.Init` reads no type, and a term renaming
 * fixes the members of the group and moves no other variable onto one; so
 * each map leaves unchanged which members every member reads.
 *)
module Stella.Core.Init.Rename
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Init
module L = FStar.List.Tot

val init_safe_sub_ty (sg: sig) (sigma: tsub) (bs: list (typ & exp))
  : Lemma (requires init_safe_letrec sg bs) (ensures init_safe_letrec sg (sub_ty_binds sigma bs))

val init_safe_ren_ty (sg: sig) (xi: ren) (bs: list (typ & exp))
  : Lemma (requires init_safe_letrec sg bs) (ensures init_safe_letrec sg (ren_ty_binds xi bs))

(** The members of `letrec bs` are its innermost `|bs|` term variables;
    `ren_tm` renames the group under `upn_ren |bs| ξ`. *)
val init_safe_ren_tm (sg: sig) (xi: ren) (bs: list (typ & exp))
  : Lemma (requires init_safe_letrec sg bs)
          (ensures init_safe_letrec sg (ren_tm_binds (upn_ren (L.length bs) xi) bs))
