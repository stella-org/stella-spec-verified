(**
 * Instantiating a telescope of type binders (spec 05 §Effects, spec 06
 * §Operations and handlers; design §3.1).
 *
 * A clause of a handler binds the type binders `b̄ : κ̄` of its operation,
 * pushed in written order (`push_tvars g κ̄`), so the last binder is type
 * index 0. A `perform` of the operation writes one type `σ_j : κ_j` per
 * binder, each kinded in the outer context `g` (`check_tys sg g σ̄ κ̄`).
 * Instantiating the binders at `σ̄` is the substitution
 * `list_tsub (rev σ̄)` (`Stella.Core.Semantics.Step.binders_tsub`), which
 * sends index `i < |σ̄|` to `σ_{|σ̄|-1-i}` and lowers the outer indices by
 * `|σ̄|`. It goes from `push_tvars g κ̄` to `g` (`ty_sub_ok_tys`), so it
 * keeps every judgement (`typing_subst_tys`).
 *
 * A clause reads two kinds of type under its binders. A type of the outer
 * context shifted past them (`ren_ty (shift m)`) comes back under the
 * instantiation (`sub_tys_shift`). An instance `eff_inst m τ̄ τ` of the
 * operation's signature becomes the instance `op_inst τ̄ σ̄ τ` that
 * `perform` reads (`sub_tys_eff_inst`). Those instances depend on the
 * effect's arguments `τ̄` only up to type equality (`op_inst_canon`).
 *)
module Stella.Core.Typing.Subst.Tys
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Subst.Ty
module L = FStar.List.Tot

(** * The context morphism *)

(** A substitution from `g` to `g'` extended by a substitute `s : κ` of
    `g'` goes from `g` under a binder of kind `κ` to `g'`. At `σ = tvar`
    this is `Stella.Core.Typing.Subst.Ty.ty_sub_ok_subst1`. *)
val ty_sub_ok_scons (sg: sig) (sigma: tsub) (g g': ctx) (k: kind) (s: typ)
  : Lemma (requires ty_sub_ok sg sigma g g' /\ check sg g' s k)
          (ensures ty_sub_ok sg (scons s sigma) (push_tvar g k) g')

(** The binders `κ̄` instantiated at `σ̄`, the types kinded in `g`. *)
val ty_sub_ok_tys (sg: sig) (g: ctx) (ss: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ss ks)
          (ensures ty_sub_ok sg (list_tsub (L.rev ss)) (push_tvars g ks) g)

(** * The judgement *)

(** A derivation under the binders `κ̄`, instantiated at `σ̄`. *)
val typing_subst_tys (#sg: sig) (#ln: lctx) (#g: ctx) (#ks: list kind) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln (push_tvars g ks) d e t r) (ss: list typ)
  : Pure (typing sg ln g (sub_jctx (list_tsub (L.rev ss)) d)
            (sub_ty_exp (list_tsub (L.rev ss)) e)
            (sub_ty (list_tsub (L.rev ss)) t) (sub_ty (list_tsub (L.rev ss)) r))
         (requires sig_ok sg /\ tvars_wf g /\ check_tys sg g ss ks)
         (ensures fun _ -> True)

(** A derivation under the binders `κ̄` and then the term variables
    `x̄ : τ̄`, as a clause's body stands, instantiated at `σ̄`: the term
    variables keep their places, at the instantiated types. *)
val typing_subst_tys_vars (#sg: sig) (#ln: lctx) (#g: ctx) (#ks: list kind) (#ts: list typ)
  (#d: jctx) (#e: exp) (#t #r: typ) (h: typing sg ln (push_vars (push_tvars g ks) ts) d e t r)
  (ss: list typ)
  : Pure (typing sg ln (push_vars g (sub_tys (list_tsub (L.rev ss)) ts))
            (sub_jctx (list_tsub (L.rev ss)) d) (sub_ty_exp (list_tsub (L.rev ss)) e)
            (sub_ty (list_tsub (L.rev ss)) t) (sub_ty (list_tsub (L.rev ss)) r))
         (requires sig_ok sg /\ tvars_wf g /\ check_tys sg g ss ks)
         (ensures fun _ -> True)

(** * Types read under the binders *)

(** The length of the types agrees with that of the binders. *)
val check_tys_length (sg: sig) (g: ctx) (ss: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ss ks) (ensures L.length ss == L.length ks)

(** A type of the outer context shifted past the `|σ̄|` binders comes
    back. *)
val sub_tys_shift (ss: list typ) (n: nat) (t: typ)
  : Lemma (requires n == L.length ss)
          (ensures sub_ty (list_tsub (L.rev ss)) (ren_ty (shift n) t) == t)

(** The instance under the binders, instantiated, is the instance that
    `perform` reads. *)
val sub_tys_eff_inst (ss ts: list typ) (n: nat) (t: typ)
  : Lemma (requires n == L.length ss)
          (ensures sub_ty (list_tsub (L.rev ss)) (eff_inst n ts t) == op_inst ts ss t)

(** The effect's arguments matter up to type equality. *)
val op_inst_canon (ts ts' ss: list typ) (t: typ)
  : Lemma (requires canon_tys ts == canon_tys ts')
          (ensures ty_eq (op_inst ts ss t) (op_inst ts' ss t))
