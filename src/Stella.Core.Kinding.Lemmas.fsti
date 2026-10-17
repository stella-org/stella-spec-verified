(**
 * Well-kinded rows and constraints are over row variables, and ex falso
 * leaves structural kinding alone.
 *
 *   - Only row syntax and row variables have a row kind, given that `Σ`'s
 *     type constructors and the context's type variables have quantifiable
 *     kinds. So every tail of the canonical form of a well-kinded row is a
 *     variable of that row kind, and a well-formed constraint is
 *     `var_tailed`. This is the hypothesis of the completeness half of the
 *     inconsistency characterization (`Stella.Core.Entail.Lemmas`).
 *   - In an inconsistent context, the structural checks of kinding are
 *     still made, and only the sharpness premises hold trivially
 *     (design §2.2 item 4).
 *)
module Stella.Core.Kinding.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
module L = FStar.List.Tot

(** * Row kinds come from row syntax and row variables *)

(** Kind instantiation keeps a kind producing `Type`. *)
val kinst_result (ks: list kind) (k: kind)
  : Lemma (requires result k = KType) (ensures result (kinst_kind ks k) = KType)

(** A synthesized kind produces `Type`, unless the type is a variable. *)
val synth_result (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires tycons_wf sg /\ tvars_wf g /\ Some? (synth_kind sg g t))
          (ensures TVar? t \/ result (Some?.v (synth_kind sg g t)) = KType)

(** `c` is a type variable of kind `Row e`. *)
let row_var (g: ctx) (e: elt_kind) (c: ctyp) : bool =
  match c with
  | CVar i -> L.nth g.tvars i = Some (KRow e)
  | _ -> false

(** Every tail of a row of kind `Row e` is a type variable of kind `Row e`. *)
val check_row_tails (sg: sig) (g: ctx) (r: typ) (e: elt_kind)
  : Lemma (requires tycons_wf sg /\ tvars_wf g /\ check sg g r (KRow e))
          (ensures forall (c: ctyp). L.mem c (row_tails (canon r)) ==> row_var g e c)

val constr_ok_var_tailed (sg: sig) (g: ctx) (c: constr)
  : Lemma (requires tycons_wf sg /\ tvars_wf g /\ constr_ok sg g c) (ensures var_tailed c)

val wf_hyps_var_tailed (sg: sig) (g: ctx)
  : Lemma (requires tycons_wf sg /\ tvars_wf g /\ wf_hyps sg g)
          (ensures var_tailed_all (hyps g))

(** * Ex falso does not relax structural kinding

    Each lemma assumes an inconsistent context. *)

(** An application of a constructor of kind `Type` is ill-kinded. *)
val ex_falso_app (sg: sig) (g: ctx) (q: qname) (k: kind)
  : Lemma (requires inconsistent (hyps g) /\ Some? (sg.tycons q) /\
                    (Some?.v (sg.tycons q)).tc_kind = KType)
          (ensures check sg g (TApp (TCon q []) (TCon q [])) k = false)

(** An unbound type variable is ill-kinded. *)
val ex_falso_unbound (sg: sig) (g: ctx) (i: nat) (k: kind)
  : Lemma (requires inconsistent (hyps g) /\ L.length g.tvars <= i)
          (ensures check sg g (TVar i) k = false)

(** The sharpness premises do hold: a row repeating a key is well-kinded. *)
val ex_falso_sharpness (sg: sig) (g: ctx) (k: key) (t: typ)
  : Lemma (requires inconsistent (hyps g) /\ struct_key k /\ check sg g t KType)
          (ensures check sg g (TRowExt (EntTy k t) (TRowExt (EntTy k t) TRowEmpty)) (KRow EType))
