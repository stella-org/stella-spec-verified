(**
 * Coverage under the syntactic operations a step performs (spec 06
 * §Coverage, §Properties).
 *
 * A step substitutes, rearranges, or moves what the term already holds,
 * and a kind or a type it substitutes carries no global name. So the
 * operations on terms that the reduction rules use keep or bound the
 * global names of a term (`Stella.Core.Semantics.Env.globals`):
 *
 *   - kind instantiation, type substitution and type renaming, and the
 *     renamings of term variables and of join points, keep `globals`
 *     exactly: they rewrite kinds, type annotations, variable indices
 *     and join indices, none of which is a global name;
 *   - a term substitution places its substitutes at the variables it
 *     replaces, so a covered term with covered substitutes gives a covered
 *     result (`covers_sub_tm`);
 *   - the value `θ(o)` a decision tree reads out of the scrutinee values
 *     is a subterm of one of them (`covers_proj`), and so is each value
 *     argument of a chain (`covers_value_args`);
 *   - an evaluation context with a covered term in its hole is covered
 *     when the context is (`covers_plug1_replace`, `covers_plug_replace`).
 *
 * Coverage depends on a term only through its `globals`
 * (`covers_globals`), so terms with equal global names have equal
 * coverage (`covers_globals_eq`).
 *)
module Stella.Core.Semantics.Covers
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Typing.Aux
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
module L = FStar.List.Tot

(** * Equal names, equal coverage *)

val covers_globals_eq (sg: sig) (gi: genv) (e e': exp)
  : Lemma (requires globals e == globals e') (ensures covers sg gi e == covers sg gi e')

(** * Lists and branches *)

(** The terms of a list are covered one by one. *)
val covers_exps (sg: sig) (gi: genv) (es: list exp)
  : Lemma (exp_all_exps (covered sg gi) es == L.for_all (covers sg gi) es)

(** The branch a dispatch selects out of covered branches is covered. *)
val covers_branch (#lb: eqtype) (sg: sig) (gi: genv) (l: lb) (bs: list (lb & dtree)) (dt: dtree)
  : Lemma (requires exp_all_brs (covered sg gi) bs /\ L.assoc l bs == Some dt)
          (ensures covers_dt sg gi dt)

(** * Operations that keep the global names *)

(** Kind instantiation `e[k̄ := κ̄]` rewrites the kinds of global references
    and the kinds of annotations, never a name. *)
val covers_kinst (ks: list kind) (e: exp)
  : Lemma (globals (kinst_exp ks e) == globals e)

(** A type substitution rewrites type annotations only. *)
val covers_sub_ty_exp (sigma: tsub) (e: exp)
  : Lemma (globals (sub_ty_exp sigma e) == globals e)

(** A renaming of type variables rewrites type annotations only. *)
val covers_ren_ty_exp (xi: ren) (e: exp)
  : Lemma (globals (ren_ty_exp xi e) == globals e)

(** A renaming of term variables rewrites variable indices only. *)
val covers_ren_tm (xi: ren) (e: exp)
  : Lemma (globals (ren_tm xi e) == globals e)

(** A renaming of join points rewrites join indices only. *)
val covers_ren_jp (xi: ren) (e: exp)
  : Lemma (globals (ren_jp xi e) == globals e)

(** * Term substitution *)

(** Every substitute of `σ` is covered. *)
let esub_covers (sg: sig) (gi: genv) (sigma: esub) : prop =
  forall (i: nat). {:pattern sigma i} covers sg gi (sigma i)

(** A covered term with covered substitutes gives a covered result: the
    substitution places its substitutes at variables, and moves every
    other node as it stands. *)
val covers_sub_tm (sg: sig) (gi: genv) (sigma: esub) (e: exp)
  : Lemma (requires esub_covers sg gi sigma /\ covers sg gi e)
          (ensures covers sg gi (sub_tm sigma e))

(** The same for a decision tree. *)
val covers_sub_tm_dt (sg: sig) (gi: genv) (sigma: esub) (dt: dtree)
  : Lemma (requires esub_covers sg gi sigma /\ covers_dt sg gi dt)
          (ensures covers_dt sg gi (sub_tm_dt sigma dt))

(** `e[x := v]`. *)
val covers_subst1_tm (sg: sig) (gi: genv) (v e: exp)
  : Lemma (requires covers sg gi v /\ covers sg gi e) (ensures covers sg gi (subst1_tm v e))

(** `dt[x := v]`, the substitution of `bind x = o in dt`. *)
val covers_subst1_dt (sg: sig) (gi: genv) (v: exp) (dt: dtree)
  : Lemma (requires covers sg gi v /\ covers_dt sg gi dt)
          (ensures covers_dt sg gi (sub_tm_dt (scons v evar) dt))

(** `e[x̄ := v̄]`, the simultaneous substitution of a list of terms. *)
val covers_list_esub (sg: sig) (gi: genv) (vs: list exp) (e: exp)
  : Lemma (requires L.for_all (covers sg gi) vs /\ covers sg gi e)
          (ensures covers sg gi (sub_tm (list_esub vs) e))

(** Reversing a list keeps every element covered. *)
val covers_rev (sg: sig) (gi: genv) (vs: list exp)
  : Lemma (requires L.for_all (covers sg gi) vs) (ensures L.for_all (covers sg gi) (L.rev vs))

(** * Values read out of values *)

(** The value arguments of a covered chain are covered. *)
val covers_value_args (sg: sig) (gi: genv) (e: exp) (q: qname) (ks: list kind)
  (args: list spine_arg)
  : Lemma (requires covers sg gi e /\ decompose_global_app e == Some (q, ks, args))
          (ensures L.for_all (covers sg gi) (value_args args))

(** `θ(o)` is covered when the scrutinee values `θ` are. *)
val covers_proj (sg: sig) (gi: genv) (th: list exp) (o: occ) (v: exp)
  : Lemma (requires L.for_all (covers sg gi) th /\ proj sg th o == Some v)
          (ensures covers sg gi v)

(** * Evaluation contexts *)

(** A covered context around a covered term is covered. *)
val covers_plug1_replace (sg: sig) (gi: genv) (f: frame) (e e': exp)
  : Lemma (requires covers sg gi (plug1 f e) /\ covers sg gi e')
          (ensures covers sg gi (plug1 f e'))

(** The hole of a covered evaluation context holds a covered term. *)
val covers_plug (sg: sig) (gi: genv) (fs: list frame) (e: exp)
  : Lemma (requires covers sg gi (plug fs e)) (ensures covers sg gi e)

(** `covers_plug1_replace` for a whole evaluation context. *)
val covers_plug_replace (sg: sig) (gi: genv) (fs: list frame) (e e': exp)
  : Lemma (requires covers sg gi (plug fs e) /\ covers sg gi e')
          (ensures covers sg gi (plug fs e'))
