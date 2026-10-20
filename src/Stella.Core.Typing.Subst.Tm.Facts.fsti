(**
 * The syntactic facts that the substitution lemma of term variables reads
 * (`Stella.Core.Typing.Subst.Tm`; design §1.1, §1.3).
 *
 *   - Values. A term substitution keeps the static value forms and the
 *     run-time values, whatever it substitutes: a value has no variable at
 *     a position that its value grammar reads, the body of a `λ` being no
 *     such position. The value at an occurrence of the substituted values
 *     is the substituted value at that occurrence.
 *   - Region names. A term substitution replaces variables, which name no
 *     atom, so the atoms of a term are among those of its image. The
 *     excluded set of the cofinite premise of `region` grows.
 *   - The forms the rules read off a term: the member types of a `letrec`
 *     and the operations of the clauses of a handler are unchanged.
 *)
module Stella.Core.Typing.Subst.Tm.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Sig
open Stella.Core.Typing.Aux
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Values *)

val value_form_sub_tm (sg: sig) (sigma: esub) (e: exp)
  : Lemma (requires value_form sg e) (ensures value_form sg (sub_tm sigma e))

val is_value_sub_tm (sg: sig) (sigma: esub) (e: exp)
  : Lemma (requires V.is_value sg e) (ensures V.is_value sg (sub_tm sigma e))

val values_sub_tm (sg: sig) (sigma: esub) (es: list exp)
  : Lemma (requires L.for_all (V.is_value sg) es)
          (ensures L.for_all (V.is_value sg) (sub_tm_exps sigma es))

val proj_sub_tm (sg: sig) (sigma: esub) (th: list exp) (o: occ) (v: exp)
  : Lemma (requires proj sg th o == Some v)
          (ensures proj sg (sub_tm_exps sigma th) o == Some (sub_tm sigma v))

(** * Region names *)

val frn_sub_tm (sigma: esub) (e: exp) (a: atom)
  : Lemma (requires L.mem a (frn_exp e)) (ensures L.mem a (frn_exp (sub_tm sigma e)))

(** A term renaming keeps local closure. *)
val lc_ren_tm (xi: ren) (e: exp) : Lemma (requires lc_exp e) (ensures lc_exp (ren_tm xi e))

(** * Forms *)

val sub_tm_binds_fst (sigma: esub) (bs: list (typ & exp))
  : Lemma (L.map fst (sub_tm_binds sigma bs) == L.map fst bs)

val clause_ops_sub_tm (sigma: esub) (cs: list clause)
  : Lemma (clause_ops (sub_tm_cls sigma cs) == clause_ops cs)
