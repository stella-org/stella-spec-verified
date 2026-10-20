(**
 * The syntactic facts that the renaming lemmas of typing read
 * (`Stella.Core.Typing.Rename.Ty`, `Stella.Core.Typing.Rename.Tm`;
 * design §1.1).
 *
 *   - Types. A type renaming distributes over the lists and layouts a rule
 *     reads, and over the types of `Stella.Core.Prim`; it keeps the head of
 *     an application, the known keys and, mapped, the canonical entries of
 *     a row. The declared scheme of a global has no free type variable, so
 *     every renaming fixes its instances at kinds, and commutes with the
 *     fields of a constructor at an instance.
 *   - Region names. A type renaming and a term renaming keep the atoms of a
 *     term, so they keep the excluded set of the cofinite premise of
 *     `region`.
 *   - Values. A type substitution, so a type renaming, and a term renaming
 *     keep the static value forms and the run-time values, and the value
 *     at an occurrence is the image of the one before. The cursor of a
 *     chain under a type renaming is the substitution case
 *     (`Stella.Core.Spine.Wf.chain_cursor_sub_ty`) at `ren_tsub ξ`.
 *)
module Stella.Core.Typing.Rename.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Typing.Aux
module L = FStar.List.Tot
module V = Stella.Core.Value

(** `f` applied under `Some`. *)
let map_opt (#a #b: Type) (f: a -> b) (o: option a) : option b =
  match o with
  | Some x -> Some (f x)
  | None -> None

(** * Lists and layouts *)

val ren_layout_snd (xi: ren) (l: layout) : Lemma
  (L.map snd (ren_layout xi l) == ren_tys xi (L.map snd l))

val ren_layout_assoc (xi: ren) (l: layout) (k: key)
  : Lemma (L.assoc k (ren_layout xi l) == map_opt (ren_ty xi) (L.assoc k l))

val ren_layout_row (xi: ren) (l: layout)
  : Lemma (ren_ty xi (layout_row l) == layout_row (ren_layout xi l))

val ren_ty_binds_fst (xi: ren) (bs: list (typ & exp))
  : Lemma (L.map fst (ren_ty_binds xi bs) == ren_tys xi (L.map fst bs))

val ren_tm_binds_fst (xi: ren) (bs: list (typ & exp))
  : Lemma (L.map fst (ren_tm_binds xi bs) == L.map fst bs)

val ren_tapps (xi: ren) (h: typ) (ts: list typ)
  : Lemma (ren_ty xi (tapps h ts) == tapps (ren_ty xi h) (ren_tys xi ts))

(** * Types of `Prim` *)

val ren_t_fun (xi: ren) (t1 r t2: typ)
  : Lemma (ren_ty xi (t_fun t1 r t2) == t_fun (ren_ty xi t1) (ren_ty xi r) (ren_ty xi t2))

val ren_t_record (xi: ren) (r: typ) : Lemma (ren_ty xi (t_record r) == t_record (ren_ty xi r))

val ren_t_variant (xi: ren) (r: typ) : Lemma (ren_ty xi (t_variant r) == t_variant (ren_ty xi r))

val ren_lit_type (xi: ren) (c: lit) : Lemma (ren_ty xi (lit_type c) == lit_type c)

(** * Binders *)

(** Instantiating a `forall` commutes with a renaming lifted under it. *)
val ren_subst1 (xi: ren) (s t: typ)
  : Lemma (ren_ty xi (subst1_ty s t) == subst1_ty (ren_ty xi s) (ren_ty (up_ren xi) t))

(** A type shifted past `n` binders is renamed by the renaming lifted past
    them. *)
val ren_shift_up (n: nat) (xi: ren) (t: typ)
  : Lemma (ren_ty (upn_ren n xi) (ren_ty (shift n) t) == ren_ty (shift n) (ren_ty xi t))

val ren_layout_shift_up (n: nat) (xi: ren) (l: layout)
  : Lemma (ren_layout (upn_ren n xi) (ren_layout (shift n) l) ==
           ren_layout (shift n) (ren_layout xi l))

(** * Rows *)

val ty_head_ren (xi: ren) (t: typ) : Lemma (ty_head (ren_ty xi t) == ty_head t)

val known_keys_ren (xi: ren) (t: typ) (k: key)
  : Lemma (requires L.mem k (known_keys t)) (ensures L.mem k (known_keys (ren_ty xi t)))

(** A canonical entry of a row has its image among the entries of the
    renamed row. *)
val entries_ren (xi: ren) (t: typ) (e: centry)
  : Lemma (requires L.mem e (row_entries (canon t)))
          (ensures L.mem (cren_ent xi e) (row_entries (canon (ren_ty xi t))))

(** The entry `k : τ` that `T_VariantValue` and `TO_Field` read. *)
val entries_ren_ty (xi: ren) (r: typ) (k: key) (t: typ)
  : Lemma (requires L.mem (k, PTy (canon t)) (row_entries (canon r)))
          (ensures L.mem (k, PTy (canon (ren_ty xi t))) (row_entries (canon (ren_ty xi r))))

(** The element `k : E τ̄` that `T_Perform` reads. *)
val entries_ren_eff (xi: ren) (r: typ) (k: key) (q: qname) (ts: list typ)
  : Lemma (requires L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)))
          (ensures L.mem (k, PEff q (canon_tys (ren_tys xi ts)))
              (row_entries (canon (ren_ty xi r))))

(** * Declared types *)

(** An instance at kinds of the type of a global has no free type
    variable. *)
val global_inst_ren (sg: sig) (q: qname) (nk: nat) (t: typ) (ks: list kind) (xi: ren)
  : Lemma (requires sig_wf sg /\ global_type sg q == Some (nk, t))
          (ensures ren_ty xi (kinst_ty ks t) == kinst_ty ks t)

(** The fields of a constructor at renamed type arguments are the renamed
    fields. *)
val ctor_fields_ren (sg: sig) (c: qname) (ks: list kind) (ss: list typ) (xi: ren)
  : Lemma (requires sig_wf sg)
          (ensures ctor_fields sg c ks (ren_tys xi ss)
              == map_opt (ren_tys xi) (ctor_fields sg c ks ss))

(** Kinded type lists have the length of their kind lists. *)
val check_tys_length (sg: sig) (g: ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ts ks) (ensures L.length ts == L.length ks)

(** The argument and result instances of `perform`. *)
val op_inst_ren_sig (sg: sig) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  (ts ss: list typ) (xi: ren)
  : Lemma (requires effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os /\
                    L.length ts == L.length ei.eff_params /\ L.length ss == L.length os.binders)
          (ensures ren_ty xi (op_inst ts ss os.arg)
              == op_inst (ren_tys xi ts) (ren_tys xi ss) os.arg /\
                   ren_ty xi (op_inst ts ss os.res)
                     == op_inst (ren_tys xi ts) (ren_tys xi ss) os.res)

(** The instances a clause reads under its `m` binders. *)
val eff_inst_ren_sig (sg: sig) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  (ts: list typ) (xi: ren)
  : Lemma (requires effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os /\
                    L.length ts == L.length ei.eff_params)
          (ensures (let m = L.length os.binders in
                    ren_ty (upn_ren m xi) (eff_inst m ts os.arg)
                      == eff_inst m (ren_tys xi ts) os.arg /\
                    ren_ty (upn_ren m xi) (eff_inst m ts os.res)
                      == eff_inst m (ren_tys xi ts) os.res))

(** * Region names *)

val frn_ren_ty (xi: ren) (t: typ) : Lemma (frn_ty (ren_ty xi t) == frn_ty t)

val frn_ren_ty_exp (xi: ren) (e: exp) : Lemma (frn_exp (ren_ty_exp xi e) == frn_exp e)

val frn_ren_tm (xi: ren) (e: exp) : Lemma (frn_exp (ren_tm xi e) == frn_exp e)

(** * Values under a type substitution *)

val ren_ty_exps_as_sub (xi: ren) (es: list exp)
  : Lemma (ren_ty_exps xi es == sub_ty_exps (ren_tsub xi) es)

val value_form_sub_ty (sg: sig) (sigma: tsub) (e: exp)
  : Lemma (value_form sg (sub_ty_exp sigma e) == value_form sg e)

val is_value_sub_ty (sg: sig) (sigma: tsub) (e: exp)
  : Lemma (V.is_value sg (sub_ty_exp sigma e) == V.is_value sg e)

val values_sub_ty (sg: sig) (sigma: tsub) (es: list exp)
  : Lemma (L.for_all (V.is_value sg) (sub_ty_exps sigma es) == L.for_all (V.is_value sg) es)

val proj_sub_ty (sg: sig) (sigma: tsub) (th: list exp) (o: occ)
  : Lemma (proj sg (sub_ty_exps sigma th) o == map_opt (sub_ty_exp sigma) (proj sg th o))

val value_form_ren_ty (sg: sig) (xi: ren) (e: exp)
  : Lemma (value_form sg (ren_ty_exp xi e) == value_form sg e)

val is_value_ren_ty (sg: sig) (xi: ren) (e: exp)
  : Lemma (V.is_value sg (ren_ty_exp xi e) == V.is_value sg e)

val values_ren_ty (sg: sig) (xi: ren) (es: list exp)
  : Lemma (L.for_all (V.is_value sg) (ren_ty_exps xi es) == L.for_all (V.is_value sg) es)

val proj_ren_ty (sg: sig) (xi: ren) (th: list exp) (o: occ)
  : Lemma (proj sg (ren_ty_exps xi th) o == map_opt (ren_ty_exp xi) (proj sg th o))

(** The cursor of a renamed chain reaches the same remainder, and its
    instances are the renamed ones. *)
val chain_cursor_ren_ty (sg: sig) (xi: ren) (e: exp) (t: typ) (th: tsub)
  : Lemma (requires sig_wf sg /\ chain_cursor sg e == Some (t, th))
          (ensures (match chain_cursor sg (ren_ty_exp xi e) with
                    | Some (t', th') ->
                      t' == t /\ sub_ty th' t == ren_ty xi (sub_ty th t) /\
                      (forall (t1 r t2: typ). as_function sg t == Some (t1, r, t2) ==>
                         sub_ty th' t1 == ren_ty xi (sub_ty th t1)) /\
                      (forall (c: constr) (b: typ). t == TConstr c b ==>
                         sub_constr th' c == ren_constr xi (sub_constr th c))
                    | None -> False))

(** * Values under a term renaming *)

val value_form_ren_tm (sg: sig) (xi: ren) (e: exp)
  : Lemma (value_form sg (ren_tm xi e) == value_form sg e)

val is_value_ren_tm (sg: sig) (xi: ren) (e: exp)
  : Lemma (V.is_value sg (ren_tm xi e) == V.is_value sg e)

val values_ren_tm (sg: sig) (xi: ren) (es: list exp)
  : Lemma (L.for_all (V.is_value sg) (ren_tm_exps xi es) == L.for_all (V.is_value sg) es)

val proj_ren_tm (sg: sig) (xi: ren) (th: list exp) (o: occ)
  : Lemma (proj sg (ren_tm_exps xi th) o == map_opt (ren_tm xi) (proj sg th o))
