(**
 * The facts that the kind instantiation lemma of typing reads
 * (`Stella.Core.Typing.Kinst`; design §1.2, §2.3).
 *
 * A kind instantiation `kinst ks` replaces the kind variables of a type or
 * a term and touches nothing else: no type variable, no term variable, no
 * key and no region reference. So
 *
 *   - it distributes over the lists and layouts a rule reads and over the
 *     types of `Stella.Core.Prim`, commutes with instantiating a `forall`,
 *     keeps the head of an application and the shape of a type, and maps
 *     the canonical entries of a row to entries of the instantiated row;
 *   - instantiations compose on the declared scheme of a global, whose kind
 *     variables are those of its scheme, so the instance of a global's type
 *     at instantiated kinds is the instantiated instance; the same holds
 *     for the fields of a constructor at the kinds of its data type;
 *   - it keeps the atoms of a term and commutes with opening a region;
 *   - it keeps the static value forms and the run-time values, and the
 *     value at an occurrence is the image of the one before. The cursor of
 *     a chain reads the declared remainder only through its shape, and a
 *     chain's kind vector instantiates the remainder without changing its
 *     shape, so saturation is kept.
 *)
module Stella.Core.Typing.Kinst.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Rename.Facts
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Lists and layouts *)

val kinst_kinds_length (ks kl: list kind) : Lemma (L.length (kinst_kinds ks kl) == L.length kl)

val kinst_tys_length (ks: list kind) (ts: list typ) : Lemma (L.length (kinst_tys ks ts) == L.length ts)

val kinst_layout_snd (ks: list kind) (l: layout)
  : Lemma (L.map snd (kinst_layout ks l) == kinst_tys ks (L.map snd l))

val kinst_layout_assoc (ks: list kind) (l: layout) (k: key)
  : Lemma (L.assoc k (kinst_layout ks l) == map_opt (kinst_ty ks) (L.assoc k l))

val kinst_layout_row (ks: list kind) (l: layout)
  : Lemma (kinst_ty ks (layout_row l) == layout_row (kinst_layout ks l))

val kinst_binds_fst (ks: list kind) (bs: list (typ & exp))
  : Lemma (L.map fst (kinst_binds ks bs) == kinst_tys ks (L.map fst bs))

val kinst_tapps (ks: list kind) (h: typ) (ts: list typ)
  : Lemma (kinst_ty ks (tapps h ts) == tapps (kinst_ty ks h) (kinst_tys ks ts))

(** * Types of `Prim` *)

val kinst_t_fun (ks: list kind) (t1 r t2: typ)
  : Lemma (kinst_ty ks (t_fun t1 r t2) == t_fun (kinst_ty ks t1) (kinst_ty ks r) (kinst_ty ks t2))

val kinst_t_record (ks: list kind) (r: typ)
  : Lemma (kinst_ty ks (t_record r) == t_record (kinst_ty ks r))

val kinst_t_variant (ks: list kind) (r: typ)
  : Lemma (kinst_ty ks (t_variant r) == t_variant (kinst_ty ks r))

val kinst_lit_type (ks: list kind) (c: lit) : Lemma (kinst_ty ks (lit_type c) == lit_type c)

val kinst_t_unit (ks: list kind) : Lemma (kinst_ty ks t_unit == t_unit)

(** * Binders *)

val kinst_subst1 (ks: list kind) (s t: typ)
  : Lemma (kinst_ty ks (subst1_ty s t) == subst1_ty (kinst_ty ks s) (kinst_ty ks t))

(** * Rows *)

val ty_head_kinst (ks: list kind) (t: typ) : Lemma (ty_head (kinst_ty ks t) == ty_head t)

val known_keys_kinst (ks: list kind) (t: typ) (k: key)
  : Lemma (requires L.mem k (known_keys t)) (ensures L.mem k (known_keys (kinst_ty ks t)))

(** The entry `k : τ` that `T_VariantValue` and `TO_Field` read. *)
val entries_kinst_ty (ks: list kind) (r: typ) (k: key) (t: typ)
  : Lemma (requires L.mem (k, PTy (canon t)) (row_entries (canon r)))
          (ensures L.mem (k, PTy (canon (kinst_ty ks t))) (row_entries (canon (kinst_ty ks r))))

(** The element `k : E τ̄` that `T_Perform` reads. *)
val entries_kinst_eff (ks: list kind) (r: typ) (k: key) (q: qname) (ts: list typ)
  : Lemma (requires L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)))
          (ensures L.mem (k, PEff q (canon_tys (kinst_tys ks ts)))
              (row_entries (canon (kinst_ty ks r))))

(** * Declared types *)

(** The type of a global at instantiated kinds (spec 06 §The global
    environment). *)
val global_type_kinst (sg: sig) (q: qname) (nk: nat) (t: typ) (ks0 ks: list kind)
  : Lemma (requires sig_wf sg /\ global_type sg q == Some (nk, t) /\ L.length ks0 == nk)
          (ensures kinst_ty ks (kinst_ty ks0 t) == kinst_ty (kinst_kinds ks ks0) t)

(** The fields of a constructor at instantiated kinds and type arguments,
    the kinds being as many as the kind variables of the constructor. *)
val ctor_fields_kinst (sg: sig) (c: qname) (ks0: list kind) (ss fs: list typ) (ks: list kind)
  : Lemma (requires sig_wf sg /\ ctor_fields sg c ks0 ss == Some fs /\
                    (match sg.ctors c with Some ci -> L.length ks0 == ci.ct_nk | None -> False))
          (ensures ctor_fields sg c (kinst_kinds ks ks0) (kinst_tys ks ss) == Some (kinst_tys ks fs))

(** A constructor of a data type `T` has as many kind variables as a kinded
    instance `T [[κ̄]] σ̄` has kinds. *)
val ctor_nk_of_data (sg: sig) (g: ctx) (tq: qname) (ks0: list kind) (ss: list typ)
  (cs: list qname) (c: qname)
  : Lemma (requires sig_ok sg /\ check sg g (tapps (TCon tq ks0) ss) KType /\
                    has_class sg tq (TcData cs) /\ L.mem c cs)
          (ensures (match sg.ctors c with Some ci -> L.length ks0 == ci.ct_nk | None -> False))

(** * Region names *)

val frn_kinst_exp (ks: list kind) (e: exp) : Lemma (frn_exp (kinst_exp ks e) == frn_exp e)

val open_region_kinst (a: atom) (ks: list kind) (e: exp)
  : Lemma (open_region a (kinst_exp ks e) == kinst_exp ks (open_region a e))

(** * Values *)

val value_form_kinst (sg: sig) (ks: list kind) (e: exp)
  : Lemma (value_form sg (kinst_exp ks e) == value_form sg e)

val is_value_kinst (sg: sig) (ks: list kind) (e: exp)
  : Lemma (V.is_value sg (kinst_exp ks e) == V.is_value sg e)

val values_kinst (sg: sig) (ks: list kind) (es: list exp)
  : Lemma (L.for_all (V.is_value sg) (kinst_exps ks es) == L.for_all (V.is_value sg) es)

val proj_kinst (sg: sig) (ks: list kind) (th: list exp) (o: occ)
  : Lemma (proj sg (kinst_exps ks th) o == map_opt (kinst_exp ks) (proj sg th o))
