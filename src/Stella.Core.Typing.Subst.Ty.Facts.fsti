(**
 * The facts that the type substitution lemma of typing reads
 * (`Stella.Core.Typing.Subst.Ty`; design §1.1, §1.3, §2.2).
 *
 *   - Types. A type substitution distributes over the lists and layouts a
 *     rule reads and over the types of `Stella.Core.Prim`, commutes with
 *     instantiating a `forall` and with shifting past binders, keeps the
 *     head of a constructor application, and maps the canonical entries of
 *     a row to entries of the substituted row.
 *   - Declared types. The scheme of a global has no free type variable, so
 *     every substitution fixes its instances at kinds. A constructor's
 *     fields at substituted type arguments are the substituted fields: the
 *     scheme `forall ā. τ̄ -{()}-> T [[k̄]] ā` (`Stella.Core.Sig.Wf.ctor_ok`)
 *     ends in a data type, which no substitution turns into an arrow.
 *   - Region names. A type substitution removes no atom of a term, so the
 *     excluded set of the cofinite premise of `region` only grows.
 *   - Region facts. In a context whose type variables have quantifiable
 *     kinds, a row of kind `Row Effect` has only row variables of that kind
 *     as tails, and every region it names is in scope. Entering a region
 *     whose atom is out of scope therefore entails that the row lacks the
 *     region's key: the facts the region adds cover every tail. So a
 *     well-scoped substitution carries the facts of a region to facts of
 *     its image (design §2.2).
 *)
module Stella.Core.Typing.Subst.Ty.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Rename.Facts
module L = FStar.List.Tot

(** * Lists and layouts *)

val sub_layout_snd (sigma: tsub) (l: layout)
  : Lemma (L.map snd (sub_layout sigma l) == sub_tys sigma (L.map snd l))

val sub_layout_assoc (sigma: tsub) (l: layout) (k: key)
  : Lemma (L.assoc k (sub_layout sigma l) == map_opt (sub_ty sigma) (L.assoc k l))

val sub_layout_row (sigma: tsub) (l: layout)
  : Lemma (sub_ty sigma (layout_row l) == layout_row (sub_layout sigma l))

val sub_ty_binds_fst (sigma: tsub) (bs: list (typ & exp))
  : Lemma (L.map fst (sub_ty_binds sigma bs) == sub_tys sigma (L.map fst bs))

val sub_tapps (sigma: tsub) (h: typ) (ts: list typ)
  : Lemma (sub_ty sigma (tapps h ts) == tapps (sub_ty sigma h) (sub_tys sigma ts))

(** * Types of `Prim` *)

val sub_t_fun (sigma: tsub) (t1 r t2: typ)
  : Lemma (sub_ty sigma (t_fun t1 r t2) == t_fun (sub_ty sigma t1) (sub_ty sigma r) (sub_ty sigma t2))

val sub_t_record (sigma: tsub) (r: typ) : Lemma (sub_ty sigma (t_record r) == t_record (sub_ty sigma r))

val sub_t_variant (sigma: tsub) (r: typ)
  : Lemma (sub_ty sigma (t_variant r) == t_variant (sub_ty sigma r))

val sub_lit_type (sigma: tsub) (c: lit) : Lemma (sub_ty sigma (lit_type c) == lit_type c)

(** * Binders *)

(** Instantiating a `forall` commutes with a substitution lifted under
    it. *)
val sub_subst1 (sigma: tsub) (s t: typ)
  : Lemma (sub_ty sigma (subst1_ty s t) == subst1_ty (sub_ty sigma s) (sub_ty (up_tsub sigma) t))

(** A type shifted past `n` binders is substituted by the substitution
    lifted past them. *)
val sub_shift_up (n: nat) (sigma: tsub) (t: typ)
  : Lemma (sub_ty (upn_tsub n sigma) (ren_ty (shift n) t) == ren_ty (shift n) (sub_ty sigma t))

val sub_layout_shift_up (n: nat) (sigma: tsub) (l: layout)
  : Lemma (sub_layout (upn_tsub n sigma) (ren_layout (shift n) l) ==
           ren_layout (shift n) (sub_layout sigma l))

(** `upn_tsub` lifted once more is `upn_tsub` past one more binder. *)
val upn_tsub_succ (n: nat) (sigma: tsub) (i: nat)
  : Lemma (upn_tsub n (up_tsub sigma) i == upn_tsub (n + 1) sigma i)

(** * Rows *)

(** The head of a constructor application is kept. *)
val ty_head_sub (sigma: tsub) (t: typ)
  : Lemma (requires Some? (ty_head t)) (ensures ty_head (sub_ty sigma t) == ty_head t)

(** The entry `k : τ` that `T_VariantValue` and `TO_Field` read. *)
val entries_sub_ty (sigma: tsub) (r: typ) (k: key) (t: typ)
  : Lemma (requires L.mem (k, PTy (canon t)) (row_entries (canon r)))
          (ensures L.mem (k, PTy (canon (sub_ty sigma t))) (row_entries (canon (sub_ty sigma r))))

(** The element `k : E τ̄` that `T_Perform` reads. *)
val entries_sub_eff (sigma: tsub) (r: typ) (k: key) (q: qname) (ts: list typ)
  : Lemma (requires L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)))
          (ensures L.mem (k, PEff q (canon_tys (sub_tys sigma ts)))
              (row_entries (canon (sub_ty sigma r))))

(** * Declared types *)

(** An instance at kinds of the type of a global has no free type
    variable. *)
val global_inst_sub (sg: sig) (q: qname) (nk: nat) (t: typ) (ks: list kind) (sigma: tsub)
  : Lemma (requires sig_wf sg /\ global_type sg q == Some (nk, t))
          (ensures sub_ty sigma (kinst_ty ks t) == kinst_ty ks t)

(** The fields of a constructor at substituted type arguments are the
    substituted fields. *)
val ctor_fields_sub (sg: sig) (c: qname) (ks: list kind) (ss fs: list typ) (sigma: tsub)
  : Lemma (requires sig_ok sg /\ ctor_fields sg c ks ss == Some fs)
          (ensures ctor_fields sg c ks (sub_tys sigma ss) == Some (sub_tys sigma fs))

(** The argument and result instances of `perform`. *)
val op_inst_sub_sig (sg: sig) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  (ts ss: list typ) (sigma: tsub)
  : Lemma (requires effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os /\
                    L.length ts == L.length ei.eff_params /\ L.length ss == L.length os.binders)
          (ensures sub_ty sigma (op_inst ts ss os.arg)
                     == op_inst (sub_tys sigma ts) (sub_tys sigma ss) os.arg /\
                   sub_ty sigma (op_inst ts ss os.res)
                     == op_inst (sub_tys sigma ts) (sub_tys sigma ss) os.res)

(** The instances a clause reads under its `m` binders. *)
val eff_inst_sub_sig (sg: sig) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  (ts: list typ) (sigma: tsub)
  : Lemma (requires effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os /\
                    L.length ts == L.length ei.eff_params)
          (ensures (let m = L.length os.binders in
                    sub_ty (upn_tsub m sigma) (eff_inst m ts os.arg)
                      == eff_inst m (sub_tys sigma ts) os.arg /\
                    sub_ty (upn_tsub m sigma) (eff_inst m ts os.res)
                      == eff_inst m (sub_tys sigma ts) os.res))

(** * Region names *)

(** A type substitution keeps every atom of a term. *)
val frn_sub_ty_exp (sigma: tsub) (e: exp) (a: atom)
  : Lemma (requires L.mem a (frn_exp e)) (ensures L.mem a (frn_exp (sub_ty_exp sigma e)))

(** * Region facts *)

(** A row of kind `Row Effect` lacks the key of a region entered with an
    atom out of scope. *)
val region_lacks_row (sg: sig) (g: ctx) (a: atom) (l: layout) (r: typ)
  : Lemma (requires tycons_wf sg /\ tvars_wf g /\ check sg g r (KRow EEffect) /\
                    ~(L.mem a (rdom g)))
          (ensures entails (hyps (enter_region g a l)) (CLacks (RegionKey (RFree a)) r))
