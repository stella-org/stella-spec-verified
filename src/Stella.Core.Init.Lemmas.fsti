(**
 * Facts about the initialization-safety judgement of `Stella.Core.Init`.
 *
 *   - The arity of a global, read from its declared type, agrees with the
 *     spine cursor (spec 06 §The spine cursor): a spine the cursor walks is
 *     within the arity, a saturated one has exactly the arity's number of
 *     value arguments, and one more value argument after saturation makes a
 *     default application (`over_applied_default`).
 *   - Inversion of `reads_imm` and `reads_lat` on the forms whose sets are
 *     read off the form itself.
 *)
module Stella.Core.Init.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Init
module L = FStar.List.Tot

(** * Arity and the spine cursor *)

val value_count_append (a1 a2: list spine_arg)
  : Lemma (value_count (L.append a1 a2) == value_count a1 + value_count a2)

(** Kind instantiation keeps the arrows of a declared type. *)
val decl_arity_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (decl_arity sg (kinst_ty ks t) == decl_arity sg t)

(** The cursor consumes one arrow of the declared type per value
    argument. *)
val cursor_arity (sg: sig) (t: typ) (th: tsub) (args: list spine_arg)
  : Lemma (requires Some? (cursor sg t th args))
          (ensures (match cursor sg t th args with
                   | Some (t', _) -> decl_arity sg t == value_count args + decl_arity sg t'
                   | None -> True))

(** A saturated remainder has no arrow left. *)
val saturated_arity (sg: sig) (t: typ)
  : Lemma (requires saturated sg t) (ensures decl_arity sg t == 0)

(** A spine the cursor walks has at most the arity's number of value
    arguments. *)
val spine_cursor_arity (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg)
  : Lemma (requires Some? (spine_cursor sg q ks args))
          (ensures (match spine_cursor sg q ks args with
                   | Some (t', _) -> global_arity sg q == Some (value_count args + decl_arity sg t')
                   | None -> True))

(** A saturated spine has exactly the arity's number of value arguments. *)
val spine_saturated_arity (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg)
  : Lemma (requires spine_saturated sg q ks args)
          (ensures global_arity sg q == Some (value_count args))

(** An application the cursor consumes, its head no member, is within the
    spine. *)
val spine_app_cursor (sg: sig) (g: group) (q: qname) (ks: list kind)
                     (args: list spine_arg) (v: exp)
  : Lemma (requires None? (g.gmem q) /\ Some? (spine_cursor sg q ks (L.append args [SVal v])))
          (ensures spine_app sg g (EApp (recompose q ks args) v))

(** A saturated spine applied to one more value argument is a default
    application of its result. *)
val over_applied_default (sg: sig) (g: group) (q: qname) (ks: list kind)
                         (args: list spine_arg) (v: exp)
  : Lemma (requires spine_saturated sg q ks args)
          (ensures not (spine_app sg g (EApp (recompose q ks args) v)) /\
                   default_parts sg g (EApp (recompose q ks args) v) == [recompose q ks args; v])

(** * Inversion *)

(** A form that reads nothing now: a `λ`, a literal, `recordEmpty`,
    `readCell`, `force`, `opaque`. *)
let reads_nothing_now (e: exp) : bool =
  match e with
  | ELam _ _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> true
  | _ -> false

val imm_nothing (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                (d: reads_imm sg g ve je e m)
  : Lemma (requires reads_nothing_now e) (ensures False)

(** A form that holds nothing for later: a literal, `recordEmpty`,
    `readCell`, `force`, `opaque`. *)
let holds_nothing (e: exp) : bool =
  match e with
  | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> true
  | _ -> false

val lat_nothing (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                (d: reads_lat sg g ve je e m)
  : Lemma (requires holds_nothing e) (ensures False)

(** A variable reads now only the member it is. *)
val imm_var (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
            (i: nat) (d: reads_imm sg g ve je e m)
  : Lemma (requires e == EVar i) (ensures vlook ve i == VMem m)

(** A global reads now only the member it is. *)
val imm_global (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
               (q: qname) (ks: list kind) (d: reads_imm sg g ve je e m)
  : Lemma (requires e == EGlobal q ks) (ensures g.gmem q == Some m)

(** The `imm` of an application within a spine is that of its parts: given
    that neither part reads `m` now, neither does the application. *)
val imm_spine_app (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                  (f v: exp)
                  (nf: (reads_imm sg g ve je f m -> Lemma False))
                  (nv: (reads_imm sg g ve je v m -> Lemma False))
                  (d: reads_imm sg g ve je e m)
  : Lemma (requires e == EApp f v /\ spine_app sg g e) (ensures False)

(** The `imm` of `Λ`, a type application, a constraint `Λ` or application,
    `openEff` and `openEffC` is that of its subexpression. *)
val imm_through (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                (b: exp)
                (nb: (reads_imm sg g ve je b m -> Lemma False))
                (d: reads_imm sg g ve je e m)
  : Lemma (requires through e == Some b) (ensures False)

(** The `imm` of `extend`, `update`, `merge` and `inject` is that of its
    parts. *)
val imm_build (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
              (nb: (b: exp{L.memP b (builds e)} -> reads_imm sg g ve je b m -> Lemma False))
              (d: reads_imm sg g ve je e m)
  : Lemma (requires Cons? (builds e)) (ensures False)

(** * Groups of function values *)

(** Every group of function values is initialization-safe: `imm` of a `λ`
    is empty (spec 10 §The rule). *)
val function_group_safe (sg: sig) (g: group)
  : Lemma (requires forall (r: exp). L.memP r g.grhs ==> ELam? r)
          (ensures init_safe sg g)
