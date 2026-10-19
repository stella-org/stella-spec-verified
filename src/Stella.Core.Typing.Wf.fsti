(**
 * Well-formedness of the contexts of the typing relation, and the kinds of
 * the types its rules read from `Σ` (spec 05 §Contexts; design §4.2,
 * §4.4).
 *
 *   - `wf_ctx` is preserved by every extension of a context that a typing
 *     rule makes.
 *   - `octx_ok sg g om`: every type of `Ω` has kind `Type`. Under it an
 *     occurrence has a type of kind `Type`; the `Ω` of a `case` and every
 *     refinement of `Ω` by a dispatch keep it.
 *   - The instance of a global's scheme, the instance of an operation
 *     signature that `perform` reads, and the field types of a constructor
 *     that `switchCtor` reads have kind `Type`.
 *)
module Stella.Core.Typing.Wf
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Kinding.Keys
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot

(** * The lists of `wf_ctx` *)

val tys_ok_nth (sg: sig) (g: ctx) (ts: list typ) (i: nat) (t: typ)
  : Lemma (requires tys_ok sg g ts /\ L.nth ts i == Some t) (ensures check sg g t KType)

val layout_ok_assoc (sg: sig) (g: ctx) (l: layout) (k: key) (t: typ)
  : Lemma (requires layout_ok sg g l /\ L.assoc k l == Some t) (ensures check sg g t KType)

val regions_ok_assoc (sg: sig) (g: ctx) (rs: list (atom & layout)) (a: atom) (l: layout)
  : Lemma (requires regions_ok sg g rs /\ L.assoc a rs == Some l) (ensures layout_ok sg g l)

(** A well-formed layout has structural keys. *)
val layout_ok_keys_struct (sg: sig) (g: ctx) (l: layout)
  : Lemma (requires layout_ok sg g l) (ensures keys_struct (L.map fst l))

(** A layout kinded as a `Row Type` row is well formed. *)
val layout_row_ok (sg: sig) (g: ctx) (l: layout)
  : Lemma (requires check sg g (layout_row l) (KRow EType)) (ensures layout_ok sg g l)

val tys_ok_weaken (sg: sig) (g g': ctx) (ts: list typ)
  : Lemma (requires ctx_ext g g' /\ tys_ok sg g ts) (ensures tys_ok sg g' ts)

val layout_ok_weaken (sg: sig) (g g': ctx) (l: layout)
  : Lemma (requires ctx_ext g g' /\ layout_ok sg g l) (ensures layout_ok sg g' l)

val regions_ok_weaken (sg: sig) (g g': ctx) (rs: list (atom & layout))
  : Lemma (requires ctx_ext g g' /\ regions_ok sg g rs) (ensures regions_ok sg g' rs)

(** * Extending a well-formed context *)

val wf_ctx_push_var (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires wf_ctx sg g /\ check sg g t KType) (ensures wf_ctx sg (push_var g t))

val wf_ctx_push_vars (sg: sig) (g: ctx) (ts: list typ)
  : Lemma (requires wf_ctx sg g /\ tys_ok sg g ts) (ensures wf_ctx sg (push_vars g ts))

val wf_ctx_push_tvar (sg: sig) (g: ctx) (k: kind)
  : Lemma (requires wf_ctx sg g /\ kind_wf g.nk k /\ qkind g.nk k)
          (ensures wf_ctx sg (push_tvar g k))

val wf_ctx_push_tvars (sg: sig) (g: ctx) (ks: list kind)
  : Lemma (requires wf_ctx sg g /\ qkinds_wf g.nk ks) (ensures wf_ctx sg (push_tvars g ks))

(** The type binders of a clause for the operation `op` of `E`. *)
val wf_ctx_clause_binders (sg: sig) (g: ctx) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  : Lemma (requires effects_wf sg /\ wf_ctx sg g /\ sg.effects q == Some ei /\ op_of ei op == Some os)
          (ensures wf_ctx sg (push_tvars g os.binders))

val wf_ctx_add_assump (sg: sig) (g: ctx) (c: constr)
  : Lemma (requires wf_ctx sg g /\ constr_ok sg g c) (ensures wf_ctx sg (add_assump g c))

(** Entering a region whose layout is well formed in `g`, as a layout
    kinded as a `Row Type` row is (`layout_row_ok`). The facts it adds are
    well formed whatever the atom (`wf_hyps_enter_region`), so freshness is
    no condition, and the layout's keys need not be distinct. *)
val wf_ctx_enter_region (sg: sig) (g: ctx) (a: atom) (l: layout)
  : Lemma (requires wf_ctx sg g /\ layout_ok sg g l) (ensures wf_ctx sg (enter_region g a l))

(** * `Ω` *)

(** Every type of `Ω` has kind `Type` in `g`. *)
let rec octx_ok (sg: sig) (g: ctx) (om: octx) : Tot bool (decreases om) =
  match om with
  | [] -> true
  | (_, t) :: om -> check sg g t KType && octx_ok sg g om

val octx_ok_assoc (sg: sig) (g: ctx) (om: octx) (o: occ) (t: typ)
  : Lemma (requires octx_ok sg g om /\ L.assoc o om == Some t) (ensures check sg g t KType)

val octx_ok_weaken (sg: sig) (g g': ctx) (om: octx)
  : Lemma (requires ctx_ext g g' /\ octx_ok sg g om) (ensures octx_ok sg g' om)

val octx_ok_append (sg: sig) (g: ctx) (om1 om2: octx)
  : Lemma (requires octx_ok sg g om1 /\ octx_ok sg g om2) (ensures octx_ok sg g (L.append om1 om2))

(** Occurrence typing gives a type of kind `Type`. A record field takes
    the payload type its rule writes and kinds. *)
val occ_typing_regular (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t)
  : Lemma (requires octx_ok sg g om) (ensures check sg g t KType)

(** The `Ω` of the scrutinees of a `case`. *)
val octx_ok_scrut_occs (sg: sig) (g: ctx) (i: nat) (ts: list typ)
  : Lemma (requires tys_ok sg g ts) (ensures octx_ok sg g (scrut_occs i ts))

(** The refinement of a `switchKey` branch, `o ? k ↦ τ`. *)
val octx_ok_key_branch (sg: sig) (g: ctx) (om: octx) (o: occ) (k: key) (pt: typ)
  : Lemma (requires octx_ok sg g om /\ check sg g pt KType)
          (ensures octx_ok sg g ((OVariant o k, pt) :: om))

(** The refinement of a `switchKey` default, `o ↦ Variant ρ'`. *)
val octx_ok_key_default (sg: sig) (g: ctx) (om: octx) (o: occ) (vr': typ)
  : Lemma (requires prim_wf sg /\ octx_ok sg g om /\ check sg g vr' (KRow EType))
          (ensures octx_ok sg g ((o, t_variant vr') :: om))

(** * Instances read from `Σ` *)

(** `M.x [[κ̄]]` has a type of kind `Type`. *)
val check_global_inst (sg: sig) (g: ctx) (q: qname) (ks: list kind) (n: nat) (t: typ)
  : Lemma (requires sig_wf sg /\ global_type sg q == Some (n, t) /\ L.length ks == n /\
                    qkinds_wf g.nk ks)
          (ensures check sg g (kinst_ty ks t) KType)

(** The argument and the result type of `perform k.op [σ̄]` on an element
    `E τ̄`, `τ̄` kinded at `E`'s parameters and `σ̄` at the operation's
    binders. *)
val check_op_inst (sg: sig) (g: ctx) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  (ts ss: list typ)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os /\
                    check_tys sg g ts ei.eff_params /\ check_tys sg g ss os.binders)
          (ensures check sg g (op_inst ts ss os.arg) KType /\ check sg g (op_inst ts ss os.res) KType)

(** The fields `τ̄[ā := σ̄]` of a constructor `c` of `T`, at an instance
    `T [[κ̄]] σ̄` of kind `Type`, have kind `Type`: the scheme of `c` binds
    `T`'s parameters at their kinds (`Stella.Core.Sig.Wf.ctor_ok`). *)
val ctor_fields_ok (sg: sig) (g: ctx) (tq: qname) (ks: list kind) (ss: list typ) (cs: list qname)
  (c: qname) (fs: list typ)
  : Lemma (requires sig_ok sg /\ check sg g (tapps (TCon tq ks) ss) KType /\
                    has_class sg tq (TcData cs) /\ L.mem c cs /\ ctor_fields sg c ks ss == Some fs)
          (ensures tys_ok sg g fs)

(** The refinement of a `switchCtor` branch, `o ! Ctor . j ↦ τ_j`. *)
val octx_ok_ctor_branch (sg: sig) (g: ctx) (om: octx) (o: occ) (tq: qname) (ks: list kind)
  (ss: list typ) (cs: list qname) (c: qname) (fs: list typ)
  : Lemma (requires sig_ok sg /\ octx_ok sg g om /\
                    check sg g (tapps (TCon tq ks) ss) KType /\ has_class sg tq (TcData cs) /\
                    L.mem c cs /\ ctor_fields sg c ks ss == Some fs)
          (ensures octx_ok sg g (L.append (field_occs o c 0 fs) om))
