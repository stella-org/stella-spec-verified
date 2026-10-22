(**
 * Typing is preserved by kind instantiation (design §1.2, §2.3; spec 01
 * §Kind schemes; spec 06 §The global environment).
 *
 * `kinst ks` instantiates the kind variables of `Γ` with the kinds `ks`,
 * well-formed quantifiable kinds under `nk'` kind variables
 * (`Stella.Core.Kinding.Subst.kinst_ok`). It acts on every kind and type
 * of the judgement: the context (`kinst_ctx ks nk'`), the term
 * (`kinst_exp`), its type and its row, `Δ` (`kinst_jctx`) and `Ω`
 * (`kinst_octx`). The theorems assume `sig_ok`; the context needs no
 * well-formedness.
 *
 *   - Kinding is preserved by `Stella.Core.Kinding.Subst.check_kinst`, and
 *     entailment by `Stella.Core.Entail.Lemmas.entails_kinst`.
 *   - A global `M.x [[κ̄]]` has the type `σ[k̄ := κ̄]` of its scheme
 *     `forall k̄. σ`, whose kind variables are its own, so the instance at
 *     `κ̄`, instantiated, is the instance at the instantiated kinds
 *     (`Stella.Core.Spine.Lemmas.kinst_ty_comp`). The same holds of the
 *     fields of a constructor at the kinds of its data type, and of the
 *     cursor of a chain (`Stella.Core.Spine.Lemmas.chain_cursor_kinst`).
 *   - The signatures of operations and the parameters of effects mention
 *     no kind variable, so they are fixed, and so are the closed types of
 *     `force`, `fill` and `region⟨a⟩` (`check_closed_kinst`).
 *   - The facts a region adds name the type variables of kind
 *     `Row Effect`. Instantiating a kind variable can give a type variable
 *     that kind, so the instance of the context of a region body has at
 *     most the facts of the region entered in the instantiated context,
 *     which typing is weakened to (`Stella.Core.Typing.Weaken`).
 *   - Initialization safety reads no kind
 *     (`Stella.Core.Typing.Kinst.Init`), and the value forms, the values
 *     and the value at an occurrence are kept
 *     (`Stella.Core.Typing.Kinst.Facts`).
 *
 * The unfolding of a global (`typing_global_unfold`) instantiates a
 * definition typed in its declaration context with closed regions in
 * scope (`decl_rctx`), and carries the instance, a value, into any
 * well-formed context with those regions, under any `Δ` and at any kinded
 * row.
 *)
module Stella.Core.Typing.Kinst
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Tm
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Instantiating the contexts of the judgement *)

(** `Ω` with its types instantiated. *)
let rec kinst_octx (ks: list kind) (om: octx) : Tot octx (decreases om) =
  match om with
  | [] -> []
  | (o, t) :: om -> (o, kinst_ty ks t) :: kinst_octx ks om

(** A join point's signature instantiated. *)
let kinst_jt (ks: list kind) (jt: list typ & typ & typ) : list typ & typ & typ =
  match jt with
  | (ts, t, r) -> (kinst_tys ks ts, kinst_ty ks t, kinst_ty ks r)

(** `Δ` with its types instantiated. *)
let rec kinst_jctx (ks: list kind) (d: jctx) : Tot jctx (decreases d) =
  match d with
  | [] -> []
  | jt :: d -> kinst_jt ks jt :: kinst_jctx ks d

(** * The judgements *)

val occ_typing_kinst (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (ks: list kind) (nk': nat)
  : Pure (occ_typing sg (kinst_ctx ks nk' g) (kinst_octx ks om) o (kinst_ty ks t))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

val typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (ks: list kind) (nk': nat)
  : Pure (typing sg ln (kinst_ctx ks nk' g) (kinst_jctx ks d) (kinst_exp ks e) (kinst_ty ks t)
            (kinst_ty ks r))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

val exps_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d r es ts) (ks: list kind) (nk': nat)
  : Pure (exps_typing sg ln (kinst_ctx ks nk' g) (kinst_jctx ks d) (kinst_ty ks r)
            (kinst_exps ks es) (kinst_tys ks ts))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

val chain_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (ks: list kind) (nk': nat)
  : Pure (chain_typing sg ln (kinst_ctx ks nk' g) (kinst_jctx ks d) (kinst_ty ks r) (kinst_exp ks e))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

val binds_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (ks: list kind) (nk': nat)
  : Pure (binds_typing sg ln (kinst_ctx ks nk' g) (kinst_binds ks bs))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

val cells_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (ks: list kind) (nk': nat)
  : Pure (cells_typing sg ln (kinst_ctx ks nk' g) (kinst_cells ks cells) (kinst_layout ks lay))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

val match_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om) (ks: list kind) (nk': nat)
  : Pure (match_typing sg ln (kinst_ctx ks nk' g) (kinst_jctx ks d) (kinst_ty ks r)
            (kinst_exps ks th) (kinst_octx ks om))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

val dt_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d om dt t r) (ks: list kind) (nk': nat)
  : Pure (dt_typing sg ln (kinst_ctx ks nk' g) (kinst_jctx ks d) (kinst_octx ks om)
            (kinst_dt ks dt) (kinst_ty ks t) (kinst_ty ks r))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

(** The branches of a `switchCtor` at `T [[κ̄]] σ̄`. A constructor of `T`
    has as many kind variables as `κ̄` has kinds, which the kinding premise
    of `TD_SwitchCtor` gives. *)
val ctor_brs_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kl: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ)
  (h: ctor_brs_typing sg ln g d om o kl ss cs bs t r) (ks: list kind) (nk': nat)
  : Pure (ctor_brs_typing sg ln (kinst_ctx ks nk' g) (kinst_jctx ks d) (kinst_octx ks om) o
            (kinst_kinds ks kl) (kinst_tys ks ss) cs (kinst_brs ks bs) (kinst_ty ks t)
            (kinst_ty ks r))
         (requires sig_ok sg /\ kinst_ok ks nk' g /\
                   (forall (c: qname). L.mem c cs ==>
                      (match sg.ctors c with Some ci -> L.length kl == ci.ct_nk | None -> False)))
         (ensures fun _ -> True)

val lit_brs_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (ks: list kind) (nk': nat)
  : Pure (lit_brs_typing sg ln (kinst_ctx ks nk' g) (kinst_jctx ks d) (kinst_octx ks om)
            (kinst_ty ks lt) (kinst_brs ks bs) (kinst_ty ks t) (kinst_ty ks r))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

val key_brs_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (ks: list kind) (nk': nat)
  : Pure (key_brs_typing sg ln (kinst_ctx ks nk' g) (kinst_jctx ks d) (kinst_octx ks om) o
            (kinst_layout ks kts) (kinst_brs ks bs) (kinst_ty ks t) (kinst_ty ks r))
         (requires sig_ok sg /\ kinst_ok ks nk' g)
         (ensures fun _ -> True)

(** The clauses of a handler of `E τ̄`, `E` being the effect `q` of `Σ`,
    whose operation signatures mention no kind variable. *)
val clauses_typing_kinst (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause)
  (h: clauses_typing sg ln g ei ts r b cs) (q: qname) (ks: list kind) (nk': nat)
  : Pure (clauses_typing sg ln (kinst_ctx ks nk' g) ei (kinst_tys ks ts) (kinst_ty ks r)
            (kinst_ty ks b) (kinst_cls ks cs))
         (requires sig_ok sg /\ kinst_ok ks nk' g /\ sg.effects q == Some ei)
         (ensures fun _ -> True)

(** * Unfolding a global *)

(** The context a definition of `Σ` with `nk` kind variables is typed in
    at run time: its declaration context with the regions `rs` of `Γ_R`
    in scope, which a value installed at link time may mention, in a region
    frame or in the type of a location it forces. `decl_rctx nk []` is
    `decl_ctx nk`. *)
let decl_rctx (nk: nat) (rs: list (atom & layout)) : ctx = { decl_ctx nk with regions = rs }

(** A definition `v : σ` typed in `decl_rctx nk rs`, instantiated at
    kinds `κ̄` of `nk'` kind variables. The layouts of `rs` are closed,
    well formed in `closed_ctx rs` (`wf_ctx sg (closed_ctx rs)`, which
    `Stella.Core.Typing.Runtime.rctx_ok_wf_ctx` gives), so the instantiation
    fixes them (`Stella.Core.Typing.Aux.Lemmas.check_closed_kinst`). *)
val typing_decl_kinst (#sg: sig) (#ln: lctx) (#nk: nat) (#rs: list (atom & layout))
  (#v: exp) (#t: typ)
  (h: typing sg ln (decl_rctx nk rs) [] v t TRowEmpty) (ks: list kind) (nk': nat)
  : Pure (typing sg ln (decl_rctx nk' rs) [] (kinst_exp ks v) (kinst_ty ks t) TRowEmpty)
         (requires sig_ok sg /\ L.length ks == nk /\ qkinds_wf nk' ks /\
                   wf_ctx sg (closed_ctx rs))
         (ensures fun _ -> True)

(** The unfolding `M.x [[κ̄]] → v[k̄ := κ̄]` (spec 06 §The global
    environment): the definition `v : σ`, a value typed in
    `decl_rctx nk rs`, gives `v[k̄ := κ̄] : σ[k̄ := κ̄]` in every
    well-formed context `g` whose kind variables the kinds `κ̄` are formed
    under and which has the regions of `rs` with their layouts
    (`layouts_ext`): the regions in scope at the unfolding may extend those
    at the definition. It stands under any `Δ` and at any kinded ambient
    row `r`.

    The instance mentions no type variable, term variable or hypothesis,
    so the identity type renaming carries it into `g`
    (`Stella.Core.Typing.Rename.Ty`); it is a value
    (`Stella.Core.Typing.Kinst.Facts.is_value_kinst`), retyped at `Δ` and
    `r` (`Stella.Core.Typing.Values.value_typing`). *)
val typing_global_unfold (#sg: sig) (#ln: lctx) (#nk: nat) (#rs: list (atom & layout))
  (#v: exp) (#t: typ)
  (h: typing sg ln (decl_rctx nk rs) [] v t TRowEmpty) (ks: list kind) (g: ctx) (d: jctx)
  (r: typ)
  : Pure (typing sg ln g d (kinst_exp ks v) (kinst_ty ks t) r)
         (requires sig_ok sg /\ wf_ctx sg g /\ L.length ks == nk /\ qkinds_wf g.nk ks /\
                   V.is_value sg v /\ wf_ctx sg (closed_ctx rs) /\
                   layouts_ext (closed_ctx rs) g /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True)
