(**
 * Normalizing the derivation of an application chain (spec 05 §Typing a
 * chain).
 *
 * `T_Global`, `T_App`, `T_TyApp` and `T_CApp` apply to the nodes of a
 * chain headed by a constructor or a foreign as well as `T_Chain` does,
 * and `T_Conv` may stand anywhere in between. Every derivation of such a
 * chain whose cursor `⟨ σ ; θ ⟩` is defined is re-derived node by node as
 * `chain_typing`, at the same ambient row and under `Δ = []`, under which
 * the rules type the subterms of a chain, and its type is `θ(σ)` up to type
 * equality (`chain_normal`). A value argument keeps its derivation,
 * converted to the instance `θ(τ1)` of the domain it meets.
 *
 * A constructor chain always has a defined cursor once it is typed: a
 * constructor's remainders are `forall`s, pure arrows and, once saturated,
 * an instance `T [[κ̄]] σ̄` of its data type, which is no function type, no
 * `forall` and no constrained type (`ty_eq_tapps_inv`). A foreign's
 * remainder can be a type variable that the accumulated substitution
 * turns into an arrow; applying the chain there is an ordinary
 * application, and the cursor is undefined.
 *)
module Stella.Core.Typing.Chain
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Type equality of applications *)

(** Pointwise type equality. *)
let rec tys_eq (ts ts': list typ) : Tot bool (decreases ts) =
  match ts, ts' with
  | [], [] -> true
  | t :: ts, t' :: ts' -> ty_eq t t' && tys_eq ts ts'
  | _ -> false

(** Two applications of type constructors are equal exactly when the
    constructors, their kinds and, pointwise, their arguments are. *)
val ty_eq_tapps_inv (q q': qname) (ks ks': list kind) (ss ss': list typ)
  : Lemma (requires ty_eq (tapps (TCon q ks) ss) (tapps (TCon q' ks') ss'))
          (ensures q == q' /\ ks == ks' /\ tys_eq ss ss')

(** An application of a type constructor is no `forall` and no constrained
    type. *)
val ty_eq_tapps_binder (q: qname) (ks: list kind) (ss: list typ) (t: typ)
  : Lemma (requires TForall? t \/ TConstr? t) (ensures ~(ty_eq (tapps (TCon q ks) ss) t))

(** * Chains *)

(** `e` is a chain headed by a data constructor. *)
let ctor_headed (sg: sig) (e: exp) : bool =
  match decompose_global_app e with
  | Some (q, _, _) -> is_ctor sg q
  | None -> false

(** The ambient row of a typed chain converts like that of any computation:
    each value argument is converted to the new row. *)
val chain_typing_conv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r1: typ) (#e: exp)
  (hc: chain_typing sg ln g d r1 e) (r2: typ)
  : Pure (chain_typing sg ln g d r2 e)
         (requires sig_ok sg /\ ty_eq r1 r2 /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True)

(** Chain normalization: a typed chain headed by a constructor or a
    foreign, whose cursor is defined, or headed by a constructor, is typed
    by `chain_typing` at its row under `Δ = []`, its cursor is defined,
    and its type is the instance of the cursor up to type equality. *)
val chain_normal (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r)
  : Pure (chain_typing sg ln g [] r e)
         (requires sig_ok sg /\ Some? (decompose_global_app e) /\
                   (Some? (chain_cursor sg e) \/ ctor_headed sg e))
         (ensures fun _ ->
           match chain_cursor sg e with
           | Some (s, th) -> ty_eq t (sub_ty th s)
           | None -> False)

(** The same, as a statement: the derivation exists. *)
val chain_normal_exists (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r)
  : Lemma (requires sig_ok sg /\ Some? (decompose_global_app e) /\
                    (Some? (chain_cursor sg e) \/ ctor_headed sg e))
          (ensures (exists (hc: chain_typing sg ln g [] r e). True) /\
                   (match chain_cursor sg e with
                    | Some (s, th) -> ty_eq t (sub_ty th s)
                    | None -> False))

(** A run-time value headed by a global is a chain that normalizes: a
    constructor chain, or a foreign chain whose cursor is defined. *)
val value_chain_normalizes (sg: sig) (e: exp)
  : Lemma (requires V.value_head sg e)
          (ensures Some? (decompose_global_app e) /\
                   (Some? (chain_cursor sg e) \/ ctor_headed sg e))
