(**
 * The value arguments of a typed chain, and the fields of a saturated
 * constructor chain (spec 05 §Typing a chain, §Join points and decision
 * trees).
 *
 * `chain_typing` types each value argument at the instance of the domain
 * of the arrow it meets, so the value arguments of a typed chain are typed
 * pointwise against the domains its cursor collects
 * (`Stella.Core.Spine.Lemmas.chain_domains`). For a saturated constructor
 * chain `C [[κ̄]] [σ̄] v̄` of the data type `T` those domains are the fields
 * `ctor_fields C κ̄ σ̄` that a `switchCtor` branch on `C` adds to `Ω` for an
 * occurrence of type `T [[κ̄]] σ̄`, and the `j`-th value argument, the value
 * at `o ! C . j` (`ctor_field`), has the `j`-th field type.
 *)
module Stella.Core.Typing.Ctor
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Rows
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Chain
module L = FStar.List.Tot

(** * Lists of typed terms *)

val exps_typing_length (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts)
  : Lemma (L.length es == L.length ts)

val exps_typing_snoc (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (#e: exp) (#t: typ)
  (h: exps_typing sg ln g d r es ts) (h1: typing sg ln g d e t r)
  : exps_typing sg ln g d r (L.append es [e]) (L.append ts [t])

(** The `j`-th term of a typed list has the `j`-th type. *)
val exps_typing_nth (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (j: nat) (e: exp) (t: typ)
  : Pure (typing sg ln g d e t r)
         (requires L.nth es j == Some e /\ L.nth ts j == Some t)
         (ensures fun _ -> True)

(** * Chains *)

(** The value arguments of a typed chain have the domains its cursor
    meets, at the ambient row of the chain, under its `Δ`. *)
val chain_typing_domains (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (hc: chain_typing sg ln g d r e)
  : exps_typing sg ln g d r (chain_value_args e) (chain_domains sg e)

(** A saturated constructor chain `C [[κ̄]] [σ̄] v̄` has the type
    `T [[κ̄]] σ̄`, `T` the owner of `C`; it has `ct_arity` value arguments,
    and they have the field types `ctor_fields C κ̄ σ̄`. *)
val ctor_chain_fields_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (hc: chain_typing sg ln g d r e) (c: qname) (ks: list kind) (args: list spine_arg)
  (ci: ctor_info) (t: typ) (th: tsub) (fs: list typ)
  : Pure (exps_typing sg ln g d r (value_args args) fs)
         (requires sig_ok sg /\ decompose_global_app e == Some (c, ks, args) /\
                   sg.ctors c == Some ci /\ chain_cursor sg e == Some (t, th) /\ saturated sg t /\
                   ctor_fields sg c ks (ty_args args) == Some fs)
         (ensures fun _ ->
           sub_ty th t == tapps (TCon ci.ct_owner ks) (ty_args args) /\
           L.length fs == ci.ct_arity /\ L.length (value_args args) == ci.ct_arity)

(** The fields of a saturated constructor chain exist: they are the
    domains of its cursor. *)
val ctor_chain_fields (sg: sig) (e: exp) (c: qname) (ks: list kind) (args: list spine_arg)
  (ci: ctor_info) (t: typ) (th: tsub)
  : Lemma (requires sig_ok sg /\ decompose_global_app e == Some (c, ks, args) /\
                    sg.ctors c == Some ci /\ chain_cursor sg e == Some (t, th) /\ saturated sg t)
          (ensures ctor_fields sg c ks (ty_args args) == Some (chain_domains sg e))

(** * Lists of typed terms up to type equality *)

(** Each term converted to a type equal to its own, kinded. *)
val exps_typing_conv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (ts': list typ)
  : Pure (exps_typing sg ln g d r es ts')
         (requires tys_eq ts ts' /\ tys_ok sg g ts' /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True)

(** * Constructor chains at a data type *)

(** A remainder whose instance is a data type `T [[κ̄]] σ̄` up to type
    equality is saturated: the instance of a `forall`, a constrained type
    or a function type is none. *)
val saturated_of_data (sg: sig) (s: typ) (th: tsub) (tq: qname) (ks: list kind) (ss: list typ)
  (cs: list qname)
  : Lemma (requires prim_wf sg /\ has_class sg tq (TcData cs) /\
                    ty_eq (sub_ty th s) (tapps (TCon tq ks) ss))
          (ensures saturated sg s)

(** The fields of a constructor at pointwise equal type arguments are
    pointwise equal, and one instance exists when the other does. *)
val ctor_fields_tys_eq (sg: sig) (c: qname) (ks: list kind) (ss ss': list typ)
  : Lemma (requires sig_ok sg /\ tys_eq ss ss' /\ Some? (ctor_fields sg c ks ss))
          (ensures (match ctor_fields sg c ks ss, ctor_fields sg c ks ss' with
                    | Some fs, Some fs' -> tys_eq fs fs'
                    | _ -> False))

(** A value `C [[κ̄]] [σ̄] v̄` typed at an occurrence type `T [[κ̄']] σ̄'`, `C` a
    constructor of the data type `T`, as `switchCtor` reads it: whatever
    rules derive its type, `C` is owned by `T`, `κ̄ = κ̄'`, and the value
    arguments `v̄` have the fields `ctor_fields C κ̄' σ̄'` that the branch on
    `C` adds to `Ω`, at the row of the value, under `Δ = []`. *)
val ctor_value_fields_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp)
  (#t_o #r: typ) (h: typing sg ln g d v t_o r) (c: qname) (ks: list kind)
  (args: list spine_arg) (tq: qname) (ks': list kind) (ss': list typ) (cs: list qname)
  (fs': list typ)
  : Pure (exps_typing sg ln g [] r (value_args args) fs')
         (requires sig_ok sg /\ decompose_global_app v == Some (c, ks, args) /\ is_ctor sg c /\
                   ty_eq t_o (tapps (TCon tq ks') ss') /\
                   check sg g (tapps (TCon tq ks') ss') KType /\
                   has_class sg tq (TcData cs) /\ L.mem c cs /\
                   ctor_fields sg c ks' ss' == Some fs')
         (ensures fun _ ->
           ks == ks' /\ (Some?.v (sg.ctors c)).ct_owner == tq /\
           L.length fs' == L.length (value_args args))
