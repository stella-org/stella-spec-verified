(**
 * The global environment `G`, faults, stores and configurations, and the
 * conformance of `G` to `Σ` (spec 06 §Reduction, §The global environment,
 * §Faults, §Conformance of the global environment).
 *
 * ## The environment
 *
 * `G` holds, for each top-level value `M.x`, its definition `v`, and for
 * each foreign `M.f`, its implementation `δ_f` and its ABI precondition.
 * The scheme of a definition is read from `Σ` (`sg.values`), so `G` holds
 * terms, functions and predicates only.
 *
 * Spec 06 §The global environment lists every data constructor `M.Ctor`
 * in `G` as well. Here a constructor has no entry: it has nothing to
 * unfold to and no implementation, a chain headed by one is a value as it
 * stands, and `Σ` records it. So coverage asks nothing of a constructor
 * (`covered`), where condition (1) of the spec asks that linking supplied
 * it.
 *
 * An implementation receives `values(ᾱ)`, the value arguments of the chain
 * and nothing else: kind, type and constraint arguments are erased, so it
 * cannot depend on them. It is a function of those values, which is what
 * being Core-modelled asks: the outcome is determined by the arguments and
 * is the whole of what a call does. `G` is therefore Core-modelled by
 * construction, and the conformance stated here is that of a Core-modelled
 * environment: an implementation whose outcome depends on state, which
 * the general conformance of spec 06 admits, is not represented. Because an implementation is a total
 * function returning an outcome, a call terminates and is atomic by
 * construction: it is one step, to the outcome the function gives. The
 * clause of condition (3) on termination needs no counterpart here, and
 * neither does the purpose of the clause on applying no Stella function
 * value, which is that the step be atomic. The clause itself is not
 * expressed: a total function may return a term built from a `λ` among its
 * arguments.
 *
 * ## Three obligations
 *
 * A saturated foreign call `M.f [[κ̄]] ᾱ`, with `v̄ = values(ᾱ)`, involves
 * three things, which bind different parties (spec 06 §Chains of a
 * constructor or a foreign, §Conformance of the global environment):
 *
 *   - `gpre M.f v̄`, the ABI precondition of `M.f` on `v̄`, given
 *     independently of the implementation. Respecting it is the program's
 *     obligation (`Stella.Core.Semantics.Step.pre_ok`). The rule for a
 *     saturated chain takes it as a premise, so a call outside it has no
 *     step;
 *   - `gimpl M.f = Some f` with `f v̄ = Some o`, `o` conforming, at every
 *     typed call inside `gpre`: condition (3), the implementer's obligation
 *     (`genv_ok`). That a foreign the program mentions has an
 *     implementation at all is also coverage (`covers`);
 *   - `f v̄ = None` is semantic partiality: the relation gives the call no
 *     step, as it gives none where `G` is not Core-modelled. Under
 *     `genv_ok` it happens only outside `gpre` or at a call that is not
 *     typed. Neither the rule nor condition (3) reads `f` outside `gpre`.
 *
 * ## Faults
 *
 * A fault is either the initialization fault `φ_init` (`FInit`), which only
 * forcing an `Evaluating` cell produces, or an ABI fault (`FAbi`), which
 * only a foreign produces. A foreign returns an `abi_fault`, so it cannot
 * produce `φ_init`. The payload of an ABI fault is opaque: Core records
 * only that a fault is a possible outcome (spec 06 §Faults).
 *
 * ## Conformance
 *
 * `genv_ok sg ln rs G` is `Σ; Γ_N ⊨ G` at `Γ_R = rs` and `Γ_N = ln`
 * (spec 06 §Conformance of the global environment), as three conditions:
 *
 *   (1) every name a definition of `G` mentions is covered by `G`
 *       (`covers`). That the term under evaluation is covered is a premise
 *       of the theorems, not part of `genv_ok`;
 *   (2) each definition `v` of a value `M.x : forall k̄. σ` of `Σ` is a
 *       value, typed `k̄; ·; · ⊢ v : σ ! ()` with the regions `rs` in scope
 *       (`decl_rctx`), which is how the unfolding is typed
 *       (`Stella.Core.Typing.Kinst.typing_global_unfold`);
 *   (3) for every extension `rs'`, `ln'` of `rs`, `ln` (`layouts_ext`,
 *       `lctx_incl`) that is well formed, and every saturated chain of
 *       values of a foreign `M.f` typed under `rs'` and `ln'` at its cursor
 *       instance `θ(σ)`, at `Δ = ·` and row `()`, whose values `v̄` satisfy
 *       `gpre M.f v̄`: `δ_f` exists, `δ_f(v̄)` returns an outcome, and the
 *       outcome is an ABI fault or a value of type `θ(σ)` under the same
 *       `rs'` and `ln'`; and where `Σ` records `#observ(none)` for `M.f`,
 *       not a fault. Where `gpre M.f v̄` fails, (3) asks nothing (spec 06
 *       §An ABI precondition is where condition (3) stops asking).
 *
 * The spec quantifies (3) over every well-formed `Γ_R` and `Γ_N`; here it
 * ranges over the extensions of the contexts `genv_ok` is stated at, the
 * contexts every later configuration stands under. At `rs = []` and
 * `ln = []` every well-formed pair is such an extension, so
 * `genv_ok sg [] [] G` is conformance before any region or location
 * exists, the spec's `Σ ⊨ G` for a Core-modelled `G`, and it implies
 * `genv_ok` at every pair of contexts (`genv_ok_closed`). The spec's
 * "δ_f(v̄) is defined" where the ABI preconditions hold is the outer and
 * the inner `Some` together wherever `gpre` holds.
 *
 * Conformance is stable under extending `Γ_R` with the layouts kept and
 * `Γ_N` with the types of its locations kept (`genv_ok_ext`): a definition
 * typed under fewer regions and locations is typed under more, and (3)
 * quantifies over extensions.
 *)
module Stella.Core.Semantics.Env
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Weaken
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Kinst
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Faults and outcomes (spec 06 §Faults) *)

(** A fault the ABI specifies, with a payload Core does not interpret. *)
type abi_fault =
  | AbiFault : payload:nat -> abi_fault

(** What an implementation `δ_f` returns on a call: a value, or an ABI
    fault. The type does not constrain the term of `FOVal` to be a value;
    condition (3) of `genv_ok` does, for a typed call inside `gpre`, and
    nothing else does. *)
type foreign_outcome =
  | FOVal   : exp -> foreign_outcome
  | FOFault : abi_fault -> foreign_outcome

(** `φ`: the initialization fault `φ_init`, or an ABI fault. *)
type fault =
  | FInit : fault
  | FAbi  : abi_fault -> fault

(** * Stores and configurations (spec 06 §Reduction) *)

(** A by-need cell `s ::= Suspended e | Evaluating | Ready v`. *)
type cell =
  | Suspended  : exp -> cell
  | Evaluating : cell
  | Ready      : exp -> cell

(** `N`: the cell of location `ν` is at position `ν`, as in `Γ_N`
    (design §4.5), so allocation appends. *)
type store = list cell

(** `c ::= e | fault φ` *)
type config =
  | CTerm  : exp -> config
  | CFault : fault -> config

(** The configuration an outcome of `δ_f` is. *)
let foreign_config (o: foreign_outcome) : config =
  match o with
  | FOVal v -> CTerm v
  | FOFault phi -> CFault (FAbi phi)

(** * The global environment (spec 06 §The global environment) *)

(** `G`: the definition of each top-level value; the implementation of
    each foreign, a function of the value arguments of a chain; and the ABI
    precondition of each foreign on those values. `gpre` is given apart
    from `gimpl` and constrains it only through condition (3) of
    `genv_ok`. Constructors have no entry (spec 06 lists them in `G`; see
    the module header). *)
noeq type genv = {
  gvals : qname -> option exp;
  gimpl : qname -> option (list exp -> option foreign_outcome);
  gpre  : qname -> list exp -> prop;
}

(** `M.x : forall k̄. σ` among the top-level values of `Σ`, for a name that
    `Σ` records among the values alone, as `global_type` and
    `global_scheme` classify names. *)
let value_scheme (sg: sig) (q: qname) : option value_info =
  match sg.ctors q, sg.foreigns q, sg.values q with
  | None, None, Some vi -> Some vi
  | _ -> None

(** `q` is a foreign of `Σ`. *)
let is_foreign (sg: sig) (q: qname) : bool =
  match global_scheme sg q with
  | Some (GForeign, _, _) -> true
  | _ -> false

(** * Every node of a term *)

(** `exp_all p e`: `p` holds at every term node of `e`, decision trees,
    handlers, `letrec` members and region cells included. *)
let rec exp_all (p: exp -> bool) (e: exp) : Tot bool (decreases e) =
  p e &&
  (match e with
   | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> true
   | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
   | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
   | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
   | EOpenEffC _ b | EFill _ b ->
     exp_all p b
   | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
   | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
     exp_all p e1 && exp_all p e2
   | ELetRec bs b -> exp_all_binds p bs && exp_all p b
   | ECase es dt -> exp_all_exps p es && exp_all_dt p dt
   | EMatch th dt -> exp_all_exps p th && exp_all_dt p dt
   | EJump _ es -> exp_all_exps p es
   | EHandle b h -> exp_all p b && exp_all p h.h_ret && exp_all_cls p h.h_clauses
   | ERegion _ es b -> exp_all_exps p es && exp_all p b
   | ERegionOpen _ th b -> exp_all_cells p th && exp_all p b)

and exp_all_exps (p: exp -> bool) (es: list exp) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> exp_all p e && exp_all_exps p es

and exp_all_binds (p: exp -> bool) (bs: list (typ & exp)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, e) :: bs -> exp_all p e && exp_all_binds p bs

and exp_all_cells (p: exp -> bool) (th: list (key & exp)) : Tot bool (decreases th) =
  match th with
  | [] -> true
  | (_, e) :: th -> exp_all p e && exp_all_cells p th

and exp_all_dt (p: exp -> bool) (dt: dtree) : Tot bool (decreases dt) =
  match dt with
  | DLeaf e -> exp_all p e
  | DBind _ dt -> exp_all_dt p dt
  | DSwitchCtor _ bs df -> exp_all_brs p bs && exp_all_odt p df
  | DSwitchLit _ bs df -> exp_all_brs p bs && exp_all_dt p df
  | DSwitchKey _ bs df -> exp_all_brs p bs && exp_all_odt p df
  | DGuard e dt1 dt2 -> exp_all p e && exp_all_dt p dt1 && exp_all_dt p dt2

and exp_all_odt (p: exp -> bool) (df: option dtree) : Tot bool (decreases df) =
  match df with
  | None -> true
  | Some dt -> exp_all_dt p dt

and exp_all_brs (#lb: eqtype) (p: exp -> bool) (bs: list (lb & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, dt) :: bs -> exp_all_dt p dt && exp_all_brs p bs

and exp_all_cls (p: exp -> bool) (cs: list clause) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | CFull _ _ _ _ b :: cs -> exp_all p b && exp_all_cls p cs
  | CFast _ _ _ b :: cs -> exp_all p b && exp_all_cls p cs

(** * Coverage (spec 06 §Conformance, condition (1)) *)

(** A node is covered by `G`: a reference to a top-level value of `Σ` has
    a definition, and a reference to a foreign an implementation. A
    constructor needs nothing, since `G` has no entry for one where spec 06
    lists `M.Ctor`, and a name `Σ` does not classify heads no typed term. *)
let covered (sg: sig) (gi: genv) (e: exp) : bool =
  match e with
  | EGlobal q _ ->
    (if Some? (value_scheme sg q) then Some? (gi.gvals q) else true) &&
    (if is_foreign sg q then Some? (gi.gimpl q) else true)
  | _ -> true

(** `G` covers every global name occurring anywhere in `e`. *)
let covers (sg: sig) (gi: genv) (e: exp) : bool = exp_all (covered sg gi) e

let covers_dt (sg: sig) (gi: genv) (dt: dtree) : bool = exp_all_dt (covered sg gi) dt

(** * Conformance (spec 06 §Conformance of the global environment) *)

(** `Γ; · ⊢ e : τ ! ()` under `Γ_N = ln` has a derivation. *)
let typed (sg: sig) (ln: lctx) (g: ctx) (e: exp) (t: typ) : prop =
  exists (h: typing sg ln g [] e t TRowEmpty). True

(** (1) Every definition of `G` is covered by `G`. *)
let gvals_covered (sg: sig) (gi: genv) : prop =
  forall (q: qname). {:pattern gi.gvals q}
    (match gi.gvals q with
     | Some v -> covers sg gi v
     | None -> True)

(** The definition of the value `q`, if `Σ` records `q` as a value and `G`
    defines it, is a value of its declared scheme, typed in its declaration
    context with the regions `rs` in scope, under `Γ_N = ln`, at `Δ = ·` and
    row `()`. *)
let gval_typed (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) (q: qname) : prop =
  match sg.values q, gi.gvals q with
  | Some vi, Some v -> V.is_value sg v /\ typed sg ln (decl_rctx vi.vl_nk rs) v vi.vl_ty
  | _ -> True

(** (2) Every definition of a value of `Σ` is typed (`gval_typed`). *)
let gvals_typed (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) : prop =
  forall (q: qname). {:pattern gval_typed sg ln rs gi q} gval_typed sg ln rs gi q

(** `#observ(none)` is recorded for `q`. *)
let observ_none (sg: sig) (q: qname) : bool =
  match sg.foreigns q with
  | Some fi -> fi.fr_observ_none
  | None -> false

(** An outcome of `δ_q` conforms at `τ` under `rs` and `ln`: an ABI fault,
    unless `q` is `#observ(none)`, or a value of type `τ` at `Δ = ·` and
    row `()`. *)
let outcome_ok (sg: sig) (ln: lctx) (rs: list (atom & layout)) (q: qname) (t: typ)
  (o: foreign_outcome) : prop =
  match o with
  | FOFault _ -> ~(observ_none sg q)
  | FOVal v -> V.is_value sg v /\ typed sg ln (closed_ctx rs) v t

(** The run-time contexts `rs'`, `ln'` are a well-formed extension of `rs`,
    `ln`: every region of `rs` with its layout, every location of `ln`
    with its type. *)
let rt_ext (sg: sig) (ln: lctx) (rs: list (atom & layout)) (ln': lctx) (rs': list (atom & layout))
  : prop =
  rctx_ok sg rs' /\ lctx_ok sg rs' ln' /\
  layouts_ext (closed_ctx rs) (closed_ctx rs') /\ lctx_incl ln ln'

(** The obligation (3) on one chain `e` under `rs'` and `ln'`: if `e` is a
    saturated chain `M.f [[κ̄]] ᾱ` of values of a foreign (`foreign_redex`),
    typed at its cursor instance `θ(σ)` (`chain_cursor sg e = Some (σ, θ)`),
    and `values(ᾱ)` satisfies the ABI precondition `gpre M.f`, then `δ_f`
    exists, `δ_f(values(ᾱ))` returns an outcome, and that outcome conforms
    at `θ(σ)`. Outside `gpre` it asks nothing, of `δ_f` or of its
    result. *)
let foreign_call_ok (sg: sig) (gi: genv) (ln': lctx) (rs': list (atom & layout)) (e: exp) : prop =
  match chain_cursor sg e, decompose_global_app e with
  | Some (t, th), Some (q, _, args) ->
    (V.foreign_redex sg e /\ typed sg ln' (closed_ctx rs') e (sub_ty th t) /\
     gi.gpre q (value_args args)) ==>
    (match gi.gimpl q with
     | Some f ->
       (match f (value_args args) with
        | Some o -> outcome_ok sg ln' rs' q (sub_ty th t) o
        | None -> False)
     | None -> False)
  | _ -> True

(** (3) Every implementation conforms under every well-formed extension of
    `rs` and `ln`. *)
let gimpl_ok (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) : prop =
  forall (rs': list (atom & layout)) (ln': lctx) (e: exp).
    {:pattern foreign_call_ok sg gi ln' rs' e}
    rt_ext sg ln rs ln' rs' ==> foreign_call_ok sg gi ln' rs' e

(** `Σ; Γ_N ⊨ G` at `Γ_R = rs`, `Γ_N = ln`: the obligation of whoever
    supplies `G`, the implementations of the foreigns in particular. It
    says nothing of the term under evaluation, whose obligation is
    `Stella.Core.Semantics.Step.pre_ok`. *)
let genv_ok (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) : prop =
  gvals_covered sg gi /\ gvals_typed sg ln rs gi /\ gimpl_ok sg ln rs gi

(** * Reading conformance *)

val genv_ok_covered (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) (q: qname) (v: exp)
  : Lemma (requires genv_ok sg ln rs gi /\ gi.gvals q == Some v) (ensures covers sg gi v)

val genv_ok_gval (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) (q: qname)
  (vi: value_info) (v: exp)
  : Lemma (requires genv_ok sg ln rs gi /\ sg.values q == Some vi /\ gi.gvals q == Some v)
          (ensures V.is_value sg v /\ typed sg ln (decl_rctx vi.vl_nk rs) v vi.vl_ty)

(** Condition (3) at the contexts themselves, the extension by nothing. *)
val genv_ok_foreign (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) (e: exp)
  : Lemma (requires genv_ok sg ln rs gi /\ rctx_ok sg rs /\ lctx_ok sg rs ln)
          (ensures foreign_call_ok sg gi ln rs e)

(** * Stability *)

(** Conformance is stable under extending `Γ_R`, keeping the layouts, and
    `Γ_N`, keeping its types. The definitions are weakened
    (`Stella.Core.Typing.Weaken.typing_weaken_ext`, `typing_lctx_ext`), and
    an extension of the new contexts is one of the old. The new contexts
    need not be well formed for this. *)
val genv_ok_ext (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv)
  (ln': lctx) (rs': list (atom & layout))
  : Lemma (requires genv_ok sg ln rs gi /\
                    layouts_ext (closed_ctx rs) (closed_ctx rs') /\ lctx_incl ln ln')
          (ensures genv_ok sg ln' rs' gi)

(** Conformance before any region or location exists gives conformance
    at every pair of contexts. *)
val genv_ok_closed (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout))
  : Lemma (requires genv_ok sg [] [] gi) (ensures genv_ok sg ln rs gi)
