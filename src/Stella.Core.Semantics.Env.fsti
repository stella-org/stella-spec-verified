(**
 * The global environment `G`, faults, stores and configurations, coverage,
 * and the conformance of `G` to `Σ` (spec 06 §Reduction, §The global
 * environment, §Faults, §Conformance of the global environment; D53).
 *
 * ## The environment
 *
 * `G` holds, for each top-level value `M.x`, its definition `v`, and for
 * each foreign `M.f`, an entry of three parts (spec 06 §An implementation,
 * and the typed view it is read through; §An ABI precondition is where
 * condition (3) stops asking):
 *
 *   - `fe_adapt`, the typed adapter `δᵀ_f(ξ, v̄)`: given the instance `ξ`
 *     of the chain (`chain_instance`) and its typed value arguments `v̄`,
 *     an annotated outcome. The instance is ghost information: it lets the
 *     outcome carry the annotations the cursor computes, `M.Nil [τ]` or
 *     `opaque ω [IO τ]`;
 *   - `fe_erased`, the erased function `δᵤ_f(w̄)`: given the erased value
 *     arguments `w̄ = ⌊v̄⌋` (`Stella.Core.Erase`), an erased outcome. No
 *     instance and no annotation reaches it;
 *   - `fe_pre`, the erased precondition `Pᶜ_f(w̄)`, a predicate on the
 *     erased value arguments.
 *
 * The scheme of a definition is read from `Σ` (`sg.values`), so `G` holds
 * terms and functions only.
 *
 * Spec 06 §The global environment lists every data constructor `M.Ctor`
 * in `G` as well. Here a constructor has no entry: it has nothing to
 * unfold to and no implementation, a chain headed by one is a value as it
 * stands, and `Σ` records it. So coverage asks nothing of a constructor
 * (`covered_name`), where the coverage of spec 06 §Coverage asks that
 * linking supplied its entry.
 *
 * ## What is represented
 *
 * An entry of `G` is a candidate for the correspondence contract of a
 * Core-modelled foreign: its precondition, adapter and erased function are
 * functions of the call alone, with no host state. The shape of `G` does
 * not make it Core-modelled; `genv_ok` completes the contract, and an
 * entry whose adapter breaks erasure coherence has the same shape and
 * does not conform. The conformance stated here is that of a Core-modelled
 * environment. The host state `H`, the general
 * implementation `δ_f(H, ·)`, its typed view `δᵀ_f(H, ·, ·)` and the
 * general precondition `Pᴴ_f(H, ·)` are not represented, and neither is
 * the general, state-dependent conformance spec 06 admits beside the
 * Core-modelled one. Of the correspondence contract, clause (a) holds by
 * construction, the precondition `fe_pre` reading erased arguments alone,
 * so two typed argument lists erasing alike stand inside it or outside it
 * together; and clauses (b) and (c) hold by construction, the adapter and
 * the erased function being functions of the call alone, which read no
 * state, write none, and create no identity the call does not determine.
 * Clause (d), erasure coherence, and the definedness of both functions
 * are asked by condition (3) below.
 *
 * The adapter is a total function returning an optional outcome, and
 * condition (3) guarantees `Some` for every well-typed call inside the
 * precondition. So a call terminates and is atomic: it is one step, to the
 * outcome the adapter gives. The clause of condition (3) on termination needs no
 * counterpart here, and neither does the purpose of the clause on applying
 * no Stella function value, which is that the step be atomic. The clause
 * itself is not expressed: a total function may return a term built from a
 * `λ` among its arguments.
 *
 * ## Three obligations
 *
 * A saturated foreign call `M.f [[κ̄]] ᾱ`, with `v̄ = values(ᾱ)` and
 * `ξ = instance(M.f [[κ̄]] ᾱ)`, involves three things, which bind different
 * parties (spec 06 §Chains of a constructor or a foreign, §Conformance of
 * the global environment):
 *
 *   - `fe_pre ⌊v̄⌋`, the precondition of the entry of `M.f`. Respecting it
 *     is the program's obligation (`Stella.Core.Semantics.Step.pre_ok`).
 *     The rule for a saturated chain takes it as a premise, so a call
 *     outside it has no step;
 *   - `fe_adapt ξ v̄ = Some o` and `fe_erased ⌊v̄⌋ = Some u` with
 *     `eraseOutcome(o) = u` and `o` conforming, at every typed call inside
 *     `fe_pre`: condition (3), the implementer's obligation (`genv_ok`).
 *     That a foreign the program mentions has an entry at all is coverage
 *     (`covers`);
 *   - `fe_adapt ξ v̄ = None` is semantic partiality: the relation gives the
 *     call no step, as it gives none where `G` is not Core-modelled. Under
 *     `genv_ok` it happens only outside `fe_pre` or at a call that is not
 *     typed. Neither the rule nor condition (3) reads the adapter outside
 *     `fe_pre`.
 *
 * ## Faults
 *
 * A fault is either the initialization fault `φ_init` (`FInit`), which only
 * forcing an `Evaluating` cell produces, or an ABI fault (`FAbi`), which
 * only a foreign produces. A foreign returns an `abi_fault`
 * (`Stella.Core.Erase`), so it cannot produce `φ_init`. The payload of an
 * ABI fault is opaque: Core records only that a fault is a possible outcome
 * (spec 06 §Faults).
 *
 * ## Coverage
 *
 * `globals e` lists the global value names occurring in `e`, at every node,
 * under binders, in handlers, in decision trees and in region cells
 * included (spec 06 §Coverage). `G` covers `e` (`covers`) when each of them
 * has its entry; `covers_globals` reads `covers` through `globals`. A
 * foreign's outcome is covered relative to its arguments
 * (`covers_relative`): `globals(v) ⊆ dom(G) ∪ globals(v̄)`, so arguments
 * covered give a result covered (`covers_relative_covers`).
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
 *   (3) for each entry of a foreign `M.f` in `G`, every well-formed
 *       extension `rs'`, `ln'` of `rs`, `ln` (`layouts_ext`, `lctx_incl`),
 *       and every saturated chain of values of `M.f` typed under `rs'` and
 *       `ln'` at its cursor instance `θ(σ)`, at `Δ = ·` and row `()`, whose
 *       erased values `⌊v̄⌋` satisfy `fe_pre`: the adapter and the erased
 *       function both return an outcome (definedness); the adapter's
 *       outcome erases to the erased function's (erasure coherence,
 *       clause (d) of the correspondence contract); the adapter's outcome
 *       is an ABI fault, or a value of type `θ(σ)` under the same `rs'` and
 *       `ln'` covered relative to `v̄`; and where `Σ` records
 *       `#observ(none)` for `M.f`, not a fault. Outside `fe_pre`, (3) asks
 *       nothing (spec 06 §An ABI precondition is where condition (3) stops
 *       asking).
 *
 * The spec quantifies (3) over every well-formed `Γ_R` and `Γ_N`; here it
 * ranges over the extensions of the contexts `genv_ok` is stated at, the
 * contexts every later configuration stands under. At `rs = []` and
 * `ln = []` every well-formed pair is such an extension, so
 * `genv_ok sg [] [] G` is conformance before any region or location
 * exists, the spec's `Σ ⊨ G` for a Core-modelled `G`, and it implies
 * `genv_ok` at every pair of contexts (`genv_ok_closed`).
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
open Stella.Core.Spine.Lemmas
open Stella.Core.Erase
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Weaken
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Kinst
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Faults (spec 06 §Faults) *)

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

(** The configuration a typed outcome is. *)
let foreign_config (o: foreign_outcome) : config =
  match o with
  | FOVal v -> CTerm v
  | FOFault phi -> CFault (FAbi phi)

(** * The instance of a chain (spec 05 §The instance of a chain) *)

(** `ξ = ⟨ κ̄ ; τ̄ ⟩`: the kind arguments and the type arguments of a chain,
    in written order. A constraint argument contributes nothing, and the
    value arguments do not enter. *)
type chain_inst = {
  inst_kinds : list kind;
  inst_types : list typ;
}

(** `instance(M.g [[κ̄]] ᾱ) = ⟨ κ̄ ; types(ᾱ) ⟩`. For a saturated chain it
    determines the cursor's substitution, and so the instantiated result
    type `θ(σ)`. It is read only of a chain; of any other term it is
    `⟨ · ; · ⟩`. *)
let chain_instance (e: exp) : chain_inst =
  match decompose_global_app e with
  | Some (_, ks, args) -> { inst_kinds = ks; inst_types = ty_args args }
  | None -> { inst_kinds = []; inst_types = [] }

(** * The global environment (spec 06 §The global environment) *)

(** The entry of a foreign `M.f`: its typed adapter `δᵀ_f`, its erased
    function `δᵤ_f`, and its erased precondition `Pᶜ_f`. The outer `None`
    of either function is semantic partiality; condition (3) of `genv_ok`
    rules it out inside `fe_pre` at a typed call. *)
noeq type foreign_entry = {
  fe_adapt  : chain_inst -> list exp -> option foreign_outcome;
  fe_erased : list uexp -> option uoutcome;
  fe_pre    : list uexp -> prop;
}

(** `G`: the definition of each top-level value, and the entry of each
    foreign. Constructors have no entry (spec 06 lists them in `G`; see
    the module header). *)
noeq type genv = {
  gvals    : qname -> option exp;
  gforeign : qname -> option foreign_entry;
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

(** * The global names of a term (spec 06 §Coverage) *)

(** `globals(e)`: the global value names occurring in `e`, wherever they
    occur, with repetitions, at every node `exp_all` visits. *)
let rec globals (e: exp) : Tot (list qname) (decreases e) =
  match e with
  | EGlobal q _ -> [q]
  | EVar _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> []
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b ->
    globals b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    L.append (globals e1) (globals e2)
  | ELetRec bs b -> L.append (globals_binds bs) (globals b)
  | ECase es dt -> L.append (globals_exps es) (globals_dt dt)
  | EMatch th dt -> L.append (globals_exps th) (globals_dt dt)
  | EJump _ es -> globals_exps es
  | EHandle b h -> L.append (globals b) (L.append (globals h.h_ret) (globals_cls h.h_clauses))
  | ERegion _ es b -> L.append (globals_exps es) (globals b)
  | ERegionOpen _ th b -> L.append (globals_cells th) (globals b)

(** `globals(ē)`, the union over a sequence. *)
and globals_exps (es: list exp) : Tot (list qname) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> L.append (globals e) (globals_exps es)

and globals_binds (bs: list (typ & exp)) : Tot (list qname) (decreases bs) =
  match bs with
  | [] -> []
  | (_, e) :: bs -> L.append (globals e) (globals_binds bs)

and globals_cells (th: list (key & exp)) : Tot (list qname) (decreases th) =
  match th with
  | [] -> []
  | (_, e) :: th -> L.append (globals e) (globals_cells th)

and globals_dt (dt: dtree) : Tot (list qname) (decreases dt) =
  match dt with
  | DLeaf e -> globals e
  | DBind _ dt -> globals_dt dt
  | DSwitchCtor _ bs df -> L.append (globals_brs bs) (globals_odt df)
  | DSwitchLit _ bs df -> L.append (globals_brs bs) (globals_dt df)
  | DSwitchKey _ bs df -> L.append (globals_brs bs) (globals_odt df)
  | DGuard e dt1 dt2 -> L.append (globals e) (L.append (globals_dt dt1) (globals_dt dt2))

and globals_odt (df: option dtree) : Tot (list qname) (decreases df) =
  match df with
  | None -> []
  | Some dt -> globals_dt dt

and globals_brs (#lb: eqtype) (bs: list (lb & dtree)) : Tot (list qname) (decreases bs) =
  match bs with
  | [] -> []
  | (_, dt) :: bs -> L.append (globals_dt dt) (globals_brs bs)

and globals_cls (cs: list clause) : Tot (list qname) (decreases cs) =
  match cs with
  | [] -> []
  | CFull _ _ _ _ b :: cs -> L.append (globals b) (globals_cls cs)
  | CFast _ _ _ b :: cs -> L.append (globals b) (globals_cls cs)

(** * Coverage (spec 06 §Coverage) *)

(** The name `q` is covered by `G`: a top-level value of `Σ` has a
    definition, and a foreign an entry. A constructor needs nothing, since
    `G` has no entry for one where spec 06 lists `M.Ctor`, and a name `Σ`
    does not classify heads no typed term. *)
let covered_name (sg: sig) (gi: genv) (q: qname) : bool =
  (if Some? (value_scheme sg q) then Some? (gi.gvals q) else true) &&
  (if is_foreign sg q then Some? (gi.gforeign q) else true)

(** A node is covered by `G`: a global it references is. *)
let covered (sg: sig) (gi: genv) (e: exp) : bool =
  match e with
  | EGlobal q _ -> covered_name sg gi q
  | _ -> true

(** `G covers e`: every global name occurring anywhere in `e` is covered. *)
let covers (sg: sig) (gi: genv) (e: exp) : bool = exp_all (covered sg gi) e

let covers_dt (sg: sig) (gi: genv) (dt: dtree) : bool = exp_all_dt (covered sg gi) dt

(** `q ∈ dom(G) ∪ globals(v̄)`: the name is covered by `G` or occurs in one
    of `v̄`. *)
let covered_or_in (sg: sig) (gi: genv) (vs: list exp) (q: qname) : bool =
  covered_name sg gi q || L.mem q (globals_exps vs)

(** `globals(v) ⊆ dom(G) ∪ globals(v̄)`: every global name occurring in `v`
    is covered by `G` or occurs in one of `v̄` (spec 06 §Conformance of the
    global environment, condition (3)). *)
let covers_relative (sg: sig) (gi: genv) (vs: list exp) (v: exp) : bool =
  L.for_all (covered_or_in sg gi vs) (globals v)

(** `covers` read through `globals`. *)
val covers_globals (sg: sig) (gi: genv) (e: exp)
  : Lemma (covers sg gi e == L.for_all (covered_name sg gi) (globals e))

(** Arguments covered give a result covered. *)
val covers_relative_covers (sg: sig) (gi: genv) (vs: list exp) (v: exp)
  : Lemma (requires covers_relative sg gi vs v /\ L.for_all (covers sg gi) vs)
          (ensures covers sg gi v)

(** A term is covered relative to any list holding it. *)
val covers_relative_self (sg: sig) (gi: genv) (vs: list exp) (v: exp)
  : Lemma (requires L.mem v vs) (ensures covers_relative sg gi vs v)

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

(** A typed outcome of a call of `q` on the value arguments `v̄` conforms
    at `τ` under `rs` and `ln`: an ABI fault, unless `q` is
    `#observ(none)`; or a value of type `τ` at `Δ = ·` and row `()`,
    covered relative to `v̄`. *)
let outcome_ok (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout)) (q: qname)
  (vs: list exp) (t: typ) (o: foreign_outcome) : prop =
  match o with
  | FOFault _ -> ~(observ_none sg q)
  | FOVal v -> V.is_value sg v /\ typed sg ln (closed_ctx rs) v t /\ covers_relative sg gi vs v

(** The run-time contexts `rs'`, `ln'` are a well-formed extension of `rs`,
    `ln`: every region of `rs` with its layout, every location of `ln`
    with its type. *)
let rt_ext (sg: sig) (ln: lctx) (rs: list (atom & layout)) (ln': lctx) (rs': list (atom & layout))
  : prop =
  rctx_ok sg rs' /\ lctx_ok sg rs' ln' /\
  layouts_ext (closed_ctx rs) (closed_ctx rs') /\ lctx_incl ln ln'

(** What (3) asks of the entry `fe` of `q` at one call, with instance `ξ`
    and value arguments `v̄`, at the result type `τ`: both functions return
    an outcome, the typed one erases to the erased one, and the typed one
    conforms. *)
let entry_call_ok (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout)) (q: qname)
  (fe: foreign_entry) (xi: chain_inst) (vs: list exp) (t: typ) : prop =
  match fe.fe_adapt xi vs, fe.fe_erased (L.map erase vs) with
  | Some o, Some u -> erase_outcome o == u /\ outcome_ok sg gi ln rs q vs t o
  | _ -> False

(** The obligation (3) on one chain `e` under `rs'` and `ln'`: if `e` is a
    saturated chain `M.f [[κ̄]] ᾱ` of values of a foreign with an entry
    `fe` in `G` (`foreign_redex`), typed at its cursor instance `θ(σ)`
    (`chain_cursor sg e = Some (σ, θ)`), and `⌊values(ᾱ)⌋` satisfies
    `fe_pre`, then `fe` meets `entry_call_ok` at
    `ξ = instance(M.f [[κ̄]] ᾱ)`, `v̄ = values(ᾱ)` and `θ(σ)`. Outside
    `fe_pre` it asks nothing, of either function or of their results. *)
let foreign_call_ok (sg: sig) (gi: genv) (ln': lctx) (rs': list (atom & layout)) (e: exp) : prop =
  match chain_cursor sg e, decompose_global_app e with
  | Some (t, th), Some (q, _, args) ->
    (match gi.gforeign q with
     | Some fe ->
       (V.foreign_redex sg e /\ typed sg ln' (closed_ctx rs') e (sub_ty th t) /\
        fe.fe_pre (L.map erase (value_args args))) ==>
       entry_call_ok sg gi ln' rs' q fe (chain_instance e) (value_args args) (sub_ty th t)
     | None -> True)
  | _ -> True

(** (3) Every foreign entry conforms under every well-formed extension of
    `rs` and `ln`. *)
let gforeign_ok (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) : prop =
  forall (rs': list (atom & layout)) (ln': lctx) (e: exp).
    {:pattern foreign_call_ok sg gi ln' rs' e}
    rt_ext sg ln rs ln' rs' ==> foreign_call_ok sg gi ln' rs' e

(** `Σ; Γ_N ⊨ G` at `Γ_R = rs`, `Γ_N = ln`: the obligation of whoever
    supplies `G`, the foreign entries in particular. It says nothing of the
    term under evaluation, whose obligation is
    `Stella.Core.Semantics.Step.pre_ok`. *)
let genv_ok (sg: sig) (ln: lctx) (rs: list (atom & layout)) (gi: genv) : prop =
  gvals_covered sg gi /\ gvals_typed sg ln rs gi /\ gforeign_ok sg ln rs gi

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
