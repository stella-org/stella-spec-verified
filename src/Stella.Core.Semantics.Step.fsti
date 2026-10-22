(**
 * The reduction relation (spec 06 §Reduction, §Ordinary reduction,
 * §Chains of a constructor or a foreign, §Pattern matching, §Join points,
 * §Evaluation contexts).
 *
 *     pure_head sg G e c                    G ⊢ e → c, a head rule that
 *                                           leaves the store alone
 *     step sg G R N e R' N' c               G ⊢ N; e → N'; c
 *
 * A configuration (`Stella.Core.Semantics.Env.config`) is a term or a
 * fault. Besides the store `N` a step carries `R`, the region names
 * allocated so far, from which an opening picks a fresh one. Every
 * judgement takes `Σ` explicitly, since values, the saturation of a
 * foreign's chain and the class of a global all depend on it, and one `Σ`
 * is used throughout a derivation.
 *
 * ## Head rules
 *
 * The head rules are grouped by the part of the configuration they touch,
 * one inductive per group. `pure_head` holds the rules that read neither
 * the store nor `R`: the rules of spec 06 §Ordinary reduction other than
 * those of `letrec`, `force` and `fill`, the rule for a saturated foreign's
 * chain, the rules of spec 06 §Pattern matching and of spec 06 §Join
 * points. The rules of operations and handlers, of regions and cells, and
 * of recursive bindings are relations of their own, each added to `step`
 * by a constructor of its own.
 *
 * The spec's metavariables are premises: a `v` or `w` is a term that
 * `is_value` accepts. Substitution is de Bruijn (`Stella.Core.Subst`):
 * `e[x := v]` is `subst1_tm v e` and `v[a := σ]` is `subst1_ty_exp σ v`.
 * Region binders are locally nameless, so a locally closed type
 * substituted under a `region [ℓ]` mentions only free region names, and
 * nothing is captured. The type a step of a closed well-typed term
 * substitutes is locally closed: it is kinded where it stands
 * (`Stella.Core.Kinding.Facts.check_lc`).
 *
 * Where the spec writes `θ = {s_i ↦ v_i}`, a `match` holds the list `v̄`
 * of the scrutinee values, and `θ(o)` is `proj sg θ o`
 * (`Stella.Core.Typing.Aux`). A dispatch reads `θ(o)` and requires it to
 * be defined, its default branch included: the spec's "otherwise" is read
 * as "θ(o) is defined and is not one of the cases the branches name".
 *
 * ## Join points
 *
 * `letjoin j (x̄ : τ̄) : τ = e1 in Tl[jump j (v̄)]` refers to `j` from the
 * hole of `Tl` by the join index `n = |Tl|`, each `letjoin` of `Tl`
 * binding one join point. The definition `e1` stands under the join
 * binder of `j` and its own parameters; moved to the hole, it stands under
 * the `n` join binders of `Tl` as well, so its join indices are shifted by
 * `n` (`ren_jp (shift n)`) before its parameters are replaced by `v̄`, the
 * last parameter being index 0 (`list_esub (rev v̄)`). The reduct is
 *
 *     letjoin j (x̄ : τ̄) : τ = e1 in Tl[ sub_tm (list_esub (rev v̄)) (ren_jp (shift n) e1) ]
 *
 * which is the term the typing lemmas produce for a definition weakened
 * past the join points of `Tl` (`Stella.Core.Typing.Join.typing_weaken_jps`)
 * and then instantiated (`Stella.Core.Typing.Subst.Tm.Inst.typing_subst_values`).
 *
 * In `letjoin j … in v → v` the value `v` stands under the join binder;
 * a value mentions no free join index (`Stella.Core.Value.letjoin_value`),
 * so it is its own reduct outside the binder.
 *
 * ## Contexts
 *
 * `step` closes the head rules under one frame at a time (`S_Ctx`), and
 * propagates a fault out of one frame (`S_CtxFault`). Since an evaluation
 * context is a list of frames (`Stella.Core.Semantics.Ctx`), induction on
 * the context shows that `step` relates `Ev[e]` to `Ev[e']`, and `Ev[e]`
 * to a fault, whenever `e` steps so, which are the spec's two context
 * rules; a step at the root is the case `Ev = []`.
 *
 * `fail τ` is notation for `perform Partial.abort [τ] Prim.Unit`
 * (`Stella.Core.Syntax.fail_exp`), so it needs no rule of its own.
 *)
module Stella.Core.Semantics.Step
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Dispatch (spec 06 §Pattern matching) *)

(** The constructor `Ctor` of a value that is an application of `Ctor`,
    a chain headed by a data constructor. *)
let ctor_head (sg: sig) (v: exp) : option qname =
  match decompose_global_app v with
  | Some (q, _, _) -> if is_ctor sg q then Some q else None
  | None -> None

(** The literal a value is. *)
let lit_of (v: exp) : option lit =
  match v with
  | ELit c -> Some c
  | _ -> None

(** The key `k` of `carrier(v) = (k, w)`, looking through every `weaken`
    (`variant_view`). *)
let carrier_key (v: exp) : option key =
  match variant_view v with
  | Some (k, _) -> Some k
  | None -> None

(** The branch of the case `l`, if the branches name it. *)
let branch (#lb: eqtype) (l: option lb) (bs: list (lb & dtree)) : option dtree =
  match l with
  | Some l -> L.assoc l bs
  | None -> None

(** The Boolean literal. *)
let bool_lit (b: bool) : exp = ELit (LBool b)

(** * The pure head rules *)

noeq type pure_head (sg: sig) (gi: genv) : exp -> config -> Type =

  (* -- Abstraction (spec 06 §Ordinary reduction) -- *)

  (** `(λ(x : τ) / ρ. e) v  →  e[x := v]` *)
  | PH_Beta :
      #t:typ -> #r:typ -> #body:exp -> #v:exp ->
      squash (V.is_value sg v) ->
      pure_head sg gi (EApp (ELam t r body) v) (CTerm (subst1_tm v body))

  (** `(Λ(a : κ). v) [σ]  →  v[a := σ]` *)
  | PH_TyBeta :
      #k:kind -> #v:exp -> #s:typ ->
      squash (V.is_value sg v) ->
      pure_head sg gi (ETyApp (ETyLam k v) s) (CTerm (subst1_ty_exp s v))

  (** `(Λ(_ : C). v) [•]  →  v` *)
  | PH_CBeta :
      #c:constr -> #v:exp ->
      squash (V.is_value sg v) ->
      pure_head sg gi (ECApp (ECLam c v)) (CTerm v)

  (** `(openEff [ρ] v) w  →  openEffC [ρ] (v w)` *)
  | PH_OpenEffApp :
      #r:typ -> #v:exp -> #w:exp ->
      squash (V.is_value sg v /\ V.is_value sg w) ->
      pure_head sg gi (EApp (EOpenEff r v) w) (CTerm (EOpenEffC r (EApp v w)))

  (** `openEffC [ρ] v  →  v` *)
  | PH_OpenEffC :
      #r:typ -> #v:exp ->
      squash (V.is_value sg v) ->
      pure_head sg gi (EOpenEffC r v) (CTerm v)

  (** `let x : τ = v in e  →  e[x := v]` *)
  | PH_Let :
      #t:typ -> #v:exp -> #body:exp ->
      squash (V.is_value sg v) ->
      pure_head sg gi (ELet t v body) (CTerm (subst1_tm v body))

  (* -- Records (spec 06 §Ordinary reduction) -- *)

  (** `select k (extend k v1 v2)  →  v1` *)
  | PH_SelectHit :
      #k:key -> #v1:exp -> #v2:exp ->
      squash (V.is_value sg v1 /\ V.is_value sg v2) ->
      pure_head sg gi (ESelect k (EExtend k v1 v2)) (CTerm v1)

  (** `select k (extend k' v1 v2)  →  select k v2`, `k ≠ k'` *)
  | PH_SelectMiss :
      #k:key -> #k':key -> #v1:exp -> #v2:exp ->
      squash (k <> k') ->
      squash (V.is_value sg v1 /\ V.is_value sg v2) ->
      pure_head sg gi (ESelect k (EExtend k' v1 v2)) (CTerm (ESelect k v2))

  (** `restrict k (extend k v1 v2)  →  v2` *)
  | PH_RestrictHit :
      #k:key -> #v1:exp -> #v2:exp ->
      squash (V.is_value sg v1 /\ V.is_value sg v2) ->
      pure_head sg gi (ERestrict k (EExtend k v1 v2)) (CTerm v2)

  (** `restrict k (extend k' v1 v2)  →  extend k' v1 (restrict k v2)`,
      `k ≠ k'` *)
  | PH_RestrictMiss :
      #k:key -> #k':key -> #v1:exp -> #v2:exp ->
      squash (k <> k') ->
      squash (V.is_value sg v1 /\ V.is_value sg v2) ->
      pure_head sg gi (ERestrict k (EExtend k' v1 v2)) (CTerm (EExtend k' v1 (ERestrict k v2)))

  (** `update k (extend k v1 v2) v3  →  extend k v3 v2` *)
  | PH_UpdateHit :
      #k:key -> #v1:exp -> #v2:exp -> #v3:exp ->
      squash (V.is_value sg v1 /\ V.is_value sg v2 /\ V.is_value sg v3) ->
      pure_head sg gi (EUpdate k (EExtend k v1 v2) v3) (CTerm (EExtend k v3 v2))

  (** `update k (extend k' v1 v2) v3  →  extend k' v1 (update k v2 v3)`,
      `k ≠ k'` *)
  | PH_UpdateMiss :
      #k:key -> #k':key -> #v1:exp -> #v2:exp -> #v3:exp ->
      squash (k <> k') ->
      squash (V.is_value sg v1 /\ V.is_value sg v2 /\ V.is_value sg v3) ->
      pure_head sg gi (EUpdate k (EExtend k' v1 v2) v3)
        (CTerm (EExtend k' v1 (EUpdate k v2 v3)))

  (** `merge {} v  →  v` *)
  | PH_MergeEmpty :
      #v:exp ->
      squash (V.is_value sg v) ->
      pure_head sg gi (EMerge ERecEmpty v) (CTerm v)

  (** `merge (extend k v1 v2) v3  →  extend k v1 (merge v2 v3)` *)
  | PH_MergeExtend :
      #k:key -> #v1:exp -> #v2:exp -> #v3:exp ->
      squash (V.is_value sg v1 /\ V.is_value sg v2 /\ V.is_value sg v3) ->
      pure_head sg gi (EMerge (EExtend k v1 v2) v3) (CTerm (EExtend k v1 (EMerge v2 v3)))

  (* -- Globals (spec 06 §The global environment, §Chains of a constructor
        or a foreign) -- *)

  (** `M.x [[κ̄]]  →  v[k̄ := κ̄]` for `(M.x : forall k̄. σ = v) ∈ G`, `κ̄`
      instantiating all of `k̄`. *)
  | PH_Unfold :
      #q:qname -> #ks:list kind -> #vi:value_info -> #v:exp ->
      squash (value_scheme sg q == Some vi /\ L.length ks == vi.vl_nk) ->
      squash (gi.gvals q == Some v) ->
      pure_head sg gi (EGlobal q ks) (CTerm (kinst_exp ks v))

  (** `M.f [[κ̄]] ᾱ  →  δ_f(values(ᾱ))` for a saturated chain of values of
      a foreign (`foreign_redex`) whose values satisfy the ABI
      precondition `gpre M.f`, where `δ_f` exists and returns an outcome
      on them: a value as a term, an ABI fault as a fault
      (`foreign_config`). A call outside `gpre` has no step, whatever
      `δ_f` returns on it, and neither has one on which `δ_f` returns
      `None` (spec 06 §Chains of a constructor or a foreign). *)
  | PH_Foreign :
      #e:exp -> #q:qname -> #ks:list kind -> #args:list spine_arg ->
      #f:(list exp -> option foreign_outcome) -> #o:foreign_outcome ->
      squash (V.foreign_redex sg e /\ decompose_global_app e == Some (q, ks, args)) ->
      squash (gi.gpre q (value_args args)) ->
      squash (gi.gimpl q == Some f /\ f (value_args args) == Some o) ->
      pure_head sg gi e (foreign_config o)

  (* -- Pattern matching (spec 06 §Pattern matching) -- *)

  (** `case (v̄) of dt  →  match {s_i ↦ v_i} dt` *)
  | PH_Case :
      #vs:list exp -> #dt:dtree ->
      squash (L.for_all (V.is_value sg) vs) ->
      pure_head sg gi (ECase vs dt) (CTerm (EMatch vs dt))

  (** `match θ (leaf e)  →  e` *)
  | PH_Leaf :
      #th:list exp -> #e:exp ->
      pure_head sg gi (EMatch th (DLeaf e)) (CTerm e)

  (** `match θ (bind x = o in dt)  →  match θ (dt[x := θ(o)])` *)
  | PH_Bind :
      #th:list exp -> #o:occ -> #dt:dtree -> #v:exp ->
      squash (proj sg th o == Some v) ->
      pure_head sg gi (EMatch th (DBind o dt)) (CTerm (EMatch th (sub_tm_dt (scons v evar) dt)))

  (** `match θ (guard true dt1 dt2)  →  match θ dt1` *)
  | PH_GuardTrue :
      #th:list exp -> #dt1:dtree -> #dt2:dtree ->
      pure_head sg gi (EMatch th (DGuard (bool_lit true) dt1 dt2)) (CTerm (EMatch th dt1))

  (** `match θ (guard false dt1 dt2)  →  match θ dt2` *)
  | PH_GuardFalse :
      #th:list exp -> #dt1:dtree -> #dt2:dtree ->
      pure_head sg gi (EMatch th (DGuard (bool_lit false) dt1 dt2)) (CTerm (EMatch th dt2))

  (** `switchCtor o { Ctor_i -> dt_i } …  →  match θ dt_i` when `θ(o)` is
      an application of `Ctor_i` *)
  | PH_SwitchCtor :
      #th:list exp -> #o:occ -> #bs:list (qname & dtree) -> #df:option dtree ->
      #v:exp -> #dt:dtree ->
      squash (proj sg th o == Some v /\ branch (ctor_head sg v) bs == Some dt) ->
      pure_head sg gi (EMatch th (DSwitchCtor o bs df)) (CTerm (EMatch th dt))

  (** `switchCtor o { … } default -> dt_0  →  match θ dt_0` otherwise *)
  | PH_SwitchCtorDef :
      #th:list exp -> #o:occ -> #bs:list (qname & dtree) -> #dt0:dtree -> #v:exp ->
      squash (proj sg th o == Some v /\ branch (ctor_head sg v) bs == None) ->
      pure_head sg gi (EMatch th (DSwitchCtor o bs (Some dt0))) (CTerm (EMatch th dt0))

  (** `switchLit o { c_i -> dt_i } …  →  match θ dt_i` when `θ(o) = c_i` *)
  | PH_SwitchLit :
      #th:list exp -> #o:occ -> #bs:list (lit & dtree) -> #dt0:dtree -> #v:exp -> #dt:dtree ->
      squash (proj sg th o == Some v /\ branch (lit_of v) bs == Some dt) ->
      pure_head sg gi (EMatch th (DSwitchLit o bs dt0)) (CTerm (EMatch th dt))

  (** `switchLit o { … } default -> dt_0  →  match θ dt_0` otherwise *)
  | PH_SwitchLitDef :
      #th:list exp -> #o:occ -> #bs:list (lit & dtree) -> #dt0:dtree -> #v:exp ->
      squash (proj sg th o == Some v /\ branch (lit_of v) bs == None) ->
      pure_head sg gi (EMatch th (DSwitchLit o bs dt0)) (CTerm (EMatch th dt0))

  (** `switchKey o { k_i -> dt_i } …  →  match θ dt_i` when
      `carrier(θ(o)) = (k_i, w)` *)
  | PH_SwitchKey :
      #th:list exp -> #o:occ -> #bs:list (key & dtree) -> #df:option dtree ->
      #v:exp -> #dt:dtree ->
      squash (proj sg th o == Some v /\ branch (carrier_key v) bs == Some dt) ->
      pure_head sg gi (EMatch th (DSwitchKey o bs df)) (CTerm (EMatch th dt))

  (** `switchKey o { … } default -> dt_0  →  match θ dt_0` otherwise *)
  | PH_SwitchKeyDef :
      #th:list exp -> #o:occ -> #bs:list (key & dtree) -> #dt0:dtree -> #v:exp ->
      squash (proj sg th o == Some v /\ branch (carrier_key v) bs == None) ->
      pure_head sg gi (EMatch th (DSwitchKey o bs (Some dt0))) (CTerm (EMatch th dt0))

  (* -- Join points (spec 06 §Join points) -- *)

  (** `letjoin j (x̄ : τ̄) : τ = e1 in Tl[jump j (v̄)]
         →  letjoin j (x̄ : τ̄) : τ = e1 in Tl[e1[x̄ := v̄]]`,
      the jump referring to `j` by the index `n = |Tl|` and the definition
      shifted past the `n` join binders of `Tl`. *)
  | PH_Join :
      #ts:list typ -> #t:typ -> #e1:exp -> #fs:list frame -> #n:nat -> #vs:list exp ->
      squash (tl_frames fs /\ n == L.length fs) ->
      squash (L.for_all (V.is_value sg) vs /\ L.length vs == L.length ts) ->
      pure_head sg gi (ELetJoin ts t e1 (plug fs (EJump n vs)))
        (CTerm (ELetJoin ts t e1 (plug fs (sub_tm (list_esub (L.rev vs)) (ren_jp (shift n) e1)))))

  (** `letjoin j (x̄ : τ̄) : τ = e1 in v  →  v` *)
  | PH_JoinValue :
      #ts:list typ -> #t:typ -> #e1:exp -> #v:exp ->
      squash (V.is_value sg v) ->
      pure_head sg gi (ELetJoin ts t e1 v) (CTerm v)

(** A value is no redex of a pure head rule. *)
val value_no_pure_head (#sg: sig) (#gi: genv) (#e: exp) (#c: config) (h: pure_head sg gi e c)
  : Lemma (requires V.is_value sg e) (ensures False)

(** * Steps *)

(** `G ⊢ N; e → N'; c`, with `R` and `R'` the region names allocated
    before and after. *)
noeq type step (sg: sig) (gi: genv)
  : list atom -> store -> exp -> list atom -> store -> config -> Type =
  (** A head rule that leaves `R` and `N` as they are. *)
  | S_Pure :
      #ra:list atom -> #st:store -> #e:exp -> #c:config ->
      pure_head sg gi e c ->
      step sg gi ra st e ra st c

  (** `G ⊢ N; e → N'; e'` gives `G ⊢ N; f[e] → N'; f[e']`. *)
  | S_Ctx :
      #ra:list atom -> #st:store -> #e:exp -> #ra':list atom -> #st':store -> #e':exp ->
      f:frame ->
      squash (frame_ok sg f) ->
      step sg gi ra st e ra' st' (CTerm e') ->
      step sg gi ra st (plug1 f e) ra' st' (CTerm (plug1 f e'))

  (** `G ⊢ N; e → N'; fault φ` gives `G ⊢ N; f[e] → N'; fault φ`. *)
  | S_CtxFault :
      #ra:list atom -> #st:store -> #e:exp -> #ra':list atom -> #st':store -> #phi:fault ->
      f:frame ->
      squash (frame_ok sg f) ->
      step sg gi ra st e ra' st' (CFault phi) ->
      step sg gi ra st (plug1 f e) ra' st' (CFault phi)

(** A step under a whole evaluation context. *)
val step_plug (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#e': exp)
  (fs: list frame) (h: step sg gi ra st e ra' st' (CTerm e'))
  : Pure (step sg gi ra st (plug fs e) ra' st' (CTerm (plug fs e')))
         (requires frames_ok sg fs) (ensures fun _ -> True)

(** A fault under a whole evaluation context. *)
val step_plug_fault (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#phi: fault)
  (fs: list frame) (h: step sg gi ra st e ra' st' (CFault phi))
  : Pure (step sg gi ra st (plug fs e) ra' st' (CFault phi))
         (requires frames_ok sg fs) (ensures fun _ -> True)

(** * The fragment of stage 5 *)

(** A node is none of `perform`, `handle`, `region`, an open region frame,
    `readCell`, `writeCell`, `letrec`, `force` and `fill`, whose rules are
    not among the pure head rules. A `fail` leaf is a `perform`. *)
let stage5_node (e: exp) : bool =
  match e with
  | EPerform _ _ _ _ | EHandle _ _ | ERegion _ _ _ | ERegionOpen _ _ _
  | EReadCell _ _ | EWriteCell _ _ _ | ELetRec _ _ | EForce _ | EFill _ _ -> false
  | _ -> true

(** `e` has no such node anywhere, decision trees, `λ` bodies and every
    other subterm included. *)
let stage5_frag (e: exp) : bool = exp_all stage5_node e

(** * Preconditions *)

(** The call of the chain `r = M.f [[κ̄]] ᾱ` respects the ABI precondition
    of `M.f`: `gpre M.f (values(ᾱ))`. Whether `δ_f` exists and returns an
    outcome on it is not asked here: coverage (`covers`) gives the
    implementation, and condition (3) of `genv_ok` its outcome on a typed
    call inside `gpre`. *)
let foreign_pre_ok (gi: genv) (r: exp) : prop =
  match decompose_global_app r with
  | Some (q, _, args) -> gi.gpre q (value_args args)
  | None -> False

(** `e` respects the preconditions as far as its next step: every
    saturated chain of values of a foreign in an evaluation position of `e`
    respects the ABI precondition of its foreign (spec 06 §Conformance of
    the global environment, "e respects preconditions under G", read for
    the step from `e`; the reducts of `e` carry it themselves).

    This is the program's obligation, and the only one on the term; it is
    discharged by the program, not by `G` (spec 06 §An ABI precondition is
    where condition (3) stops asking). The implementer's obligation is
    `genv_ok`, and a call on which `δ_f` returns `None` is a point where
    the relation is partial, which neither obligation rules out outside
    `gpre`. *)
let pre_ok (sg: sig) (gi: genv) (e: exp) : prop =
  forall (fs: list frame) (r: exp). {:pattern plug fs r}
    (frames_ok sg fs /\ e == plug fs r /\ V.foreign_redex sg r) ==> foreign_pre_ok gi r

(** * Descending into a frame *)

val stage5_frag_plug1 (f: frame) (e: exp)
  : Lemma (requires stage5_frag (plug1 f e)) (ensures stage5_frag e)

val covers_plug1 (sg: sig) (gi: genv) (f: frame) (e: exp)
  : Lemma (requires covers sg gi (plug1 f e)) (ensures covers sg gi e)

val pre_ok_plug1 (sg: sig) (gi: genv) (f: frame) (e: exp)
  : Lemma (requires frame_ok sg f /\ pre_ok sg gi (plug1 f e)) (ensures pre_ok sg gi e)

(** At the root, `pre_ok` is the precondition of the redex itself. *)
val pre_ok_root (sg: sig) (gi: genv) (e: exp)
  : Lemma (requires pre_ok sg gi e /\ V.foreign_redex sg e) (ensures foreign_pre_ok gi e)

(** * Introducing preconditions *)

(** `pre_ok` read one frame at a time: `e` respects the preconditions if
    it does at its root, when it is a saturated foreign chain, and if every
    hole of a frame `e` is plugged from does. *)
val pre_ok_intro (sg: sig) (gi: genv) (e: exp)
  : Lemma (requires (V.foreign_redex sg e ==> foreign_pre_ok gi e) /\
                    (forall (f: frame) (x: exp).
                       (frame_ok sg f /\ plug1 f x == e) ==> pre_ok sg gi x))
          (ensures pre_ok sg gi e)

(** A value respects every precondition: every hole of an evaluation
    context it is plugged from holds a value
    (`Stella.Core.Semantics.Ctx.plug1_not_value`), and a saturated foreign
    chain is none. *)
val value_pre_ok (sg: sig) (gi: genv) (v: exp)
  : Lemma (requires V.is_value sg v) (ensures pre_ok sg gi v)

(** * Values and faults *)

(** A value does not step. *)
val value_no_step (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#c: config) (h: step sg gi ra st e ra' st' c)
  : Lemma (requires V.is_value sg e) (ensures False)

(** The redex `r` is a saturated chain of values of a foreign `M.f` whose
    values `v̄` satisfy `gpre M.f`, and `δ_f(v̄)` is the ABI fault `a`. *)
let foreign_faults (sg: sig) (gi: genv) (r: exp) (a: abi_fault) : prop =
  V.foreign_redex sg r /\
  (match decompose_global_app r with
   | Some (q, _, args) ->
     gi.gpre q (value_args args) /\
     (match gi.gimpl q with
      | Some f -> f (value_args args) == Some (FOFault a)
      | None -> False)
   | None -> False)

(** A step of the stage-5 fragment to a fault produces an ABI fault, never
    `φ_init`, and leaves `R` and `N` as they are: it is the rule for a
    saturated foreign chain at an evaluation position of `e`, whose
    implementation returns that fault, propagated out of the context. *)
val step_fault_shape (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#phi: fault) (h: step sg gi ra st e ra' st' (CFault phi))
  : Lemma (requires stage5_frag e)
          (ensures FAbi? phi /\ ra' == ra /\ st' == st /\
                   (exists (fs: list frame) (r: exp) (a: abi_fault).
                      phi == FAbi a /\ frames_ok sg fs /\ e == plug fs r /\
                      foreign_faults sg gi r a))
