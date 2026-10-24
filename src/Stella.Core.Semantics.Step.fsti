(**
 * The reduction relation (spec 06 §Reduction, §Ordinary reduction,
 * §Chains of a constructor or a foreign, §Pattern matching, §Join points,
 * §Operations and handlers, §Where a handler finishes, §Regions, §Cells,
 * §Evaluation contexts).
 *
 *     pure_head sg G e c                    G ⊢ e → c, a head rule that
 *                                           leaves the store alone
 *     eff_head sg G e c                     G ⊢ e → c, a rule of
 *                                           operations and handlers
 *     region_head sg G R e R' c             G ⊢ e → c, a rule of regions
 *                                           and cells, from the names `R`
 *                                           to the names `R'`
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
 * points. `eff_head` holds the rules of spec 06 §Operations and handlers
 * and §Where a handler finishes. They read neither the store nor `R`
 * either, and form a group of their own: the rules that install, remove
 * and reinstall a handler. `region_head` holds the rules of spec 06
 * §Regions and §Cells. They leave the store alone, and the opening of a
 * region is the one rule that changes `R`, adding the name it allocates.
 * Each group is added to `step` by a constructor of its own (`S_Pure`,
 * `S_Eff`, `S_Region`). The rules of recursive bindings are not among the
 * rules of `step`.
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
 * (`Stella.Core.Syntax.fail_exp`), so it needs no rule of its own: the
 * rules of operations and handlers reduce it.
 *
 * ## Fragments
 *
 * `stage5_frag` is the fragment whose terms only the pure head rules
 * reduce, `stage6_frag` the fragment whose terms the pure head rules and
 * the rules of operations and handlers reduce, and `stage7_frag` the
 * fragment whose terms these and the rules of regions and cells reduce.
 * Each rules out the forms of the rules beyond it, at every node of the
 * term. `stage6_step` picks out the derivations of `step` that use no rule
 * of regions and cells.
 *)
module Stella.Core.Semantics.Step
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Prim
open Stella.Core.Region
open Stella.Core.Spine
open Stella.Core.Erase
open Stella.Core.Typing.Aux
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Ctx.Ren
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

  (** `M.f [[κ̄]] ᾱ  →  δᵀ_f(instance(M.f [[κ̄]] ᾱ), values(ᾱ))` for a
      saturated chain of values of a foreign (`foreign_redex`) with an entry
      `fe` in `G`, whose erased values `⌊values(ᾱ)⌋` satisfy the erased
      precondition `fe_pre`, where the typed adapter returns an outcome on
      the instance of the chain (`chain_instance`) and its values: a value
      as a term, an ABI fault as a fault (`foreign_config`). The instance is
      read and not passed on: the erased function `fe_erased` is not
      consulted, and erasure coherence (condition (3) of `genv_ok`) is what
      ties the outcome to it. A call outside `fe_pre` has no step, whatever
      the adapter returns on it, and neither has one on which the adapter
      returns `None` (spec 06 §Chains of a constructor or a foreign).

      The rule of spec 06 also has the premise that `G` is Core-modelled.
      The relation here is defined for every `G` of this shape, and that
      premise is clause (d) of the correspondence contract with the
      definedness of both functions, which `genv_ok` asks and every
      theorem assumes. *)
  | PH_Foreign :
      #e:exp -> #q:qname -> #ks:list kind -> #args:list spine_arg ->
      #fe:foreign_entry -> #o:foreign_outcome ->
      squash (V.foreign_redex sg e /\ decompose_global_app e == Some (q, ks, args)) ->
      squash (gi.gforeign q == Some fe) ->
      squash (fe.fe_pre (L.map erase (value_args args))) ->
      squash (fe.fe_adapt (chain_instance e) (value_args args) == Some o) ->
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

(** * The rules of operations and handlers

    Spec 06 §Operations and handlers, §Where a handler finishes. A handler
    `h = { handles ent ; … }` has the key `k = key(ent)` (`handler_key`).
    The `perform` it answers stands in the hole of an `Ev_k` (`ev_k k fs`
    with `frames_ok sg fs`): no `handle` of key `k` stands between, so the
    chosen handler is the innermost one of its key, and a handler of any
    other key is a frame of `Ev_k` like any other. The key is read from
    `ent`, never from a clause; the clause is the first one named `op`
    (`clause_of`), a function of the clauses rather than a choice among
    them, so the rules are deterministic whatever clauses a handler holds.

    The element is `E τ̄` or `s : E τ̄` (`EntEff lbl q ts`), and `E`'s
    signature is read from `Σ` (`sg.effects q = Some ei`,
    `op_of ei op = Some os`). The `perform` writes one type `σ_j` per binder
    `b_j` of the operation and the clause binds as many
    (`|σ̄| = |os.binders| = nb`).

    ## de Bruijn reading

    The clause body stands under the `nb` type binders `b̄`, the last one
    being type index 0 (`Stella.Core.Syntax`, design §3.1), as the clause
    is typed under `push_tvars g os.binders`. `b̄ := σ̄` is therefore
    `sub_ty_exp (list_tsub (rev σ̄))` (`binders_tsub`), which sends type
    index `i < nb` to `σ_{nb-1-i}` and lowers the outer indices by `nb`:
    the instantiation `op_inst` applies to the operation's types.

    The body of a `full` clause stands under `x` then `k`, so `k` is term
    index 0 and `x` index 1 (`push_var (push_var … σ) κ`). Once its type
    binders are instantiated, both are replaced at once by
    `list_esub [k_v; v]`, which is `list_esub (rev [v; k_v])` for the
    telescope `(x, k)`. The body of a `fast` clause binds `x` alone, at
    index 0 (`subst1_tm`). The terms substituted stand outside the clause,
    under no type binder of it, so the type binders are instantiated
    first and the term substitution needs no type shift.

    `handle Ev_k[y] with h` stands under one new term binder `y`, the
    parameter of the continuation or the binder of the `let`, at index 0.
    The context and the handler move under it, so their free term
    variables are shifted by one (`resume`).

    ## The continuation's annotation

    Spec 06 writes the continuation `λ(y : τ') / ρ. …` with `ρ` the row the
    `handle` stands at, which the term does not record. The written
    continuation type `κ` of a `full` clause records both: instantiated at
    `σ̄`, it is a function type `τ' -{ρ}-> β` (`as_function`), and the
    annotation of the `λ` is read from it. Where it is no function type,
    the rule does not apply. The `let` of a `fast` clause is annotated with
    the instantiated result type `op_inst τ̄ σ̄ τ_res`.

    `fail τ` is `perform Partial.abort [τ] Prim.Unit`, so these rules
    reduce it, the form of the clause for `abort` deciding which. *)

(** The first clause of `cs` for the operation `op`. *)
let rec clause_of (op: opname) (cs: list clause) : Tot (option clause) (decreases cs) =
  match cs with
  | [] -> None
  | c :: cs -> if clause_op c = op then Some c else clause_of op cs

(** A clause found by `clause_of op` is one of `cs` and is named `op`. *)
val clause_of_mem (op: opname) (cs: list clause) (c: clause)
  : Lemma (requires clause_of op cs == Some c) (ensures clause_op c == op /\ L.memP c cs)

(** `b̄ := σ̄` for the type binders `b̄` of a clause. *)
let binders_tsub (ss: list typ) : tsub = list_tsub (L.rev ss)

(** `handle Ev_k[y] with h` under the binder of `y`, index 0. *)
let resume (fs: list frame) (h: handler) : exp =
  EHandle (plug (ren_frames (shift 1) fs) (EVar 0)) (ren_handler (shift 1) h)

(** The continuation `λ(y : τ') / ρ. handle Ev_k[y] with h`. *)
let continuation (tp rho: typ) (fs: list frame) (h: handler) : exp =
  ELam tp rho (resume fs h)

(** `e_i[b̄ := σ̄, x := v, k := λ(y : τ') / ρ. handle Ev_k[y] with h]` for
    the body `e_i` of a `full` clause. *)
let full_reduct (ss: list typ) (v: exp) (tp rho: typ) (fs: list frame) (h: handler)
  (body: exp) : exp =
  sub_tm (list_esub [continuation tp rho fs h; v]) (sub_ty_exp (binders_tsub ss) body)

(** `let y : τ' = e_i[b̄ := σ̄, x := v] in (handle Ev_k[y] with h)` for the
    body `e_i` of a `fast` clause, `τ' = op_inst τ̄ σ̄ τ_res`. *)
let fast_reduct (ts ss: list typ) (os: op_sig) (v: exp) (fs: list frame) (h: handler)
  (body: exp) : exp =
  ELet (op_inst ts ss os.res) (subst1_tm v (sub_ty_exp (binders_tsub ss) body)) (resume fs h)

noeq type eff_head (sg: sig) (gi: genv) : exp -> config -> Type =

  (** `handle v with h  →  e_r[x := v]` *)
  | EH_Return :
      #v:exp -> #h:handler ->
      squash (V.is_value sg v) ->
      eff_head sg gi (EHandle v h) (CTerm (subst1_tm v h.h_ret))

  (** `handle Ev_k[perform k.op [σ̄] v] with h
         →  e_i[b̄ := σ̄, x := v, k := λ(y : τ') / ρ. handle Ev_k[y] with h]`
      for the clause `full op [b̄] (x : σ, k : κ) -> e_i`, with
      `κ[b̄ := σ̄] = τ' -{ρ}-> β`. *)
  | EH_Full :
      #fs:list frame -> #k:key -> #op:opname -> #ss:list typ -> #v:exp -> #h:handler ->
      #lbl:option string -> #q:qname -> #ts:list typ -> #ei:effect_info -> #os:op_sig ->
      #nb:nat -> #s:typ -> #kt:typ -> #body:exp -> #tp:typ -> #rho:typ -> #bt:typ ->
      squash (frames_ok sg fs /\ ev_k k fs /\ V.is_value sg v) ->
      squash (h.h_ent == EntEff lbl q ts /\ handler_key h == k) ->
      squash (sg.effects q == Some ei /\ op_of ei op == Some os) ->
      squash (clause_of op h.h_clauses == Some (CFull op nb s kt body) /\
              L.length ss == nb /\ nb == L.length os.binders) ->
      squash (as_function sg (sub_ty (binders_tsub ss) kt) == Some (tp, rho, bt)) ->
      eff_head sg gi (EHandle (plug fs (EPerform k op ss v)) h)
        (CTerm (full_reduct ss v tp rho fs h body))

  (** `handle Ev_k[perform k.op [σ̄] v] with h
         →  let y : τ' = e_i[b̄ := σ̄, x := v] in (handle Ev_k[y] with h)`
      for the clause `fast op [b̄] (x : σ) -> e_i`. *)
  | EH_Fast :
      #fs:list frame -> #k:key -> #op:opname -> #ss:list typ -> #v:exp -> #h:handler ->
      #lbl:option string -> #q:qname -> #ts:list typ -> #ei:effect_info -> #os:op_sig ->
      #nb:nat -> #s:typ -> #body:exp ->
      squash (frames_ok sg fs /\ ev_k k fs /\ V.is_value sg v) ->
      squash (h.h_ent == EntEff lbl q ts /\ handler_key h == k) ->
      squash (sg.effects q == Some ei /\ op_of ei op == Some os) ->
      squash (clause_of op h.h_clauses == Some (CFast op nb s body) /\
              L.length ss == nb /\ nb == L.length os.binders) ->
      eff_head sg gi (EHandle (plug fs (EPerform k op ss v)) h)
        (CTerm (fast_reduct ts ss os v fs h body))

(** An effect rule rewrites a `handle` and steps to a term, never to a
    fault. It reads no store and no region name: `S_Eff` concludes with
    the same `R` and `N` on both sides. *)
val eff_step_shape (#sg: sig) (#gi: genv) (#e: exp) (#c: config) (h: eff_head sg gi e c)
  : Lemma (EHandle? e /\ CTerm? c)

(** A value is no redex of an effect rule. *)
val value_no_eff_head (#sg: sig) (#gi: genv) (#e: exp) (#c: config) (h: eff_head sg gi e c)
  : Lemma (requires V.is_value sg e) (ensures False)

(** * The rules of regions and cells

    Spec 06 §Regions, §Cells. `region_head sg G R e R' c` reads `R`, the
    region names allocated so far, and gives `R'`.

    An opening allocates a name `a` that is in neither `R` nor the redex,
    its layout and initial values included, and steps to
    `region⟨a⟩ ( k̄ ↦ v̄ ) in e[ℓ := a]`: the cells hold the initial values
    under the layout's keys, in the layout's order (`init_cells`), and the
    body is opened with `a` (`Stella.Core.Region.open_region`), in its
    type annotations as well as its terms. `R'` is `a :: R`. A value
    reaching an open region frame closes it, and every other rule keeps
    `R`.

    A cell `a.k` is read or written by the innermost open region frame
    named `a`: the `readCell` or `writeCell` stands in the hole of an
    `Ev_ℓ` (`ev_l a fs` with `frames_ok sg fs`), which has no open region
    frame of that name. The reference is `RFree a`, a closed term holding
    no `RBound`, and the frame holds values (`cells_values`). A read
    requires `θ` to have a cell of the key `k` and reads the first one
    (`L.assoc`); a write requires one as well and replaces the value of
    the first one (`cells_update`), every cell keeping its key and its
    position. *)

(** `Prim.Unit` *)
let unit_exp : exp = EGlobal prim_unit_ctor []

(** `( k̄ ↦ v̄ )`: each key with the value at its position, in order. *)
let rec init_cells (ks: list key) (vs: list exp) : Tot (list (key & exp)) (decreases ks) =
  match ks, vs with
  | k :: ks', v :: vs' -> (k, v) :: init_cells ks' vs'
  | _ -> []

(** `θ[k ↦ v]`: the first cell of the key `k` holds `v`, and every cell
    keeps its key and its position. *)
let rec cells_update (th: list (key & exp)) (k: key) (v: exp)
  : Tot (list (key & exp)) (decreases th) =
  match th with
  | [] -> []
  | (k', w) :: th' -> if k' = k then (k', v) :: th' else (k', w) :: cells_update th' k v

noeq type region_head (sg: sig) (gi: genv) : list atom -> exp -> list atom -> config -> Type =

  (** `region [ℓ] ( k̄ : σ̄ ) @ ( v̄ ) in e  →  region⟨a⟩ ( k̄ ↦ v̄ ) in e[ℓ := a]`,
      `a` fresh for `R` and for the redex, with `R' = a :: R` *)
  | RH_Open :
      #ra:list atom -> #lay:list (key & typ) -> #vs:list exp -> #body:exp -> #a:atom ->
      squash (L.for_all (V.is_value sg) vs /\ L.length vs == L.length lay) ->
      squash (~(L.mem a ra) /\ ~(L.mem a (frn_exp (ERegion lay vs body)))) ->
      region_head sg gi ra (ERegion lay vs body) (a :: ra)
        (CTerm (ERegionOpen a (init_cells (L.map fst lay) vs) (open_region a body)))

  (** `region⟨a⟩ θ in v  →  v` *)
  | RH_Exit :
      #ra:list atom -> #a:atom -> #th:list (key & exp) -> #v:exp ->
      squash (V.is_value sg v) ->
      region_head sg gi ra (ERegionOpen a th v) ra (CTerm v)

  (** `region⟨a⟩ θ in Ev_ℓ[readCell a.k]  →  region⟨a⟩ θ in Ev_ℓ[θ(k)]` *)
  | RH_Read :
      #ra:list atom -> #a:atom -> #th:list (key & exp) -> #fs:list frame -> #k:key -> #v:exp ->
      squash (frames_ok sg fs /\ ev_l a fs /\ cells_values sg th) ->
      squash (L.assoc k th == Some v) ->
      region_head sg gi ra (ERegionOpen a th (plug fs (EReadCell (RFree a) k))) ra
        (CTerm (ERegionOpen a th (plug fs v)))

  (** `region⟨a⟩ θ in Ev_ℓ[writeCell a.k v]
         →  region⟨a⟩ θ[k ↦ v] in Ev_ℓ[Prim.Unit]` *)
  | RH_Write :
      #ra:list atom -> #a:atom -> #th:list (key & exp) -> #fs:list frame -> #k:key -> #v:exp ->
      squash (frames_ok sg fs /\ ev_l a fs /\ cells_values sg th) ->
      squash (V.is_value sg v /\ Some? (L.assoc k th)) ->
      region_head sg gi ra (ERegionOpen a th (plug fs (EWriteCell (RFree a) k v))) ra
        (CTerm (ERegionOpen a (cells_update th k v) (plug fs unit_exp)))

(** A rule of regions and cells rewrites a `region` or an open region
    frame and steps to a term, never to a fault. It keeps `R`, or adds to
    it one name not already in it. *)
val region_step_shape (#sg: sig) (#gi: genv) (#ra: list atom) (#e: exp) (#ra': list atom)
  (#c: config) (h: region_head sg gi ra e ra' c)
  : Lemma ((ERegion? e \/ ERegionOpen? e) /\ CTerm? c /\
           (ra' == ra \/ (exists (a: atom). ra' == a :: ra /\ ~(L.mem a ra))))

(** A value is no redex of a rule of regions and cells. *)
val value_no_region_head (#sg: sig) (#gi: genv) (#ra: list atom) (#e: exp) (#ra': list atom)
  (#c: config) (h: region_head sg gi ra e ra' c)
  : Lemma (requires V.is_value sg e) (ensures False)

(** * Steps *)

(** `G ⊢ N; e → N'; c`, with `R` and `R'` the region names allocated
    before and after. *)
noeq type step (sg: sig) (gi: genv)
  : list atom -> store -> exp -> list atom -> store -> config -> Type =
  (** A pure head rule, which leaves `R` and `N` as they are. *)
  | S_Pure :
      #ra:list atom -> #st:store -> #e:exp -> #c:config ->
      pure_head sg gi e c ->
      step sg gi ra st e ra st c

  (** A rule of operations and handlers, which leaves `R` and `N` as they
      are. *)
  | S_Eff :
      #ra:list atom -> #st:store -> #e:exp -> #c:config ->
      eff_head sg gi e c ->
      step sg gi ra st e ra st c

  (** A rule of regions and cells, which leaves `N` as it is. *)
  | S_Region :
      #ra:list atom -> #st:store -> #e:exp -> #ra':list atom -> #c:config ->
      region_head sg gi ra e ra' c ->
      step sg gi ra st e ra' st c

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

(** * The fragments of stages 5, 6 and 7 *)

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

(** A node is none of `region`, an open region frame, `readCell`,
    `writeCell`, `letrec`, `force` and `fill`, whose rules are neither
    pure head rules nor rules of operations and handlers. A `perform`, a
    `fail` leaf among them, and a `handle` are nodes of the fragment. *)
let stage6_node (e: exp) : bool =
  match e with
  | ERegion _ _ _ | ERegionOpen _ _ _ | EReadCell _ _ | EWriteCell _ _ _
  | ELetRec _ _ | EForce _ | EFill _ _ -> false
  | _ -> true

(** `e` has no such node anywhere. *)
let stage6_frag (e: exp) : bool = exp_all stage6_node e

(** A node is none of `letrec`, `force` and `fill`, whose rules are not
    among the rules of `step`. *)
let stage7_node (e: exp) : bool =
  match e with
  | ELetRec _ _ | EForce _ | EFill _ _ -> false
  | _ -> true

(** `e` has no such node anywhere. *)
let stage7_frag (e: exp) : bool = exp_all stage7_node e

(** The stage-5 fragment is part of the stage-6 fragment. *)
val stage5_frag_stage6 (e: exp) : Lemma (requires stage5_frag e) (ensures stage6_frag e)

(** The stage-6 fragment is part of the stage-7 fragment. *)
val stage6_frag_stage7 (e: exp) : Lemma (requires stage6_frag e) (ensures stage7_frag e)

(** A term of the stage-5 fragment has no `handle` at its root, so no rule
    of operations and handlers applies to it. *)
val stage5_no_eff (#sg: sig) (#gi: genv) (#e: exp) (#c: config) (h: eff_head sg gi e c)
  : Lemma (requires stage5_frag e) (ensures False)

(** A term of the stage-6 fragment has no `region` and no open region
    frame at its root, so no rule of regions and cells applies to it. *)
val stage6_no_region (#sg: sig) (#gi: genv) (#ra: list atom) (#e: exp) (#ra': list atom)
  (#c: config) (h: region_head sg gi ra e ra' c)
  : Lemma (requires stage6_frag e) (ensures False)

(** The derivation `s` uses no rule of regions and cells: its head rule,
    under the frames of `S_Ctx` and `S_CtxFault`, is a pure head rule or a
    rule of operations and handlers. *)
let rec stage6_step (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#c: config) (s: step sg gi ra st e ra' st' c)
  : Tot bool (decreases s) =
  match s with
  | S_Pure _ | S_Eff _ -> true
  | S_Region _ -> false
  | S_Ctx _ _ s' -> stage6_step s'
  | S_CtxFault _ _ s' -> stage6_step s'

(** * Preconditions *)

(** The call of the chain `r = M.f [[κ̄]] ᾱ` respects the precondition of
    the entry of `M.f`: `fe_pre ⌊values(ᾱ)⌋`. Whether `M.f` has an entry
    and its adapter an outcome on the call is not asked here: coverage
    (`covers`) gives the entry, and condition (3) of `genv_ok` the outcome
    of a typed call inside `fe_pre`; a foreign with no entry has no
    precondition to respect. *)
let foreign_pre_ok (gi: genv) (r: exp) : prop =
  match decompose_global_app r with
  | Some (q, _, args) ->
    (match gi.gforeign q with
     | Some fe -> fe.fe_pre (L.map erase (value_args args))
     | None -> True)
  | None -> False

(** `e` respects the preconditions as far as its next step: every
    saturated chain of values of a foreign in an evaluation position of `e`
    respects the erased precondition of its foreign's entry, on its erased
    value arguments (spec 06 §An ABI precondition is where condition (3)
    stops asking, "e respects preconditions under G", read for the step
    from `e`; the reducts of `e` carry it themselves).

    This is the program's obligation, the only one of the three
    obligations that the term carries; it is
    discharged by the program, not by `G` (spec 06 §An ABI precondition is
    where condition (3) stops asking). The implementer's obligation is
    `genv_ok`, and a call on which the adapter returns `None` is a point
    where the relation is partial, which neither obligation rules out
    outside `fe_pre`. *)
let pre_ok (sg: sig) (gi: genv) (e: exp) : prop =
  forall (fs: list frame) (r: exp). {:pattern plug fs r}
    (frames_ok sg fs /\ e == plug fs r /\ V.foreign_redex sg r) ==> foreign_pre_ok gi r

(** * Descending into a frame *)

val stage5_frag_plug1 (f: frame) (e: exp)
  : Lemma (requires stage5_frag (plug1 f e)) (ensures stage5_frag e)

val stage6_frag_plug1 (f: frame) (e: exp)
  : Lemma (requires stage6_frag (plug1 f e)) (ensures stage6_frag e)

val stage7_frag_plug1 (f: frame) (e: exp)
  : Lemma (requires stage7_frag (plug1 f e)) (ensures stage7_frag e)

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

(** The redex `r` is a saturated chain of values of a foreign `M.f` with an
    entry `fe`, whose erased values `⌊v̄⌋` satisfy `fe_pre`, and the
    adapter gives the ABI fault `a` at the instance of `r` and `v̄`. *)
let foreign_faults (sg: sig) (gi: genv) (r: exp) (a: abi_fault) : prop =
  V.foreign_redex sg r /\
  (match decompose_global_app r with
   | Some (q, _, args) ->
     (match gi.gforeign q with
      | Some fe ->
        fe.fe_pre (L.map erase (value_args args)) /\
        fe.fe_adapt (chain_instance r) (value_args args) == Some (FOFault a)
      | None -> False)
   | None -> False)

(** A step of the stage-6 fragment to a fault produces an ABI fault, never
    `φ_init`, and leaves `R` and `N` as they are: it is the rule for a
    saturated foreign chain at an evaluation position of `e`, whose
    adapter returns that fault, propagated out of the context. No rule of
    operations and handlers and no rule of regions and cells produces a
    fault (`eff_step_shape`, `region_step_shape`). *)
val step_fault_shape (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#phi: fault) (h: step sg gi ra st e ra' st' (CFault phi))
  : Lemma (requires stage6_frag e)
          (ensures FAbi? phi /\ ra' == ra /\ st' == st /\
                   (exists (fs: list frame) (r: exp) (a: abi_fault).
                      phi == FAbi a /\ frames_ok sg fs /\ e == plug fs r /\
                      foreign_faults sg gi r a))

(** A step of the stage-6 fragment to a term leaves `R` and `N` as they
    are: it is a pure head rule or a rule of operations and handlers at an
    evaluation position of `e`. *)
val step_term_shape (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#e': exp) (h: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (requires stage6_frag e) (ensures ra' == ra /\ st' == st)

(** A step to a term leaves `N` as it is, and keeps `R` or adds to it one
    name not already in it: the opening of a region at an evaluation
    position of `e` is the one rule that changes `R`. *)
val step_term_names (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#e': exp) (h: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (st' == st /\ (ra' == ra \/ (exists (a: atom). ra' == a :: ra /\ ~(L.mem a ra))))

(** A step of a term of the stage-6 fragment uses no rule of regions and
    cells. *)
val stage6_frag_step (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#c: config) (s: step sg gi ra st e ra' st' c)
  : Lemma (requires stage6_frag e) (ensures stage6_step s)
