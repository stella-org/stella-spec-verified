(**
 * The initialization-safety judgement (D14; spec 10).
 *
 * A recursive group `R = { x1 = e1; …; xn = en }` is initialized in the
 * order written, and it is initialization-safe when each `ei` reads, before
 * it has a value, only members written before it (spec 10 §The rule). What
 * a right-hand side reads is an abstract interpretation of Core giving, for
 * each expression `e`, two sets of members of `R`:
 *
 *   - `imm(e)`, what evaluating `e` reads before it has a value
 *     (`reads_imm`);
 *   - `lat(e)`, what the value of `e` may read later, when a closure it
 *     holds is applied (`reads_lat`).
 *
 * Spec 10 takes them as the least fixed point of monotone rules over maps
 * from members to witness sets. Witnesses only locate a refusal, so here
 * the maps are sets, and the least fixed point is an inductive relation:
 * `reads_imm … e m` holds when `m ∈ imm(e)`, and it has a derivation exactly
 * when finitely many applications of the rules put `m` there.
 *
 * ## Members
 *
 * The judgement is taken for one group (`group`), and its sets hold the
 * members of that group alone, each named by its position in the written
 * order, `0` being the first member. A member is referred to in one of two
 * ways:
 *
 *   - in a local `letrec`, by a term variable the group binds; the
 *     variable environment maps it to `VMem k`;
 *   - in a top-level `rec` group, by a global `EGlobal q ks` with `q` in the
 *     group; `gmem q` is then `Some k`.
 *
 * ## Environments
 *
 * The rules are read under two environments that follow the de Bruijn
 * binders of the term (design §1.1, §3.1).
 *
 *   - A variable environment (`venv`) has one entry per term variable in
 *     scope, the head being index 0. An entry says whether the variable is a
 *     member of `R` or a local `y`, and for a local it determines `ρ(y)`,
 *     what the value bound to `y` may read later. `ρ(y)` is itself a `lat`,
 *     so an entry stores the expression and environment it is the `lat` of,
 *     and the rules for a variable recur into them. A variable beyond the
 *     environment is bound outside `R`'s right-hand sides and is at `ρ = ∅`.
 *   - A join environment (`jenv`) has one entry per join point in scope,
 *     the head being join index 0. An entry is the `letjoin` that binds the
 *     join point, together with the environments it stands in, from which
 *     `arg_j`, `imm_j` and `lat_j` are read.
 *
 * Both are syntax: an environment is computed from the term alone, and only
 * the relations below give it a meaning.
 *
 * ## Join points
 *
 * A join point is read where it is jumped to (spec 10 §What an initializer
 * reads). `jump j (ē)` reads `imm_j` and has `lat_j` as its `lat`: the `imm`
 * and `lat` of the join body, its parameters at `arg_j`. A parameter of the
 * join point is the entry `VArg d p`, and `arg_j` at it is what an argument
 * of any `jump` to `j` within its scope, the join body and the continuation,
 * may read later. A join point jumping to itself recurs through its own
 * entry, within the same least fixed point.
 *
 * Join indices are counted syntactically: only `letjoin` pushes onto the
 * join environment, and every other form, `λ` included, passes it
 * unchanged, as `Stella.Core.Subst.ren_jp` does. In a `jp_scoped` term
 * (`Stella.Core.Value`) a jump targets a `letjoin` standing within the same
 * body of a `Δ`-discarding form, so the count finds the join point its
 * typing gives it. A jump whose index is beyond the join environment reads
 * nothing.
 *
 * ## Run-time forms
 *
 * The run-time forms (spec 06 §Run-time forms) arise from source terms by
 * substitution and reduction, and a `letrec` judged after reduction can hold
 * them, `force ν` in particular after an enclosing group is allocated. They
 * have rules of their own, each the rule of the source form it stands for:
 *
 *   - `match θ dt` is `case`, `θ` its scrutinees;
 *   - `openEffC [ρ] e` passes through, as `openEff` does;
 *   - `force ν` and `opaque ω [τ]` read nothing: a location and an opaque
 *     value are built outside every group judged here, as a variable bound
 *     outside `R`'s right-hand sides is;
 *   - `fill ν e` stores the value of `e` where `force ν` reads it back, so
 *     it takes the default rule, as `writeCell` does;
 *   - `region⟨ℓ⟩ θ in e` counts everything it holds, as `region` does, `θ`
 *     standing for the initial values.
 *)
module Stella.Core.Init
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Spine
module L = FStar.List.Tot

(** * Arity *)

(** The number of value arguments a declared type accepts: the function
    arrows on its spine, reached through `forall` and constraint arrows in
    the order the cursor consumes them (spec 05 §The cursor). It is read
    from the declared type, so an arrow that only an instantiation produces
    is not counted. A chain the cursor walks consumes one of these arrows
    per value argument, and a saturated one has consumed all of them
    (`Stella.Core.Init.Lemmas`). *)
let rec decl_arity (sg: sig) (t: typ) : Tot nat (decreases t) =
  match t with
  | TForall _ b -> decl_arity sg b
  | TConstr _ b -> decl_arity sg b
  | TApp (TApp (TApp (TCon q []) _) _) t2 ->
    if is_function_tycon sg q then 1 + decl_arity sg t2 else 0
  | _ -> 0

(** The arity of a data constructor or a foreign `M.g`, from its declared
    scheme. *)
let global_arity (sg: sig) (q: qname) : option nat =
  match global_scheme sg q with
  | Some (_, _, t) -> Some (decl_arity sg t)
  | None -> None

(** The number of value arguments of a chain. *)
let rec value_count (args: list spine_arg) : Tot nat (decreases args) =
  match args with
  | [] -> 0
  | SVal _ :: args -> 1 + value_count args
  | _ :: args -> value_count args

(** * Variable and join environments *)

(** An entry of the variable environment: what a term variable in scope is,
    and so what reading it reads.

    - `VNone`: a local at `ρ = ∅`: a variable bound outside `R`'s
      right-hand sides, a `λ` parameter, a binder of a handler clause.
    - `VMem k`: the `k`-th member of `R`.
    - `VLat ve je e`: a local whose value is that of `e` under `ve` and `je`,
      so `ρ = lat(e)`: a `let` binder, and a `bind` of a decision tree, `e`
      being the scrutinee its occurrence starts from.
    - `VRec ve je bs k`: the `k`-th member, in written order, of a group
      `letrec bs` nested in `R` and standing under `ve` and `je`, a local at
      `ρ = lat(e'_k)`, `e'_k` taken under the nested group's environment
      (`push_rec ve je bs`).
    - `VArg d p`: the parameter of index `p` of the join point `d`, at
      `ρ = arg_j`. *)
type ventry =
  | VNone : ventry
  | VMem  : k:nat -> ventry
  | VLat  : ve:list ventry -> je:list jentry -> e:exp -> ventry
  | VRec  : ve:list ventry -> je:list jentry -> bs:list (typ & exp) -> k:nat -> ventry
  | VArg  : d:jentry -> p:nat -> ventry

(** A join point `letjoin j (x̄ : τ̄) : τ = e1 in e2` standing under `ve`
    and `je`: `JDef ve je n e1 e2`, `n` being the number of parameters. *)
and jentry =
  | JDef : ve:list ventry -> je:list jentry -> n:nat -> body:exp -> cont:exp -> jentry

type venv = list ventry

type jenv = list jentry

(** The entry of term variable `i`. A variable beyond the environment is at
    `ρ = ∅`. *)
let vlook (ve: venv) (i: nat) : ventry =
  match L.nth ve i with
  | Some v -> v
  | None -> VNone

(** The join point of join index `j`. *)
let jlook (je: jenv) (j: nat) : option jentry = L.nth je j

(** An expression together with the environments it is judged under. *)
noeq type child = {
  cv : venv;
  cj : jenv;
  ce : exp;
}

let mk (ve: venv) (je: jenv) (e: exp) : child = { cv = ve; cj = je; ce = e }

(** ** Pushing binders *)

(** The body of `let y = e1 in e2`, `y` at `ρ = lat(e1)`. *)
let push_let (ve: venv) (je: jenv) (e1: exp) : venv = VLat ve je e1 :: ve

(** `VRec ve je bs (n-1) … VRec ve je bs 0`: the entries of the members of
    `letrec bs` when `n = |bs|`, the last member at index 0. *)
let rec rec_entries (ve: venv) (je: jenv) (bs: list (typ & exp)) (n: nat)
  : Tot venv (decreases n) =
  if n = 0 then [] else VRec ve je bs (n - 1) :: rec_entries ve je bs (n - 1)

(** The right-hand sides and the body of `letrec bs` standing under `ve`
    and `je`. *)
let push_rec (ve: venv) (je: jenv) (bs: list (typ & exp)) : venv =
  L.append (rec_entries ve je bs (L.length bs)) ve

(** `VArg d p … VArg d (p+n-1)`: the parameters of the join point `d`, at
    indices `0 … n-1` when `p = 0`. *)
let rec arg_entries (d: jentry) (p: nat) (n: nat) : Tot venv (decreases n) =
  if n = 0 then [] else VArg d p :: arg_entries d (p + 1) (n - 1)

(** The join point a `letjoin j (x̄ : τ̄) : τ = e1 in e2` under `ve` and `je`
    binds. *)
let join_def (ve: venv) (je: jenv) (ts: list typ) (e1 e2: exp) : jentry =
  JDef ve je (L.length ts) e1 e2

(** The join environment of the scope of `d`: `d` at index 0. *)
let join_jenv (d: jentry) : jenv =
  match d with JDef _ je _ _ _ -> d :: je

(** The body of `d`, its parameters at `arg_j`. *)
let join_body (d: jentry) : child =
  match d with JDef ve je n e1 _ -> mk (L.append (arg_entries d 0 n) ve) (d :: je) e1

(** The continuation of `d`. *)
let join_cont (d: jentry) : child =
  match d with JDef ve je _ _ e2 -> mk ve (d :: je) e2

(** The scope of `d`: the expressions in which a `jump` can target it. *)
let join_scope (d: jentry) : list child = [join_body d; join_cont d]

(** The argument a `jump` with arguments `es`, written in order, hands the
    parameter of index `p` of `d`. The last parameter is index 0, so it is
    the argument at written position `n - 1 - p`. *)
let join_arg (d: jentry) (p: nat) (es: list exp) : option exp =
  match d with JDef _ _ n _ _ -> if p < n then L.nth es (n - 1 - p) else None

(** The scrutinee an occurrence starts from (spec 04 §Occurrences). *)
let rec occ_root (o: occ) : Tot nat (decreases o) =
  match o with
  | OScrut i -> i
  | OCtor o _ _ | ORecord o _ | OVariant o _ -> occ_root o

(** The entry `bind y o` pushes in a decision tree of `case (ē)` standing
    under `cve` and `je`: `y` at the `lat` of the scrutinee `o` starts from.
    An occurrence starting from no scrutinee binds a local at `ρ = ∅`. *)
let bind_entry (cve: venv) (je: jenv) (es: list exp) (o: occ) : ventry =
  match L.nth es (occ_root o) with
  | Some e -> VLat cve je e
  | None -> VNone

(** * Subexpressions *)

(** The expressions of a decision tree of `case (es)` standing under `cve`:
    its guards and leaves, each under the entries its `bind`s push. *)
let rec dt_children (cve: venv) (es: list exp) (ve: venv) (je: jenv) (dt: dtree)
  : Tot (list child) (decreases dt) =
  match dt with
  | DLeaf e -> [mk ve je e]
  | DBind o dt -> dt_children cve es (bind_entry cve je es o :: ve) je dt
  | DSwitchCtor _ bs df -> L.append (brs_children cve es ve je bs) (odt_children cve es ve je df)
  | DSwitchLit _ bs df -> L.append (brs_children cve es ve je bs) (dt_children cve es ve je df)
  | DSwitchKey _ bs df -> L.append (brs_children cve es ve je bs) (odt_children cve es ve je df)
  | DGuard e dt1 dt2 ->
    mk ve je e :: L.append (dt_children cve es ve je dt1) (dt_children cve es ve je dt2)

and odt_children (cve: venv) (es: list exp) (ve: venv) (je: jenv) (df: option dtree)
  : Tot (list child) (decreases df) =
  match df with
  | None -> []
  | Some dt -> dt_children cve es ve je dt

and brs_children (#lb: eqtype) (cve: venv) (es: list exp) (ve: venv) (je: jenv)
                 (bs: list (lb & dtree))
  : Tot (list child) (decreases bs) =
  match bs with
  | [] -> []
  | (_, dt) :: bs -> L.append (dt_children cve es ve je dt) (brs_children cve es ve je bs)

(** The bodies of a handler's operation clauses, each binder at `ρ = ∅`. *)
let rec clause_children (ve: venv) (je: jenv) (cs: list clause)
  : Tot (list child) (decreases cs) =
  match cs with
  | [] -> []
  | CFull _ _ _ _ b :: cs -> mk (VNone :: VNone :: ve) je b :: clause_children ve je cs
  | CFast _ _ _ b :: cs -> mk (VNone :: ve) je b :: clause_children ve je cs

(** The immediate subexpressions of `e` under `ve` and `je`, each under the
    environments the rules below judge it in. The expressions of a decision
    tree are immediate subexpressions of its `case`. *)
let children (ve: venv) (je: jenv) (e: exp) : list child =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> []
  | ELam _ _ b -> [mk (VNone :: ve) je b]
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b
  | EInject _ _ b | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b
  | EWriteCell _ _ b | EOpenEffC _ b | EFill _ b -> [mk ve je b]
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> [mk ve je e1; mk ve je e2]
  | ELet _ e1 e2 -> [mk ve je e1; mk (push_let ve je e1) je e2]
  | ELetRec bs b ->
    let ve' = push_rec ve je bs in
    L.append (L.map (fun (be: typ & exp) -> mk ve' je (snd be)) bs) [mk ve' je b]
  | ECase es dt | EMatch es dt -> L.append (L.map (mk ve je) es) (dt_children ve es ve je dt)
  | ELetJoin ts _ e1 e2 -> join_scope (join_def ve je ts e1 e2)
  | EJump _ es -> L.map (mk ve je) es
  | EHandle b h -> mk ve je b :: mk (VNone :: ve) je h.h_ret :: clause_children ve je h.h_clauses
  | ERegion _ es b -> L.append (L.map (mk ve je) es) [mk ve je b]
  | ERegionOpen _ th b -> L.append (L.map (fun (kv: key & exp) -> mk ve je (snd kv)) th) [mk ve je b]

(** `sub c s`: `s` is `c` or a subexpression of it at any depth, with the
    environments it is judged under. *)
noeq type sub : child -> child -> Type =
  | SubHere  : c:child -> sub c c
  | SubChild : #c:child -> #c1:child -> #s:child ->
               squash (L.memP c1 (children c.cv c.cj c.ce)) ->
               sub c1 s ->
               sub c s

(** * Groups *)

(** The group `R` a judgement is taken for.

    - `gmem q` is `Some k` when the global `q` is the `k`-th member of `R`
      (a top-level group), and `None` for every `q` in a local group.
    - `grhs` holds the right-hand sides in written order.
    - `genv` is the variable environment they stand under. *)
noeq type group = {
  gmem : qname -> option nat;
  grhs : list exp;
  genv : venv;
}

(** The right-hand side of the `k`-th member. *)
let rhs (g: group) (k: nat) : option exp = L.nth g.grhs k

(** `VMem (n-1) … VMem 0`: the members of a local group of `n` members, the
    last at index 0 (design §3.1). *)
let rec member_env (n: nat) : Tot venv (decreases n) =
  if n = 0 then [] else VMem (n - 1) :: member_env (n - 1)

(** A local group `letrec { x̄ : σ̄ = ē }`: the right-hand sides stand under
    the members, and every variable bound outside is at `ρ = ∅`. *)
let local_group (bs: list (typ & exp)) : group = {
  gmem = (fun _ -> None);
  grhs = L.map snd bs;
  genv = member_env (L.length bs);
}

(** The position of `q` in `qs`, its first occurrence. *)
let rec index_of (q: qname) (qs: list qname) : Tot (option nat) (decreases qs) =
  match qs with
  | [] -> None
  | q' :: qs ->
    if q = q' then Some 0
    else (match index_of q qs with Some i -> Some (i + 1) | None -> None)

(** A top-level group `rec { M.x̄ = ē }`, each member named by its global
    name. Its right-hand sides are closed. *)
let top_group (ms: list (qname & exp)) : group = {
  gmem = (fun q -> index_of q (L.map fst ms));
  grhs = L.map snd ms;
  genv = [];
}

(** * Classifying a form *)

(** `e` is an application `f v` within the chain of a data constructor or a
    foreign, through type and constraint applications, with no more value
    arguments than its arity (spec 10 §What an initializer reads, the row
    `M.c ē`). An application beyond the arity is a default application of
    the result of the prefix within it.

    The head is not a member of `R`. A member of a top-level group is a
    value declaration, which a well-formed `Σ` never also records as a
    constructor or a foreign (`Stella.Core.Sig.Wf.globals_disjoint`), so the
    condition only keeps a member read as a member under any `Σ`. *)
let spine_app (sg: sig) (g: group) (e: exp) : bool =
  match decompose_global_app e with
  | Some (q, _, args) ->
    None? (g.gmem q) &&
    (match global_arity sg q with
     | Some n -> value_count args <= n
     | None -> false)
  | None -> false

(** The forms whose `imm` and `lat` are those of their one subexpression:
    `Λ (a : κ). e`, `e [σ]`, `Λ (_ : C). e`, `e [•]`, `openEff [ρ] e`, and
    `openEffC [ρ] e`. *)
let through (e: exp) : option exp =
  match e with
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | EOpenEff _ b | EOpenEffC _ b -> Some b
  | _ -> None

(** The forms that build a record or a variant of their subexpressions:
    `extend k e1 e2`, `update k e1 e2`, `merge e1 e2`, `inject k [ρ] e`. *)
let builds (e: exp) : list exp =
  match e with
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> [e1; e2]
  | EInject _ _ b -> [b]
  | _ -> []

(** The forms that take a record or a variant apart: `select k e`,
    `restrict k e`, `weaken k [τ] e`, `absurd [τ] e`. *)
let takes (e: exp) : option exp =
  match e with
  | ESelect _ b | ERestrict _ b | EWeaken _ _ b | EAbsurd _ b -> Some b
  | _ -> None

(** The subexpressions of an application within a chain (`spine_app`). *)
let spine_parts (sg: sig) (g: group) (e: exp) : list exp =
  match e with
  | EApp f v -> if spine_app sg g e then [f; v] else []
  | _ -> []

(** The subexpressions of a form taking the default rule: an application
    that is not `spine_app`, `perform`, `writeCell`, and `fill`. *)
let default_parts (sg: sig) (g: group) (e: exp) : list exp =
  match e with
  | EApp f v -> if spine_app sg g e then [] else [f; v]
  | EPerform _ _ _ b | EWriteCell _ _ b | EFill _ b -> [b]
  | _ -> []

(** `case (ē) of dt` and `match θ dt`: the scrutinees and the tree. *)
let scrutinised (e: exp) : option (list exp & dtree) =
  match e with
  | ECase es dt | EMatch es dt -> Some (es, dt)
  | _ -> None

(** The forms that count everything they hold as read through them:
    `handle`, `region`, and `region⟨ℓ⟩`. *)
let is_whole (e: exp) : bool =
  match e with
  | EHandle _ _ | ERegion _ _ _ | ERegionOpen _ _ _ -> true
  | _ -> false

(** The subtrees of a `switchCtor`, `switchLit` or `switchKey`: its branches
    and its default. *)
let switch_subtrees (dt: dtree) : list dtree =
  match dt with
  | DSwitchCtor _ bs df -> L.append (L.map snd bs) (match df with Some d -> [d] | None -> [])
  | DSwitchLit _ bs df -> L.append (L.map snd bs) [df]
  | DSwitchKey _ bs df -> L.append (L.map snd bs) (match df with Some d -> [d] | None -> [])
  | _ -> []

(** * The judgement (spec 10 §What an initializer reads)

    `reads_imm sg g ve je e m`: `m ∈ imm(e)`, evaluating `e` under `ve` and
    `je` reads the member `m` of `g` before it has a value.

    `reads_lat sg g ve je e m`: `m ∈ lat(e)`, the value of `e` may read `m`
    later.

    `reads_imm_dt sg g cve es ve je dt m` and `reads_lat_dt …`: the same for
    a decision tree of `case (es)`, the `case` standing under `cve` and
    `je`, the tree under `ve`.

    `lat*(x)` of a member `x` is the `lat` of its right-hand side, under
    `g.genv` and no join point (`LMember`, `LMemberGlobal`).

    The constructors follow the rows of the tables of spec 10, each
    contributing one part of a union. A form with no constructor for a
    relation has the empty set there: `imm` of `λ` and of a local, `imm` and
    `lat` of a global not in `R`, a literal, `recordEmpty`, `readCell ℓ.k`,
    `force ν` and `opaque ω [τ]`.

    The default rule (`IDefault`, `IDefaultLat`, `LDefault`) is
    `imm = ⋃ (imm(s) ∪ lat(s))`, `lat = ⋃ lat(s)`, the promotion of a `lat`
    read being its membership in `imm`.

    A handling expression and a region (`is_whole`) have
    `imm = ⋃_s (imm(s) ∪ lat(s))` and `lat = ⋃_s lat(s)`, over every
    subexpression `s` at any depth of their parts, each binder of a clause
    at `ρ = ∅` (spec 10 §What an initializer reads, where a handling
    expression and a region count everything they hold as read through
    them). The `imm` of each part, which spec 10 writes beside them, is
    among them, a part being a subexpression of itself at depth 0; the two
    differ only in their witnesses. *)
noeq type reads_imm (sg: sig) (g: group) : venv -> jenv -> exp -> nat -> Type =
  (* `x`, a member: `{ x }` *)
  | IMember :
      #ve:venv -> #je:jenv -> #i:nat -> #k:nat ->
      squash (vlook ve i == VMem k) ->
      reads_imm sg g ve je (EVar i) k
  | IMemberGlobal :
      #ve:venv -> #je:jenv -> #q:qname -> #ks:list kind -> #k:nat ->
      squash (g.gmem q == Some k) ->
      reads_imm sg g ve je (EGlobal q ks) k
  (* `Λ`, `e [σ]`, constraint `Λ`, `e [•]`, `openEff`, `openEffC`: `imm(e)` *)
  | IThrough :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (through e == Some b) ->
      reads_imm sg g ve je b m ->
      reads_imm sg g ve je e m
  (* `extend`, `update`, `merge`, `inject`: `⋃ imm(eₖ)` *)
  | IBuild :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (L.memP b (builds e)) ->
      reads_imm sg g ve je b m ->
      reads_imm sg g ve je e m
  (* `select`, `restrict`, `weaken`, `absurd`: `imm(e)` *)
  | ITake :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (takes e == Some b) ->
      reads_imm sg g ve je b m ->
      reads_imm sg g ve je e m
  (* `M.c ē` within its arity: `⋃ imm(eₖ)` *)
  | ISpine :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (L.memP b (spine_parts sg g e)) ->
      reads_imm sg g ve je b m ->
      reads_imm sg g ve je e m
  (* the default rule: `⋃ (imm(sₖ) ∪ lat(sₖ))` *)
  | IDefault :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (L.memP b (default_parts sg g e)) ->
      reads_imm sg g ve je b m ->
      reads_imm sg g ve je e m
  | IDefaultLat :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (L.memP b (default_parts sg g e)) ->
      reads_lat sg g ve je b m ->
      reads_imm sg g ve je e m
  (* `let y = e1 in e2`: `imm(e1) ∪ imm(e2)`, `y` at `lat(e1)` *)
  | ILetBound :
      #ve:venv -> #je:jenv -> #t:typ -> #e1:exp -> #e2:exp -> #m:nat ->
      reads_imm sg g ve je e1 m ->
      reads_imm sg g ve je (ELet t e1 e2) m
  | ILetBody :
      #ve:venv -> #je:jenv -> #t:typ -> #e1:exp -> #e2:exp -> #m:nat ->
      reads_imm sg g (push_let ve je e1) je e2 m ->
      reads_imm sg g ve je (ELet t e1 e2) m
  (* `letrec { ȳ = ē' } in e`: `⋃ imm(e'ₖ) ∪ imm(e)`, each `yₖ` at `lat(e'ₖ)` *)
  | ILetRecRhs :
      #ve:venv -> #je:jenv -> #bs:list (typ & exp) -> #e:exp -> #t:typ -> #r:exp -> #m:nat ->
      squash (L.memP (t, r) bs) ->
      reads_imm sg g (push_rec ve je bs) je r m ->
      reads_imm sg g ve je (ELetRec bs e) m
  | ILetRecBody :
      #ve:venv -> #je:jenv -> #bs:list (typ & exp) -> #e:exp -> #m:nat ->
      reads_imm sg g (push_rec ve je bs) je e m ->
      reads_imm sg g ve je (ELetRec bs e) m
  (* `case (ē) of dt`: `⋃ imm(eₖ) ∪ imm(dt)` *)
  | ICaseScrut :
      #ve:venv -> #je:jenv -> #e:exp -> #es:list exp -> #dt:dtree -> #b:exp -> #m:nat ->
      squash (scrutinised e == Some (es, dt)) ->
      squash (L.memP b es) ->
      reads_imm sg g ve je b m ->
      reads_imm sg g ve je e m
  | ICaseTree :
      #ve:venv -> #je:jenv -> #e:exp -> #es:list exp -> #dt:dtree -> #m:nat ->
      squash (scrutinised e == Some (es, dt)) ->
      reads_imm_dt sg g ve es ve je dt m ->
      reads_imm sg g ve je e m
  (* `letjoin j … = e1 in e2`: `imm(e2)` *)
  | ILetJoin :
      #ve:venv -> #je:jenv -> #ts:list typ -> #t:typ -> #e1:exp -> #e2:exp -> #m:nat ->
      reads_imm sg g ve (join_def ve je ts e1 e2 :: je) e2 m ->
      reads_imm sg g ve je (ELetJoin ts t e1 e2) m
  (* `jump j (ē)`: `⋃ imm(eₖ) ∪ imm_j` *)
  | IJumpArg :
      #ve:venv -> #je:jenv -> #j:nat -> #es:list exp -> #b:exp -> #m:nat ->
      squash (L.memP b es) ->
      reads_imm sg g ve je b m ->
      reads_imm sg g ve je (EJump j es) m
  | IJumpBody :
      #ve:venv -> #je:jenv -> #j:nat -> #es:list exp -> #d:jentry -> #m:nat ->
      squash (jlook je j == Some d) ->
      reads_imm sg g (join_body d).cv (join_body d).cj (join_body d).ce m ->
      reads_imm sg g ve je (EJump j es) m
  (* `handle`, `region`, `region⟨ℓ⟩`: `⋃ₛ (imm(s) ∪ lat(s))` *)
  | IWhole :
      #ve:venv -> #je:jenv -> #e:exp -> #c:child -> #s:child -> #m:nat ->
      squash (is_whole e) ->
      squash (L.memP c (children ve je e)) ->
      sub c s ->
      reads_imm sg g s.cv s.cj s.ce m ->
      reads_imm sg g ve je e m
  | IWholeLat :
      #ve:venv -> #je:jenv -> #e:exp -> #c:child -> #s:child -> #m:nat ->
      squash (is_whole e) ->
      squash (L.memP c (children ve je e)) ->
      sub c s ->
      reads_lat sg g s.cv s.cj s.ce m ->
      reads_imm sg g ve je e m

and reads_lat (sg: sig) (g: group) : venv -> jenv -> exp -> nat -> Type =
  (* `x`, a member: `lat*(x)` *)
  | LMember :
      #ve:venv -> #je:jenv -> #i:nat -> #k:nat -> #r:exp -> #m:nat ->
      squash (vlook ve i == VMem k) ->
      squash (rhs g k == Some r) ->
      reads_lat sg g g.genv [] r m ->
      reads_lat sg g ve je (EVar i) m
  | LMemberGlobal :
      #ve:venv -> #je:jenv -> #q:qname -> #ks:list kind -> #k:nat -> #r:exp -> #m:nat ->
      squash (g.gmem q == Some k) ->
      squash (rhs g k == Some r) ->
      reads_lat sg g g.genv [] r m ->
      reads_lat sg g ve je (EGlobal q ks) m
  (* `y`, a local: `ρ(y)` *)
  | LLocal :
      #ve:venv -> #je:jenv -> #i:nat -> #ve':venv -> #je':jenv -> #e':exp -> #m:nat ->
      squash (vlook ve i == VLat ve' je' e') ->
      reads_lat sg g ve' je' e' m ->
      reads_lat sg g ve je (EVar i) m
  | LLocalRec :
      #ve:venv -> #je:jenv -> #i:nat -> #ve':venv -> #je':jenv -> #bs:list (typ & exp) ->
      #k:nat -> #t:typ -> #r:exp -> #m:nat ->
      squash (vlook ve i == VRec ve' je' bs k) ->
      squash (L.nth bs k == Some (t, r)) ->
      reads_lat sg g (push_rec ve' je' bs) je' r m ->
      reads_lat sg g ve je (EVar i) m
  (* a parameter of a join point: `arg_j`, what an argument of a `jump` to
     it in its scope may read later *)
  | LJoinArg :
      #ve:venv -> #je:jenv -> #i:nat -> #d:jentry -> #p:nat -> #c:child ->
      #ve':venv -> #je':jenv -> #j:nat -> #es:list exp -> #a:exp -> #m:nat ->
      squash (vlook ve i == VArg d p) ->
      squash (L.memP c (join_scope d)) ->
      sub c (mk ve' je' (EJump j es)) ->
      squash (j + L.length (join_jenv d) == L.length je') ->
      squash (join_arg d p es == Some a) ->
      reads_lat sg g ve' je' a m ->
      reads_lat sg g ve je (EVar i) m
  (* `λ (y : τ) / r. e`: `imm(e) ∪ lat(e)`, `y` at `∅` *)
  | LLam :
      #ve:venv -> #je:jenv -> #t:typ -> #r:typ -> #b:exp -> #m:nat ->
      reads_imm sg g (VNone :: ve) je b m ->
      reads_lat sg g ve je (ELam t r b) m
  | LLamLat :
      #ve:venv -> #je:jenv -> #t:typ -> #r:typ -> #b:exp -> #m:nat ->
      reads_lat sg g (VNone :: ve) je b m ->
      reads_lat sg g ve je (ELam t r b) m
  | LThrough :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (through e == Some b) ->
      reads_lat sg g ve je b m ->
      reads_lat sg g ve je e m
  | LBuild :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (L.memP b (builds e)) ->
      reads_lat sg g ve je b m ->
      reads_lat sg g ve je e m
  | LTake :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (takes e == Some b) ->
      reads_lat sg g ve je b m ->
      reads_lat sg g ve je e m
  | LSpine :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (L.memP b (spine_parts sg g e)) ->
      reads_lat sg g ve je b m ->
      reads_lat sg g ve je e m
  | LDefault :
      #ve:venv -> #je:jenv -> #e:exp -> #b:exp -> #m:nat ->
      squash (L.memP b (default_parts sg g e)) ->
      reads_lat sg g ve je b m ->
      reads_lat sg g ve je e m
  (* `let`: `lat(e2)` *)
  | LLet :
      #ve:venv -> #je:jenv -> #t:typ -> #e1:exp -> #e2:exp -> #m:nat ->
      reads_lat sg g (push_let ve je e1) je e2 m ->
      reads_lat sg g ve je (ELet t e1 e2) m
  (* `letrec`: `lat(e)` *)
  | LLetRec :
      #ve:venv -> #je:jenv -> #bs:list (typ & exp) -> #e:exp -> #m:nat ->
      reads_lat sg g (push_rec ve je bs) je e m ->
      reads_lat sg g ve je (ELetRec bs e) m
  (* `case`: `lat(dt)` *)
  | LCase :
      #ve:venv -> #je:jenv -> #e:exp -> #es:list exp -> #dt:dtree -> #m:nat ->
      squash (scrutinised e == Some (es, dt)) ->
      reads_lat_dt sg g ve es ve je dt m ->
      reads_lat sg g ve je e m
  (* `letjoin`: `lat(e2)` *)
  | LLetJoin :
      #ve:venv -> #je:jenv -> #ts:list typ -> #t:typ -> #e1:exp -> #e2:exp -> #m:nat ->
      reads_lat sg g ve (join_def ve je ts e1 e2 :: je) e2 m ->
      reads_lat sg g ve je (ELetJoin ts t e1 e2) m
  (* `jump j (ē)`: `lat_j` *)
  | LJump :
      #ve:venv -> #je:jenv -> #j:nat -> #es:list exp -> #d:jentry -> #m:nat ->
      squash (jlook je j == Some d) ->
      reads_lat sg g (join_body d).cv (join_body d).cj (join_body d).ce m ->
      reads_lat sg g ve je (EJump j es) m
  (* `handle`, `region`, `region⟨ℓ⟩`: `⋃ₛ lat(s)` *)
  | LWhole :
      #ve:venv -> #je:jenv -> #e:exp -> #c:child -> #s:child -> #m:nat ->
      squash (is_whole e) ->
      squash (L.memP c (children ve je e)) ->
      sub c s ->
      reads_lat sg g s.cv s.cj s.ce m ->
      reads_lat sg g ve je e m

and reads_imm_dt (sg: sig) (g: group) : venv -> list exp -> venv -> jenv -> dtree -> nat -> Type =
  (* `leaf e`: `imm(e)` *)
  | ITLeaf :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #e:exp -> #m:nat ->
      reads_imm sg g ve je e m ->
      reads_imm_dt sg g cve es ve je (DLeaf e) m
  (* `bind y o dt`: `imm(dt)`, `y` at the `lat` of the scrutinee of `o` *)
  | ITBind :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #o:occ -> #dt:dtree -> #m:nat ->
      reads_imm_dt sg g cve es (bind_entry cve je es o :: ve) je dt m ->
      reads_imm_dt sg g cve es ve je (DBind o dt) m
  (* `switchCtor`, `switchLit`, `switchKey`: `⋃ imm(dtₖ)` *)
  | ITSwitch :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #dt:dtree -> #dt':dtree -> #m:nat ->
      squash (L.memP dt' (switch_subtrees dt)) ->
      reads_imm_dt sg g cve es ve je dt' m ->
      reads_imm_dt sg g cve es ve je dt m
  (* `guard e dt1 dt2`: `imm(e) ∪ imm(dt1) ∪ imm(dt2)` *)
  | ITGuard :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #e:exp -> #dt1:dtree -> #dt2:dtree -> #m:nat ->
      reads_imm sg g ve je e m ->
      reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m
  | ITGuardYes :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #e:exp -> #dt1:dtree -> #dt2:dtree -> #m:nat ->
      reads_imm_dt sg g cve es ve je dt1 m ->
      reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m
  | ITGuardNo :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #e:exp -> #dt1:dtree -> #dt2:dtree -> #m:nat ->
      reads_imm_dt sg g cve es ve je dt2 m ->
      reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m

and reads_lat_dt (sg: sig) (g: group) : venv -> list exp -> venv -> jenv -> dtree -> nat -> Type =
  | LTLeaf :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #e:exp -> #m:nat ->
      reads_lat sg g ve je e m ->
      reads_lat_dt sg g cve es ve je (DLeaf e) m
  | LTBind :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #o:occ -> #dt:dtree -> #m:nat ->
      reads_lat_dt sg g cve es (bind_entry cve je es o :: ve) je dt m ->
      reads_lat_dt sg g cve es ve je (DBind o dt) m
  | LTSwitch :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #dt:dtree -> #dt':dtree -> #m:nat ->
      squash (L.memP dt' (switch_subtrees dt)) ->
      reads_lat_dt sg g cve es ve je dt' m ->
      reads_lat_dt sg g cve es ve je dt m
  (* `guard e dt1 dt2`: `lat(dt1) ∪ lat(dt2)` *)
  | LTGuardYes :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #e:exp -> #dt1:dtree -> #dt2:dtree -> #m:nat ->
      reads_lat_dt sg g cve es ve je dt1 m ->
      reads_lat_dt sg g cve es ve je (DGuard e dt1 dt2) m
  | LTGuardNo :
      #cve:venv -> #es:list exp -> #ve:venv -> #je:jenv -> #e:exp -> #dt1:dtree -> #dt2:dtree -> #m:nat ->
      reads_lat_dt sg g cve es ve je dt2 m ->
      reads_lat_dt sg g cve es ve je (DGuard e dt1 dt2) m

(** * The rule (spec 10 §The rule) *)

(** `g` is initialization-safe: for each `i`, every member `m` the `i`-th
    right-hand side reads before it has a value, under `g.genv` and no join
    point, is written before it, `dom(imm(eᵢ)) ⊆ { x₁, …, xᵢ₋₁ }`. *)
let init_safe (sg: sig) (g: group) : prop =
  forall (i: nat) (r: exp) (m: nat) (_: reads_imm sg g g.genv [] r m).
    rhs g i == Some r ==> m < i

(** A local group `letrec { x̄ : σ̄ = ē } in e`, the premise of its typing
    rule (spec 05 §Basic rules). *)
let init_safe_letrec (sg: sig) (bs: list (typ & exp)) : prop =
  init_safe sg (local_group bs)

(** A top-level group `rec { M.x̄ = ē }` (spec 06 §Module initialization). *)
let init_safe_top (sg: sig) (ms: list (qname & exp)) : prop =
  init_safe sg (top_group ms)
