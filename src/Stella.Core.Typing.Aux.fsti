(**
 * The contexts and the auxiliary definitions of the typing relation
 * (`Stella.Core.Typing`; spec 05, spec 06 §Run-time forms).
 *
 *   - the join-point context `Δ`, the occurrence context `Ω`, and the
 *     location context `Γ_N` (design §4.3–§4.5);
 *   - the structural well-formedness of a local context;
 *   - the static value restriction `value_form`;
 *   - the projection of an occurrence out of the values of a `match`, and
 *     the view of a variant value through its `weaken`s;
 *   - the lookups and instantiations the rules read from `Σ`;
 *   - the branch row of a `switchKey` and the split of a variant row into
 *     it and a residual.
 *)
module Stella.Core.Typing.Aux
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
module L = FStar.List.Tot

(** * Contexts *)

(** `Δ`: for each join point in scope, its parameter types, its result type
    and its ambient effect row, `j : (τ̄) -> τ ! ρ`. The head is join index 0.
    `Δ` is emptied at every non-tail position and at every boundary
    (`Stella.Core.Typing`; design §4.3), so it is never carried under a
    type binder and its types need no shifting. *)
type jctx = list (list typ & typ & typ)

(** `Ω`: the types of occurrences, extended at the head, so a lookup finds
    the most recent entry (`L.assoc`). It exists only while a decision tree
    is checked (design §4.4). *)
type octx = list (occ & typ)

(** `Γ_N`: the type of each by-need location, indexed by the location
    (design §4.5). The typing rules read it unchanged under every binder, so
    its types are closed (`lctx_ok`). *)
type lctx = list typ

(** * Well-formed contexts *)

(** Every type of `ts` has kind `Type`. *)
let rec tys_ok (sg: sig) (g: ctx) (ts: list typ) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | t :: ts -> check sg g t KType && tys_ok sg g ts

(** A layout is well formed: every key is structural and every cell type
    has kind `Type`, which is what kinding it as a `Row Type` row says of
    each entry (`Stella.Core.Typing.Wf.layout_row_ok`). Its keys being
    distinct is no part of it. *)
let rec layout_ok (sg: sig) (g: ctx) (l: layout) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | (k, t) :: l -> struct_key k && check sg g t KType && layout_ok sg g l

let rec regions_ok (sg: sig) (g: ctx) (rs: list (atom & layout)) : Tot bool (decreases rs) =
  match rs with
  | [] -> true
  | (_, l) :: rs -> layout_ok sg g l && regions_ok sg g rs

(** The structure of a local context is well formed (design §4.2): the type
    variables have well-formed quantifiable kinds, the facts and assumptions
    are well-formed constraints, every term variable has a type of kind
    `Type`, and every layout of a region is well formed (`layout_ok`), so
    its keys are structural. Whether the assumptions are consistent is not
    part of it (design §2.2), and neither is the distinctness of the region
    names or of the keys of a layout: that is the run-time invariant on
    `Γ_R` (`Stella.Core.Typing.Runtime.rctx_ok`). *)
let wf_ctx (sg: sig) (g: ctx) : bool =
  tvars_wf g && wf_hyps sg g && tys_ok sg g g.vars && regions_ok sg g g.regions

(** The context a closed run-time type is kinded in: no kind variable, no
    type variable, no constraint, and the regions `rs` of `Γ_R`. *)
let closed_ctx (rs: list (atom & layout)) : ctx = { decl_ctx 0 with regions = rs }

(** Every location type has kind `Type` in `closed_ctx rs`, `rs` being
    `Γ_R`: a store cell is typed at `·;·` with `Γ_R` in front (spec 06
    §Run-time forms), so a location type mentions no type variable a binder
    could capture, and only region names that every context of the run-time
    term has in scope. *)
let lctx_ok (sg: sig) (rs: list (atom & layout)) (ln: lctx) : bool = tys_ok sg (closed_ctx rs) ln

(** * Value forms (spec 04 §Value forms) *)

(** `q` is a data constructor, a name `Σ` records among the constructors
    alone (`global_scheme`). *)
let is_ctor (sg: sig) (q: qname) : bool =
  match global_scheme sg q with
  | Some (GCtor, _, _) -> true
  | _ -> false

(** The static value restriction on the body of a `Λ` and a constraint `Λ`:

      v ::= c | λ (x : τ) / ρ . e | Λ (a : κ). v | Λ (_ : C). v
          | M.Ctor [[κ̄]] ᾱ | {} | extend k v1 v2 | inject k [ρ] v

    where `M.Ctor [[κ̄]] ᾱ` is an application chain headed by a data constructor
    whose value arguments are value forms (`ctor_chain_form`). A variable is
    no value form. *)
let rec value_form (sg: sig) (e: exp) : Tot bool (decreases %[e; 1]) =
  match e with
  | ELit _ | ELam _ _ _ | ERecEmpty -> true
  | ETyLam _ v | ECLam _ v | EInject _ _ v -> value_form sg v
  | EExtend _ v1 v2 -> value_form sg v1 && value_form sg v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ctor_chain_form sg e
  | _ -> false

and ctor_chain_form (sg: sig) (e: exp) : Tot bool (decreases %[e; 0]) =
  match e with
  | EGlobal q _ -> is_ctor sg q
  | EApp f v -> ctor_chain_form sg f && value_form sg v
  | ETyApp f _ | ECApp f -> ctor_chain_form sg f
  | _ -> false

(** * Occurrences of run-time values (spec 06 §Pattern matching) *)

(** `values(ᾱ)`: the value arguments among the arguments `ᾱ` of a chain, in
    written order. *)
let rec value_args (args: list spine_arg) : Tot (list exp) (decreases args) =
  match args with
  | [] -> []
  | SVal v :: args -> v :: value_args args
  | _ :: args -> value_args args

(** The `j`-th value argument of `v`, a chain headed by the constructor
    `q`. *)
let ctor_field (sg: sig) (q: qname) (j: nat) (v: exp) : option exp =
  match decompose_global_app v with
  | Some (q', _, args) -> if q' = q && is_ctor sg q then L.nth (value_args args) j else None
  | None -> None

(** The payload at the key `k` of a record built by `extend`. *)
let rec record_field (k: key) (v: exp) : Tot (option exp) (decreases v) =
  match v with
  | EExtend k' v1 v2 -> if k' = k then Some v1 else record_field k v2
  | _ -> None

(** The payload of a variant that injects the key `k`, looking through every
    `weaken`, which widens the type and leaves the injected key alone. *)
let rec variant_payload (k: key) (v: exp) : Tot (option exp) (decreases v) =
  match v with
  | EInject k' _ v1 -> if k' = k then Some v1 else None
  | EWeaken _ _ v1 -> variant_payload k v1
  | _ -> None

(** The key and the payload of a variant value: `inject k [ρ] v` seen
    through every `weaken` around it, giving `k` and `v`. It is `None` for
    any other term. *)
let rec variant_view (e: exp) : Tot (option (key & exp)) (decreases e) =
  match e with
  | EInject k _ v -> Some (k, v)
  | EWeaken _ _ e -> variant_view e
  | _ -> None

(** `θ(o)`: the value at the occurrence `o`, following its projection path
    from the scrutinee values `θ` of a `match` (design §3.1). It is `None`
    where the path does not match the value. *)
let rec proj (sg: sig) (th: list exp) (o: occ) : Tot (option exp) (decreases o) =
  match o with
  | OScrut i -> L.nth th i
  | OCtor o q j ->
    (match proj sg th o with
     | Some v -> ctor_field sg q j v
     | None -> None)
  | ORecord o k ->
    (match proj sg th o with
     | Some v -> record_field k v
     | None -> None)
  | OVariant o k ->
    (match proj sg th o with
     | Some v -> variant_payload k v
     | None -> None)

(** The occurrence context `{ s_i ↦ τ_i }` of the scrutinees of a `case`,
    `τ_i` the type of the `i`-th, counted from `i`. *)
let rec scrut_occs (i: nat) (ts: list typ) : Tot octx (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> (OScrut i, t) :: scrut_occs (i + 1) ts

(** `{ o ! Ctor . j ↦ τ_j }` for the fields `τ_j` of `Ctor`, counted from
    `j`. *)
let rec field_occs (o: occ) (q: qname) (j: nat) (fs: list typ) : Tot octx (decreases fs) =
  match fs with
  | [] -> []
  | t :: fs -> (OCtor o q j, t) :: field_occs o q (j + 1) fs

(** * Lookups in `Σ` *)

(** `M.x : forall k̄. σ` among the data constructors, the foreigns and the
    top-level values: `|k̄|` and `σ`. It is defined only for a name recorded
    in exactly one of the three tables. *)
let global_type (sg: sig) (q: qname) : option (nat & typ) =
  match sg.ctors q, sg.foreigns q, sg.values q with
  | Some ci, None, None -> Some (ci.ct_nk, ci.ct_ty)
  | None, Some fi, None -> Some (fi.fr_nk, fi.fr_ty)
  | None, None, Some vi -> Some (vi.vl_nk, vi.vl_ty)
  | _ -> None

(** `Σ` records the type constructor `q` with the class `c`. *)
let has_class (sg: sig) (q: qname) (c: tycon_class) : bool =
  match sg.tycons q with
  | Some ti -> ti.tc_class = c
  | None -> false

(** The type constructor at the head of an application. *)
let rec ty_head (t: typ) : Tot (option qname) (decreases t) =
  match t with
  | TCon q _ -> Some q
  | TApp f _ -> ty_head f
  | _ -> None

(** `τ` is an application of a type constructor of class opaque
    (spec 06 §Opaque values). *)
let opaque_type (sg: sig) (t: typ) : bool =
  match ty_head t with
  | Some q -> has_class sg q (TcIntrinsic ClsOpaque)
  | None -> false

(** `forall ā. σ` instantiated at `τ̄`, outermost binder first: `None` when
    `σ` has fewer binders than `τ̄` has types. *)
let rec inst_foralls (t: typ) (ss: list typ) : Tot (option typ) (decreases ss) =
  match ss with
  | [] -> Some t
  | s :: ss ->
    (match t with
     | TForall _ b -> inst_foralls (subst1_ty s b) ss
     | _ -> None)

(** The argument types of the function arrows of `τ1 -> … -> τn -> τ`. *)
let rec fun_args (sg: sig) (t: typ) : Tot (list typ) (decreases t) =
  match t with
  | TApp (TApp (TApp (TCon q []) t1) _) t2 ->
    if is_function_tycon sg q then t1 :: fun_args sg t2 else []
  | _ -> []

(** The field types `τ̄[ā := σ̄]` of the constructor `q : forall k̄. forall ā.
    τ̄ -> T ā` at the instance `T [[κ̄]] σ̄` (spec 05 §Join points and decision
    trees). The kind scheme is instantiated at the kinds `κ̄` of the type
    constructor. *)
let ctor_fields (sg: sig) (q: qname) (ks: list kind) (ss: list typ) : option (list typ) =
  match sg.ctors q with
  | Some ci ->
    (match inst_foralls (kinst_ty ks ci.ct_ty) ss with
     | Some t -> Some (fun_args sg t)
     | None -> None)
  | None -> None

(** * Rows *)

(** The layout `( k1 : σ1, …, kn : σn )` read as the row `( k1 : σ1 | … |
    kn : σn | () )`, which is how it is kinded (spec 05 §Regions). *)
let rec layout_row (l: layout) : Tot typ (decreases l) =
  match l with
  | [] -> TRowEmpty
  | (k, t) :: l -> TRowExt (EntTy k t) (layout_row l)

(** The row `( k1 : τ1 | … | kn : τn | ρ )`: the entries a `switchKey`
    dispatches on, each key with the payload type its branch writes, in
    front of `ρ`. A layout read as a row is the case `ρ = ()`. *)
let rec brs_row (kts: list (key & typ)) (r: typ) : Tot typ (decreases kts) =
  match kts with
  | [] -> r
  | (k, t) :: kts -> TRowExt (EntTy k t) (brs_row kts r)

(** The variant row `ρ` splits into the entries `k̄ : τ̄` of the branches
    and the residual row `ρ'`: `ρ ≡ ( k1 : τ1 | … | kn : τn | ρ' )`. The
    split of an exhaustive `switchKey` has the residual `()`. It is a type
    equality and nothing else, so every renaming, substitution and region
    map keeps it (`Stella.Core.Typing.Aux.Lemmas`). For the same reason it
    kinds neither the payloads nor the residual when `ρ` is kinded
    (`Stella.Core.Typing.Examples.split_payload_unkinded`), so a rule that
    reads a split kinds them itself. *)
let key_split (r: typ) (kts: list (key & typ)) (r': typ) : bool = ty_eq r (brs_row kts r')

(** * Operations and clauses *)

(** `τ[ā := τ̄]` for a type `τ` of an operation signature of `E (ā : κ̄)`,
    standing under the operation's `m` binders `b̄` (design §3.1): the
    effect's parameters are instantiated and the binders are kept, so the
    result stands under the `m` type binders of a clause. *)
let eff_inst (m: nat) (ts: list typ) (t: typ) : typ = subst_ty m (L.rev ts) t

(** `τ[ā := τ̄][b̄ := σ̄]`, the instance a `perform` reads. *)
let op_inst (ts ss: list typ) (t: typ) : typ = subst_ty 0 (L.rev ss) (eff_inst (L.length ss) ts t)

let clause_op (c: clause) : opname =
  match c with
  | CFull op _ _ _ _ -> op
  | CFast op _ _ _ -> op

let rec clause_ops (cs: list clause) : Tot (list opname) (decreases cs) =
  match cs with
  | [] -> []
  | c :: cs -> clause_op c :: clause_ops cs

(** Every operation of `ops` has a clause. *)
let rec ops_covered (ops: list (opname & op_sig)) (names: list opname) : Tot bool (decreases ops) =
  match ops with
  | [] -> true
  | (op, _) :: ops -> L.mem op names && ops_covered ops names

(** The clauses name distinct operations and cover every operation of the
    effect. That each names an operation of the effect is the premise of its
    own typing. *)
let clauses_cover (ei: effect_info) (cs: list clause) : bool =
  L.noRepeats (clause_ops cs) && ops_covered ei.eff_ops (clause_ops cs)
