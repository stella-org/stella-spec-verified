(**
 * The abstract syntax of Stella's Typed Core.
 *
 * This module holds the AST of kinds, types, terms, decision trees and
 * handlers, together with the run-time forms of the semantics, and the view
 * of a global application chain as a head and its arguments. The binder-aware operations are in `Stella.Core.Subst` (the de Bruijn
 * sorts) and `Stella.Core.Region` (region names).
 *
 * References in comments take two forms:
 *
 *   - "design §N.M" is section N.M of `docs/design/01-Representation.md`, the
 *     design document of this repository;
 *   - "spec 0N §Heading" is the section "Heading" of
 *     `docs/technical-references/03-Typed-Core/0N-*.md` in stella-lang:
 *     01 = Kinds and Types, 02 = Rows, 03 = Effects, 04 = Terms and Matching,
 *     05 = Typing Rules, 06 = Semantics.
 *
 * ## Binder representation (design §1)
 *
 * There are FOUR independent index spaces, one per sort of binder, and an
 * operation on one of them never touches the others:
 *
 *   - term variables `x`         de Bruijn (`EVar i`)
 *   - type variables `a`         de Bruijn (`TVar i`)
 *   - join points `j`            de Bruijn (`EJump j _`)
 *   - region names `ℓ`           locally nameless (`RBound i` / `RFree a`)
 *
 * Kind variables (`KVar i`) are NOT a binder sort of terms or types: kinds have
 * no binders (D3, prenex kind schemes), so `KVar i` simply names the `i`-th
 * variable of the kind scheme of the enclosing declaration, in WRITTEN order
 * (`forall k0 k1 … . κ`), and the only operation on it is simultaneous
 * instantiation.
 *
 * ### Index conventions
 *
 * Index 0 is always the innermost binder. Where one construct binds several
 * variables of one sort at once — `letrec`'s members, a join point's
 * parameters, a clause's type binders `b̄` and its `x`/`k` — they are read as a
 * telescope extending the context left to right, so the LAST written binder
 * is index 0. Concretely:
 *
 *   - `letrec { x1 … xn } in e`   xn is index 0, x1 is index n-1
 *   - `letjoin j (x1 … xn) …`     the same for the parameters
 *   - `full op [b1 … bm] (x, k)`  bm is type index 0; k is term index 0, x is 1
 *   - `fast op [b1 … bm] (x)`     bm is type index 0; x is term index 0
 *
 * This matches the typing context's `ctx.tvars` / `ctx.vars` (design §4.2,
 * §3.1), whose head is index 0, so that pushing binders in written order
 * produces the context.
 *
 * ### Why region names are locally nameless (design §1.3)
 *
 * Opening a region at run time replaces its binder by a globally fresh name
 * (spec 06 §Regions), which is literally the locally nameless (LN) `open`:
 * bound occurrences are indices, free ones are names. Types bind no region
 * name, so a type mentions either an atom or an index pointing at a `region`
 * binder of the surrounding TERM. Region indices are therefore counted by
 * `ERegion` binders only, and a type contains `RBound` only while it sits
 * inside the body of such a binder.
 *)
module Stella.Core.Syntax
module U64 = FStar.UInt64
module I32 = FStar.Int32
module L = FStar.List.Tot

(** ** Names *)

(** A globally unique name. Used for run-time region names (the keys of the
    run-time region context `Γ_R`) and for by-need locations `ν` (the keys of
    the location context `Γ_N`; both in design §4.5), and for the free side
    of a locally nameless region reference. The two
    uses never meet in one position, so one carrier type suffices. *)
type atom = nat

(** A fully qualified name `M.x` (spec 01 §Names and binding): the module path
    `M = M1.M2…` and the final identifier. Core names are always qualified;
    an unqualified local name is a de Bruijn index instead. *)
type qname = {
  qmod : list string;
  qid  : string;
}

(** The name of an operation of an effect, `op` in `perform k.op`. It is
    resolved against the effect at the head of the element's payload, never
    against the key (spec 03 §perform and handle), so it is not qualified. *)
type opname = string

(** ** Kinds (spec 01 §Kinds) *)

(** Row element kinds `ε`. *)
type elt_kind =
  | EType
  | EEffect

(** Kinds `κ`. Kind equality is syntactic, so `kind` is an eqtype.
    `KVar i` is the `i`-th variable of the enclosing declaration's kind
    scheme, counted in written order (see the module header). *)
type kind =
  | KVar   : nat -> kind
  | KType  : kind
  | KEffect: kind
  | KRow   : elt_kind -> kind
  | KArrow : kind -> kind -> kind

(** ** Region references and row keys (spec 01 §Names and binding) *)

(** A region name `ℓ`, locally nameless. `RBound i` refers to the `i`-th
    enclosing `ERegion` binder of the term (0 = innermost); `RFree a` is an
    opened region, either statically (the typing rule opens the body with a
    fresh atom) or at run time (a name of `Γ_R`). *)
type region_ref =
  | RBound : nat  -> region_ref
  | RFree  : atom -> region_ref

(** The five row keys (spec 01 §Names and binding). The three structural ones
    carry their written content, `EffectKey` a declaration's identity, and
    `RegionKey` a region name. The theory of rows treats all five as rigid constants. *)
type key =
  | SymbolKey   : string     -> key
  | TagKey      : string     -> key
  | PositionKey : nat        -> key
  | EffectKey   : qname      -> key
  | RegionKey   : region_ref -> key

(** ** Types (spec 01 §Types)

    `typ`, `entry` and `constr` are eqtypes: type equality is computational,
    `canon t1 = canon t2` (design §2), which needs decidable syntactic
    equality of the canonical forms.

    The only type-level binder is `TForall`. A constraint abstraction
    `C => τ` binds nothing. *)
type typ =
  | TVar      : nat -> typ                    (** a *)
  | TCon      : qname -> list kind -> typ     (** T [[κ̄]]; `T` when κ̄ = [] *)
  | TApp      : typ -> typ -> typ             (** τ1 τ2 *)
  | TForall   : kind -> typ -> typ            (** forall (a : κ). τ — binds TVar 0 *)
  | TConstr   : constr -> typ -> typ          (** C => τ *)
  | TRowEmpty : typ                           (** () *)
  | TRowExt   : entry -> typ -> typ           (** ( ent | ρ ) *)
  | TRowUnion : typ -> typ -> typ             (** ρ1 ⊎ ρ2 *)

(** Row elements `ent`. The two `Row Effect` forms with a payload are merged
    into `EntEff`: `None` is the unlabelled `E τ̄` (key `EffectKey E`) and
    `Some s` the labelled `SymbolKey s : E τ̄` (key `SymbolKey s`). A label is
    always a `SymbolKey` in the grammar, so only the symbol is stored. *)
and entry =
  | EntTy     : key -> typ -> entry                     (** k : τ *)
  | EntEff    : option string -> qname -> list typ -> entry
                                                        (** E τ̄  /  s : E τ̄ *)
  | EntRegion : region_ref -> entry                     (** region ℓ *)

(** Constraints `C`. *)
and constr =
  | CLacks : key -> typ -> constr       (** k ∉ ρ *)
  | CDisj  : typ -> typ -> constr       (** ρ1 # ρ2 *)

(** `τ1 -{ρ}-> τ2`, given the qualified name of `Prim.Function`. Core has no
    arrow syntax (spec 01 §Types), so the name is a parameter rather than a
    constant of this module, as `Partial` is for `fail` below. *)
let fun_ty (function_name: qname) (t1 rho t2: typ) : typ =
  TApp (TApp (TApp (TCon function_name []) t1) rho) t2

(** `h τ1 … τn`, the arguments applied in order. *)
let rec tapps (h: typ) (ts: list typ) : Tot typ (decreases ts) =
  match ts with
  | [] -> h
  | t :: ts -> tapps (TApp h t) ts

(** ** Literals (spec 04 §Term syntax; D37, D27) *)

(** A Unicode scalar value: a code point that is not a surrogate (D27). *)
type uchar = n:nat{n <= 0x10FFFF /\ (n < 0xD800 \/ 0xDFFF < n)}

(** The IEEE 754 binary64 field decomposition of a bit pattern, on `nat` so
    that it computes under the normaliser and in Z3 without bit-vectors. *)
let number_exponent (b: U64.t) : nat = (U64.v b / pow2 52) % pow2 11

let number_mantissa (b: U64.t) : nat = U64.v b % pow2 52

let is_nan_bits (b: U64.t) : bool =
  number_exponent b = pow2 11 - 1 && number_mantissa b <> 0

(** The one NaN pattern a Core literal may hold, `7ff8000000000000`
    (the encoding the implementation plan fixes for every NaN). *)
let canonical_nan : U64.t = 0x7FF8000000000000uL

(** NaN canonicalisation: every NaN pattern is read as the canonical one,
    every other pattern is kept, so `0.0` and `-0.0` stay apart (D37). *)
let canon_number (b: U64.t) : U64.t =
  if is_nan_bits b then canonical_nan else b

val canon_number_idem (b: U64.t)
  : Lemma (canon_number (canon_number b) == canon_number b)

(** A `Number` literal is a binary64 bit pattern that is already canonical.
    Keeping the invariant in the type makes literal identity — "equality of
    the bit pattern with all NaNs taken as one" (D37) — coincide with the
    structural equality of `lit`, which is what `switchLit`'s distinctness
    premise and its reduction rule compare by. *)
type number = b:U64.t{canon_number b == b}

let mk_number (b: U64.t) : number =
  canon_number_idem b;
  canon_number b

(** Literals. `Unit` is not one: it is the data constructor `Prim.Unit`
    (spec 05 §Basic rules). *)
type lit =
  | LInt    : I32.t -> lit           (** 32-bit signed (D37) *)
  | LNumber : number -> lit          (** binary64 bits, canonical NaN (D37) *)
  | LChar   : uchar -> lit           (** one scalar value (D27) *)
  | LString : list uchar -> lit      (** a sequence of scalar values (D27) *)
  | LBool   : bool -> lit

(** ** Occurrences (spec 04 §Occurrences)

    Projection paths from a scrutinee. They contain no binder and no variable:
    `OScrut i` is a position in the `case`'s scrutinee list, not a de Bruijn
    index. Keys may in principle hold a region reference, so region
    operations still traverse them. *)
type occ =
  | OScrut   : nat -> occ                    (** s_i *)
  | OCtor    : occ -> qname -> nat -> occ    (** o ! Ctor . j *)
  | ORecord  : occ -> key -> occ             (** o . k *)
  | OVariant : occ -> key -> occ             (** o ? k *)

(** ** Terms (spec 04 §Term syntax, spec 03 §perform and handle,
       spec 06 §Values / §Run-time forms)

    One AST holds both the source terms and the forms that arise only during
    reduction (design §3); `is_source` tells them apart.

    Binding summary (term / type / join / region indices bound):

    | constructor     | binds                                                   |
    | --------------- | ------------------------------------------------------- |
    | `ELam t ρ e`    | term 1 in `e`                                           |
    | `ETyLam k v`    | type 1 in `v`                                           |
    | `ELet t e1 e2`  | term 1 in `e2`                                          |
    | `ELetRec bs e`  | term `length bs` in every initializer and in `e`        |
    | `ELetJoin ts t e1 e2` | term `length ts` in `e1`; join 1 in `e1` and `e2` |
    | `DBind o dt`    | term 1 in `dt`                                          |
    | handler return  | term 1 in `h_ret`                                       |
    | `CFull op m σ κ e` | type `m` in `σ`, `κ` and `e`; term 2 in `e`          |
    | `CFast op m σ e`   | type `m` in `σ` and `e`; term 1 in `e`               |
    | `ERegion ι es e`| region 1 in `e` only (not in `ι`, not in `es`)          |

    `ELam t ρ e` is `λ (x : τ) / ρ . e`. Its row `ρ`, a type of kind
    `Row Effect`, is the row its body is evaluated under and the row of its
    arrow `τ -{ρ}-> τ'`, whatever row is ambient where it stands (spec 04
    §Term syntax, spec 05 §Basic rules).

    The annotations of `ELam` (its parameter type and its row), `ELet`,
    `ELetRec` and `ELetJoin` stand outside the term binders they annotate;
    since types contain no term variable this only matters for the clause
    annotations, which DO stand under the clause's type binders `b̄` (they
    mention them: spec 05 §Effects, `σ_i'`). *)
type exp =
  (* -- variables, abstraction, application -- *)
  | EVar       : nat -> exp                           (** x *)
  | EGlobal    : qname -> list kind -> exp            (** M.x [[κ̄]] *)
  | ELit       : lit -> exp                           (** c *)
  | ELam       : typ -> typ -> exp -> exp             (** λ (x : τ) / ρ . e *)
  | EApp       : exp -> exp -> exp                    (** e1 e2 *)
  | ETyLam     : kind -> exp -> exp                   (** Λ (a : κ). v *)
  | ETyApp     : exp -> typ -> exp                    (** e [τ] *)
  | ECLam      : constr -> exp -> exp                 (** Λ (_ : C). v *)
  | ECApp      : exp -> exp                           (** e [•] *)
  (* -- bindings, matching, join points -- *)
  | ELet       : typ -> exp -> exp -> exp             (** let x : τ = e1 in e2 *)
  | ELetRec    : list (typ & exp) -> exp -> exp       (** letrec { x̄ : σ̄ = ē } in e *)
  | ECase      : list exp -> dtree -> exp             (** case (ē) of dt *)
  | ELetJoin   : list typ -> typ -> exp -> exp -> exp (** letjoin j (x̄ : τ̄) : τ = e1 in e2 *)
  | EJump      : nat -> list exp -> exp               (** jump j (ē) *)
  (* -- records -- *)
  | ERecEmpty  : exp                                  (** {} *)
  | EExtend    : key -> exp -> exp -> exp             (** extend k e1 e2 *)
  | ESelect    : key -> exp -> exp                    (** select k e *)
  | ERestrict  : key -> exp -> exp                    (** restrict k e *)
  | EUpdate    : key -> exp -> exp -> exp             (** update k e1 e2 *)
  | EMerge     : exp -> exp -> exp                    (** merge e1 e2 *)
  (* -- variants -- *)
  | EInject    : key -> typ -> exp -> exp             (** inject k [ρ] e *)
  | EWeaken    : key -> typ -> exp -> exp             (** weaken k [τ] e *)
  | EAbsurd    : typ -> exp -> exp                    (** absurd [τ] e *)
  (* -- effects -- *)
  | EPerform   : key -> opname -> list typ -> exp -> exp
                                                      (** perform k.op [τ̄] e *)
  | EHandle    : exp -> handler -> exp                (** handle e with h *)
  | EOpenEff   : typ -> exp -> exp                    (** openEff [ρ] e *)
  (* -- regions of cells -- *)
  | ERegion    : list (key & typ) -> list exp -> exp -> exp
                                (** region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e; binds ℓ in e *)
  | EReadCell  : region_ref -> key -> exp             (** readCell ℓ.k *)
  | EWriteCell : region_ref -> key -> exp -> exp      (** writeCell ℓ.k e *)
  (* -- run-time forms (spec 06 §Run-time forms) -- *)
  | EMatch     : list exp -> dtree -> exp             (** match θ dt *)
  | EOpenEffC  : typ -> exp -> exp                    (** openEffC [ρ] e *)
  | EForce     : atom -> exp                          (** force ν *)
  | EFill      : atom -> exp -> exp                   (** fill ν e *)
  | ERegionOpen: atom -> list (key & exp) -> exp -> exp
                                                      (** region⟨ℓ⟩ θ in e; binds nothing *)
  | EOpaque    : nat -> typ -> exp                    (** opaque ω [τ] *)

(** Decision trees (spec 04 §Decision trees). `fail` is derived notation and
    has no constructor; see `fail_dt`. `switchLit`'s default is mandatory and
    so is not an `option`. *)
and dtree =
  | DLeaf       : exp -> dtree                                        (** leaf e *)
  | DBind       : occ -> dtree -> dtree                               (** bind x = o in dt *)
  | DSwitchCtor : occ -> list (qname & dtree) -> option dtree -> dtree
  | DSwitchLit  : occ -> list (lit & dtree) -> dtree -> dtree
  | DSwitchKey  : occ -> list (key & dtree) -> option dtree -> dtree
  | DGuard      : exp -> dtree -> dtree -> dtree                      (** guard e dt1 dt2 *)

(** A handler `{ handles ent ; return (x : τ) -> e_r ; cl1 ; … ; cln }`
    (spec 03 §perform and handle). The element is written whole because
    typing needs its payload; reduction reads only its key. *)
and handler = {
  h_ent     : entry;          (** the element the handler removes *)
  h_ret_ty  : typ;            (** the annotation τ of the return binder x *)
  h_ret     : exp;            (** e_r, under one term binder *)
  h_clauses : list clause;
}

(** Operation clauses (spec 03 §full and fast clauses, spec 05 §Effects).
    `nb` is the number `m` of type binders `b̄`; the binders themselves need
    no kind, which is read from `Σ` for the operation.

    - `CFull op m σ κ e` is `full op [b̄] (x : σ, k : κ) -> e`, where `κ` is
      the written continuation type `τ' -{ρ}-> β`.
    - `CFast op m σ e`   is `fast op [b̄] (x : σ) -> e`.

    `σ`, `κ` and `e` all stand under the `m` type binders. *)
and clause =
  | CFull : op:opname -> nb:nat -> arg_ty:typ -> k_ty:typ -> body:exp -> clause
  | CFast : op:opname -> nb:nat -> arg_ty:typ -> body:exp -> clause

(** ** Derived notation *)

(** `fail τ ≡ perform Partial.abort [τ] Prim.Unit` (spec 03 §Partiality).
    `Partial` is a `Prelude` declaration, not a builtin, so its name and that
    of `Prim.Unit` are parameters (design §3). *)
let fail_exp (partial unit_ctor: qname) (t: typ) : exp =
  EPerform (EffectKey partial) "abort" [t] (EGlobal unit_ctor [])

(** The decision-tree `fail`: `leaf (perform Partial.abort [τ] Prim.Unit)`
    (spec 04 §Decision trees). *)
let fail_dt (partial unit_ctor: qname) (t: typ) : dtree =
  DLeaf (fail_exp partial unit_ctor t)

(** ** Global application chains (spec 04 §Value forms, spec 06 §Values)

    A data constructor or a foreign applied to arguments has no syntax of its
    own: it is the chain of `EApp`, `ETyApp` and `ECApp` over `EGlobal q ks`.
    The kind vector `[[κ̄]]` stays on `EGlobal`; the type, constraint and value
    arguments are read off the chain, which is the spec's spine view of
    `M.g [[κ̄]] α1 … αn` (spec 05 §Chains of a constructor or a foreign).

    One syntax serves both the static and the run-time value forms. The value
    restriction admits a constructor chain whose arguments are values as the
    body of a `Λ` (spec 04 §Value forms), e.g. `Λ a. M.Cons [a] v1 v2`, and no
    evaluation context goes under `Λ`, so that chain is itself a run-time
    value. Reduction reads the chain itself, as the typing rules do, and has
    no other run-time form of the call (spec 06 §Chains of a constructor or a
    foreign; design §3, §6.2). *)

(** An argument of a chain, an entry `α` of its spine view (spec 06 §Chains
    of a constructor or a foreign). *)
type spine_arg =
  | STy     : typ -> spine_arg             (** [τ] *)
  | SConstr : spine_arg                    (** [•] *)
  | SVal    : exp -> spine_arg             (** v *)

(** `e α`: one more argument applied to `e`. *)
let apply_arg (e: exp) (a: spine_arg) : exp =
  match a with
  | STy t -> ETyApp e t
  | SConstr -> ECApp e
  | SVal v -> EApp e v

(** `e α1 … αn`, the arguments in written order, `α1` applied first. *)
let rec apply_args (e: exp) (args: list spine_arg) : Tot exp (decreases args) =
  match args with
  | [] -> e
  | a :: args -> apply_args (apply_arg e a) args

(** The chain `M.g [[κ̄]] α1 … αn`. *)
let recompose (q: qname) (ks: list kind) (args: list spine_arg) : exp =
  apply_args (EGlobal q ks) args

(** The view of a chain: `decompose_global_app e` peels `EApp`, `ETyApp` and
    `ECApp` off `e` down to an `EGlobal q ks`, and returns `q`, `ks` and the
    arguments in written order. It is `None` when the innermost function
    position is not a global. *)
let rec decompose_global_app (e: exp)
  : Tot (option (qname & list kind & list spine_arg)) (decreases e) =
  match e with
  | EGlobal q ks -> Some (q, ks, [])
  | EApp f v ->
    (match decompose_global_app f with
     | Some (q, ks, args) -> Some (q, ks, L.append args [SVal v])
     | None -> None)
  | ETyApp f t ->
    (match decompose_global_app f with
     | Some (q, ks, args) -> Some (q, ks, L.append args [STy t])
     | None -> None)
  | ECApp f ->
    (match decompose_global_app f with
     | Some (q, ks, args) -> Some (q, ks, L.append args [SConstr])
     | None -> None)
  | _ -> None

val apply_args_snoc (e: exp) (args: list spine_arg) (a: spine_arg)
  : Lemma (apply_args e (L.append args [a]) == apply_arg (apply_args e args) a)

(** Applying one argument to a chain extends its spine view by that
    argument. *)
val decompose_apply_arg (e: exp) (a: spine_arg)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures (let Some (q, ks, args0) = decompose_global_app e in
                    decompose_global_app (apply_arg e a) == Some (q, ks, L.append args0 [a])))

(** Applying arguments to a chain extends its spine view. *)
val decompose_apply_args (e: exp) (args: list spine_arg)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures (let Some (q, ks, args0) = decompose_global_app e in
                    decompose_global_app (apply_args e args) == Some (q, ks, L.append args0 args)))

(** The round trip from a view. *)
val decompose_recompose (q: qname) (ks: list kind) (args: list spine_arg)
  : Lemma (decompose_global_app (recompose q ks args) == Some (q, ks, args))

(** The round trip from a chain. *)
val recompose_decompose (e: exp)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures (let Some (q, ks, args) = decompose_global_app e in
                    recompose q ks args == e))

(** ** Source terms *)

(** `is_source e` holds when `e` contains none of the run-time forms of
    spec 06 §Run-time forms (`match`, `openEffC`, `force`, `fill`,
    `region⟨ℓ⟩`, `opaque`). Every other form is source syntax, a global
    application chain included.

    It says nothing about region references: a source region body is typed
    after being opened with an atom (design §1.3), so `RFree` occurs in
    terms the typing rules treat as source. *)
let rec is_source (e: exp) : Tot bool (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ -> true
  | ELam _ _ e | ETyLam _ e | ETyApp e _ | ECLam _ e | ECApp e
  | ESelect _ e | ERestrict _ e | EInject _ _ e | EWeaken _ _ e
  | EAbsurd _ e | EPerform _ _ _ e | EOpenEff _ e | EWriteCell _ _ e ->
    is_source e
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    is_source e1 && is_source e2
  | ELetRec bs e -> is_source_binds bs && is_source e
  | ECase es dt -> is_source_exps es && is_source_dt dt
  | EJump _ es -> is_source_exps es
  | EHandle e h -> is_source e && is_source h.h_ret && is_source_cls h.h_clauses
  | ERegion _ es e -> is_source_exps es && is_source e
  | EMatch _ _ | EOpenEffC _ _ | EForce _ | EFill _ _
  | ERegionOpen _ _ _ | EOpaque _ _ -> false

and is_source_exps (es: list exp) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> is_source e && is_source_exps es

and is_source_binds (bs: list (typ & exp)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, e) :: bs -> is_source e && is_source_binds bs

and is_source_dt (dt: dtree) : Tot bool (decreases dt) =
  match dt with
  | DLeaf e -> is_source e
  | DBind _ dt -> is_source_dt dt
  | DSwitchCtor _ bs d -> is_source_brs bs && is_source_odt d
  | DSwitchLit _ bs d -> is_source_brs bs && is_source_dt d
  | DSwitchKey _ bs d -> is_source_brs bs && is_source_odt d
  | DGuard e dt1 dt2 -> is_source e && is_source_dt dt1 && is_source_dt dt2

and is_source_odt (d: option dtree) : Tot bool (decreases d) =
  match d with
  | None -> true
  | Some dt -> is_source_dt dt

and is_source_brs (#a: eqtype) (bs: list (a & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, dt) :: bs -> is_source_dt dt && is_source_brs bs

and is_source_cls (cs: list clause) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | CFull _ _ _ _ e :: cs | CFast _ _ _ e :: cs -> is_source e && is_source_cls cs
