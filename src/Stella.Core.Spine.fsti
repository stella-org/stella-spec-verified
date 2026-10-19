(**
 * The spine cursor and saturation (spec 06 §The spine cursor, §Saturation is
 * a position in the declared type).
 *
 * A global application chain `M.g [[κ̄]] α1 … αn` (design §3,
 * `Stella.Core.Syntax.decompose_global_app`) is classified at run time from
 * the declaration of `M.g` and its arguments alone, with no `Γ`. The cursor
 * walks the DECLARED type scheme of `M.g`, consuming one argument at a time,
 * and returns the unconsumed declared remainder `σ` together with the
 * accumulated type substitution `θ`. The chain's type is the instance
 * `θ(σ)`, i.e. `sub_ty θ σ`. The cursor checks no well-formedness:
 * kinding, entailment and the types of value arguments are the typing
 * rules' business (spec 06 §Typing a spine).
 *
 * Saturation is a property of `σ`, not of `θ(σ)`: substitution can produce
 * an arrow that the declaration never called for, and that arrow is no
 * argument position of `M.g`.
 *)
module Stella.Core.Spine
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
module L = FStar.List.Tot

(** * Function types *)

(** `q` is a function type constructor: `Σ` records it as intrinsic, with
    the canonical-value class of `Function` (spec 06 §Opaque values). *)
let is_function_tycon (sg: sig) (q: qname) : bool =
  match sg.tycons q with
  | Some ti -> (match ti.tc_class with TcIntrinsic ClsFunction -> true | _ -> false)
  | None -> false

(** The parts `τ1`, `ρ` and `τ2` of a function type `τ1 -{ρ}-> τ2`
    (`fun_ty`), or `None` when `t` is not one. *)
let as_function (sg: sig) (t: typ) : option (typ & typ & typ) =
  match t with
  | TApp (TApp (TApp (TCon q []) t1) r) t2 ->
    if is_function_tycon sg q then Some (t1, r, t2) else None
  | _ -> None

val as_function_fun_ty (sg: sig) (q: qname) (t1 r t2: typ)
  : Lemma (requires is_function_tycon sg q)
          (ensures as_function sg (fun_ty q t1 r t2) == Some (t1, r, t2))

(** * The declared scheme of a global *)

(** The two classes of global that head a chain with no body to unfold
    to (spec 06 §Forming and reducing a spine). *)
type global_class =
  | GCtor        (** a data constructor *)
  | GForeign     (** a foreign *)

(** `M.g : forall k̄. σ` among the constructors and foreigns of `Σ`: its
    class, `|k̄|`, and `σ`. The lookup is defined only for a name that `Σ`
    records in exactly one of its value-level tables (constructors,
    foreigns, top-level values), as a well-formed `Σ` records every name
    (`Stella.Core.Sig.Wf.globals_disjoint`). *)
let global_scheme (sg: sig) (q: qname) : option (global_class & nat & typ) =
  match sg.ctors q, sg.foreigns q, sg.values q with
  | Some ci, None, None -> Some (GCtor, ci.ct_nk, ci.ct_ty)
  | None, Some fi, None -> Some (GForeign, fi.fr_nk, fi.fr_ty)
  | _ -> None

(** * The cursor (spec 06 §The spine cursor) *)

(** One argument consumed from the declared remainder `t` under `θ`:

      [τ]  against  forall (a : κ). σ   gives  ⟨ σ ; τ .: θ ⟩
      [•]  against  C => σ              gives  ⟨ σ ; θ ⟩
      v    against  τ1 -{ρ}-> τ2        gives  ⟨ τ2 ; θ ⟩

    and nothing otherwise. The body of `forall` has the bound variable at
    index 0, so `scons τ θ` (`τ .: θ`) is its accumulated substitution.

    The arrows a cursor consumes are pure: a constructor's by declaration
    and a foreign's by D23. That is a condition on `Σ`
    (`Stella.Core.Sig.Wf.globals_ok`, `Stella.Core.Spine.Wf.cursor_arrow_pure`),
    and the cursor does not examine `ρ`. *)
let cursor_step (sg: sig) (t: typ) (th: tsub) (a: spine_arg) : option (typ & tsub) =
  match a, t with
  | STy s, TForall _ body -> Some (body, scons s th)
  | SConstr, TConstr _ body -> Some (body, th)
  | SVal _, _ ->
    (match as_function sg t with
     | Some (_, _, t2) -> Some (t2, th)
     | None -> None)
  | _, _ -> None

(** The arguments consumed in written order from `⟨ t ; θ ⟩`. *)
let rec cursor (sg: sig) (t: typ) (th: tsub) (args: list spine_arg)
  : Tot (option (typ & tsub)) (decreases args) =
  match args with
  | [] -> Some (t, th)
  | a :: args ->
    match cursor_step sg t th a with
    | Some (t', th') -> cursor sg t' th' args
    | None -> None

(** `cursorΣ(M.g, ς)` for the chain `M.g [[κ̄]] ς`. The kind vector of
    `EGlobal` instantiates the whole kind scheme up front (kind schemes are
    prenex, D3), so the cursor is defined only when `|κ̄| = |k̄|`, and starts
    from `σ[k̄ := κ̄]` and the identity substitution. A declared type has no
    free type variable (`Stella.Core.Sig.Wf`), so `θ` is consulted only at
    the variables of consumed binders. *)
let spine_cursor (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg)
  : option (typ & tsub) =
  match global_scheme sg q with
  | Some (_, nk, t) -> if L.length ks = nk then cursor sg (kinst_ty ks t) tvar args else None
  | None -> None

(** The cursor after one more argument is one step from the cursor
    before it, which is how the spec states it (spec 06 §The spine
    cursor). *)
val cursor_snoc (sg: sig) (t: typ) (th: tsub) (args: list spine_arg) (a: spine_arg)
  : Lemma (cursor sg t th (L.append args [a]) ==
           (match cursor sg t th args with
            | Some (t', th') -> cursor_step sg t' th' a
            | None -> None))

val spine_cursor_snoc (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg) (a: spine_arg)
  : Lemma (spine_cursor sg q ks (L.append args [a]) ==
           (match spine_cursor sg q ks args with
            | Some (t', th') -> cursor_step sg t' th' a
            | None -> None))

(** * The cursor of a chain *)

(** The cursor of `e` read as a global application chain; `None` when `e`
    is no chain or its cursor is undefined. The type of the chain is
    `θ(σ)` for `chain_cursor sg e = Some (σ, θ)`. *)
let chain_cursor (sg: sig) (e: exp) : option (typ & tsub) =
  match decompose_global_app e with
  | Some (q, ks, args) -> spine_cursor sg q ks args
  | None -> None

(** The atomic reference starts the cursor. *)
val chain_cursor_global (sg: sig) (q: qname) (ks: list kind)
  : Lemma (chain_cursor sg (EGlobal q ks) ==
           (match global_scheme sg q with
            | Some (_, nk, t) -> if L.length ks = nk then Some (kinst_ty ks t, tvar) else None
            | None -> None))

(** Each `EApp`, `ETyApp` and `ECApp` node over a chain is one step of the
    cursor. *)
val chain_cursor_apply_arg (sg: sig) (e: exp) (a: spine_arg)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures chain_cursor sg (apply_arg e a) ==
                   (match chain_cursor sg e with
                    | Some (t', th') -> cursor_step sg t' th' a
                    | None -> None))

(** A function type stays one under a substitution, with its parts
    substituted. The converse fails: a substitution can turn a variable
    into a function type. *)
val as_function_sub (sg: sig) (sigma: tsub) (t t1 r t2: typ)
  : Lemma (requires as_function sg t == Some (t1, r, t2))
          (ensures as_function sg (sub_ty sigma t) == Some (sub_ty sigma t1, sub_ty sigma r, sub_ty sigma t2))

(** The accumulated substitution agrees with type application: the
    instance of `forall (a : κ). σ` under `θ`, applied to `τ`, is the
    instance of `σ` under `τ .: θ`. *)
val cursor_instance_forall (s: typ) (th: tsub) (body: typ)
  : Lemma (subst1_ty s (sub_ty (up_tsub th) body) == sub_ty (scons s th) body)

(** * Chains under substitution

    A type substitution keeps the head of a chain and maps each type
    argument and each value argument; a term substitution maps the value
    arguments of a chain alone, and the cursor does not read them. *)

let sub_arg (sigma: tsub) (a: spine_arg) : spine_arg =
  match a with
  | STy t -> STy (sub_ty sigma t)
  | SConstr -> SConstr
  | SVal v -> SVal (sub_ty_exp sigma v)

let sub_tm_arg (sigma: esub) (a: spine_arg) : spine_arg =
  match a with
  | SVal v -> SVal (sub_tm sigma v)
  | _ -> a

val decompose_sub_ty_exp (sigma: tsub) (e: exp)
  : Lemma (decompose_global_app (sub_ty_exp sigma e) ==
           (match decompose_global_app e with
            | Some (q, ks, args) -> Some (q, ks, L.map (sub_arg sigma) args)
            | None -> None))

(** A term substitution can put a chain where a variable stood, so a chain
    is kept only where there is one. *)
val decompose_sub_tm (sigma: esub) (e: exp)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures (let Some (q, ks, args) = decompose_global_app e in
                    decompose_global_app (sub_tm sigma e) == Some (q, ks, L.map (sub_tm_arg sigma) args)))

val chain_cursor_sub_tm (sg: sig) (sigma: esub) (e: exp)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures chain_cursor sg (sub_tm sigma e) == chain_cursor sg e)

(** * Saturation (spec 06 §Saturation is a position in the declared type) *)

(** A declared remainder is saturated when it is not a `forall`, not a
    constraint arrow, and not a function type. *)
let saturated (sg: sig) (t: typ) : bool =
  match t with
  | TForall _ _ | TConstr _ _ -> false
  | _ -> None? (as_function sg t)

(** Kind instantiation keeps the shape of a type, so instantiating the kind
    scheme up front leaves saturation unchanged. *)
val saturated_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (saturated sg (kinst_ty ks t) == saturated sg t)

(** The cursor of `M.g [[κ̄]] ς` is defined and its remainder is
    saturated. *)
let spine_saturated (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg) : bool =
  match spine_cursor sg q ks args with
  | Some (t, _) -> saturated sg t
  | None -> false

(** The cursor of `M.g [[κ̄]] ς` is defined and its remainder is not
    saturated. Where the cursor is undefined, `ς` is neither. *)
let spine_unsaturated (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg) : bool =
  match spine_cursor sg q ks args with
  | Some (t, _) -> not (saturated sg t)
  | None -> false
