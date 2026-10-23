(**
 * Erasure `⌊·⌋` (spec 06 §Erasure), and the outcomes of a foreign call,
 * typed and erased.
 *
 * ## Erased syntax
 *
 * `uexp` is the syntax of erased terms `u`, what erasure produces: the
 * grammar of `exp` with every annotation written for the checker dropped,
 * and with no form for `Λ`, a type or constraint application, `openEff`,
 * `openEffC` or `weaken`, which erasure removes. Each case of `erase` is
 * one equation of spec 06 §Erasure:
 *
 *     ⌊λ (x : τ) / ρ . e⌋ = λ x . ⌊e⌋
 *     ⌊Λ (a : κ). v⌋ = ⌊v⌋      ⌊e [τ]⌋ = ⌊e⌋      ⌊Λ (_ : C). v⌋ = ⌊v⌋    ⌊e [•]⌋ = ⌊e⌋
 *     ⌊M.x [[κ̄]]⌋ = M.x
 *     ⌊openEff [ρ] e⌋ = ⌊e⌋     ⌊openEffC [ρ] e⌋ = ⌊e⌋
 *     ⌊weaken k [τ] e⌋ = ⌊e⌋    ⌊inject k [ρ] e⌋ = inject k ⌊e⌋
 *     ⌊letjoin j (x̄ : τ̄) : τ = e1 in e2⌋ = letjoin j (x̄) = ⌊e1⌋ in ⌊e2⌋
 *     ⌊{ handles ent ; return (x : τ) -> e_r ; cl_i }⌋
 *         = { key key(ent) ; return x -> ⌊e_r⌋ ; ⌊cl_i⌋ }
 *     ⌊full op [b̄] (x : σ, k : τ) -> e⌋ = full op (x, k) -> ⌊e⌋
 *     ⌊fast op [b̄] (x : σ) -> e⌋ = fast op (x) -> ⌊e⌋
 *     ⌊handle e with h⌋ = handle ⌊e⌋ with ⌊h⌋
 *     ⌊region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e⌋ = region ℓ ( k̄ ) @ ( ⌊ē⌋ ) in ⌊e⌋
 *     ⌊region⟨ℓ⟩ θ in e⌋ = region⟨ℓ⟩ ⌊θ⌋ in ⌊e⌋
 *     ⌊readCell ℓ.k⌋ = readCell ℓ.k      ⌊writeCell ℓ.k e⌋ = writeCell ℓ.k ⌊e⌋
 *     ⌊opaque ω [τ]⌋ = opaque ω
 *     ⌊force ν⌋ = force ν      ⌊fill ν e⌋ = fill ν ⌊e⌋
 *
 * and every other form homomorphically, dropping what it writes for the
 * checker: `let`, `perform`, `absurd`, `letrec`, a decision tree node by
 * node, `match θ dt` as `match ⌊θ⌋ ⌊dt⌋`, and a variable, a literal, an
 * application, a record form, `case` and `jump` keeping their shape. `fail τ`
 * is notation for a `perform` (`Stella.Core.Syntax.fail_exp`), so it erases
 * as its expansion. A chain erases to its head and its values,
 * `⌊M.g [[κ̄]] ᾱ⌋ = M.g ⌊values(ᾱ)⌋`, by the equations for its nodes.
 *
 * The binders of the erased syntax are those of `exp` less the type
 * binders. Term variables, join points and region names are de Bruijn or
 * locally nameless exactly as in `exp` (design §1), and erasure removes no
 * binder of theirs, so it leaves every index as it stands: `letjoin` keeps
 * the number of its parameters, `letrec` its members, a clause its `x` and
 * `k`, and a region its name.
 *
 * ## Cells by key
 *
 * Spec 06 §Erasure names a cell by its position: `⌊readCell ℓ.k⌋ =
 * readCell ℓ.i`, `i` the position of `k` in the layout of `ℓ`, and `⌊θ⌋`
 * maps positions to values. Here an erased `readCell` and `writeCell` keep
 * the key `k`, and an erased open region keeps the keys of its cells.
 * Under a fixed `Γ_R` the key of a cell and its position determine each
 * other, so within one run the two erasures carry the same information. A
 * foreign's erased function and erased precondition do not depend on
 * `Γ_R`, however, and condition (3) of conformance ranges over every
 * `Γ_R`. Two cell references with different keys in different layouts
 * may have one position, so an erased function may read a key where it
 * could not read a position: the environments that conform here include
 * those that conform under positional erasure, and a few more.
 *
 * ## Outcomes
 *
 * A foreign call has an outcome: a value or an ABI fault, typed
 * (`foreign_outcome`, what the typed adapter `δᵀ_f` gives) or erased
 * (`uoutcome`, what the erased function `δᵤ_f` gives). The fault is the
 * same at both levels, and `erase_outcome` is spec 06's `eraseOutcome`:
 *
 *     eraseOutcome(value v) = value ⌊v⌋      eraseOutcome(fault φ) = fault φ
 *
 * This module reads no typing judgement and no signature.
 *)
module Stella.Core.Erase
open Stella.Core.Syntax
open Stella.Core.Rows
module L = FStar.List.Tot

(** * Erased terms *)

type uexp =
  | UVar       : nat -> uexp                              (** x *)
  | UGlobal    : qname -> uexp                            (** M.x *)
  | ULit       : lit -> uexp                              (** c *)
  | ULam       : uexp -> uexp                             (** λ x . u *)
  | UApp       : uexp -> uexp -> uexp                     (** u1 u2 *)
  | ULet       : uexp -> uexp -> uexp                     (** let x = u1 in u2 *)
  | ULetRec    : list uexp -> uexp -> uexp                (** letrec { x̄ = ū } in u *)
  | UCase      : list uexp -> udtree -> uexp              (** case (ū) of dt *)
  | ULetJoin   : nat -> uexp -> uexp -> uexp              (** letjoin j (x1 … xn) = u1 in u2 *)
  | UJump      : nat -> list uexp -> uexp                 (** jump j (ū) *)
  | URecEmpty  : uexp                                     (** {} *)
  | UExtend    : key -> uexp -> uexp -> uexp              (** extend k u1 u2 *)
  | USelect    : key -> uexp -> uexp                      (** select k u *)
  | URestrict  : key -> uexp -> uexp                      (** restrict k u *)
  | UUpdate    : key -> uexp -> uexp -> uexp              (** update k u1 u2 *)
  | UMerge     : uexp -> uexp -> uexp                     (** merge u1 u2 *)
  | UInject    : key -> uexp -> uexp                      (** inject k u *)
  | UAbsurd    : uexp -> uexp                             (** absurd u *)
  | UPerform   : key -> opname -> uexp -> uexp            (** perform k.op u *)
  | UHandle    : uexp -> uhandler -> uexp                 (** handle u with h *)
  | URegion    : list key -> list uexp -> uexp -> uexp    (** region ℓ ( k̄ ) @ ( ū ) in u *)
  | UReadCell  : region_ref -> key -> uexp                (** readCell ℓ.k *)
  | UWriteCell : region_ref -> key -> uexp -> uexp        (** writeCell ℓ.k u *)
  | UMatch     : list uexp -> udtree -> uexp              (** match θ dt *)
  | UForce     : atom -> uexp                             (** force ν *)
  | UFill      : atom -> uexp -> uexp                     (** fill ν u *)
  | URegionOpen: atom -> list (key & uexp) -> uexp -> uexp (** region⟨ℓ⟩ θ in u *)
  | UOpaque    : nat -> uexp                              (** opaque ω *)

(** Erased decision trees: those of `exp`, node by node. *)
and udtree =
  | UDLeaf       : uexp -> udtree
  | UDBind       : occ -> udtree -> udtree
  | UDSwitchCtor : occ -> list (qname & udtree) -> option udtree -> udtree
  | UDSwitchLit  : occ -> list (lit & udtree) -> udtree -> udtree
  | UDSwitchKey  : occ -> list (key & udtree) -> option udtree -> udtree
  | UDGuard      : uexp -> udtree -> udtree -> udtree

(** `{ key k ; return x -> u_r ; cl_i }`: an erased handler carries the key
    of its element alone. *)
and uhandler = {
  uh_key     : key;
  uh_ret     : uexp;
  uh_clauses : list uclause;
}

(** `full op (x, k) -> u` and `fast op (x) -> u`. The marker survives
    erasure; the type binders `b̄` and the annotations go. *)
and uclause =
  | UCFull : op:opname -> body:uexp -> uclause
  | UCFast : op:opname -> body:uexp -> uclause

(** * Erasure (spec 06 §Erasure) *)

let rec erase (e: exp) : Tot uexp (decreases e) =
  match e with
  | EVar i -> UVar i
  | EGlobal q _ -> UGlobal q
  | ELit c -> ULit c
  | ELam _ _ b -> ULam (erase b)
  | EApp e1 e2 -> UApp (erase e1) (erase e2)
  | ETyLam _ v -> erase v
  | ETyApp b _ -> erase b
  | ECLam _ v -> erase v
  | ECApp b -> erase b
  | ELet _ e1 e2 -> ULet (erase e1) (erase e2)
  | ELetRec bs b -> ULetRec (erase_binds bs) (erase b)
  | ECase es dt -> UCase (erase_exps es) (erase_dt dt)
  | ELetJoin ts _ e1 e2 -> ULetJoin (L.length ts) (erase e1) (erase e2)
  | EJump j es -> UJump j (erase_exps es)
  | ERecEmpty -> URecEmpty
  | EExtend k e1 e2 -> UExtend k (erase e1) (erase e2)
  | ESelect k b -> USelect k (erase b)
  | ERestrict k b -> URestrict k (erase b)
  | EUpdate k e1 e2 -> UUpdate k (erase e1) (erase e2)
  | EMerge e1 e2 -> UMerge (erase e1) (erase e2)
  | EInject k _ b -> UInject k (erase b)
  | EWeaken _ _ b -> erase b
  | EAbsurd _ b -> UAbsurd (erase b)
  | EPerform k op _ b -> UPerform k op (erase b)
  | EHandle b h ->
    UHandle (erase b)
      { uh_key = ent_key h.h_ent; uh_ret = erase h.h_ret; uh_clauses = erase_cls h.h_clauses }
  | EOpenEff _ b -> erase b
  | ERegion lay es b -> URegion (L.map fst lay) (erase_exps es) (erase b)
  | EReadCell l k -> UReadCell l k
  | EWriteCell l k b -> UWriteCell l k (erase b)
  | EMatch th dt -> UMatch (erase_exps th) (erase_dt dt)
  | EOpenEffC _ b -> erase b
  | EForce nu -> UForce nu
  | EFill nu b -> UFill nu (erase b)
  | ERegionOpen a th b -> URegionOpen a (erase_cells th) (erase b)
  | EOpaque w _ -> UOpaque w

and erase_exps (es: list exp) : Tot (list uexp) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> erase e :: erase_exps es

and erase_binds (bs: list (typ & exp)) : Tot (list uexp) (decreases bs) =
  match bs with
  | [] -> []
  | (_, e) :: bs -> erase e :: erase_binds bs

and erase_cells (th: list (key & exp)) : Tot (list (key & uexp)) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> (k, erase e) :: erase_cells th

and erase_dt (dt: dtree) : Tot udtree (decreases dt) =
  match dt with
  | DLeaf e -> UDLeaf (erase e)
  | DBind o dt -> UDBind o (erase_dt dt)
  | DSwitchCtor o bs df -> UDSwitchCtor o (erase_brs bs) (erase_odt df)
  | DSwitchLit o bs df -> UDSwitchLit o (erase_brs bs) (erase_dt df)
  | DSwitchKey o bs df -> UDSwitchKey o (erase_brs bs) (erase_odt df)
  | DGuard e dt1 dt2 -> UDGuard (erase e) (erase_dt dt1) (erase_dt dt2)

and erase_odt (df: option dtree) : Tot (option udtree) (decreases df) =
  match df with
  | None -> None
  | Some dt -> Some (erase_dt dt)

and erase_brs (#lb: eqtype) (bs: list (lb & dtree)) : Tot (list (lb & udtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (l, dt) :: bs -> (l, erase_dt dt) :: erase_brs bs

and erase_cls (cs: list clause) : Tot (list uclause) (decreases cs) =
  match cs with
  | [] -> []
  | CFull op _ _ _ b :: cs -> UCFull op (erase b) :: erase_cls cs
  | CFast op _ _ b :: cs -> UCFast op (erase b) :: erase_cls cs

(** `erase_exps` is `erase` pointwise. *)
val erase_exps_map (es: list exp) : Lemma (erase_exps es == L.map erase es)

(** * Outcomes *)

(** A fault the ABI specifies, with a payload Core does not interpret
    (spec 06 §Faults). The same fault is the outcome of a typed call and of
    its erasure. *)
type abi_fault =
  | AbiFault : payload:nat -> abi_fault

(** The outcome of a typed foreign call, what the typed adapter `δᵀ_f`
    gives: an annotated term, or an ABI fault. The type does not constrain
    the term of `FOVal` to be a value; condition (3) of conformance
    (`Stella.Core.Semantics.Env.genv_ok`) does. *)
type foreign_outcome =
  | FOVal   : exp -> foreign_outcome
  | FOFault : abi_fault -> foreign_outcome

(** The outcome of an erased foreign call, what the erased function `δᵤ_f`
    gives: an erased term, or an ABI fault. *)
type uoutcome =
  | UOVal   : uexp -> uoutcome
  | UOFault : abi_fault -> uoutcome

(** `eraseOutcome` (spec 06 §An implementation, and the typed view it is
    read through): the erasure of the value, or the same fault. *)
let erase_outcome (o: foreign_outcome) : uoutcome =
  match o with
  | FOVal v -> UOVal (erase v)
  | FOFault phi -> UOFault phi
