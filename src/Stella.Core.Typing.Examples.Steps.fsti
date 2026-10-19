(**
 * Derivations of `Stella.Core.Typing` for terms on either side of a
 * reduction step, over `Stella.Core.Typing.Examples.ex_sig`: each redex and
 * its contractum have the same type at the same ambient row.
 *
 *   - Chains at a non-empty ambient row: `openEffC [(Partial)] (Just [Int] 1)`
 *     and its contractum `Just [Int] 1`, an unsaturated foreign chain, which
 *     is a value, and a saturated one, which is a redex.
 *   - Region frames: a frame whose outer row is a type variable has no
 *     type, and a frame with closed types keeps its type under a type
 *     substitution, here the step `(Λ r. λ (u : Unit) / r. …) [(region a)]`.
 *   - Variant values: a `switchKey` default refines its occurrence to the
 *     residual type, which the scrutinee value has as well.
 *   - `switchKey` under a substitution: the split of a variant row is kept
 *     when an instantiation merges two entries of one key, under an
 *     assumption that the instance contradicts.
 *)
module Stella.Core.Typing.Examples.Steps
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Examples
module V = Stella.Core.Value

(** * Chains at a non-empty row *)

(** `( Partial )` *)
let partial_row : typ = TRowExt partial_ent TRowEmpty

let lit_int (n: Int32.t) : exp = ELit (LInt n)

(** `Prelude.Just [Int] 1` *)
let just_one : exp = EApp (ETyApp (EGlobal (prelude "Just") []) t_int) (lit_int 1l)

(** `openEffC [(Partial)] (Prelude.Just [Int] 1)`, which steps to
    `Prelude.Just [Int] 1`. *)
let open_just_one : exp = EOpenEffC partial_row just_one

val open_just_one_typing :
  typing ex_sig [] (decl_ctx 0) [] true open_just_one (maybe_ty t_int) partial_row

val just_one_typing : typing ex_sig [] (decl_ctx 0) [] true just_one (maybe_ty t_int) partial_row

(** `Prelude.konst [Int] 1`, a value: its declared remainder is an arrow. *)
let konst_one : exp = EApp (ETyApp (EGlobal (prelude "konst") []) t_int) (lit_int 1l)

val konst_one_value : unit -> Lemma (V.is_value ex_sig konst_one)

val konst_one_typing :
  typing ex_sig [] (decl_ctx 0) [] true konst_one (t_fun t_int TRowEmpty t_int) partial_row

(** `Prelude.konst [Int] 1 2`, saturated, a redex. *)
let konst_one_two : exp = EApp konst_one (lit_int 2l)

val konst_one_two_redex : unit -> Lemma (V.foreign_redex ex_sig konst_one_two)

val konst_one_two_typing :
  typing ex_sig [] (decl_ctx 0) [] true konst_one_two t_int partial_row

(** * Region frames *)

(** The region `a` of `Γ_R`, with the empty layout. *)
let reg_a : atom = 7

(** The run-time context: no binder, and `Γ_R = { region a : () }`. *)
let g_run : ctx = closed_ctx [(reg_a, [])]

(** `region⟨a⟩ ∅ in Prim.Unit` *)
let frame : exp = ERegionOpen reg_a [] (EGlobal prim_unit_ctor [])

(** `Λ (r : Row Effect). λ (u : Unit) / r. region⟨a⟩ ∅ in Prim.Unit`: the
    frame stands at the row `r`, which is no closed type. *)
let frame_at_var : exp = ETyLam (KRow EEffect) (ELam t_unit (TVar 0) frame)

val frame_at_var_untypable (#d: jctx) (#tl: bool) (#t #r: typ)
  (h: typing ex_sig [] g_run d tl frame_at_var t r)
  : Lemma False

(** `( region a )` *)
let region_row : typ = TRowExt (EntRegion (RFree reg_a)) TRowEmpty

(** `λ (u : Unit) / r. openEffC [r] (region⟨a⟩ ∅ in Prim.Unit)`, under
    `r : Row Effect`. The frame stands at `()`. *)
let frame_fn : exp = ELam t_unit (TVar 0) (EOpenEffC (TVar 0) frame)

(** `(Λ (r : Row Effect). frame_fn) [(region a)]`, which steps to
    `frame_fn[r := (region a)]`. *)
let frame_redex : exp = ETyApp (ETyLam (KRow EEffect) frame_fn) region_row

(** `λ (u : Unit) / (region a). openEffC [(region a)] (region⟨a⟩ ∅ in Prim.Unit)` *)
let frame_contractum : exp = ELam t_unit region_row (EOpenEffC region_row frame)

val frame_contractum_inst : unit -> Lemma (subst1_ty_exp region_row frame_fn == frame_contractum)

(** The frame has the type `Unit ! ()` under `r`, and the same in the
    instance, where `r` is `( region a )`. *)
val frame_typing_under_var :
  typing ex_sig [] (push_var (push_tvar g_run (KRow EEffect)) t_unit) [] false frame t_unit
    TRowEmpty

val frame_typing_inst : typing ex_sig [] (push_var g_run t_unit) [] false frame t_unit TRowEmpty

val frame_redex_typing :
  typing ex_sig [] g_run [] true frame_redex (t_fun t_unit region_row t_unit) TRowEmpty

val frame_contractum_typing :
  typing ex_sig [] g_run [] true frame_contractum (t_fun t_unit region_row t_unit) TRowEmpty

(** * A variant value at its residual type *)

(** `( y : Bool )` *)
let row_yb : typ = TRowExt (EntTy key_y t_bool) TRowEmpty

(** `( x : Int )` *)
let row_xi : typ = TRowExt (EntTy key_x t_int) TRowEmpty

(** `inject y [(x : Int)] true : Variant ( y : Bool | x : Int )` *)
let inj_y : exp = EInject key_y row_xi (ELit (LBool true))

(** `case (inject y [(x : Int)] true) of
       switchKey s0 { x -> inject y [()] false } default -> bind z = s0 in z`.
    The default takes the scrutinee at the residual `Variant ( y : Bool )`,
    and its `match` binds the value `inj_y` there. *)
let case_inj : exp =
  ECase [inj_y]
    (DSwitchKey (OScrut 0)
       [(key_x, DLeaf (EInject key_y TRowEmpty (ELit (LBool false))))]
       (Some (DBind (OScrut 0) (DLeaf (EVar 0)))))

val case_inj_typing : typing ex_sig [] (decl_ctx 0) [] true case_inj (t_variant row_yb) TRowEmpty

val inj_y_residual_typing :
  typing ex_sig [] (decl_ctx 0) [] false inj_y (t_variant row_yb) TRowEmpty

(** The annotation of a variant value is checked: with a region reference
    that no `region` binds in its row, `inject y [ρ] true` has no type,
    `Variant ( y : Bool )` included. *)
let row_dangling : typ =
  TRowExt (EntTy key_x (t_fun t_int (TRowExt (EntRegion (RBound 0)) TRowEmpty) t_int)) TRowEmpty

let inj_dangling : exp = EInject key_y row_dangling (ELit (LBool true))

val inj_dangling_untypable (#g: ctx) (#d: jctx) (#tl: bool) (#t #r: typ)
  (h: typing ex_sig [] g d tl inj_dangling t r)
  : Lemma False

(** * `switchKey` under a substitution *)

(** `( y : Int )` *)
let row_yi : typ = TRowExt (EntTy key_y t_int) TRowEmpty

(** `y ∉ c`, for a row `c` *)
let lacks_y (c: typ) : constr = CLacks key_y c

(** `λ (x : Variant ( y : Int | c )) / (). case x of
       switchKey s0 { y -> 0 } default -> bind z = s0 in 1` *)
let switch_fn (c: typ) : exp =
  ELam (t_variant (TRowExt (EntTy key_y t_int) c)) TRowEmpty
    (ECase [EVar 0]
       (DSwitchKey (OScrut 0) [(key_y, DLeaf (lit_int 0l))]
          (Some (DBind (OScrut 0) (DLeaf (lit_int 1l))))))

(** `(Λ (r : Row Type). Λ (_ : y ∉ r). switch_fn r) [(y : Int)]`. The
    contractum assumes `y ∉ ( y : Int )`, which no instance satisfies, and
    its scrutinee has the type `Variant ( y : Int | y : Int )`, whose
    canonical form has one entry: the split by the branch `y : Int` keeps
    the residual `( y : Int )`. *)
let switch_redex : exp =
  ETyApp (ETyLam (KRow EType) (ECLam (lacks_y (TVar 0)) (switch_fn (TVar 0)))) row_yi

let switch_contractum : exp = ECLam (lacks_y row_yi) (switch_fn row_yi)

val switch_contractum_inst : unit ->
  Lemma (subst1_ty_exp row_yi (ECLam (lacks_y (TVar 0)) (switch_fn (TVar 0))) == switch_contractum)

(** `y ∉ ( y : Int ) => Variant ( y : Int | y : Int ) -> Int` *)
let switch_ty : typ =
  TConstr (lacks_y row_yi) (t_fun (t_variant (TRowExt (EntTy key_y t_int) row_yi)) TRowEmpty t_int)

val switch_redex_typing : typing ex_sig [] (decl_ctx 0) [] true switch_redex switch_ty TRowEmpty

val switch_contractum_typing :
  typing ex_sig [] (decl_ctx 0) [] true switch_contractum switch_ty TRowEmpty
