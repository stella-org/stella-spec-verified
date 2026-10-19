(**
 * The cursor under a well-formed signature (spec 05 §The cursor, §Typing a
 * chain).
 *
 *   - Under `prim_wf`, the function types the cursor reads are those of
 *     `Prim.Function`, and such a type is kinded exactly when its parts
 *     are.
 *   - Under `sig_ok`, every arrow the cursor consumes in the declared type
 *     of a constructor or a foreign is pure: its row is `()` up to type
 *     equality, before and after the accumulated substitution.
 *   - Regularity of the cursor: when the type and constraint arguments of a
 *     chain are well formed against the cursor (`spine_args_ok`, the table
 *     of spec 05 §Typing a chain without its row for value arguments), the
 *     instance `θ(σ)` of every remainder `σ` the cursor reaches is kinded.
 *     The step lemmas carry this one argument at a time, as a typing rule
 *     that builds a chain one node at a time reads it.
 *   - A type substitution of a chain keeps the remainder its cursor
 *     reaches and substitutes the remainder's instance.
 *)
module Stella.Core.Spine.Wf
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Spine
module L = FStar.List.Tot

(** * Function types *)

val as_function_t_fun (sg: sig) (t t1 r t2: typ)
  : Lemma (requires prim_wf sg /\ as_function sg t == Some (t1, r, t2)) (ensures t == t_fun t1 r t2)

val check_as_function (sg: sig) (g: ctx) (t t1 r t2: typ)
  : Lemma (requires prim_wf sg /\ as_function sg t == Some (t1, r, t2))
          (ensures check sg g t KType <==>
                   check sg g t1 KType /\ check sg g r (KRow EEffect) /\ check sg g t2 KType)

(** * Purity (D23) *)

(** An arrow the cursor of a constructor or a foreign reaches is pure. *)
val cursor_arrow_pure (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg) (t: typ)
  (th: tsub) (t1 r t2: typ)
  : Lemma (requires sig_ok sg /\ spine_cursor sg q ks args == Some (t, th) /\
                    as_function sg t == Some (t1, r, t2))
          (ensures ty_eq r TRowEmpty /\ ty_eq (sub_ty th r) TRowEmpty)

(** * Well-formed arguments (spec 05 §Typing a chain) *)

(** The argument `a` is well formed in `g` against the remainder `σ`
    under `θ`: a `[τ]` consumes `forall (a : κ)` and has kind `κ`, a `[•]`
    consumes `C =>` and `θ(C)` is entailed, and a value argument consumes a
    function type. A value argument's own typing is a premise of the typing
    rules. *)
let arg_ok (sg: sig) (g: ctx) (t: typ) (th: tsub) (a: spine_arg) : bool =
  match a, t with
  | STy s, TForall k _ -> check sg g s k
  | SConstr, TConstr c _ -> entails (hyps g) (sub_constr th c)
  | SVal _, _ -> Some? (as_function sg t)
  | _, _ -> false

(** Each argument is well formed against the cursor before it. *)
let rec cursor_args_ok (sg: sig) (g: ctx) (t: typ) (th: tsub) (args: list spine_arg)
  : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: args ->
    arg_ok sg g t th a &&
    (match cursor_step sg t th a with
     | Some (t', th') -> cursor_args_ok sg g t' th' args
     | None -> false)

(** The kinds and the arguments of `M.g [[κ̄]] ᾱ` are well formed in `g`:
    `κ̄` are well-formed quantifiable kinds, as many as the kind variables
    of `M.g`, and every argument of `ᾱ` is well formed against the cursor. *)
let spine_args_ok (sg: sig) (g: ctx) (q: qname) (ks: list kind) (args: list spine_arg) : bool =
  match global_scheme sg q with
  | Some (_, nk, t) ->
    L.length ks = nk && qkinds_wf g.nk ks && cursor_args_ok sg g (kinst_ty ks t) tvar args
  | None -> false

val cursor_args_ok_snoc (sg: sig) (g: ctx) (t: typ) (th: tsub) (args: list spine_arg)
  (a: spine_arg)
  : Lemma (cursor_args_ok sg g t th (L.append args [a]) ==
           (cursor_args_ok sg g t th args &&
            (match cursor sg t th args with
             | Some (t', th') -> arg_ok sg g t' th' a
             | None -> false)))

val spine_args_ok_snoc (sg: sig) (g: ctx) (q: qname) (ks: list kind) (args: list spine_arg)
  (a: spine_arg)
  : Lemma (spine_args_ok sg g q ks (L.append args [a]) ==
           (spine_args_ok sg g q ks args &&
            (match spine_cursor sg q ks args with
             | Some (t', th') -> arg_ok sg g t' th' a
             | None -> false)))

(** * Regularity *)

(** The atomic reference: the declared scheme instantiated at kinds of the
    context, under the identity substitution, is kinded. *)
val spine_cursor_nil_regular (sg: sig) (g: ctx) (q: qname) (ks: list kind)
  : Lemma (requires sig_wf sg /\ spine_args_ok sg g q ks [])
          (ensures (match spine_cursor sg q ks [] with
                    | Some (t, th) -> check sg g (sub_ty th t) KType
                    | None -> False))

(** One well-formed argument keeps the instance kinded. *)
val cursor_step_regular (sg: sig) (g: ctx) (t: typ) (th: tsub) (a: spine_arg) (t': typ)
  (th': tsub)
  : Lemma (requires prim_wf sg /\ check sg g (sub_ty th t) KType /\ arg_ok sg g t th a /\
                    cursor_step sg t th a == Some (t', th'))
          (ensures check sg g (sub_ty th' t') KType)

val cursor_regular (sg: sig) (g: ctx) (t: typ) (th: tsub) (args: list spine_arg) (t': typ)
  (th': tsub)
  : Lemma (requires prim_wf sg /\ check sg g (sub_ty th t) KType /\ cursor_args_ok sg g t th args /\
                    cursor sg t th args == Some (t', th'))
          (ensures check sg g (sub_ty th' t') KType)

(** The instance `θ(σ)` of the remainder of a chain with well-formed
    arguments is kinded. *)
val spine_cursor_regular (sg: sig) (g: ctx) (q: qname) (ks: list kind) (args: list spine_arg)
  (t: typ) (th: tsub)
  : Lemma (requires sig_ok sg /\ spine_args_ok sg g q ks args /\
                    spine_cursor sg q ks args == Some (t, th))
          (ensures check sg g (sub_ty th t) KType)

(** At a remainder that is an arrow `τ1 -{ρ}-> τ2`, the next value
    argument's type `θ(τ1)` and the result `θ(τ2)` are kinded, and `θ(ρ)`
    is pure. *)
val spine_cursor_fun_regular (sg: sig) (g: ctx) (q: qname) (ks: list kind)
  (args: list spine_arg) (t: typ) (th: tsub) (t1 r t2: typ)
  : Lemma (requires sig_ok sg /\ spine_args_ok sg g q ks args /\
                    spine_cursor sg q ks args == Some (t, th) /\ as_function sg t == Some (t1, r, t2))
          (ensures check sg g (sub_ty th t1) KType /\ check sg g (sub_ty th t2) KType /\
                   ty_eq (sub_ty th r) TRowEmpty)

(** * Chains under type substitution *)

(** A type substitution keeps the remainder the cursor of a chain reaches,
    and maps its instance and, at an arrow, the instances of the arrow's
    parts, and at a constraint arrow the instance of its constraint: the
    declared type is closed, so the accumulated substitution is consulted
    only at the variables of consumed binders, which the chain's
    substituted type arguments instantiate. A renaming is the substitution
    `ren_tsub ξ` (`Stella.Core.Subst.Lemmas.TyExp.ren_ty_exp_as_sub`). *)
val chain_cursor_sub_ty (sg: sig) (sigma: tsub) (e: exp) (t: typ) (th: tsub)
  : Lemma (requires sig_wf sg /\ chain_cursor sg e == Some (t, th))
          (ensures (match chain_cursor sg (sub_ty_exp sigma e) with
                    | Some (t', th') ->
                      t' == t /\ sub_ty th' t == sub_ty sigma (sub_ty th t) /\
                      (forall (t1 r t2: typ). as_function sg t == Some (t1, r, t2) ==>
                         sub_ty th' t1 == sub_ty sigma (sub_ty th t1) /\
                         sub_ty th' r == sub_ty sigma (sub_ty th r) /\
                         sub_ty th' t2 == sub_ty sigma (sub_ty th t2)) /\
                      (forall (c: constr) (b: typ). t == TConstr c b ==>
                         sub_constr th' c == sub_constr sigma (sub_constr th c))
                    | None -> False))
