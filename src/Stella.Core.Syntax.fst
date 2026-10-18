(* The proofs of `canon_number_idem` and of the chain view, and the
   decidable-equality checks of `Stella.Core.Syntax`. *)
module Stella.Core.Syntax
module U64 = FStar.UInt64
module I32 = FStar.Int32
module L = FStar.List.Tot

let canon_number_idem (b: U64.t)
  : Lemma (canon_number (canon_number b) == canon_number b)
  = assert_norm (is_nan_bits canonical_nan)

let rec apply_args_snoc (e: exp) (args: list spine_arg) (a: spine_arg)
  : Lemma (ensures apply_args e (L.append args [a]) == apply_arg (apply_args e args) a)
          (decreases args) =
  match args with
  | [] -> ()
  | b :: args -> apply_args_snoc (apply_arg e b) args a

let decompose_apply_arg (e: exp) (a: spine_arg)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures (let Some (q, ks, args0) = decompose_global_app e in
                    decompose_global_app (apply_arg e a) == Some (q, ks, L.append args0 [a]))) =
  ()

let rec decompose_apply_args (e: exp) (args: list spine_arg)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures (let Some (q, ks, args0) = decompose_global_app e in
                    decompose_global_app (apply_args e args) == Some (q, ks, L.append args0 args)))
          (decreases args) =
  match args with
  | [] -> let Some (_, _, args0) = decompose_global_app e in L.append_l_nil args0
  | a :: rest ->
    let Some (_, _, args0) = decompose_global_app e in
    decompose_apply_arg e a;
    decompose_apply_args (apply_arg e a) rest;
    L.append_assoc args0 [a] rest

let decompose_recompose (q: qname) (ks: list kind) (args: list spine_arg)
  : Lemma (decompose_global_app (recompose q ks args) == Some (q, ks, args)) =
  decompose_apply_args (EGlobal q ks) args

let rec recompose_decompose (e: exp)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures (let Some (q, ks, args) = decompose_global_app e in
                    recompose q ks args == e))
          (decreases e) =
  match e with
  | EGlobal _ _ -> ()
  | EApp f v ->
    recompose_decompose f;
    let Some (q, ks, args) = decompose_global_app f in
    apply_args_snoc (EGlobal q ks) args (SVal v)
  | ETyApp f t ->
    recompose_decompose f;
    let Some (q, ks, args) = decompose_global_app f in
    apply_args_snoc (EGlobal q ks) args (STy t)
  | ECApp f ->
    recompose_decompose f;
    let Some (q, ks, args) = decompose_global_app f in
    apply_args_snoc (EGlobal q ks) args SConstr

(* Every syntactic class is an eqtype, as computational type equality
   (design §2) needs. Each ascription fails to check if a change to the AST
   loses decidable equality, e.g. through a function field. *)
let _ : eqtype = kind
let _ : eqtype = key
let _ : eqtype = typ
let _ : eqtype = entry
let _ : eqtype = constr
let _ : eqtype = lit
let _ : eqtype = exp
let _ : eqtype = dtree
let _ : eqtype = handler
let _ : eqtype = spine_arg
