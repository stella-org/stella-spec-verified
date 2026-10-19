(**
 * Chains and their cursors under the maps of the metatheory, and the
 * cursor of a saturated constructor chain (spec 05 §The cursor, §Typing a
 * chain, §Join points and decision trees).
 *
 *   - Kind instantiations compose on a type whose kind variables the inner
 *     vector covers (`kvs_below`), as the declared scheme of a global is.
 *   - A kind instantiation, a region map, a term renaming and a join
 *     renaming keep the head of a chain and map its arguments. The cursor
 *     reads only the declared type and the type arguments, so a term or
 *     join renaming keeps it; a kind instantiation instantiates the
 *     remainder and the instances; a region map keeps the remainder, which
 *     has no region reference, and maps the instances.
 *   - The cursor of a chain collects, at each value argument, the instance
 *     `θ(τ1)` of the arrow's domain it meets (`chain_domains`).
 *   - A saturated constructor chain `C [[κ̄]] [σ̄] v̄` of the data type `T`
 *     consists of the type arguments `σ̄` followed by the value arguments,
 *     its instance is `T [[κ̄]] σ̄`, and its domains are the fields
 *     `ctor_fields C κ̄ σ̄`.
 *)
module Stella.Core.Spine.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Typing.Aux
module L = FStar.List.Tot

(** * Kind instantiation *)

(** Every kind variable of `t` is below `n`. *)
let rec kvs_below (n: nat) (t: typ) : Tot bool (decreases t) =
  match t with
  | TVar _ | TRowEmpty -> true
  | TCon _ kl -> kinds_below n kl
  | TApp t1 t2 | TRowUnion t1 t2 -> kvs_below n t1 && kvs_below n t2
  | TForall k b -> kind_wf n k && kvs_below n b
  | TConstr c b -> kvs_below_constr n c && kvs_below n b
  | TRowExt en r -> kvs_below_ent n en && kvs_below n r

and kvs_below_ent (n: nat) (en: entry) : Tot bool (decreases en) =
  match en with
  | EntTy _ t -> kvs_below n t
  | EntEff _ _ ts -> kvs_below_tys n ts
  | EntRegion _ -> true

and kvs_below_constr (n: nat) (c: constr) : Tot bool (decreases c) =
  match c with
  | CLacks _ t -> kvs_below n t
  | CDisj t1 t2 -> kvs_below n t1 && kvs_below n t2

and kvs_below_tys (n: nat) (ts: list typ) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | t :: ts -> kvs_below n t && kvs_below_tys n ts

and kinds_below (n: nat) (kl: list kind) : Tot bool (decreases kl) =
  match kl with
  | [] -> true
  | k :: kl -> kind_wf n k && kinds_below n kl

(** A kinded type mentions only the kind variables in scope. *)
val check_kvs_below (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg g t k) (ensures kvs_below g.nk t)

val kinst_ty_comp (ks ks0: list kind) (t: typ)
  : Lemma (requires kvs_below (L.length ks0) t)
          (ensures kinst_ty ks (kinst_ty ks0 t) == kinst_ty (kinst_kinds ks ks0) t)

val kinst_constr_comp (ks ks0: list kind) (c: constr)
  : Lemma (requires kvs_below_constr (L.length ks0) c)
          (ensures kinst_constr ks (kinst_constr ks0 c) == kinst_constr (kinst_kinds ks ks0) c)

(** * Chains under the maps *)

let kinst_arg (ks: list kind) (a: spine_arg) : spine_arg =
  match a with
  | STy t -> STy (kinst_ty ks t)
  | SConstr -> SConstr
  | SVal v -> SVal (kinst_exp ks v)

let rmap_arg (f: nat -> region_ref -> region_ref) (d: nat) (a: spine_arg) : spine_arg =
  match a with
  | STy t -> STy (rmap_ty (f d) t)
  | SConstr -> SConstr
  | SVal v -> SVal (rmap_exp f d v)

(** A map of the value arguments alone. *)
let val_arg (fv: exp -> exp) (a: spine_arg) : spine_arg =
  match a with
  | SVal v -> SVal (fv v)
  | _ -> a

val decompose_kinst (ks: list kind) (e: exp)
  : Lemma (decompose_global_app (kinst_exp ks e) ==
           (match decompose_global_app e with
            | Some (q, kl, args) -> Some (q, kinst_kinds ks kl, L.map (kinst_arg ks) args)
            | None -> None))

val decompose_rmap (f: nat -> region_ref -> region_ref) (d: nat) (e: exp)
  : Lemma (decompose_global_app (rmap_exp f d e) ==
           (match decompose_global_app e with
            | Some (q, kl, args) -> Some (q, kl, L.map (rmap_arg f d) args)
            | None -> None))

(** A renaming maps a variable to a variable, so it makes no chain and
    breaks none. *)
val decompose_ren_tm (xi: ren) (e: exp)
  : Lemma (decompose_global_app (ren_tm xi e) ==
           (match decompose_global_app e with
            | Some (q, kl, args) -> Some (q, kl, L.map (val_arg (ren_tm xi)) args)
            | None -> None))

val decompose_ren_jp (xi: ren) (e: exp)
  : Lemma (decompose_global_app (ren_jp xi e) ==
           (match decompose_global_app e with
            | Some (q, kl, args) -> Some (q, kl, L.map (val_arg (ren_jp xi)) args)
            | None -> None))

(** The cursor does not read the value arguments. *)
val cursor_val_args (sg: sig) (fv: exp -> exp) (t: typ) (th: tsub) (args: list spine_arg)
  : Lemma (cursor sg t th (L.map (val_arg fv) args) == cursor sg t th args)

val chain_cursor_ren_tm (sg: sig) (xi: ren) (e: exp)
  : Lemma (chain_cursor sg (ren_tm xi e) == chain_cursor sg e)

val chain_cursor_ren_jp (sg: sig) (xi: ren) (e: exp)
  : Lemma (chain_cursor sg (ren_jp xi e) == chain_cursor sg e)

(** A kind instantiation of a chain instantiates the remainder its cursor
    reaches and, pointwise, the accumulated substitution, so it commutes
    with the instance of the remainder, of an arrow's parts, and of a
    constraint. *)
val chain_cursor_kinst (sg: sig) (ks: list kind) (e: exp) (t: typ) (th: tsub)
  : Lemma (requires sig_wf sg /\ chain_cursor sg e == Some (t, th))
          (ensures (match chain_cursor sg (kinst_exp ks e) with
                    | Some (t', th') ->
                      t' == kinst_ty ks t /\
                      (forall (i: nat). th' i == kinst_ty ks (th i)) /\
                      sub_ty th' t' == kinst_ty ks (sub_ty th t) /\
                      (forall (t1 r t2: typ). as_function sg t == Some (t1, r, t2) ==>
                         as_function sg t' == Some (kinst_ty ks t1, kinst_ty ks r, kinst_ty ks t2) /\
                         sub_ty th' (kinst_ty ks t1) == kinst_ty ks (sub_ty th t1) /\
                         sub_ty th' (kinst_ty ks r) == kinst_ty ks (sub_ty th r) /\
                         sub_ty th' (kinst_ty ks t2) == kinst_ty ks (sub_ty th t2)) /\
                      (forall (c: constr) (b: typ). t == TConstr c b ==>
                         sub_constr th' (kinst_constr ks c) == kinst_constr ks (sub_constr th c))
                    | None -> False))

(** A region map of a chain keeps the remainder its cursor reaches, which
    is part of a declared type and so mentions no region, and maps the
    accumulated substitution pointwise and every instance. *)
val chain_cursor_rmap (sg: sig) (f: nat -> region_ref -> region_ref) (d: nat) (e: exp) (t: typ)
  (th: tsub)
  : Lemma (requires sig_wf sg /\ chain_cursor sg e == Some (t, th))
          (ensures (match chain_cursor sg (rmap_exp f d e) with
                    | Some (t', th') ->
                      t' == t /\ rmap_ty (f d) t == t /\
                      (forall (i: nat). th' i == rmap_ty (f d) (th i)) /\
                      sub_ty th' t == rmap_ty (f d) (sub_ty th t) /\
                      (forall (t1 r t2: typ). as_function sg t == Some (t1, r, t2) ==>
                         sub_ty th' t1 == rmap_ty (f d) (sub_ty th t1) /\
                         sub_ty th' r == rmap_ty (f d) (sub_ty th r) /\
                         sub_ty th' t2 == rmap_ty (f d) (sub_ty th t2)) /\
                      (forall (c: constr) (b: typ). t == TConstr c b ==>
                         sub_constr th' c == rmap_constr (f d) (sub_constr th c))
                    | None -> False))

(** * The domains of a chain *)

(** The instance `θ(τ1)` of the domain of the arrow `τ1 -{ρ}-> τ2` that a
    value argument meets at the remainder `t` under `θ`; nothing for a type
    or constraint argument. *)
let arg_domain (sg: sig) (t: typ) (th: tsub) (a: spine_arg) : list typ =
  match a with
  | SVal _ ->
    (match as_function sg t with
     | Some (t1, _, _) -> [sub_ty th t1]
     | None -> [])
  | _ -> []

(** The domains met by the arguments consumed in written order, up to the
    first one the cursor does not consume. *)
let rec cursor_domains (sg: sig) (t: typ) (th: tsub) (args: list spine_arg)
  : Tot (list typ) (decreases args) =
  match args with
  | [] -> []
  | a :: args ->
    L.append (arg_domain sg t th a)
      (match cursor_step sg t th a with
       | Some (t', th') -> cursor_domains sg t' th' args
       | None -> [])

(** The domains of the chain `e`, one per value argument when its cursor is
    defined. *)
let chain_domains (sg: sig) (e: exp) : list typ =
  match decompose_global_app e with
  | Some (q, ks, args) ->
    (match global_scheme sg q with
     | Some (_, nk, t) -> if L.length ks = nk then cursor_domains sg (kinst_ty ks t) tvar args else []
     | None -> [])
  | None -> []

(** The value arguments of the chain `e`. *)
let chain_value_args (e: exp) : list exp =
  match decompose_global_app e with
  | Some (_, _, args) -> value_args args
  | None -> []

val cursor_domains_snoc (sg: sig) (t: typ) (th: tsub) (args: list spine_arg) (a: spine_arg)
  : Lemma (cursor_domains sg t th (L.append args [a]) ==
           L.append (cursor_domains sg t th args)
             (match cursor sg t th args with
              | Some (t', th') -> arg_domain sg t' th' a
              | None -> []))

(** Each `EApp`, `ETyApp` and `ECApp` node over a chain adds the domain its
    argument meets, and its value argument if it has one. *)
val chain_domains_apply_arg (sg: sig) (e: exp) (a: spine_arg)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures chain_domains sg (apply_arg e a) ==
                   L.append (chain_domains sg e)
                     (match chain_cursor sg e with
                      | Some (t', th') -> arg_domain sg t' th' a
                      | None -> []) /\
                   chain_value_args (apply_arg e a) ==
                   L.append (chain_value_args e) (match a with SVal v -> [v] | _ -> []))

(** * Saturated constructor chains *)

(** The type arguments of a spine, in written order. *)
let rec ty_args (args: list spine_arg) : Tot (list typ) (decreases args) =
  match args with
  | [] -> []
  | STy t :: args -> t :: ty_args args
  | _ :: args -> ty_args args

(** A constructor chain whose cursor reaches a saturated remainder consists
    of the type arguments `σ̄`, one per parameter of the data type, followed
    by the value arguments, one per field. Its instance is `T [[κ̄]] σ̄`, `T`
    the constructor's owner, and the domains its value arguments meet are
    the fields `ctor_fields C κ̄ σ̄`. *)
val ctor_chain_saturated (sg: sig) (e: exp) (c: qname) (ks: list kind) (args: list spine_arg)
  (ci: ctor_info) (t: typ) (th: tsub)
  : Lemma (requires sig_ok sg /\ decompose_global_app e == Some (c, ks, args) /\
                    sg.ctors c == Some ci /\ chain_cursor sg e == Some (t, th) /\ saturated sg t)
          (ensures args == L.append (L.map STy (ty_args args)) (L.map SVal (value_args args)) /\
                   sub_ty th t == tapps (TCon ci.ct_owner ks) (ty_args args) /\
                   ctor_fields sg c ks (ty_args args) == Some (chain_domains sg e) /\
                   L.length (chain_domains sg e) == L.length (value_args args) /\
                   L.length (value_args args) == ci.ct_arity)
