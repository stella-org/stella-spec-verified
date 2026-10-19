(**
 * Well-formedness of the global signature `Σ` (spec 01 §Kinds, §Kind
 * schemes; spec 05 §Contexts, §Typing a chain).
 *
 * `sig_wf` holds the kinding conditions on the entries:
 *
 *   - A type constructor's kind is a well-formed quantifiable kind under its
 *     kind variables and produces `Type`.
 *   - An effect's parameter kinds are well-formed quantifiable kinds with no
 *     kind variable. Each operation's binder kinds are too, and its argument
 *     and result types have kind `Type` under the effect's parameters and,
 *     inside them, the operation's binders (design §3.1).
 *   - The type of a data constructor, a foreign, and a top-level value has
 *     kind `Type` under its kind variables, with no type variable in scope.
 *   - A name is at most one of a data constructor, a foreign, and a
 *     top-level value (`globals_disjoint`).
 *   - The operations of an effect have distinct names, so that `op_of`
 *     finds the one declaration of a name and a handler covers it by name.
 *
 * `prim_wf` says that `Σ` records the names of `Prim` that the typing rules
 * mention (`Stella.Core.Prim`) as the rules assume them.
 *
 * `globals_ok` relates the constructors to their data types and the
 * foreigns to D23:
 *
 *   - A constructor of the data type `T : forall k̄. κ̄ -> Type` has the
 *     scheme `forall k̄. forall (ā : κ̄). τ̄ -{()}-> T [[k̄]] ā`
 *     (`ctor_scheme`), and its arity is `|τ̄|`.
 *   - A constructor's owner lists it, and every name a data type lists is a
 *     constructor owned by that type. The constructors of one data type have
 *     distinct tags.
 *   - Every arrow of a foreign's type outside a constraint is pure (D23,
 *     `arrows_pure`).
 *
 * So every arrow the cursor consumes in a constructor's or a foreign's
 * declared type is pure (`Stella.Core.Spine.Wf`). The arrows inside the
 * fields of a constructor are not constrained: a data type may hold an
 * effectful function.
 *
 * `sig_ok` is the conjunction of the three, the assumption on `Σ` of the
 * typing relation's metatheory. Each class of entry has its own condition,
 * so that a fact needing only one of them assumes only that one.
 *)
module Stella.Core.Sig.Wf
open Stella.Core.Syntax
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
module L = FStar.List.Tot

(** * Entries *)

let tycon_ok (ti: tycon_info) : bool =
  kind_wf ti.tc_nk ti.tc_kind && qkind ti.tc_nk ti.tc_kind && result ti.tc_kind = KType

let op_ok (sg: sig) (params: list kind) (os: op_sig) : bool =
  let g = push_tvars (push_tvars (decl_ctx 0) params) os.binders in
  qkinds_wf 0 os.binders && check sg g os.arg KType && check sg g os.res KType

let rec ops_ok (sg: sig) (params: list kind) (ops: list (opname & op_sig))
  : Tot bool (decreases ops) =
  match ops with
  | [] -> true
  | (_, os) :: ops -> op_ok sg params os && ops_ok sg params ops

let rec op_names (ops: list (opname & op_sig)) : Tot (list opname) (decreases ops) =
  match ops with
  | [] -> []
  | (op, _) :: ops -> op :: op_names ops

let effect_ok (sg: sig) (ei: effect_info) : bool =
  qkinds_wf 0 ei.eff_params && L.noRepeats (op_names ei.eff_ops) &&
  ops_ok sg ei.eff_params ei.eff_ops

(** A type scheme `forall k̄. σ` with `n = |k̄|`. *)
let scheme_ok (sg: sig) (n: nat) (t: typ) : bool = check sg (decl_ctx n) t KType

(** * The signature *)

let tycons_wf (sg: sig) : prop =
  forall (q: qname). match sg.tycons q with Some ti -> tycon_ok ti | None -> True

let effects_wf (sg: sig) : prop =
  forall (q: qname). match sg.effects q with Some ei -> effect_ok sg ei | None -> True

let ctors_wf (sg: sig) : prop =
  forall (q: qname). match sg.ctors q with Some ci -> scheme_ok sg ci.ct_nk ci.ct_ty | None -> True

let foreigns_wf (sg: sig) : prop =
  forall (q: qname).
    match sg.foreigns q with Some fi -> scheme_ok sg fi.fr_nk fi.fr_ty | None -> True

let values_wf (sg: sig) : prop =
  forall (q: qname). match sg.values q with Some vi -> scheme_ok sg vi.vl_nk vi.vl_ty | None -> True

(** Every name is recorded in at most one of the value-level tables, so a
    global is a data constructor, a foreign, or a top-level value, and never
    two of them. *)
let globals_disjoint (sg: sig) : prop =
  forall (q: qname).
    (Some? (sg.ctors q) ==> None? (sg.foreigns q) /\ None? (sg.values q)) /\
    (Some? (sg.foreigns q) ==> None? (sg.values q))

let sig_wf (sg: sig) : prop =
  tycons_wf sg /\ effects_wf sg /\ ctors_wf sg /\ foreigns_wf sg /\ values_wf sg /\
  globals_disjoint sg

(** * The names of `Prim` *)

(** `Σ` records the type constructor `q` with no kind variable, the kind
    `k`, and the class `c`. *)
let prim_tycon (sg: sig) (q: qname) (k: kind) (c: tycon_class) : bool =
  match sg.tycons q with
  | Some ti -> ti.tc_nk = 0 && ti.tc_kind = k && ti.tc_class = c
  | None -> false

(** The intrinsic class `c` belongs to the type constructor `q0` alone, so
    that a function, record or variant type is an application of the one
    constructor the rules name. *)
let class_unique (sg: sig) (c: canon_class) (q0: qname) : prop =
  forall (q: qname).
    (match sg.tycons q with Some ti -> ti.tc_class = TcIntrinsic c | None -> false) ==> q == q0

(** `Σ` records each name of `Prim` with its kind and class:

      Function                           : Type -> Row Effect -> Type -> Type   function
      Record, Variant                    : Row Type -> Type                     record, variant
      Int, Number, String, Char, Boolean : Type                                 literal
      IO                                 : Type -> Type                         opaque
      Unit                               : Type                                 data

    none with a kind variable. `Unit`'s only constructor is `Prim.Unit :
    Unit`, of tag 0 and arity 0. The function, record and variant classes
    belong to `Function`, `Record` and `Variant` alone. *)
let prim_wf (sg: sig) : prop =
  prim_tycon sg prim_function (KArrow KType (KArrow (KRow EEffect) (KArrow KType KType)))
    (TcIntrinsic ClsFunction) /\
  prim_tycon sg prim_record (KArrow (KRow EType) KType) (TcIntrinsic ClsRecord) /\
  prim_tycon sg prim_variant (KArrow (KRow EType) KType) (TcIntrinsic ClsVariant) /\
  prim_tycon sg prim_int KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_number KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_string KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_char KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_boolean KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_io (KArrow KType KType) (TcIntrinsic ClsOpaque) /\
  prim_tycon sg prim_unit KType (TcData [prim_unit_ctor]) /\
  sg.ctors prim_unit_ctor ==
    Some ({ ct_owner = prim_unit; ct_tag = 0; ct_arity = 0; ct_nk = 0; ct_ty = t_unit }) /\
  class_unique sg ClsFunction prim_function /\
  class_unique sg ClsRecord prim_record /\
  class_unique sg ClsVariant prim_variant


(** * Data constructors against their data type *)

(** The argument kinds `κ̄` of `κ1 -> … -> κn -> κ`, `κ` not an arrow. *)
let rec arg_kinds (k: kind) : Tot (list kind) (decreases k) =
  match k with
  | KArrow k1 k2 -> k1 :: arg_kinds k2
  | _ -> []

(** `KVar i … KVar (i + n - 1)` *)
let rec kvars_from (i n: nat) : Tot (list kind) (decreases n) =
  if n = 0 then [] else KVar i :: kvars_from (i + 1) (n - 1)

(** The `n` kind variables of a kind scheme in written order,
    `KVar 0 … KVar (n - 1)`. *)
let kind_vars (n: nat) : list kind = kvars_from 0 n

(** The variables `a1 … an` of `forall (a1 : κ1) … (an : κn)`, seen inside
    it: `TVar (n - 1) … TVar 0`. *)
let rec type_vars (n: nat) : Tot (list typ) (decreases n) =
  if n = 0 then [] else TVar (n - 1) :: type_vars (n - 1)

(** `forall (a1 : κ1) … (an : κn). σ`, `ks` being `κ̄`. *)
let rec foralls (ks: list kind) (t: typ) : Tot typ (decreases ks) =
  match ks with
  | [] -> t
  | k :: ks -> TForall k (foralls ks t)

(** `τ1 -{()}-> … -{()}-> τn -{()}-> τ` *)
let rec pure_arrows (fs: list typ) (t: typ) : Tot typ (decreases fs) =
  match fs with
  | [] -> t
  | f :: fs -> t_fun f TRowEmpty (pure_arrows fs t)

(** The scheme `forall k̄. forall (ā : κ̄). τ̄ -{()}-> T [[k̄]] ā` of a
    constructor with the fields `τ̄` of the data type
    `T : forall k̄. κ̄ -> Type` (spec 05 §Join points and decision trees,
    `Ctor_i : forall ā. τ̄_i -> T ā`). The scheme has the `|k̄|` kind
    variables of `T`. *)
let ctor_scheme (q: qname) (ti: tycon_info) (fs: list typ) : typ =
  let ps = arg_kinds ti.tc_kind in
  foralls ps (pure_arrows fs (tapps (TCon q (kind_vars ti.tc_nk)) (type_vars (L.length ps))))

(** `σ` with its first `n` `forall`s removed. *)
let rec drop_foralls (n: nat) (t: typ) : Tot typ (decreases n) =
  if n = 0 then t
  else match t with
       | TForall _ b -> drop_foralls (n - 1) b
       | _ -> t

(** The domains of the leading pure arrows of a type. *)
let rec pure_domains (t: typ) : Tot (list typ) (decreases t) =
  match t with
  | TApp (TApp (TApp (TCon q []) t1) TRowEmpty) t2 ->
    if q = prim_function then t1 :: pure_domains t2 else []
  | _ -> []

(** The fields read off the type `σ` of a constructor of the data type
    `ti`: the domains of the pure arrows under the binders of `ti`'s
    parameters. `ctor_ok` requires `σ` to be the constructor scheme at
    these fields. *)
let ctor_decl_fields (ti: tycon_info) (t: typ) : list typ =
  pure_domains (drop_foralls (L.length (arg_kinds ti.tc_kind)) t)

(** The constructor `c` builds a value of its owner `T`, a data type that
    lists `c`. It has the kind variables of `T`, its type is `T`'s
    constructor scheme at its fields, and its arity is the number of its
    fields. *)
let ctor_ok (sg: sig) (c: qname) (ci: ctor_info) : bool =
  match sg.tycons ci.ct_owner with
  | Some ti ->
    (match ti.tc_class with
     | TcData cs ->
       let fs = ctor_decl_fields ti ci.ct_ty in
       L.mem c cs && ci.ct_nk = ti.tc_nk && ci.ct_ty = ctor_scheme ci.ct_owner ti fs &&
       ci.ct_arity = L.length fs
     | TcIntrinsic _ -> false)
  | None -> false

(** Every name of `cs` is a constructor whose owner is `q`. *)
let rec owned_by (sg: sig) (q: qname) (cs: list qname) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: cs ->
    (match sg.ctors c with Some ci -> ci.ct_owner = q | None -> false) && owned_by sg q cs

(** The tags of the constructors `cs`. *)
let rec ctor_tags (sg: sig) (cs: list qname) : Tot (list nat) (decreases cs) =
  match cs with
  | [] -> []
  | c :: cs -> (match sg.ctors c with Some ci -> ci.ct_tag | None -> 0) :: ctor_tags sg cs

(** The data type `q` lists constructors it owns, with distinct tags. *)
let data_ok (sg: sig) (q: qname) (cs: list qname) : bool =
  owned_by sg q cs && L.noRepeats (ctor_tags sg cs)

(** * Pure arrows (D23) *)

(** In the application `f a`, where `f` is `Function τ`, `a` is the arrow's
    row; it is pure when it is `()` up to type equality. *)
let arrow_row_pure (f a: typ) : bool =
  match f with
  | TApp (TCon q []) _ -> q <> prim_function || ty_eq a TRowEmpty
  | _ -> true

(** Every arrow of a type is pure, wherever it stands: in the domain or
    the result of an arrow, under a `forall`, in an argument of a type
    application, in the payload of a row element. A constraint carries no
    run-time content and is not looked into (D23). *)
let rec arrows_pure (t: typ) : Tot bool (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> true
  | TApp f a -> arrow_row_pure f a && arrows_pure f && arrows_pure a
  | TForall _ b | TConstr _ b -> arrows_pure b
  | TRowExt en r -> ent_arrows_pure en && arrows_pure r
  | TRowUnion a b -> arrows_pure a && arrows_pure b

and ent_arrows_pure (en: entry) : Tot bool (decreases en) =
  match en with
  | EntTy _ t -> arrows_pure t
  | EntEff _ _ ts -> tys_arrows_pure ts
  | EntRegion _ -> true

and tys_arrows_pure (ts: list typ) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | t :: ts -> arrows_pure t && tys_arrows_pure ts

(** * Constructors and foreigns in the signature *)

let ctors_ok (sg: sig) : prop =
  forall (c: qname). match sg.ctors c with Some ci -> ctor_ok sg c ci | None -> True

let datas_ok (sg: sig) : prop =
  forall (q: qname).
    match sg.tycons q with
    | Some ti -> (match ti.tc_class with TcData cs -> data_ok sg q cs | TcIntrinsic _ -> True)
    | None -> True

let foreigns_pure (sg: sig) : prop =
  forall (q: qname). match sg.foreigns q with Some fi -> arrows_pure fi.fr_ty | None -> True

let globals_ok (sg: sig) : prop = ctors_ok sg /\ datas_ok sg /\ foreigns_pure sg

(** * The assumption of the metatheory *)

let sig_ok (sg: sig) : prop = sig_wf sg /\ prim_wf sg /\ globals_ok sg

(** * Reading `globals_ok` *)

(** A name that a data type lists is a constructor owned by it. *)
val ctor_of_data (sg: sig) (q: qname) (ti: tycon_info) (cs: list qname) (c: qname)
  : Lemma (requires datas_ok sg /\ sg.tycons q == Some ti /\ ti.tc_class == TcData cs /\ L.mem c cs)
          (ensures Some? (sg.ctors c) /\ (Some?.v (sg.ctors c)).ct_owner == q)

(** Two constructors of one data type with the same tag are one. *)
val ctor_tags_distinct (sg: sig) (c1 c2: qname) (ci1 ci2: ctor_info)
  : Lemma (requires globals_ok sg /\ sg.ctors c1 == Some ci1 /\ sg.ctors c2 == Some ci2 /\
                    ci1.ct_owner == ci2.ct_owner /\ ci1.ct_tag == ci2.ct_tag)
          (ensures c1 == c2)
