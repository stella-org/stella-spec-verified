(**
 * Region names: the locally nameless operations
 * (design §1.3).
 *
 * A region name is either `RBound i`, the `i`-th enclosing `ERegion` binder
 * of the term, or `RFree a`, an atom. Types bind no region name, so every
 * operation on a type is a plain map or fold over the region references it
 * contains; on a term, the depth (the number of `ERegion` binders crossed)
 * is threaded through. `ERegion` binds a region name in its body only, not
 * in its layout and not in its initial values (spec 01 §Region names).
 *
 *   - `rmap_*`               map every region reference (`open`/`close`)
 *   - `lc_*_at n`            local closure: no `RBound` escapes `n` binders
 *   - `frn_*`                the atoms occurring free (spec 01 §Region names)
 *)
module Stella.Core.Region
open Stella.Core.Syntax
module L = FStar.List.Tot

(** List append, for the `frn_*` folds. *)
unfold let ( @ ) (#a: Type) (l1 l2: list a) : list a = L.append l1 l2

(** * Maps over region references

    `rmap_ty f t` applies `f` to every region reference of `t`. On a term,
    `rmap_exp f d e` applies `f d'` to a reference standing under `d' - d`
    `ERegion` binders of `e`. `ERegionOpen` binds nothing and its name is an
    atom, which no map touches. *)

let rmap_key (f: region_ref -> region_ref) (k: key) : key =
  match k with
  | RegionKey r -> RegionKey (f r)
  | _ -> k

let rec rmap_ty (f: region_ref -> region_ref) (t: typ) : Tot typ (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> t
  | TApp t1 t2 -> TApp (rmap_ty f t1) (rmap_ty f t2)
  | TForall k t -> TForall k (rmap_ty f t)
  | TConstr cn t -> TConstr (rmap_constr f cn) (rmap_ty f t)
  | TRowExt en t -> TRowExt (rmap_ent f en) (rmap_ty f t)
  | TRowUnion t1 t2 -> TRowUnion (rmap_ty f t1) (rmap_ty f t2)

and rmap_ent (f: region_ref -> region_ref) (en: entry) : Tot entry (decreases en) =
  match en with
  | EntTy k t -> EntTy (rmap_key f k) (rmap_ty f t)
  | EntEff s q ts -> EntEff s q (rmap_tys f ts)
  | EntRegion r -> EntRegion (f r)

and rmap_constr (f: region_ref -> region_ref) (cn: constr) : Tot constr (decreases cn) =
  match cn with
  | CLacks k t -> CLacks (rmap_key f k) (rmap_ty f t)
  | CDisj t1 t2 -> CDisj (rmap_ty f t1) (rmap_ty f t2)

and rmap_tys (f: region_ref -> region_ref) (ts: list typ) : Tot (list typ) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> rmap_ty f t :: rmap_tys f ts

and rmap_layout (f: region_ref -> region_ref) (l: list (key & typ))
  : Tot (list (key & typ)) (decreases l) =
  match l with
  | [] -> []
  | (k, t) :: l -> (rmap_key f k, rmap_ty f t) :: rmap_layout f l

let rec rmap_occ (f: region_ref -> region_ref) (o: occ) : Tot occ (decreases o) =
  match o with
  | OScrut _ -> o
  | OCtor o n j -> OCtor (rmap_occ f o) n j
  | ORecord o k -> ORecord (rmap_occ f o) (rmap_key f k)
  | OVariant o k -> OVariant (rmap_occ f o) (rmap_key f k)

(** `rmap_kbrs` is the map on the branches of a `switchKey`, whose labels
    are keys; `rmap_brs` leaves the labels of the other switches alone. *)
let rec rmap_exp (f: nat -> region_ref -> region_ref) (d: nat) (e: exp) : Tot exp (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EForce _ -> e
  | ELam t r b -> ELam (rmap_ty (f d) t) (rmap_ty (f d) r) (rmap_exp f d b)
  | EApp e1 e2 -> EApp (rmap_exp f d e1) (rmap_exp f d e2)
  | ETyLam k b -> ETyLam k (rmap_exp f d b)
  | ETyApp b t -> ETyApp (rmap_exp f d b) (rmap_ty (f d) t)
  | ECLam cn b -> ECLam (rmap_constr (f d) cn) (rmap_exp f d b)
  | ECApp b -> ECApp (rmap_exp f d b)
  | ELet t e1 e2 -> ELet (rmap_ty (f d) t) (rmap_exp f d e1) (rmap_exp f d e2)
  | ELetRec bs b -> ELetRec (rmap_binds f d bs) (rmap_exp f d b)
  | ECase es dt -> ECase (rmap_exps f d es) (rmap_dt f d dt)
  | ELetJoin ts t e1 e2 ->
    ELetJoin (rmap_tys (f d) ts) (rmap_ty (f d) t) (rmap_exp f d e1) (rmap_exp f d e2)
  | EJump j es -> EJump j (rmap_exps f d es)
  | EExtend k e1 e2 -> EExtend (rmap_key (f d) k) (rmap_exp f d e1) (rmap_exp f d e2)
  | ESelect k b -> ESelect (rmap_key (f d) k) (rmap_exp f d b)
  | ERestrict k b -> ERestrict (rmap_key (f d) k) (rmap_exp f d b)
  | EUpdate k e1 e2 -> EUpdate (rmap_key (f d) k) (rmap_exp f d e1) (rmap_exp f d e2)
  | EMerge e1 e2 -> EMerge (rmap_exp f d e1) (rmap_exp f d e2)
  | EInject k t b -> EInject (rmap_key (f d) k) (rmap_ty (f d) t) (rmap_exp f d b)
  | EWeaken k t b -> EWeaken (rmap_key (f d) k) (rmap_ty (f d) t) (rmap_exp f d b)
  | EAbsurd t b -> EAbsurd (rmap_ty (f d) t) (rmap_exp f d b)
  | EPerform k op ts b -> EPerform (rmap_key (f d) k) op (rmap_tys (f d) ts) (rmap_exp f d b)
  | EHandle b h ->
    EHandle (rmap_exp f d b)
      { h_ent = rmap_ent (f d) h.h_ent;
        h_ret_ty = rmap_ty (f d) h.h_ret_ty;
        h_ret = rmap_exp f d h.h_ret;
        h_clauses = rmap_cls f d h.h_clauses }
  | EOpenEff t b -> EOpenEff (rmap_ty (f d) t) (rmap_exp f d b)
  | ERegion l es b -> ERegion (rmap_layout (f d) l) (rmap_exps f d es) (rmap_exp f (d + 1) b)
  | EReadCell r k -> EReadCell (f d r) (rmap_key (f d) k)
  | EWriteCell r k b -> EWriteCell (f d r) (rmap_key (f d) k) (rmap_exp f d b)
  | EMatch th dt -> EMatch (rmap_exps f d th) (rmap_dt f d dt)
  | EOpenEffC t b -> EOpenEffC (rmap_ty (f d) t) (rmap_exp f d b)
  | EFill nu b -> EFill nu (rmap_exp f d b)
  | ERegionOpen ell th b -> ERegionOpen ell (rmap_cells f d th) (rmap_exp f d b)
  | EOpaque w t -> EOpaque w (rmap_ty (f d) t)

and rmap_exps (f: nat -> region_ref -> region_ref) (d: nat) (es: list exp)
  : Tot (list exp) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> rmap_exp f d e :: rmap_exps f d es

and rmap_binds (f: nat -> region_ref -> region_ref) (d: nat) (bs: list (typ & exp))
  : Tot (list (typ & exp)) (decreases bs) =
  match bs with
  | [] -> []
  | (t, e) :: bs -> (rmap_ty (f d) t, rmap_exp f d e) :: rmap_binds f d bs

and rmap_cells (f: nat -> region_ref -> region_ref) (d: nat) (th: list (key & exp))
  : Tot (list (key & exp)) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> (rmap_key (f d) k, rmap_exp f d e) :: rmap_cells f d th

and rmap_dt (f: nat -> region_ref -> region_ref) (d: nat) (dt: dtree) : Tot dtree (decreases dt) =
  match dt with
  | DLeaf e -> DLeaf (rmap_exp f d e)
  | DBind o dt -> DBind (rmap_occ (f d) o) (rmap_dt f d dt)
  | DSwitchCtor o bs df -> DSwitchCtor (rmap_occ (f d) o) (rmap_brs f d bs) (rmap_odt f d df)
  | DSwitchLit o bs df -> DSwitchLit (rmap_occ (f d) o) (rmap_brs f d bs) (rmap_dt f d df)
  | DSwitchKey o bs df -> DSwitchKey (rmap_occ (f d) o) (rmap_kbrs f d bs) (rmap_odt f d df)
  | DGuard e dt1 dt2 -> DGuard (rmap_exp f d e) (rmap_dt f d dt1) (rmap_dt f d dt2)

and rmap_odt (f: nat -> region_ref -> region_ref) (d: nat) (df: option dtree)
  : Tot (option dtree) (decreases df) =
  match df with
  | None -> None
  | Some dt -> Some (rmap_dt f d dt)

and rmap_brs (#lb: eqtype) (f: nat -> region_ref -> region_ref) (d: nat) (bs: list (lb & dtree))
  : Tot (list (lb & dtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (l, dt) :: bs -> (l, rmap_dt f d dt) :: rmap_brs f d bs

and rmap_kbrs (f: nat -> region_ref -> region_ref) (d: nat) (bs: list (key & dtree))
  : Tot (list (key & dtree)) (decreases bs) =
  match bs with
  | [] -> []
  | (k, dt) :: bs -> (rmap_key (f d) k, rmap_dt f d dt) :: rmap_kbrs f d bs

and rmap_cls (f: nat -> region_ref -> region_ref) (d: nat) (cs: list clause)
  : Tot (list clause) (decreases cs) =
  match cs with
  | [] -> []
  | CFull op nb s kt b :: cs ->
    CFull op nb (rmap_ty (f d) s) (rmap_ty (f d) kt) (rmap_exp f d b) :: rmap_cls f d cs
  | CFast op nb s b :: cs -> CFast op nb (rmap_ty (f d) s) (rmap_exp f d b) :: rmap_cls f d cs

val rmap_tys_length (f: region_ref -> region_ref) (l: list typ)
  : Lemma (ensures L.length (rmap_tys f l) == L.length l)
          [SMTPat (L.length (rmap_tys f l))]

val rmap_binds_length (f: nat -> region_ref -> region_ref) (d: nat) (l: list (typ & exp))
  : Lemma (ensures L.length (rmap_binds f d l) == L.length l)
          [SMTPat (L.length (rmap_binds f d l))]

(** * Open and close *)

(** The locally nameless `open` and `close` of one region reference at
    binder depth `d`. *)
let open_rr (a: atom) (d: nat) (r: region_ref) : region_ref =
  if r = RBound d then RFree a else r

let close_rr (a: atom) (d: nat) (r: region_ref) : region_ref =
  if r = RFree a then RBound d else r

(** On a type, at the depth `d` of the region binder being opened or
    closed. *)
let open_region_ty (d: nat) (a: atom) (t: typ) : typ = rmap_ty (open_rr a d) t

let close_region_ty (d: nat) (a: atom) (t: typ) : typ = rmap_ty (close_rr a d) t

(** `open_region_at d a e` replaces `RBound d` (counted from `e`'s root,
    i.e. `RBound (d + k)` under `k` further `ERegion` binders) by `RFree a`. *)
let open_region_at (d: nat) (a: atom) (e: exp) : exp = rmap_exp (open_rr a) d e

let close_region_at (d: nat) (a: atom) (e: exp) : exp = rmap_exp (close_rr a) d e

(** `e[ℓ := a]` for the body `e` of `region [ℓ] … in e` (spec 06 §Regions). *)
let open_region (a: atom) (e: exp) : exp = open_region_at 0 a e

(** Its inverse on bodies in which `a` does not occur
    (`Stella.Core.Region.Lemmas.close_open_region`). *)
let close_region (a: atom) (e: exp) : exp = close_region_at 0 a e

(** * Local closure

    `lc_*_at n x` holds when every `RBound i` of `x` refers to one of `n`
    enclosing `ERegion` binders, i.e. `i < n + k` under `k` further binders
    of `x` itself. `lc_* = lc_*_at 0`: no `RBound` dangles. A type contains
    `RBound` only while it stands in a term's region body, so the types met
    during typing, whose region bodies are opened with atoms first, are
    `lc_ty`. *)

let lc_rr (n: nat) (r: region_ref) : bool =
  match r with
  | RBound i -> i < n
  | RFree _ -> true

let lc_key (n: nat) (k: key) : bool =
  match k with
  | RegionKey r -> lc_rr n r
  | _ -> true

let rec lc_ty_at (n: nat) (t: typ) : Tot bool (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> true
  | TApp t1 t2 -> lc_ty_at n t1 && lc_ty_at n t2
  | TForall _ t -> lc_ty_at n t
  | TConstr cn t -> lc_constr_at n cn && lc_ty_at n t
  | TRowExt en t -> lc_ent_at n en && lc_ty_at n t
  | TRowUnion t1 t2 -> lc_ty_at n t1 && lc_ty_at n t2

and lc_ent_at (n: nat) (en: entry) : Tot bool (decreases en) =
  match en with
  | EntTy k t -> lc_key n k && lc_ty_at n t
  | EntEff _ _ ts -> lc_tys_at n ts
  | EntRegion r -> lc_rr n r

and lc_constr_at (n: nat) (cn: constr) : Tot bool (decreases cn) =
  match cn with
  | CLacks k t -> lc_key n k && lc_ty_at n t
  | CDisj t1 t2 -> lc_ty_at n t1 && lc_ty_at n t2

and lc_tys_at (n: nat) (ts: list typ) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | t :: ts -> lc_ty_at n t && lc_tys_at n ts

and lc_layout_at (n: nat) (l: list (key & typ)) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | (k, t) :: l -> lc_key n k && lc_ty_at n t && lc_layout_at n l

let lc_ty (t: typ) : bool = lc_ty_at 0 t

let rec lc_occ_at (n: nat) (o: occ) : Tot bool (decreases o) =
  match o with
  | OScrut _ -> true
  | OCtor o _ _ -> lc_occ_at n o
  | ORecord o k | OVariant o k -> lc_occ_at n o && lc_key n k

let rec lc_exp_at (n: nat) (e: exp) : Tot bool (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EForce _ -> true
  | ELam t r b -> lc_ty_at n t && lc_ty_at n r && lc_exp_at n b
  | EApp e1 e2 -> lc_exp_at n e1 && lc_exp_at n e2
  | ETyLam _ b -> lc_exp_at n b
  | ETyApp b t -> lc_exp_at n b && lc_ty_at n t
  | ECLam cn b -> lc_constr_at n cn && lc_exp_at n b
  | ECApp b -> lc_exp_at n b
  | ELet t e1 e2 -> lc_ty_at n t && lc_exp_at n e1 && lc_exp_at n e2
  | ELetRec bs b -> lc_binds_at n bs && lc_exp_at n b
  | ECase es dt -> lc_exps_at n es && lc_dt_at n dt
  | ELetJoin ts t e1 e2 -> lc_tys_at n ts && lc_ty_at n t && lc_exp_at n e1 && lc_exp_at n e2
  | EJump _ es -> lc_exps_at n es
  | EExtend k e1 e2 -> lc_key n k && lc_exp_at n e1 && lc_exp_at n e2
  | ESelect k b -> lc_key n k && lc_exp_at n b
  | ERestrict k b -> lc_key n k && lc_exp_at n b
  | EUpdate k e1 e2 -> lc_key n k && lc_exp_at n e1 && lc_exp_at n e2
  | EMerge e1 e2 -> lc_exp_at n e1 && lc_exp_at n e2
  | EInject k t b -> lc_key n k && lc_ty_at n t && lc_exp_at n b
  | EWeaken k t b -> lc_key n k && lc_ty_at n t && lc_exp_at n b
  | EAbsurd t b -> lc_ty_at n t && lc_exp_at n b
  | EPerform k _ ts b -> lc_key n k && lc_tys_at n ts && lc_exp_at n b
  | EHandle b h ->
    lc_exp_at n b && lc_ent_at n h.h_ent && lc_ty_at n h.h_ret_ty && lc_exp_at n h.h_ret &&
    lc_cls_at n h.h_clauses
  | EOpenEff t b -> lc_ty_at n t && lc_exp_at n b
  | ERegion l es b -> lc_layout_at n l && lc_exps_at n es && lc_exp_at (n + 1) b
  | EReadCell r k -> lc_rr n r && lc_key n k
  | EWriteCell r k b -> lc_rr n r && lc_key n k && lc_exp_at n b
  | EMatch th dt -> lc_exps_at n th && lc_dt_at n dt
  | EOpenEffC t b -> lc_ty_at n t && lc_exp_at n b
  | EFill _ b -> lc_exp_at n b
  | ERegionOpen _ th b -> lc_cells_at n th && lc_exp_at n b
  | EOpaque _ t -> lc_ty_at n t

and lc_exps_at (n: nat) (es: list exp) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> lc_exp_at n e && lc_exps_at n es

and lc_binds_at (n: nat) (bs: list (typ & exp)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (t, e) :: bs -> lc_ty_at n t && lc_exp_at n e && lc_binds_at n bs

and lc_cells_at (n: nat) (th: list (key & exp)) : Tot bool (decreases th) =
  match th with
  | [] -> true
  | (k, e) :: th -> lc_key n k && lc_exp_at n e && lc_cells_at n th

and lc_dt_at (n: nat) (dt: dtree) : Tot bool (decreases dt) =
  match dt with
  | DLeaf e -> lc_exp_at n e
  | DBind o dt -> lc_occ_at n o && lc_dt_at n dt
  | DSwitchCtor o bs df -> lc_occ_at n o && lc_brs_at n bs && lc_odt_at n df
  | DSwitchLit o bs df -> lc_occ_at n o && lc_brs_at n bs && lc_dt_at n df
  | DSwitchKey o bs df -> lc_occ_at n o && lc_kbrs_at n bs && lc_odt_at n df
  | DGuard e dt1 dt2 -> lc_exp_at n e && lc_dt_at n dt1 && lc_dt_at n dt2

and lc_odt_at (n: nat) (df: option dtree) : Tot bool (decreases df) =
  match df with
  | None -> true
  | Some dt -> lc_dt_at n dt

and lc_brs_at (#lb: eqtype) (n: nat) (bs: list (lb & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, dt) :: bs -> lc_dt_at n dt && lc_brs_at n bs

and lc_kbrs_at (n: nat) (bs: list (key & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (k, dt) :: bs -> lc_key n k && lc_dt_at n dt && lc_kbrs_at n bs

and lc_cls_at (n: nat) (cs: list clause) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | CFull _ _ s kt b :: cs -> lc_ty_at n s && lc_ty_at n kt && lc_exp_at n b && lc_cls_at n cs
  | CFast _ _ s b :: cs -> lc_ty_at n s && lc_exp_at n b && lc_cls_at n cs

let lc_exp (e: exp) : bool = lc_exp_at 0 e

(** * Free region names

    `frn_* x` lists the atoms occurring in `x` as region names (spec 01
    §Region names, `frn(τ)`), with repetitions. On a term it includes the
    name of every open region `region⟨ℓ⟩`. *)

let frn_rr (r: region_ref) : list atom =
  match r with
  | RFree a -> [a]
  | RBound _ -> []

let frn_key (k: key) : list atom =
  match k with
  | RegionKey r -> frn_rr r
  | _ -> []

let rec frn_ty (t: typ) : Tot (list atom) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> []
  | TApp t1 t2 -> frn_ty t1 @ frn_ty t2
  | TForall _ t -> frn_ty t
  | TConstr cn t -> frn_constr cn @ frn_ty t
  | TRowExt en t -> frn_ent en @ frn_ty t
  | TRowUnion t1 t2 -> frn_ty t1 @ frn_ty t2

and frn_ent (en: entry) : Tot (list atom) (decreases en) =
  match en with
  | EntTy k t -> frn_key k @ frn_ty t
  | EntEff _ _ ts -> frn_tys ts
  | EntRegion r -> frn_rr r

and frn_constr (cn: constr) : Tot (list atom) (decreases cn) =
  match cn with
  | CLacks k t -> frn_key k @ frn_ty t
  | CDisj t1 t2 -> frn_ty t1 @ frn_ty t2

and frn_tys (ts: list typ) : Tot (list atom) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> frn_ty t @ frn_tys ts

and frn_layout (l: list (key & typ)) : Tot (list atom) (decreases l) =
  match l with
  | [] -> []
  | (k, t) :: l -> frn_key k @ frn_ty t @ frn_layout l

let rec frn_occ (o: occ) : Tot (list atom) (decreases o) =
  match o with
  | OScrut _ -> []
  | OCtor o _ _ -> frn_occ o
  | ORecord o k | OVariant o k -> frn_occ o @ frn_key k

let rec frn_exp (e: exp) : Tot (list atom) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EForce _ -> []
  | ELam t r b -> frn_ty t @ frn_ty r @ frn_exp b
  | EApp e1 e2 -> frn_exp e1 @ frn_exp e2
  | ETyLam _ b -> frn_exp b
  | ETyApp b t -> frn_exp b @ frn_ty t
  | ECLam cn b -> frn_constr cn @ frn_exp b
  | ECApp b -> frn_exp b
  | ELet t e1 e2 -> frn_ty t @ frn_exp e1 @ frn_exp e2
  | ELetRec bs b -> frn_binds bs @ frn_exp b
  | ECase es dt -> frn_exps es @ frn_dt dt
  | ELetJoin ts t e1 e2 -> frn_tys ts @ frn_ty t @ frn_exp e1 @ frn_exp e2
  | EJump _ es -> frn_exps es
  | EExtend k e1 e2 -> frn_key k @ frn_exp e1 @ frn_exp e2
  | ESelect k b -> frn_key k @ frn_exp b
  | ERestrict k b -> frn_key k @ frn_exp b
  | EUpdate k e1 e2 -> frn_key k @ frn_exp e1 @ frn_exp e2
  | EMerge e1 e2 -> frn_exp e1 @ frn_exp e2
  | EInject k t b -> frn_key k @ frn_ty t @ frn_exp b
  | EWeaken k t b -> frn_key k @ frn_ty t @ frn_exp b
  | EAbsurd t b -> frn_ty t @ frn_exp b
  | EPerform k _ ts b -> frn_key k @ frn_tys ts @ frn_exp b
  | EHandle b h ->
    frn_exp b @ frn_ent h.h_ent @ frn_ty h.h_ret_ty @ frn_exp h.h_ret @ frn_cls h.h_clauses
  | EOpenEff t b -> frn_ty t @ frn_exp b
  | ERegion l es b -> frn_layout l @ frn_exps es @ frn_exp b
  | EReadCell r k -> frn_rr r @ frn_key k
  | EWriteCell r k b -> frn_rr r @ frn_key k @ frn_exp b
  | EMatch th dt -> frn_exps th @ frn_dt dt
  | EOpenEffC t b -> frn_ty t @ frn_exp b
  | EFill _ b -> frn_exp b
  | ERegionOpen ell th b -> [ell] @ frn_cells th @ frn_exp b
  | EOpaque _ t -> frn_ty t

and frn_exps (es: list exp) : Tot (list atom) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> frn_exp e @ frn_exps es

and frn_binds (bs: list (typ & exp)) : Tot (list atom) (decreases bs) =
  match bs with
  | [] -> []
  | (t, e) :: bs -> frn_ty t @ frn_exp e @ frn_binds bs

and frn_cells (th: list (key & exp)) : Tot (list atom) (decreases th) =
  match th with
  | [] -> []
  | (k, e) :: th -> frn_key k @ frn_exp e @ frn_cells th

and frn_dt (dt: dtree) : Tot (list atom) (decreases dt) =
  match dt with
  | DLeaf e -> frn_exp e
  | DBind o dt -> frn_occ o @ frn_dt dt
  | DSwitchCtor o bs df -> frn_occ o @ frn_brs bs @ frn_odt df
  | DSwitchLit o bs df -> frn_occ o @ frn_brs bs @ frn_dt df
  | DSwitchKey o bs df -> frn_occ o @ frn_kbrs bs @ frn_odt df
  | DGuard e dt1 dt2 -> frn_exp e @ frn_dt dt1 @ frn_dt dt2

and frn_odt (df: option dtree) : Tot (list atom) (decreases df) =
  match df with
  | None -> []
  | Some dt -> frn_dt dt

and frn_brs (#lb: eqtype) (bs: list (lb & dtree)) : Tot (list atom) (decreases bs) =
  match bs with
  | [] -> []
  | (_, dt) :: bs -> frn_dt dt @ frn_brs bs

and frn_kbrs (bs: list (key & dtree)) : Tot (list atom) (decreases bs) =
  match bs with
  | [] -> []
  | (k, dt) :: bs -> frn_key k @ frn_dt dt @ frn_kbrs bs

and frn_cls (cs: list clause) : Tot (list atom) (decreases cs) =
  match cs with
  | [] -> []
  | CFull _ _ s kt b :: cs -> frn_ty s @ frn_ty kt @ frn_exp b @ frn_cls cs
  | CFast _ _ s b :: cs -> frn_ty s @ frn_exp b @ frn_cls cs

(** Membership in an append, as an SMT pattern: freshness hypotheses
    `not (L.mem a (frn_* x))` then split along the structure of `x`. *)
val mem_append (a: atom) (l1 l2: list atom)
  : Lemma (L.mem a (l1 @ l2) = (L.mem a l1 || L.mem a l2)) [SMTPat (L.mem a (l1 @ l2))]
