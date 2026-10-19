(**
 * The free indices of a term, and their behaviour under region maps
 * (design §1).
 *
 * Each de Bruijn sort of a term has a predicate saying that its free
 * indices are below a bound, counted as `Stella.Core.Subst` counts the
 * binders of that sort:
 *
 *   - `tvs_below_exp n e`: every free type variable of `e` is below `n`.
 *     `Λ` and the `b̄` of a clause bind type variables; the types of `e` are
 *     read by `Stella.Core.Kinding.Facts.tvs_below`.
 *   - `vars_below_exp n e`: every free term variable of `e` is below `n`.
 *   - `jps_below_exp n e`: every free join index of `e` is below `n`. Only
 *     `letjoin` binds a join point, so this is the syntactic counterpart
 *     of `Stella.Core.Value.jp_scoped`, which also empties the join context
 *     at the bodies that discard `Δ`; a scoped term is below every bound at
 *     least its own (`jp_scoped_jps_below`).
 *
 * The region sort is locally nameless, and `Stella.Core.Region` has its
 * predicates, `lc_exp` and `frn_exp`. A region map changes no index of the
 * other sorts (`rmap_scope`). Opening a region body is invertible on local
 * closure (`lc_open_inv`) and keeps every free atom (`frn_open_incl`); a
 * typing rule that opens a body with an atom reads the scope of the body
 * itself back from these.
 *
 * A family over terms is a mutual induction over all term classes; the
 * interface exports its instances at `exp` and `dtree`.
 *)
module Stella.Core.Scope
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Kinding.Facts
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Type variables *)

let rec tvs_below_layout (n: nat) (l: list (key & typ)) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | (_, t) :: l -> tvs_below n t && tvs_below_layout n l

let rec tvs_below_exp (n: nat) (e: exp) : Tot bool (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> true
  | ELam t r b -> tvs_below n t && tvs_below n r && tvs_below_exp n b
  | EApp e1 e2 -> tvs_below_exp n e1 && tvs_below_exp n e2
  | ETyLam _ b -> tvs_below_exp (n + 1) b
  | ETyApp b t -> tvs_below_exp n b && tvs_below n t
  | ECLam cn b -> tvs_below_constr n cn && tvs_below_exp n b
  | ECApp b -> tvs_below_exp n b
  | ELet t e1 e2 -> tvs_below n t && tvs_below_exp n e1 && tvs_below_exp n e2
  | ELetRec bs b -> tvs_below_binds n bs && tvs_below_exp n b
  | ECase es dt -> tvs_below_exps n es && tvs_below_dt n dt
  | ELetJoin ts t e1 e2 ->
    tvs_below_tys n ts && tvs_below n t && tvs_below_exp n e1 && tvs_below_exp n e2
  | EJump _ es -> tvs_below_exps n es
  | EExtend _ e1 e2 -> tvs_below_exp n e1 && tvs_below_exp n e2
  | ESelect _ b -> tvs_below_exp n b
  | ERestrict _ b -> tvs_below_exp n b
  | EUpdate _ e1 e2 -> tvs_below_exp n e1 && tvs_below_exp n e2
  | EMerge e1 e2 -> tvs_below_exp n e1 && tvs_below_exp n e2
  | EInject _ t b -> tvs_below n t && tvs_below_exp n b
  | EWeaken _ t b -> tvs_below n t && tvs_below_exp n b
  | EAbsurd t b -> tvs_below n t && tvs_below_exp n b
  | EPerform _ _ ts b -> tvs_below_tys n ts && tvs_below_exp n b
  | EHandle b h ->
    tvs_below_exp n b && tvs_below_ent n h.h_ent && tvs_below n h.h_ret_ty &&
    tvs_below_exp n h.h_ret && tvs_below_cls n h.h_clauses
  | EOpenEff t b -> tvs_below n t && tvs_below_exp n b
  | ERegion l es b -> tvs_below_layout n l && tvs_below_exps n es && tvs_below_exp n b
  | EWriteCell _ _ b -> tvs_below_exp n b
  | EMatch th dt -> tvs_below_exps n th && tvs_below_dt n dt
  | EOpenEffC t b -> tvs_below n t && tvs_below_exp n b
  | EFill _ b -> tvs_below_exp n b
  | ERegionOpen _ th b -> tvs_below_cells n th && tvs_below_exp n b
  | EOpaque _ t -> tvs_below n t

and tvs_below_exps (n: nat) (es: list exp) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> tvs_below_exp n e && tvs_below_exps n es

and tvs_below_binds (n: nat) (bs: list (typ & exp)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (t, e) :: bs -> tvs_below n t && tvs_below_exp n e && tvs_below_binds n bs

and tvs_below_cells (n: nat) (th: list (key & exp)) : Tot bool (decreases th) =
  match th with
  | [] -> true
  | (_, e) :: th -> tvs_below_exp n e && tvs_below_cells n th

and tvs_below_dt (n: nat) (dt: dtree) : Tot bool (decreases dt) =
  match dt with
  | DLeaf e -> tvs_below_exp n e
  | DBind _ dt -> tvs_below_dt n dt
  | DSwitchCtor _ bs df -> tvs_below_brs n bs && tvs_below_odt n df
  | DSwitchLit _ bs df -> tvs_below_brs n bs && tvs_below_dt n df
  | DSwitchKey _ bs df -> tvs_below_brs n bs && tvs_below_odt n df
  | DGuard e dt1 dt2 -> tvs_below_exp n e && tvs_below_dt n dt1 && tvs_below_dt n dt2

and tvs_below_odt (n: nat) (df: option dtree) : Tot bool (decreases df) =
  match df with
  | None -> true
  | Some dt -> tvs_below_dt n dt

and tvs_below_brs (#lb: eqtype) (n: nat) (bs: list (lb & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, dt) :: bs -> tvs_below_dt n dt && tvs_below_brs n bs

and tvs_below_cls (n: nat) (cs: list clause) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | CFull _ nb s kt b :: cs ->
    tvs_below (n + nb) s && tvs_below (n + nb) kt && tvs_below_exp (n + nb) b && tvs_below_cls n cs
  | CFast _ nb s b :: cs -> tvs_below (n + nb) s && tvs_below_exp (n + nb) b && tvs_below_cls n cs

(** * Term variables *)

let rec vars_below_exp (n: nat) (e: exp) : Tot bool (decreases e) =
  match e with
  | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> true
  | EVar i -> i < n
  | ELam _ _ b -> vars_below_exp (n + 1) b
  | EApp e1 e2 -> vars_below_exp n e1 && vars_below_exp n e2
  | ETyLam _ b -> vars_below_exp n b
  | ETyApp b _ -> vars_below_exp n b
  | ECLam _ b -> vars_below_exp n b
  | ECApp b -> vars_below_exp n b
  | ELet _ e1 e2 -> vars_below_exp n e1 && vars_below_exp (n + 1) e2
  | ELetRec bs b -> vars_below_binds (n + L.length bs) bs && vars_below_exp (n + L.length bs) b
  | ECase es dt -> vars_below_exps n es && vars_below_dt n dt
  | ELetJoin ts _ e1 e2 -> vars_below_exp (n + L.length ts) e1 && vars_below_exp n e2
  | EJump _ es -> vars_below_exps n es
  | EExtend _ e1 e2 -> vars_below_exp n e1 && vars_below_exp n e2
  | ESelect _ b -> vars_below_exp n b
  | ERestrict _ b -> vars_below_exp n b
  | EUpdate _ e1 e2 -> vars_below_exp n e1 && vars_below_exp n e2
  | EMerge e1 e2 -> vars_below_exp n e1 && vars_below_exp n e2
  | EInject _ _ b -> vars_below_exp n b
  | EWeaken _ _ b -> vars_below_exp n b
  | EAbsurd _ b -> vars_below_exp n b
  | EPerform _ _ _ b -> vars_below_exp n b
  | EHandle b h ->
    vars_below_exp n b && vars_below_exp (n + 1) h.h_ret && vars_below_cls n h.h_clauses
  | EOpenEff _ b -> vars_below_exp n b
  | ERegion _ es b -> vars_below_exps n es && vars_below_exp n b
  | EWriteCell _ _ b -> vars_below_exp n b
  | EMatch th dt -> vars_below_exps n th && vars_below_dt n dt
  | EOpenEffC _ b -> vars_below_exp n b
  | EFill _ b -> vars_below_exp n b
  | ERegionOpen _ th b -> vars_below_cells n th && vars_below_exp n b

and vars_below_exps (n: nat) (es: list exp) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> vars_below_exp n e && vars_below_exps n es

and vars_below_binds (n: nat) (bs: list (typ & exp)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, e) :: bs -> vars_below_exp n e && vars_below_binds n bs

and vars_below_cells (n: nat) (th: list (key & exp)) : Tot bool (decreases th) =
  match th with
  | [] -> true
  | (_, e) :: th -> vars_below_exp n e && vars_below_cells n th

and vars_below_dt (n: nat) (dt: dtree) : Tot bool (decreases dt) =
  match dt with
  | DLeaf e -> vars_below_exp n e
  | DBind _ dt -> vars_below_dt (n + 1) dt
  | DSwitchCtor _ bs df -> vars_below_brs n bs && vars_below_odt n df
  | DSwitchLit _ bs df -> vars_below_brs n bs && vars_below_dt n df
  | DSwitchKey _ bs df -> vars_below_brs n bs && vars_below_odt n df
  | DGuard e dt1 dt2 -> vars_below_exp n e && vars_below_dt n dt1 && vars_below_dt n dt2

and vars_below_odt (n: nat) (df: option dtree) : Tot bool (decreases df) =
  match df with
  | None -> true
  | Some dt -> vars_below_dt n dt

and vars_below_brs (#lb: eqtype) (n: nat) (bs: list (lb & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, dt) :: bs -> vars_below_dt n dt && vars_below_brs n bs

and vars_below_cls (n: nat) (cs: list clause) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | CFull _ _ _ _ b :: cs -> vars_below_exp (n + 2) b && vars_below_cls n cs
  | CFast _ _ _ b :: cs -> vars_below_exp (n + 1) b && vars_below_cls n cs

(** * Join points *)

let rec jps_below_exp (n: nat) (e: exp) : Tot bool (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> true
  | ELam _ _ b -> jps_below_exp n b
  | EApp e1 e2 -> jps_below_exp n e1 && jps_below_exp n e2
  | ETyLam _ b -> jps_below_exp n b
  | ETyApp b _ -> jps_below_exp n b
  | ECLam _ b -> jps_below_exp n b
  | ECApp b -> jps_below_exp n b
  | ELet _ e1 e2 -> jps_below_exp n e1 && jps_below_exp n e2
  | ELetRec bs b -> jps_below_binds n bs && jps_below_exp n b
  | ECase es dt -> jps_below_exps n es && jps_below_dt n dt
  | ELetJoin _ _ e1 e2 -> jps_below_exp (n + 1) e1 && jps_below_exp (n + 1) e2
  | EJump j es -> j < n && jps_below_exps n es
  | EExtend _ e1 e2 -> jps_below_exp n e1 && jps_below_exp n e2
  | ESelect _ b -> jps_below_exp n b
  | ERestrict _ b -> jps_below_exp n b
  | EUpdate _ e1 e2 -> jps_below_exp n e1 && jps_below_exp n e2
  | EMerge e1 e2 -> jps_below_exp n e1 && jps_below_exp n e2
  | EInject _ _ b -> jps_below_exp n b
  | EWeaken _ _ b -> jps_below_exp n b
  | EAbsurd _ b -> jps_below_exp n b
  | EPerform _ _ _ b -> jps_below_exp n b
  | EHandle b h -> jps_below_exp n b && jps_below_exp n h.h_ret && jps_below_cls n h.h_clauses
  | EOpenEff _ b -> jps_below_exp n b
  | ERegion _ es b -> jps_below_exps n es && jps_below_exp n b
  | EWriteCell _ _ b -> jps_below_exp n b
  | EMatch th dt -> jps_below_exps n th && jps_below_dt n dt
  | EOpenEffC _ b -> jps_below_exp n b
  | EFill _ b -> jps_below_exp n b
  | ERegionOpen _ th b -> jps_below_cells n th && jps_below_exp n b

and jps_below_exps (n: nat) (es: list exp) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> jps_below_exp n e && jps_below_exps n es

and jps_below_binds (n: nat) (bs: list (typ & exp)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, e) :: bs -> jps_below_exp n e && jps_below_binds n bs

and jps_below_cells (n: nat) (th: list (key & exp)) : Tot bool (decreases th) =
  match th with
  | [] -> true
  | (_, e) :: th -> jps_below_exp n e && jps_below_cells n th

and jps_below_dt (n: nat) (dt: dtree) : Tot bool (decreases dt) =
  match dt with
  | DLeaf e -> jps_below_exp n e
  | DBind _ dt -> jps_below_dt n dt
  | DSwitchCtor _ bs df -> jps_below_brs n bs && jps_below_odt n df
  | DSwitchLit _ bs df -> jps_below_brs n bs && jps_below_dt n df
  | DSwitchKey _ bs df -> jps_below_brs n bs && jps_below_odt n df
  | DGuard e dt1 dt2 -> jps_below_exp n e && jps_below_dt n dt1 && jps_below_dt n dt2

and jps_below_odt (n: nat) (df: option dtree) : Tot bool (decreases df) =
  match df with
  | None -> true
  | Some dt -> jps_below_dt n dt

and jps_below_brs (#lb: eqtype) (n: nat) (bs: list (lb & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | (_, dt) :: bs -> jps_below_dt n dt && jps_below_brs n bs

and jps_below_cls (n: nat) (cs: list clause) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | CFull _ _ _ _ b :: cs -> jps_below_exp n b && jps_below_cls n cs
  | CFast _ _ _ b :: cs -> jps_below_exp n b && jps_below_cls n cs

(** A term scoped under `n` join points has its free join indices below
    every `m >= n`: a body that discards `Δ` has none. *)
val jp_scoped_jps_below (n m: nat) (e: exp)
  : Lemma (requires n <= m /\ V.jp_scoped n e) (ensures jps_below_exp m e)

val jp_scoped_jps_below_dt (n m: nat) (dt: dtree)
  : Lemma (requires n <= m /\ V.jp_scoped_dt n dt) (ensures jps_below_dt m dt)

(** * Region maps *)

(** A region map changes no index of the other sorts. *)
val rmap_scope (f: nat -> region_ref -> region_ref) (d nt nv nj: nat) (e: exp)
  : Lemma (tvs_below_exp nt (rmap_exp f d e) == tvs_below_exp nt e /\
           vars_below_exp nv (rmap_exp f d e) == vars_below_exp nv e /\
           V.jp_scoped nj (rmap_exp f d e) == V.jp_scoped nj e)

val rmap_scope_dt (f: nat -> region_ref -> region_ref) (d nt nv nj: nat) (dt: dtree)
  : Lemma (tvs_below_dt nt (rmap_dt f d dt) == tvs_below_dt nt dt /\
           vars_below_dt nv (rmap_dt f d dt) == vars_below_dt nv dt /\
           V.jp_scoped_dt nj (rmap_dt f d dt) == V.jp_scoped_dt nj dt)

(** A body that is locally closed once opened at its binder is locally
    closed under that binder. *)
val lc_open_inv (a: atom) (d: nat) (e: exp)
  : Lemma (requires lc_exp_at d (rmap_exp (open_rr a) d e)) (ensures lc_exp_at (d + 1) e)

val lc_open_inv_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires lc_dt_at d (rmap_dt (open_rr a) d dt)) (ensures lc_dt_at (d + 1) dt)

(** Opening keeps every free atom. *)
val frn_open_incl (a: atom) (d: nat) (e: exp) (b: atom)
  : Lemma (requires L.mem b (frn_exp e)) (ensures L.mem b (frn_exp (rmap_exp (open_rr a) d e)))

val frn_open_incl_dt (a: atom) (d: nat) (dt: dtree) (b: atom)
  : Lemma (requires L.mem b (frn_dt dt)) (ensures L.mem b (frn_dt (rmap_dt (open_rr a) d dt)))

(** * Fresh atoms *)

(** An atom outside a finite list. *)
val fresh_atom (l: list atom) : a:atom{~(L.mem a l)}
