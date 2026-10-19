(* Proof structure.

   Every family is one mutual induction over the term classes, preceded by
   its instance over the type classes. A region map rewrites region
   references alone, so the type-variable, term-variable and join-point
   predicates of the image are those of the term (`rmap_scope`, one
   induction carrying the three bounds, each adjusted at the binders of
   its sort).

   Opening at depth `d` replaces `RBound d` only, which is below `d + 1`;
   every other reference is unchanged, so local closure at `d` of the image
   is local closure at `d + 1` of the term. It replaces no atom, so every
   free atom survives; the membership facts are stated as implications
   inside, so that each case calls the lemma of every component. *)
module Stella.Core.Scope
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Kinding.Facts
module L = FStar.List.Tot
module V = Stella.Core.Value

(* Join points. *)

let rec jp_scoped_jps_below n m e
  : Lemma (requires n <= m /\ V.jp_scoped n e) (ensures jps_below_exp m e) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> jp_scoped_jps_below 0 m b
  | EApp e1 e2 -> jp_scoped_jps_below n m e1; jp_scoped_jps_below n m e2
  | ETyLam _ b -> jp_scoped_jps_below 0 m b
  | ETyApp b _ -> jp_scoped_jps_below n m b
  | ECLam _ b -> jp_scoped_jps_below 0 m b
  | ECApp b -> jp_scoped_jps_below n m b
  | ELet _ e1 e2 -> jp_scoped_jps_below n m e1; jp_scoped_jps_below n m e2
  | ELetRec bs b -> jps_binds 0 m bs; jp_scoped_jps_below n m b
  | ECase es dt -> jps_exps n m es; jp_scoped_jps_below_dt n m dt
  | ELetJoin _ _ e1 e2 ->
    jp_scoped_jps_below (n + 1) (m + 1) e1; jp_scoped_jps_below (n + 1) (m + 1) e2
  | EJump _ es -> jps_exps n m es
  | EExtend _ e1 e2 -> jp_scoped_jps_below n m e1; jp_scoped_jps_below n m e2
  | ESelect _ b -> jp_scoped_jps_below n m b
  | ERestrict _ b -> jp_scoped_jps_below n m b
  | EUpdate _ e1 e2 -> jp_scoped_jps_below n m e1; jp_scoped_jps_below n m e2
  | EMerge e1 e2 -> jp_scoped_jps_below n m e1; jp_scoped_jps_below n m e2
  | EInject _ _ b -> jp_scoped_jps_below n m b
  | EWeaken _ _ b -> jp_scoped_jps_below n m b
  | EAbsurd _ b -> jp_scoped_jps_below n m b
  | EPerform _ _ _ b -> jp_scoped_jps_below n m b
  | EHandle b h ->
    jp_scoped_jps_below 0 m b; jp_scoped_jps_below 0 m h.h_ret; jps_cls 0 m h.h_clauses
  | EOpenEff _ b -> jp_scoped_jps_below n m b
  | ERegion _ es b -> jps_exps n m es; jp_scoped_jps_below 0 m b
  | EWriteCell _ _ b -> jp_scoped_jps_below n m b
  | EMatch th dt -> jps_exps n m th; jp_scoped_jps_below_dt n m dt
  | EOpenEffC _ b -> jp_scoped_jps_below n m b
  | EFill _ b -> jp_scoped_jps_below 0 m b
  | ERegionOpen _ th b -> jps_cells 0 m th; jp_scoped_jps_below 0 m b

and jps_exps (n m: nat) (es: list exp)
  : Lemma (requires n <= m /\ V.jp_scoped_exps n es) (ensures jps_below_exps m es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> jp_scoped_jps_below n m e; jps_exps n m es

and jps_binds (n m: nat) (bs: list (typ & exp))
  : Lemma (requires n <= m /\ V.jp_scoped_binds n bs) (ensures jps_below_binds m bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> jp_scoped_jps_below n m (snd p_); jps_binds n m bs

and jps_cells (n m: nat) (th: list (key & exp))
  : Lemma (requires n <= m /\ V.jp_scoped_cells n th) (ensures jps_below_cells m th)
          (decreases th) =
  match th with
  | [] -> ()
  | p_ :: th -> jp_scoped_jps_below n m (snd p_); jps_cells n m th

and jp_scoped_jps_below_dt n m dt
  : Lemma (requires n <= m /\ V.jp_scoped_dt n dt) (ensures jps_below_dt m dt) (decreases dt) =
  match dt with
  | DLeaf e -> jp_scoped_jps_below n m e
  | DBind _ dt -> jp_scoped_jps_below_dt n m dt
  | DSwitchCtor _ bs df -> jps_brs n m bs; jps_odt n m df
  | DSwitchLit _ bs df -> jps_brs n m bs; jp_scoped_jps_below_dt n m df
  | DSwitchKey _ bs df -> jps_brs n m bs; jps_odt n m df
  | DGuard e dt1 dt2 ->
    jp_scoped_jps_below n m e; jp_scoped_jps_below_dt n m dt1; jp_scoped_jps_below_dt n m dt2

and jps_odt (n m: nat) (df: option dtree)
  : Lemma (requires n <= m /\ V.jp_scoped_odt n df) (ensures jps_below_odt m df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> jp_scoped_jps_below_dt n m dt

and jps_brs (#lb: eqtype) (n m: nat) (bs: list (lb & dtree))
  : Lemma (requires n <= m /\ V.jp_scoped_brs n bs) (ensures jps_below_brs m bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> jp_scoped_jps_below_dt n m (snd p_); jps_brs n m bs

and jps_cls (n m: nat) (cs: list clause)
  : Lemma (requires n <= m /\ V.jp_scoped_cls n cs) (ensures jps_below_cls m cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> jp_scoped_jps_below n m b; jps_cls n m cs
  | CFast _ _ _ b :: cs -> jp_scoped_jps_below n m b; jps_cls n m cs

(* Region maps: types. *)

let rec tvs_rmap_ty (f: region_ref -> region_ref) (n: nat) (t: typ)
  : Lemma (ensures tvs_below n (rmap_ty f t) == tvs_below n t) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> tvs_rmap_ty f n t1; tvs_rmap_ty f n t2
  | TForall _ b -> tvs_rmap_ty f (n + 1) b
  | TConstr c b -> tvs_rmap_constr f n c; tvs_rmap_ty f n b
  | TRowExt en r -> tvs_rmap_ent f n en; tvs_rmap_ty f n r

and tvs_rmap_ent (f: region_ref -> region_ref) (n: nat) (en: entry)
  : Lemma (ensures tvs_below_ent n (rmap_ent f en) == tvs_below_ent n en) (decreases en) =
  match en with
  | EntTy _ t -> tvs_rmap_ty f n t
  | EntEff _ _ ts -> tvs_rmap_tys f n ts
  | EntRegion _ -> ()

and tvs_rmap_constr (f: region_ref -> region_ref) (n: nat) (c: constr)
  : Lemma (ensures tvs_below_constr n (rmap_constr f c) == tvs_below_constr n c) (decreases c) =
  match c with
  | CLacks _ t -> tvs_rmap_ty f n t
  | CDisj t1 t2 -> tvs_rmap_ty f n t1; tvs_rmap_ty f n t2

and tvs_rmap_tys (f: region_ref -> region_ref) (n: nat) (ts: list typ)
  : Lemma (ensures tvs_below_tys n (rmap_tys f ts) == tvs_below_tys n ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> tvs_rmap_ty f n t; tvs_rmap_tys f n ts

let rec tvs_rmap_layout (f: region_ref -> region_ref) (n: nat) (l: list (key & typ))
  : Lemma (ensures tvs_below_layout n (rmap_layout f l) == tvs_below_layout n l) (decreases l) =
  match l with
  | [] -> ()
  | p_ :: l -> tvs_rmap_ty f n (snd p_); tvs_rmap_layout f n l

(* Region maps: terms. *)

let rec rmap_scope f d nt nv nj e
  : Lemma (ensures tvs_below_exp nt (rmap_exp f d e) == tvs_below_exp nt e /\
                   vars_below_exp nv (rmap_exp f d e) == vars_below_exp nv e /\
                   V.jp_scoped nj (rmap_exp f d e) == V.jp_scoped nj e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EForce _ | EReadCell _ _ -> ()
  | ELam t r b -> tvs_rmap_ty (f d) nt t; tvs_rmap_ty (f d) nt r; rmap_scope f d nt (nv + 1) 0 b
  | EApp e1 e2 -> rmap_scope f d nt nv nj e1; rmap_scope f d nt nv nj e2
  | ETyLam _ b -> rmap_scope f d (nt + 1) nv 0 b
  | ETyApp b t -> rmap_scope f d nt nv nj b; tvs_rmap_ty (f d) nt t
  | ECLam c b -> tvs_rmap_constr (f d) nt c; rmap_scope f d nt nv 0 b
  | ECApp b -> rmap_scope f d nt nv nj b
  | ELet t e1 e2 ->
    tvs_rmap_ty (f d) nt t; rmap_scope f d nt nv nj e1; rmap_scope f d nt (nv + 1) nj e2
  | ELetRec bs b ->
    rmap_scope_binds f d nt (nv + L.length bs) 0 bs; rmap_scope f d nt (nv + L.length bs) nj b
  | ECase es dt -> rmap_scope_exps f d nt nv nj es; rmap_scope_dt f d nt nv nj dt
  | ELetJoin ts t e1 e2 ->
    tvs_rmap_tys (f d) nt ts; tvs_rmap_ty (f d) nt t;
    rmap_scope f d nt (nv + L.length ts) (nj + 1) e1; rmap_scope f d nt nv (nj + 1) e2
  | EJump _ es -> rmap_scope_exps f d nt nv nj es
  | EExtend _ e1 e2 -> rmap_scope f d nt nv nj e1; rmap_scope f d nt nv nj e2
  | ESelect _ b -> rmap_scope f d nt nv nj b
  | ERestrict _ b -> rmap_scope f d nt nv nj b
  | EUpdate _ e1 e2 -> rmap_scope f d nt nv nj e1; rmap_scope f d nt nv nj e2
  | EMerge e1 e2 -> rmap_scope f d nt nv nj e1; rmap_scope f d nt nv nj e2
  | EInject _ t b -> tvs_rmap_ty (f d) nt t; rmap_scope f d nt nv nj b
  | EWeaken _ t b -> tvs_rmap_ty (f d) nt t; rmap_scope f d nt nv nj b
  | EAbsurd t b -> tvs_rmap_ty (f d) nt t; rmap_scope f d nt nv nj b
  | EPerform _ _ ts b -> tvs_rmap_tys (f d) nt ts; rmap_scope f d nt nv nj b
  | EHandle b h ->
    rmap_scope f d nt nv 0 b;
    tvs_rmap_ent (f d) nt h.h_ent;
    tvs_rmap_ty (f d) nt h.h_ret_ty;
    rmap_scope f d nt (nv + 1) 0 h.h_ret;
    rmap_scope_cls f d nt nv 0 h.h_clauses
  | EOpenEff t b -> tvs_rmap_ty (f d) nt t; rmap_scope f d nt nv nj b
  | ERegion l es b ->
    tvs_rmap_layout (f d) nt l; rmap_scope_exps f d nt nv nj es; rmap_scope f (d + 1) nt nv 0 b
  | EWriteCell _ _ b -> rmap_scope f d nt nv nj b
  | EMatch th dt -> rmap_scope_exps f d nt nv nj th; rmap_scope_dt f d nt nv nj dt
  | EOpenEffC t b -> tvs_rmap_ty (f d) nt t; rmap_scope f d nt nv nj b
  | EFill _ b -> rmap_scope f d nt nv 0 b
  | ERegionOpen _ th b -> rmap_scope_cells f d nt nv 0 th; rmap_scope f d nt nv 0 b
  | EOpaque _ t -> tvs_rmap_ty (f d) nt t

and rmap_scope_exps (f: nat -> region_ref -> region_ref) (d nt nv nj: nat) (es: list exp)
  : Lemma (ensures tvs_below_exps nt (rmap_exps f d es) == tvs_below_exps nt es /\
                   vars_below_exps nv (rmap_exps f d es) == vars_below_exps nv es /\
                   V.jp_scoped_exps nj (rmap_exps f d es) == V.jp_scoped_exps nj es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> rmap_scope f d nt nv nj e; rmap_scope_exps f d nt nv nj es

and rmap_scope_binds (f: nat -> region_ref -> region_ref) (d nt nv nj: nat) (bs: list (typ & exp))
  : Lemma (ensures tvs_below_binds nt (rmap_binds f d bs) == tvs_below_binds nt bs /\
                   vars_below_binds nv (rmap_binds f d bs) == vars_below_binds nv bs /\
                   V.jp_scoped_binds nj (rmap_binds f d bs) == V.jp_scoped_binds nj bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> tvs_rmap_ty (f d) nt (fst p_); rmap_scope f d nt nv nj (snd p_); rmap_scope_binds f d nt nv nj bs

and rmap_scope_cells (f: nat -> region_ref -> region_ref) (d nt nv nj: nat) (th: list (key & exp))
  : Lemma (ensures tvs_below_cells nt (rmap_cells f d th) == tvs_below_cells nt th /\
                   vars_below_cells nv (rmap_cells f d th) == vars_below_cells nv th /\
                   V.jp_scoped_cells nj (rmap_cells f d th) == V.jp_scoped_cells nj th)
          (decreases th) =
  match th with
  | [] -> ()
  | p_ :: th -> rmap_scope f d nt nv nj (snd p_); rmap_scope_cells f d nt nv nj th

and rmap_scope_dt f d nt nv nj dt
  : Lemma (ensures tvs_below_dt nt (rmap_dt f d dt) == tvs_below_dt nt dt /\
                   vars_below_dt nv (rmap_dt f d dt) == vars_below_dt nv dt /\
                   V.jp_scoped_dt nj (rmap_dt f d dt) == V.jp_scoped_dt nj dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> rmap_scope f d nt nv nj e
  | DBind _ dt -> rmap_scope_dt f d nt (nv + 1) nj dt
  | DSwitchCtor _ bs df -> rmap_scope_brs f d nt nv nj bs; rmap_scope_odt f d nt nv nj df
  | DSwitchLit _ bs df -> rmap_scope_brs f d nt nv nj bs; rmap_scope_dt f d nt nv nj df
  | DSwitchKey _ bs df -> rmap_scope_kbrs f d nt nv nj bs; rmap_scope_odt f d nt nv nj df
  | DGuard e dt1 dt2 ->
    rmap_scope f d nt nv nj e; rmap_scope_dt f d nt nv nj dt1; rmap_scope_dt f d nt nv nj dt2

and rmap_scope_odt (f: nat -> region_ref -> region_ref) (d nt nv nj: nat) (df: option dtree)
  : Lemma (ensures tvs_below_odt nt (rmap_odt f d df) == tvs_below_odt nt df /\
                   vars_below_odt nv (rmap_odt f d df) == vars_below_odt nv df /\
                   V.jp_scoped_odt nj (rmap_odt f d df) == V.jp_scoped_odt nj df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> rmap_scope_dt f d nt nv nj dt

and rmap_scope_brs (#lb: eqtype) (f: nat -> region_ref -> region_ref) (d nt nv nj: nat)
  (bs: list (lb & dtree))
  : Lemma (ensures tvs_below_brs nt (rmap_brs f d bs) == tvs_below_brs nt bs /\
                   vars_below_brs nv (rmap_brs f d bs) == vars_below_brs nv bs /\
                   V.jp_scoped_brs nj (rmap_brs f d bs) == V.jp_scoped_brs nj bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> rmap_scope_dt f d nt nv nj (snd p_); rmap_scope_brs f d nt nv nj bs

and rmap_scope_kbrs (f: nat -> region_ref -> region_ref) (d nt nv nj: nat) (bs: list (key & dtree))
  : Lemma (ensures tvs_below_brs nt (rmap_kbrs f d bs) == tvs_below_brs nt bs /\
                   vars_below_brs nv (rmap_kbrs f d bs) == vars_below_brs nv bs /\
                   V.jp_scoped_brs nj (rmap_kbrs f d bs) == V.jp_scoped_brs nj bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> rmap_scope_dt f d nt nv nj (snd p_); rmap_scope_kbrs f d nt nv nj bs

and rmap_scope_cls (f: nat -> region_ref -> region_ref) (d nt nv nj: nat) (cs: list clause)
  : Lemma (ensures tvs_below_cls nt (rmap_cls f d cs) == tvs_below_cls nt cs /\
                   vars_below_cls nv (rmap_cls f d cs) == vars_below_cls nv cs /\
                   V.jp_scoped_cls nj (rmap_cls f d cs) == V.jp_scoped_cls nj cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb s kt b :: cs ->
    tvs_rmap_ty (f d) (nt + nb) s; tvs_rmap_ty (f d) (nt + nb) kt;
    rmap_scope f d (nt + nb) (nv + 2) nj b; rmap_scope_cls f d nt nv nj cs
  | CFast _ nb s b :: cs ->
    tvs_rmap_ty (f d) (nt + nb) s;
    rmap_scope f d (nt + nb) (nv + 1) nj b; rmap_scope_cls f d nt nv nj cs

(* Opening and local closure: types. *)

let lc_open_rr_inv (a: atom) (m: nat) (r: region_ref)
  : Lemma (requires lc_rr m (open_rr a m r)) (ensures lc_rr (m + 1) r) = ()

let lc_open_key_inv (a: atom) (m: nat) (k: key)
  : Lemma (requires lc_key m (rmap_key (open_rr a m) k)) (ensures lc_key (m + 1) k) = ()

let rec lc_open_ty_inv (a: atom) (m: nat) (t: typ)
  : Lemma (requires lc_ty_at m (rmap_ty (open_rr a m) t)) (ensures lc_ty_at (m + 1) t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> lc_open_ty_inv a m t1; lc_open_ty_inv a m t2
  | TForall _ b -> lc_open_ty_inv a m b
  | TConstr c b -> lc_open_constr_inv a m c; lc_open_ty_inv a m b
  | TRowExt en r -> lc_open_ent_inv a m en; lc_open_ty_inv a m r

and lc_open_ent_inv (a: atom) (m: nat) (en: entry)
  : Lemma (requires lc_ent_at m (rmap_ent (open_rr a m) en)) (ensures lc_ent_at (m + 1) en)
          (decreases en) =
  match en with
  | EntTy k t -> lc_open_key_inv a m k; lc_open_ty_inv a m t
  | EntEff _ _ ts -> lc_open_tys_inv a m ts
  | EntRegion r -> lc_open_rr_inv a m r

and lc_open_constr_inv (a: atom) (m: nat) (c: constr)
  : Lemma (requires lc_constr_at m (rmap_constr (open_rr a m) c))
          (ensures lc_constr_at (m + 1) c) (decreases c) =
  match c with
  | CLacks k t -> lc_open_key_inv a m k; lc_open_ty_inv a m t
  | CDisj t1 t2 -> lc_open_ty_inv a m t1; lc_open_ty_inv a m t2

and lc_open_tys_inv (a: atom) (m: nat) (ts: list typ)
  : Lemma (requires lc_tys_at m (rmap_tys (open_rr a m) ts)) (ensures lc_tys_at (m + 1) ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> lc_open_ty_inv a m t; lc_open_tys_inv a m ts

let rec lc_open_layout_inv (a: atom) (m: nat) (l: list (key & typ))
  : Lemma (requires lc_layout_at m (rmap_layout (open_rr a m) l))
          (ensures lc_layout_at (m + 1) l) (decreases l) =
  match l with
  | [] -> ()
  | p_ :: l -> lc_open_key_inv a m (fst p_); lc_open_ty_inv a m (snd p_); lc_open_layout_inv a m l

let rec lc_open_occ_inv (a: atom) (m: nat) (o: occ)
  : Lemma (requires lc_occ_at m (rmap_occ (open_rr a m) o)) (ensures lc_occ_at (m + 1) o)
          (decreases o) =
  match o with
  | OScrut _ -> ()
  | OCtor o _ _ -> lc_open_occ_inv a m o
  | ORecord o k | OVariant o k -> lc_open_occ_inv a m o; lc_open_key_inv a m k

(* Opening and local closure: terms. *)

let rec lc_open_inv a d e
  : Lemma (requires lc_exp_at d (rmap_exp (open_rr a) d e)) (ensures lc_exp_at (d + 1) e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EForce _ -> ()
  | ELam t r b -> lc_open_ty_inv a d t; lc_open_ty_inv a d r; lc_open_inv a d b
  | EApp e1 e2 -> lc_open_inv a d e1; lc_open_inv a d e2
  | ETyLam _ b -> lc_open_inv a d b
  | ETyApp b t -> lc_open_inv a d b; lc_open_ty_inv a d t
  | ECLam c b -> lc_open_constr_inv a d c; lc_open_inv a d b
  | ECApp b -> lc_open_inv a d b
  | ELet t e1 e2 -> lc_open_ty_inv a d t; lc_open_inv a d e1; lc_open_inv a d e2
  | ELetRec bs b -> lc_open_inv_binds a d bs; lc_open_inv a d b
  | ECase es dt -> lc_open_inv_exps a d es; lc_open_inv_dt a d dt
  | ELetJoin ts t e1 e2 ->
    lc_open_tys_inv a d ts; lc_open_ty_inv a d t; lc_open_inv a d e1; lc_open_inv a d e2
  | EJump _ es -> lc_open_inv_exps a d es
  | EExtend k e1 e2 -> lc_open_key_inv a d k; lc_open_inv a d e1; lc_open_inv a d e2
  | ESelect k b -> lc_open_key_inv a d k; lc_open_inv a d b
  | ERestrict k b -> lc_open_key_inv a d k; lc_open_inv a d b
  | EUpdate k e1 e2 -> lc_open_key_inv a d k; lc_open_inv a d e1; lc_open_inv a d e2
  | EMerge e1 e2 -> lc_open_inv a d e1; lc_open_inv a d e2
  | EInject k t b -> lc_open_key_inv a d k; lc_open_ty_inv a d t; lc_open_inv a d b
  | EWeaken k t b -> lc_open_key_inv a d k; lc_open_ty_inv a d t; lc_open_inv a d b
  | EAbsurd t b -> lc_open_ty_inv a d t; lc_open_inv a d b
  | EPerform k _ ts b -> lc_open_key_inv a d k; lc_open_tys_inv a d ts; lc_open_inv a d b
  | EHandle b h ->
    lc_open_inv a d b; lc_open_ent_inv a d h.h_ent; lc_open_ty_inv a d h.h_ret_ty;
    lc_open_inv a d h.h_ret; lc_open_inv_cls a d h.h_clauses
  | EOpenEff t b -> lc_open_ty_inv a d t; lc_open_inv a d b
  | ERegion l es b -> lc_open_layout_inv a d l; lc_open_inv_exps a d es; lc_open_inv a (d + 1) b
  | EReadCell r k -> lc_open_rr_inv a d r; lc_open_key_inv a d k
  | EWriteCell r k b -> lc_open_rr_inv a d r; lc_open_key_inv a d k; lc_open_inv a d b
  | EMatch th dt -> lc_open_inv_exps a d th; lc_open_inv_dt a d dt
  | EOpenEffC t b -> lc_open_ty_inv a d t; lc_open_inv a d b
  | EFill _ b -> lc_open_inv a d b
  | ERegionOpen _ th b -> lc_open_inv_cells a d th; lc_open_inv a d b
  | EOpaque _ t -> lc_open_ty_inv a d t

and lc_open_inv_exps (a: atom) (d: nat) (es: list exp)
  : Lemma (requires lc_exps_at d (rmap_exps (open_rr a) d es)) (ensures lc_exps_at (d + 1) es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> lc_open_inv a d e; lc_open_inv_exps a d es

and lc_open_inv_binds (a: atom) (d: nat) (bs: list (typ & exp))
  : Lemma (requires lc_binds_at d (rmap_binds (open_rr a) d bs)) (ensures lc_binds_at (d + 1) bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> lc_open_ty_inv a d (fst p_); lc_open_inv a d (snd p_); lc_open_inv_binds a d bs

and lc_open_inv_cells (a: atom) (d: nat) (th: list (key & exp))
  : Lemma (requires lc_cells_at d (rmap_cells (open_rr a) d th)) (ensures lc_cells_at (d + 1) th)
          (decreases th) =
  match th with
  | [] -> ()
  | p_ :: th -> lc_open_key_inv a d (fst p_); lc_open_inv a d (snd p_); lc_open_inv_cells a d th

and lc_open_inv_dt a d dt
  : Lemma (requires lc_dt_at d (rmap_dt (open_rr a) d dt)) (ensures lc_dt_at (d + 1) dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> lc_open_inv a d e
  | DBind o dt -> lc_open_occ_inv a d o; lc_open_inv_dt a d dt
  | DSwitchCtor o bs df -> lc_open_occ_inv a d o; lc_open_inv_brs a d bs; lc_open_inv_odt a d df
  | DSwitchLit o bs df -> lc_open_occ_inv a d o; lc_open_inv_brs a d bs; lc_open_inv_dt a d df
  | DSwitchKey o bs df -> lc_open_occ_inv a d o; lc_open_inv_kbrs a d bs; lc_open_inv_odt a d df
  | DGuard e dt1 dt2 -> lc_open_inv a d e; lc_open_inv_dt a d dt1; lc_open_inv_dt a d dt2

and lc_open_inv_odt (a: atom) (d: nat) (df: option dtree)
  : Lemma (requires lc_odt_at d (rmap_odt (open_rr a) d df)) (ensures lc_odt_at (d + 1) df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> lc_open_inv_dt a d dt

and lc_open_inv_brs (#lb: eqtype) (a: atom) (d: nat) (bs: list (lb & dtree))
  : Lemma (requires lc_brs_at d (rmap_brs (open_rr a) d bs)) (ensures lc_brs_at (d + 1) bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> lc_open_inv_dt a d (snd p_); lc_open_inv_brs a d bs

and lc_open_inv_kbrs (a: atom) (d: nat) (bs: list (key & dtree))
  : Lemma (requires lc_kbrs_at d (rmap_kbrs (open_rr a) d bs)) (ensures lc_kbrs_at (d + 1) bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> lc_open_key_inv a d (fst p_); lc_open_inv_dt a d (snd p_); lc_open_inv_kbrs a d bs

and lc_open_inv_cls (a: atom) (d: nat) (cs: list clause)
  : Lemma (requires lc_cls_at d (rmap_cls (open_rr a) d cs)) (ensures lc_cls_at (d + 1) cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs ->
    lc_open_ty_inv a d s; lc_open_ty_inv a d kt; lc_open_inv a d b; lc_open_inv_cls a d cs
  | CFast _ _ s b :: cs -> lc_open_ty_inv a d s; lc_open_inv a d b; lc_open_inv_cls a d cs

(* Opening and free atoms: types. *)

let frn_open_key (a: atom) (m: nat) (k: key) (b: atom)
  : Lemma (L.mem b (frn_key k) ==> L.mem b (frn_key (rmap_key (open_rr a m) k))) = ()

let rec frn_open_ty (a: atom) (m: nat) (t: typ) (b: atom)
  : Lemma (ensures L.mem b (frn_ty t) ==> L.mem b (frn_ty (rmap_ty (open_rr a m) t)))
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> frn_open_ty a m t1 b; frn_open_ty a m t2 b
  | TForall _ t1 -> frn_open_ty a m t1 b
  | TConstr c t1 -> frn_open_constr a m c b; frn_open_ty a m t1 b
  | TRowExt en r -> frn_open_ent a m en b; frn_open_ty a m r b

and frn_open_ent (a: atom) (m: nat) (en: entry) (b: atom)
  : Lemma (ensures L.mem b (frn_ent en) ==> L.mem b (frn_ent (rmap_ent (open_rr a m) en)))
          (decreases en) =
  match en with
  | EntTy k t -> frn_open_key a m k b; frn_open_ty a m t b
  | EntEff _ _ ts -> frn_open_tys a m ts b
  | EntRegion _ -> ()

and frn_open_constr (a: atom) (m: nat) (c: constr) (b: atom)
  : Lemma (ensures L.mem b (frn_constr c) ==> L.mem b (frn_constr (rmap_constr (open_rr a m) c)))
          (decreases c) =
  match c with
  | CLacks k t -> frn_open_key a m k b; frn_open_ty a m t b
  | CDisj t1 t2 -> frn_open_ty a m t1 b; frn_open_ty a m t2 b

and frn_open_tys (a: atom) (m: nat) (ts: list typ) (b: atom)
  : Lemma (ensures L.mem b (frn_tys ts) ==> L.mem b (frn_tys (rmap_tys (open_rr a m) ts)))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> frn_open_ty a m t b; frn_open_tys a m ts b

let rec frn_open_layout (a: atom) (m: nat) (l: list (key & typ)) (b: atom)
  : Lemma (ensures L.mem b (frn_layout l) ==> L.mem b (frn_layout (rmap_layout (open_rr a m) l)))
          (decreases l) =
  match l with
  | [] -> ()
  | p_ :: l -> frn_open_key a m (fst p_) b; frn_open_ty a m (snd p_) b; frn_open_layout a m l b

let rec frn_open_occ (a: atom) (m: nat) (o: occ) (b: atom)
  : Lemma (ensures L.mem b (frn_occ o) ==> L.mem b (frn_occ (rmap_occ (open_rr a m) o)))
          (decreases o) =
  match o with
  | OScrut _ -> ()
  | OCtor o _ _ -> frn_open_occ a m o b
  | ORecord o k | OVariant o k -> frn_open_occ a m o b; frn_open_key a m k b

(* Opening and free atoms: terms. *)

let rec frn_open (a: atom) (d: nat) (e: exp) (b: atom)
  : Lemma (ensures L.mem b (frn_exp e) ==> L.mem b (frn_exp (rmap_exp (open_rr a) d e)))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EForce _ -> ()
  | ELam t r e1 -> frn_open_ty a d t b; frn_open_ty a d r b; frn_open a d e1 b
  | EApp e1 e2 -> frn_open a d e1 b; frn_open a d e2 b
  | ETyLam _ e1 -> frn_open a d e1 b
  | ETyApp e1 t -> frn_open a d e1 b; frn_open_ty a d t b
  | ECLam c e1 -> frn_open_constr a d c b; frn_open a d e1 b
  | ECApp e1 -> frn_open a d e1 b
  | ELet t e1 e2 -> frn_open_ty a d t b; frn_open a d e1 b; frn_open a d e2 b
  | ELetRec bs e1 -> frn_open_binds a d bs b; frn_open a d e1 b
  | ECase es dt -> frn_open_exps a d es b; frn_open_dt a d dt b
  | ELetJoin ts t e1 e2 ->
    frn_open_tys a d ts b; frn_open_ty a d t b; frn_open a d e1 b; frn_open a d e2 b
  | EJump _ es -> frn_open_exps a d es b
  | EExtend k e1 e2 -> frn_open_key a d k b; frn_open a d e1 b; frn_open a d e2 b
  | ESelect k e1 -> frn_open_key a d k b; frn_open a d e1 b
  | ERestrict k e1 -> frn_open_key a d k b; frn_open a d e1 b
  | EUpdate k e1 e2 -> frn_open_key a d k b; frn_open a d e1 b; frn_open a d e2 b
  | EMerge e1 e2 -> frn_open a d e1 b; frn_open a d e2 b
  | EInject k t e1 -> frn_open_key a d k b; frn_open_ty a d t b; frn_open a d e1 b
  | EWeaken k t e1 -> frn_open_key a d k b; frn_open_ty a d t b; frn_open a d e1 b
  | EAbsurd t e1 -> frn_open_ty a d t b; frn_open a d e1 b
  | EPerform k _ ts e1 -> frn_open_key a d k b; frn_open_tys a d ts b; frn_open a d e1 b
  | EHandle e1 h ->
    frn_open a d e1 b; frn_open_ent a d h.h_ent b; frn_open_ty a d h.h_ret_ty b;
    frn_open a d h.h_ret b; frn_open_cls a d h.h_clauses b
  | EOpenEff t e1 -> frn_open_ty a d t b; frn_open a d e1 b
  | ERegion l es e1 -> frn_open_layout a d l b; frn_open_exps a d es b; frn_open a (d + 1) e1 b
  | EReadCell r k -> frn_open_key a d k b
  | EWriteCell r k e1 -> frn_open_key a d k b; frn_open a d e1 b
  | EMatch th dt -> frn_open_exps a d th b; frn_open_dt a d dt b
  | EOpenEffC t e1 -> frn_open_ty a d t b; frn_open a d e1 b
  | EFill _ e1 -> frn_open a d e1 b
  | ERegionOpen _ th e1 -> frn_open_cells a d th b; frn_open a d e1 b
  | EOpaque _ t -> frn_open_ty a d t b

and frn_open_exps (a: atom) (d: nat) (es: list exp) (b: atom)
  : Lemma (ensures L.mem b (frn_exps es) ==> L.mem b (frn_exps (rmap_exps (open_rr a) d es)))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> frn_open a d e b; frn_open_exps a d es b

and frn_open_binds (a: atom) (d: nat) (bs: list (typ & exp)) (b: atom)
  : Lemma (ensures L.mem b (frn_binds bs) ==> L.mem b (frn_binds (rmap_binds (open_rr a) d bs)))
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> frn_open_ty a d (fst p_) b; frn_open a d (snd p_) b; frn_open_binds a d bs b

and frn_open_cells (a: atom) (d: nat) (th: list (key & exp)) (b: atom)
  : Lemma (ensures L.mem b (frn_cells th) ==> L.mem b (frn_cells (rmap_cells (open_rr a) d th)))
          (decreases th) =
  match th with
  | [] -> ()
  | p_ :: th -> frn_open_key a d (fst p_) b; frn_open a d (snd p_) b; frn_open_cells a d th b

and frn_open_dt (a: atom) (d: nat) (dt: dtree) (b: atom)
  : Lemma (ensures L.mem b (frn_dt dt) ==> L.mem b (frn_dt (rmap_dt (open_rr a) d dt)))
          (decreases dt) =
  match dt with
  | DLeaf e -> frn_open a d e b
  | DBind o dt -> frn_open_occ a d o b; frn_open_dt a d dt b
  | DSwitchCtor o bs df -> frn_open_occ a d o b; frn_open_brs a d bs b; frn_open_odt a d df b
  | DSwitchLit o bs df -> frn_open_occ a d o b; frn_open_brs a d bs b; frn_open_dt a d df b
  | DSwitchKey o bs df -> frn_open_occ a d o b; frn_open_kbrs a d bs b; frn_open_odt a d df b
  | DGuard e dt1 dt2 -> frn_open a d e b; frn_open_dt a d dt1 b; frn_open_dt a d dt2 b

and frn_open_odt (a: atom) (d: nat) (df: option dtree) (b: atom)
  : Lemma (ensures L.mem b (frn_odt df) ==> L.mem b (frn_odt (rmap_odt (open_rr a) d df)))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> frn_open_dt a d dt b

and frn_open_brs (#lb: eqtype) (a: atom) (d: nat) (bs: list (lb & dtree)) (b: atom)
  : Lemma (ensures L.mem b (frn_brs bs) ==> L.mem b (frn_brs (rmap_brs (open_rr a) d bs)))
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> frn_open_dt a d (snd p_) b; frn_open_brs a d bs b

and frn_open_kbrs (a: atom) (d: nat) (bs: list (key & dtree)) (b: atom)
  : Lemma (ensures L.mem b (frn_kbrs bs) ==> L.mem b (frn_kbrs (rmap_kbrs (open_rr a) d bs)))
          (decreases bs) =
  match bs with
  | [] -> ()
  | p_ :: bs -> frn_open_key a d (fst p_) b; frn_open_dt a d (snd p_) b; frn_open_kbrs a d bs b

and frn_open_cls (a: atom) (d: nat) (cs: list clause) (b: atom)
  : Lemma (ensures L.mem b (frn_cls cs) ==> L.mem b (frn_cls (rmap_cls (open_rr a) d cs)))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt e :: cs ->
    frn_open_ty a d s b; frn_open_ty a d kt b; frn_open a d e b; frn_open_cls a d cs b
  | CFast _ _ s e :: cs -> frn_open_ty a d s b; frn_open a d e b; frn_open_cls a d cs b

let frn_open_incl a d e b = frn_open a d e b

let frn_open_incl_dt a d dt b = frn_open_dt a d dt b

(* Fresh atoms. *)

let rec max_atom (l: list atom) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | a :: l -> let m = max_atom l in if a > m then a else m

let rec max_atom_ge (l: list atom) (a: atom)
  : Lemma (requires L.mem a l) (ensures a <= max_atom l) (decreases l) =
  match l with
  | b :: l' -> if a = b then () else max_atom_ge l' a

let fresh_atom l =
  let a = max_atom l + 1 in
  if L.mem a l then max_atom_ge l a;
  a
