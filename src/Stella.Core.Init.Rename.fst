(* Proof structure.

   The judgement of `Stella.Core.Init` reads no type: it reads the shape of
   a term, the term variables and join indices it mentions, the positions
   of the members, and, to classify a chain, the declared scheme of the
   chain's head (`global_scheme`), which no map of a term changes. So two
   terms of the same shape read the same members, when their term variables
   correspond.

   `tsim ξ e e'` says that `e'` is `e` with every type and kind replaced
   arbitrarily and every free term variable `i` renamed to `ξ i`, `ξ` lifted
   under the term binders as `ren_tm` lifts it. A type substitution and a
   term renaming each relate a term to its image (`tsim_sub_ty`,
   `tsim_ren_tm`); a type renaming is the type substitution of its renaming
   (`ren_ty_binds_as_sub`).

   A `letrec` binds its members as its innermost term variables, and the
   renaming under it is lifted past them, `upn_ren n ξ` for `n` members.
   The lifting fixes every member and sends every variable bound outside the
   group above them, where the judgement reads it as a local at `ρ = ∅`, as
   it reads the variable before renaming. That is the whole condition: a
   group related to another by `upn_ren n ξ`, for any `ξ`, reads exactly the
   members the other reads (`init_safe_tsim`). Each theorem of the
   interface is an instance.

   `init_safe_tsim` is a backward simulation: a derivation that the image
   term reads a member gives one that the original term reads it. Terms
   are related by `tsim`, environments entry by entry (`ent_rel`,
   `venv_rel`, `jent_rel`, `jenv_rel`), an entry's own term and environment
   by the renaming in force where the entry was pushed, which the relation
   of the entry keeps existentially. A variable environment is related
   under `ξ` when its head entries are related and its tail is related
   under some `ξ0` with `ξ` pointwise `up_ren ξ0`; so a lookup at `i` finds
   related entries at `i` and `ξ i`, and an environment with no entry
   relates every variable to a variable beyond the other.

   The judgement's rules read a form through `through`, `builds`, `takes`,
   `spine_parts`, `default_parts`, `scrutinised`, `children` and the
   decision-tree helpers; each of them maps related terms to related
   parts. The simulation is a mutual induction on the derivation of the
   image; `sub` has a simulation of its own. Each lemma concludes that a
   derivation exists, so the relation can be existential. *)
module Stella.Core.Init.Rename
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Init
open Stella.Core.Init.Lemmas
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module T = FStar.Tactics.V2

(* Terms of the same shape. *)

let rec tsim (xi: ren) (e e': exp) : Tot bool (decreases e) =
  match e, e' with
  | EVar i, EVar i' -> i' = xi i
  | EGlobal q _, EGlobal q' _ -> q = q'
  | ELit _, ELit _ | ERecEmpty, ERecEmpty | EReadCell _ _, EReadCell _ _ | EForce _, EForce _
  | EOpaque _ _, EOpaque _ _ -> true
  | ELam _ _ b, ELam _ _ b' -> tsim (up_ren xi) b b'
  | EApp e1 e2, EApp e1' e2' | EExtend _ e1 e2, EExtend _ e1' e2'
  | EUpdate _ e1 e2, EUpdate _ e1' e2' | EMerge e1 e2, EMerge e1' e2' ->
    tsim xi e1 e1' && tsim xi e2 e2'
  | ETyLam _ b, ETyLam _ b' | ETyApp b _, ETyApp b' _ | ECLam _ b, ECLam _ b' | ECApp b, ECApp b'
  | ESelect _ b, ESelect _ b' | ERestrict _ b, ERestrict _ b' | EInject _ _ b, EInject _ _ b'
  | EWeaken _ _ b, EWeaken _ _ b' | EAbsurd _ b, EAbsurd _ b' | EPerform _ _ _ b, EPerform _ _ _ b'
  | EOpenEff _ b, EOpenEff _ b' | EWriteCell _ _ b, EWriteCell _ _ b'
  | EOpenEffC _ b, EOpenEffC _ b' | EFill _ b, EFill _ b' -> tsim xi b b'
  | ELet _ e1 e2, ELet _ e1' e2' -> tsim xi e1 e1' && tsim (up_ren xi) e2 e2'
  | ELetRec bs b, ELetRec bs' b' ->
    L.length bs = L.length bs' &&
    tsim_binds (upn_ren (L.length bs) xi) bs bs' && tsim (upn_ren (L.length bs) xi) b b'
  | ECase es dt, ECase es' dt' | EMatch es dt, EMatch es' dt' ->
    tsim_exps xi es es' && tsim_dt xi dt dt'
  | ELetJoin ts _ e1 e2, ELetJoin ts' _ e1' e2' ->
    L.length ts = L.length ts' && tsim (upn_ren (L.length ts) xi) e1 e1' && tsim xi e2 e2'
  | EJump j es, EJump j' es' -> j = j' && tsim_exps xi es es'
  | EHandle b h, EHandle b' h' ->
    tsim xi b b' && tsim (up_ren xi) h.h_ret h'.h_ret && tsim_cls xi h.h_clauses h'.h_clauses
  | ERegion _ es b, ERegion _ es' b' -> tsim_exps xi es es' && tsim xi b b'
  | ERegionOpen _ th b, ERegionOpen _ th' b' -> tsim_cells xi th th' && tsim xi b b'
  | _ -> false

and tsim_exps (xi: ren) (es es': list exp) : Tot bool (decreases es) =
  match es, es' with
  | [], [] -> true
  | e :: es, e' :: es' -> tsim xi e e' && tsim_exps xi es es'
  | _ -> false

and tsim_binds (xi: ren) (bs bs': list (typ & exp)) : Tot bool (decreases bs) =
  match bs, bs' with
  | [], [] -> true
  | (_, e) :: bs, (_, e') :: bs' -> tsim xi e e' && tsim_binds xi bs bs'
  | _ -> false

and tsim_cells (xi: ren) (th th': list (key & exp)) : Tot bool (decreases th) =
  match th, th' with
  | [], [] -> true
  | (_, e) :: th, (_, e') :: th' -> tsim xi e e' && tsim_cells xi th th'
  | _ -> false

and tsim_dt (xi: ren) (dt dt': dtree) : Tot bool (decreases dt) =
  match dt, dt' with
  | DLeaf e, DLeaf e' -> tsim xi e e'
  | DBind o dt, DBind o' dt' -> o = o' && tsim_dt (up_ren xi) dt dt'
  | DSwitchCtor _ bs df, DSwitchCtor _ bs' df' | DSwitchKey _ bs df, DSwitchKey _ bs' df' ->
    tsim_brs xi bs bs' && tsim_odt xi df df'
  | DSwitchLit _ bs df, DSwitchLit _ bs' df' -> tsim_brs xi bs bs' && tsim_dt xi df df'
  | DGuard e dt1 dt2, DGuard e' dt1' dt2' ->
    tsim xi e e' && tsim_dt xi dt1 dt1' && tsim_dt xi dt2 dt2'
  | _ -> false

and tsim_odt (xi: ren) (df df': option dtree) : Tot bool (decreases df) =
  match df, df' with
  | None, None -> true
  | Some dt, Some dt' -> tsim_dt xi dt dt'
  | _ -> false

and tsim_brs (#lb: eqtype) (xi: ren) (bs bs': list (lb & dtree)) : Tot bool (decreases bs) =
  match bs, bs' with
  | [], [] -> true
  | (_, dt) :: bs, (_, dt') :: bs' -> tsim_dt xi dt dt' && tsim_brs xi bs bs'
  | _ -> false

and tsim_cls (xi: ren) (cs cs': list clause) : Tot bool (decreases cs) =
  match cs, cs' with
  | [], [] -> true
  | CFull _ _ _ _ b :: cs, CFull _ _ _ _ b' :: cs' -> tsim (upn_ren 2 xi) b b' && tsim_cls xi cs cs'
  | CFast _ _ _ b :: cs, CFast _ _ _ b' :: cs' -> tsim (up_ren xi) b b' && tsim_cls xi cs cs'
  | _ -> false

(* The maps relate a term to its image. A type substitution changes types
   alone; the term renaming is any that fixes every variable. *)

let rec tsim_sub_ty (xi: ren) (sigma: tsub) (e: exp)
  : Lemma (requires forall (i: nat). xi i == i) (ensures tsim xi e (sub_ty_exp sigma e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> tsim_sub_ty (up_ren xi) sigma b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    tsim_sub_ty xi sigma e1; tsim_sub_ty xi sigma e2
  | ETyLam _ b -> tsim_sub_ty xi (up_tsub sigma) b
  | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> tsim_sub_ty xi sigma b
  | ELet _ e1 e2 -> tsim_sub_ty xi sigma e1; tsim_sub_ty (up_ren xi) sigma e2
  | ELetRec bs b ->
    tsim_binds_sub_ty (upn_ren (L.length bs) xi) sigma bs;
    tsim_sub_ty (upn_ren (L.length bs) xi) sigma b
  | ECase es dt | EMatch es dt -> tsim_exps_sub_ty xi sigma es; tsim_dt_sub_ty xi sigma dt
  | ELetJoin ts _ e1 e2 ->
    tsim_sub_ty (upn_ren (L.length ts) xi) sigma e1; tsim_sub_ty xi sigma e2
  | EJump _ es -> tsim_exps_sub_ty xi sigma es
  | EHandle b h ->
    tsim_sub_ty xi sigma b; tsim_sub_ty (up_ren xi) sigma h.h_ret;
    tsim_cls_sub_ty xi sigma h.h_clauses
  | ERegion _ es b -> tsim_exps_sub_ty xi sigma es; tsim_sub_ty xi sigma b
  | ERegionOpen _ th b -> tsim_cells_sub_ty xi sigma th; tsim_sub_ty xi sigma b

and tsim_exps_sub_ty (xi: ren) (sigma: tsub) (es: list exp)
  : Lemma (requires forall (i: nat). xi i == i) (ensures tsim_exps xi es (sub_ty_exps sigma es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> tsim_sub_ty xi sigma e; tsim_exps_sub_ty xi sigma es

and tsim_binds_sub_ty (xi: ren) (sigma: tsub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). xi i == i) (ensures tsim_binds xi bs (sub_ty_binds sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> tsim_sub_ty xi sigma e; tsim_binds_sub_ty xi sigma bs

and tsim_cells_sub_ty (xi: ren) (sigma: tsub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). xi i == i) (ensures tsim_cells xi th (sub_ty_cells sigma th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> tsim_sub_ty xi sigma e; tsim_cells_sub_ty xi sigma th

and tsim_dt_sub_ty (xi: ren) (sigma: tsub) (dt: dtree)
  : Lemma (requires forall (i: nat). xi i == i) (ensures tsim_dt xi dt (sub_ty_dt sigma dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> tsim_sub_ty xi sigma e
  | DBind _ dt -> tsim_dt_sub_ty (up_ren xi) sigma dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    tsim_brs_sub_ty xi sigma bs; tsim_odt_sub_ty xi sigma df
  | DSwitchLit _ bs df -> tsim_brs_sub_ty xi sigma bs; tsim_dt_sub_ty xi sigma df
  | DGuard e dt1 dt2 ->
    tsim_sub_ty xi sigma e; tsim_dt_sub_ty xi sigma dt1; tsim_dt_sub_ty xi sigma dt2

and tsim_odt_sub_ty (xi: ren) (sigma: tsub) (df: option dtree)
  : Lemma (requires forall (i: nat). xi i == i) (ensures tsim_odt xi df (sub_ty_odt sigma df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> tsim_dt_sub_ty xi sigma dt

and tsim_brs_sub_ty (#lb: eqtype) (xi: ren) (sigma: tsub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). xi i == i) (ensures tsim_brs xi bs (sub_ty_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> tsim_dt_sub_ty xi sigma dt; tsim_brs_sub_ty xi sigma bs

and tsim_cls_sub_ty (xi: ren) (sigma: tsub) (cs: list clause)
  : Lemma (requires forall (i: nat). xi i == i) (ensures tsim_cls xi cs (sub_ty_cls sigma cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    tsim_sub_ty (upn_ren 2 xi) (upn_tsub nb sigma) b; tsim_cls_sub_ty xi sigma cs
  | CFast _ nb _ b :: cs ->
    tsim_sub_ty (up_ren xi) (upn_tsub nb sigma) b; tsim_cls_sub_ty xi sigma cs

let rec ren_ty_binds_as_sub (zeta: ren) (bs: list (typ & exp))
  : Lemma (ensures ren_ty_binds zeta bs == sub_ty_binds (ren_tsub zeta) bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs ->
    ren_ty_as_sub zeta t; ren_ty_exp_as_sub zeta e; ren_ty_binds_as_sub zeta bs

let rec tsim_ren_tm (xi: ren) (e: exp) : Lemma (ensures tsim xi e (ren_tm xi e)) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> tsim_ren_tm (up_ren xi) b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    tsim_ren_tm xi e1; tsim_ren_tm xi e2
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> tsim_ren_tm xi b
  | ELet _ e1 e2 -> tsim_ren_tm xi e1; tsim_ren_tm (up_ren xi) e2
  | ELetRec bs b ->
    tsim_binds_ren_tm (upn_ren (L.length bs) xi) bs; tsim_ren_tm (upn_ren (L.length bs) xi) b
  | ECase es dt | EMatch es dt -> tsim_exps_ren_tm xi es; tsim_dt_ren_tm xi dt
  | ELetJoin ts _ e1 e2 -> tsim_ren_tm (upn_ren (L.length ts) xi) e1; tsim_ren_tm xi e2
  | EJump _ es -> tsim_exps_ren_tm xi es
  | EHandle b h ->
    tsim_ren_tm xi b; tsim_ren_tm (up_ren xi) h.h_ret; tsim_cls_ren_tm xi h.h_clauses
  | ERegion _ es b -> tsim_exps_ren_tm xi es; tsim_ren_tm xi b
  | ERegionOpen _ th b -> tsim_cells_ren_tm xi th; tsim_ren_tm xi b

and tsim_exps_ren_tm (xi: ren) (es: list exp)
  : Lemma (ensures tsim_exps xi es (ren_tm_exps xi es)) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> tsim_ren_tm xi e; tsim_exps_ren_tm xi es

and tsim_binds_ren_tm (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures tsim_binds xi bs (ren_tm_binds xi bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> tsim_ren_tm xi e; tsim_binds_ren_tm xi bs

and tsim_cells_ren_tm (xi: ren) (th: list (key & exp))
  : Lemma (ensures tsim_cells xi th (ren_tm_cells xi th)) (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> tsim_ren_tm xi e; tsim_cells_ren_tm xi th

and tsim_dt_ren_tm (xi: ren) (dt: dtree)
  : Lemma (ensures tsim_dt xi dt (ren_tm_dt xi dt)) (decreases dt) =
  match dt with
  | DLeaf e -> tsim_ren_tm xi e
  | DBind _ dt -> tsim_dt_ren_tm (up_ren xi) dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df -> tsim_brs_ren_tm xi bs; tsim_odt_ren_tm xi df
  | DSwitchLit _ bs df -> tsim_brs_ren_tm xi bs; tsim_dt_ren_tm xi df
  | DGuard e dt1 dt2 -> tsim_ren_tm xi e; tsim_dt_ren_tm xi dt1; tsim_dt_ren_tm xi dt2

and tsim_odt_ren_tm (xi: ren) (df: option dtree)
  : Lemma (ensures tsim_odt xi df (ren_tm_odt xi df)) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> tsim_dt_ren_tm xi dt

and tsim_brs_ren_tm (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures tsim_brs xi bs (ren_tm_brs xi bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> tsim_dt_ren_tm xi dt; tsim_brs_ren_tm xi bs

and tsim_cls_ren_tm (xi: ren) (cs: list clause)
  : Lemma (ensures tsim_cls xi cs (ren_tm_cls xi cs)) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> tsim_ren_tm (upn_ren 2 xi) b; tsim_cls_ren_tm xi cs
  | CFast _ _ _ b :: cs -> tsim_ren_tm (up_ren xi) b; tsim_cls_ren_tm xi cs

(* Related environments. *)

let rec ent_rel (v v': ventry) : Tot prop (decreases v) =
  match v, v' with
  | VNone, VNone -> True
  | VMem k, VMem k' -> k == k'
  | VLat ve je e, VLat ve' je' e' ->
    jenv_rel je je' /\ (exists (xi: ren). venv_rel xi ve ve' /\ tsim xi e e')
  | VRec ve je bs k, VRec ve' je' bs' k' ->
    k == k' /\ L.length bs' == L.length bs /\ jenv_rel je je' /\
    (exists (xi: ren). venv_rel xi ve ve' /\ tsim_binds (upn_ren (L.length bs) xi) bs bs')
  | VArg d p, VArg d' p' -> p == p' /\ jent_rel d d'
  | _ -> False

and venv_rel (xi: ren) (ve ve': venv) : Tot prop (decreases ve) =
  match ve, ve' with
  | [], [] -> True
  | v :: ve, v' :: ve' ->
    ent_rel v v' /\
    (exists (xi0: ren). (forall (i: nat). xi i == up_ren xi0 i) /\ venv_rel xi0 ve ve')
  | _ -> False

and jent_rel (d d': jentry) : Tot prop (decreases d) =
  match d, d' with
  | JDef ve je n e1 e2, JDef ve' je' n' e1' e2' ->
    n == n' /\ jenv_rel je je' /\
    (exists (xi: ren). venv_rel xi ve ve' /\ tsim (upn_ren n xi) e1 e1' /\ tsim xi e2 e2')

and jenv_rel (je je': jenv) : Tot prop (decreases je) =
  match je, je' with
  | [], [] -> True
  | d :: je, d' :: je' -> jent_rel d d' /\ jenv_rel je je'
  | _ -> False

(* An expression under its environments, related to another. *)
let crel3 (ve: venv) (je: jenv) (e: exp) (ve': venv) (je': jenv) (e': exp) : prop =
  jenv_rel je je' /\ (exists (xi: ren). venv_rel xi ve ve' /\ tsim xi e e')

let crel (c c': child) : prop = crel3 c.cv c.cj c.ce c'.cv c'.cj c'.ce

(* Related groups: the same members, and related right-hand sides. *)
let grel (g g': group) : prop =
  (forall (q: qname). g.gmem q == g'.gmem q) /\
  (forall (k: nat) (r': exp). rhs g' k == Some r' ==>
     (exists (r: exp). rhs g k == Some r /\ crel3 g.genv [] r g'.genv [] r'))

(* Existence of a derivation. *)
let ex (a: Type) : prop = exists (x: a). True

let ex_intro (#a: Type) (x: a) : Lemma (ex a) = introduce exists (y: a). True with x and ()

let ex_map (#a #b: Type) (f: a -> b) : Lemma (requires ex a) (ensures ex b) =
  eliminate exists (x: a). True
    with introduce exists (y: b). True with (f x) and ()

let ex_map2 (#a #b #c: Type) (f: a -> b -> c) : Lemma (requires ex a /\ ex b) (ensures ex c) =
  eliminate exists (x: a). True
    with
  eliminate exists (y: b). True
    with
  introduce exists (z: c). True with (f x y) and ()

(* Lookups. *)

let rec venv_lookup (xi: ren) (ve ve': venv) (i: nat)
  : Lemma (requires venv_rel xi ve ve') (ensures ent_rel (vlook ve i) (vlook ve' (xi i)))
          (decreases ve) =
  match ve, ve' with
  | [], [] -> ()
  | v :: ve0, v' :: ve0' ->
    eliminate exists (xi0: ren). (forall (i: nat). xi i == up_ren xi0 i) /\ venv_rel xi0 ve0 ve0'
    with if i = 0 then () else venv_lookup xi0 ve0 ve0' (i - 1)

let rec jenv_lookup (je je': jenv) (j: nat)
  : Lemma (requires jenv_rel je je')
          (ensures (match jlook je j, jlook je' j with
                    | Some d, Some d' -> jent_rel d d'
                    | None, None -> True
                    | _ -> False))
          (decreases je) =
  match je, je' with
  | [], [] -> ()
  | _ :: je0, _ :: je0' -> if j = 0 then () else jenv_lookup je0 je0' (j - 1)

let rec jenv_length (je je': jenv)
  : Lemma (requires jenv_rel je je') (ensures L.length je == L.length je') (decreases je) =
  match je, je' with
  | [], [] -> ()
  | _ :: je0, _ :: je0' -> jenv_length je0 je0'

(* Pushing entries. *)

let venv_cons (xi: ren) (xi': ren) (v v': ventry) (ve ve': venv)
  : Lemma (requires ent_rel v v' /\ venv_rel xi ve ve' /\ (forall (i: nat). xi' i == up_ren xi i))
          (ensures venv_rel xi' (v :: ve) (v' :: ve')) =
  introduce exists (xi0: ren). (forall (i: nat). xi' i == up_ren xi0 i) /\ venv_rel xi0 ve ve'
  with xi and ()

let rec pre_rel (p p': venv) : Tot prop (decreases p) =
  match p, p' with
  | [], [] -> True
  | v :: p, v' :: p' -> ent_rel v v' /\ pre_rel p p'
  | _ -> False

let rec venv_append (xi: ren) (p p': venv) (ve ve': venv)
  : Lemma (requires pre_rel p p' /\ venv_rel xi ve ve')
          (ensures venv_rel (upn_ren (L.length p) xi) (L.append p ve) (L.append p' ve'))
          (decreases p) =
  match p, p' with
  | [], [] -> assert (forall (i: nat). upn_ren 0 xi i == xi i)
  | v :: p0, v' :: p0' ->
    venv_append xi p0 p0' ve ve';
    let n = L.length p in
    let xi0 = upn_ren (n - 1) xi in
    venv_cons xi0 (upn_ren n xi) v v' (L.append p0 ve) (L.append p0' ve')

let venv_ext (xi xi': ren) (ve ve': venv)
  : Lemma (requires venv_rel xi ve ve' /\ (forall (i: nat). xi' i == xi i))
          (ensures venv_rel xi' ve ve') =
  match ve, ve' with
  | [], [] -> ()
  | _ :: ve0, _ :: ve0' ->
    eliminate exists (xi0: ren). (forall (i: nat). xi i == up_ren xi0 i) /\ venv_rel xi0 ve0 ve0'
    with introduce exists (xi0: ren). (forall (i: nat). xi' i == up_ren xi0 i) /\
      venv_rel xi0 ve0 ve0'
            with xi0 and ()

let rec rec_entries_rel (ve ve': venv) (je je': jenv) (bs bs': list (typ & exp)) (n: nat)
  : Lemma (requires ent_rel (VRec ve je bs 0) (VRec ve' je' bs' 0))
          (ensures pre_rel (rec_entries ve je bs n) (rec_entries ve' je' bs' n) /\
                   L.length (rec_entries ve je bs n) == n)
          (decreases n) =
  if n = 0 then () else rec_entries_rel ve ve' je je' bs bs' (n - 1)

let push_rec_rel (xi: ren) (ve ve': venv) (je je': jenv) (bs bs': list (typ & exp))
  : Lemma (requires venv_rel xi ve ve' /\ jenv_rel je je' /\ L.length bs' == L.length bs /\
                    tsim_binds (upn_ren (L.length bs) xi) bs bs')
          (ensures venv_rel (upn_ren (L.length bs) xi) (push_rec ve je bs) (push_rec ve' je' bs')) =
  assert (ent_rel (VRec ve je bs 0) (VRec ve' je' bs' 0));
  rec_entries_rel ve ve' je je' bs bs' (L.length bs);
  venv_append xi (rec_entries ve je bs (L.length bs)) (rec_entries ve' je' bs' (L.length bs)) ve ve'

let rec arg_entries_rel (d d': jentry) (p n: nat)
  : Lemma (requires jent_rel d d')
          (ensures pre_rel (arg_entries d p n) (arg_entries d' p n) /\
                   L.length (arg_entries d p n) == n)
          (decreases n) =
  if n = 0 then () else arg_entries_rel d d' (p + 1) (n - 1)

let crel_intro (xi: ren) (ve: venv) (je: jenv) (e: exp) (ve': venv) (je': jenv) (e': exp)
  : Lemma (requires jenv_rel je je' /\ venv_rel xi ve ve' /\ tsim xi e e')
          (ensures crel3 ve je e ve' je' e') =
  introduce exists (xi: ren). venv_rel xi ve ve' /\ tsim xi e e' with xi and ()

let join_def_rel (xi: ren) (ve ve': venv) (je je': jenv) (ts ts': list typ) (e1 e2 e1' e2': exp)
  : Lemma (requires venv_rel xi ve ve' /\ jenv_rel je je' /\ L.length ts == L.length ts' /\
                    tsim (upn_ren (L.length ts) xi) e1 e1' /\ tsim xi e2 e2')
          (ensures jent_rel (join_def ve je ts e1 e2) (join_def ve' je' ts' e1' e2')) =
  introduce exists (xi: ren).
    venv_rel xi ve ve' /\ tsim (upn_ren (L.length ts) xi) e1 e1' /\ tsim xi e2 e2'
  with xi and ()

let join_body_rel (d d': jentry)
  : Lemma (requires jent_rel d d') (ensures crel (join_body d) (join_body d')) =
  match d, d' with
  | JDef ve je n e1 e2, JDef ve' je' _ e1' e2' ->
    eliminate exists (xi: ren). venv_rel xi ve ve' /\ tsim (upn_ren n xi) e1 e1' /\ tsim xi e2 e2'
    with (arg_entries_rel d d' 0 n;
          venv_append xi (arg_entries d 0 n) (arg_entries d' 0 n) ve ve';
          crel_intro (upn_ren n xi) (L.append (arg_entries d 0 n) ve) (d :: je) e1
            (L.append (arg_entries d' 0 n) ve') (d' :: je') e1')

let join_cont_rel (d d': jentry)
  : Lemma (requires jent_rel d d') (ensures crel (join_cont d) (join_cont d')) =
  match d, d' with
  | JDef ve je n e1 e2, JDef ve' je' _ e1' e2' ->
    eliminate exists (xi: ren). venv_rel xi ve ve' /\ tsim (upn_ren n xi) e1 e1' /\ tsim xi e2 e2'
    with crel_intro xi ve (d :: je) e2 ve' (d' :: je') e2'

let join_scope_rel (d d': jentry) (c': child)
  : Lemma (requires jent_rel d d' /\ L.memP c' (join_scope d'))
          (ensures exists (c: child). L.memP c (join_scope d) /\ crel c c') =
  join_body_rel d d';
  join_cont_rel d d';
  FStar.Classical.or_elim #(c' == join_body d') #(L.memP c' [join_cont d'])
    #(fun _ -> exists (c: child). L.memP c (join_scope d) /\ crel c c')
    (fun _ -> assert (L.memP (join_body d) (join_scope d)))
    (fun _ -> assert (L.memP (join_cont d) (join_scope d)))

let join_jenv_length (d d': jentry)
  : Lemma (requires jent_rel d d') (ensures L.length (join_jenv d) == L.length (join_jenv d')) =
  match d, d' with
  | JDef _ je _ _ _, JDef _ je' _ _ _ -> jenv_length je je'

(* Lists of related terms. *)

let rhs_child (ve: venv) (je: jenv) (be: typ & exp) : child = mk ve je (snd be)

let cell_child (ve: venv) (je: jenv) (kv: key & exp) : child = mk ve je (snd kv)


let rec exps_nth (xi: ren) (es es': list exp) (k: nat)
  : Lemma (requires tsim_exps xi es es')
          (ensures (match L.nth es k, L.nth es' k with
                    | Some e, Some e' -> tsim xi e e'
                    | None, None -> True
                    | _ -> False))
          (decreases es) =
  match es, es' with
  | [], [] -> ()
  | _ :: es0, _ :: es0' -> if k = 0 then () else exps_nth xi es0 es0' (k - 1)

let rec exps_mem (xi: ren) (es es': list exp) (b': exp)
  : Lemma (requires tsim_exps xi es es' /\ L.memP b' es')
          (ensures exists (b: exp). L.memP b es /\ tsim xi b b') (decreases es) =
  match es, es' with
  | e :: es0, e' :: es0' ->
    FStar.Classical.or_elim #(b' == e') #(L.memP b' es0')
      #(fun _ -> exists (b: exp). L.memP b es /\ tsim xi b b')
      (fun _ -> ())
      (fun _ -> exps_mem xi es0 es0' b')

let rec binds_mem (xi: ren) (bs bs': list (typ & exp)) (t': typ) (r': exp)
  : Lemma (requires tsim_binds xi bs bs' /\ L.memP (t', r') bs')
          (ensures exists (t: typ) (r: exp). L.memP (t, r) bs /\ tsim xi r r') (decreases bs) =
  match bs, bs' with
  | (t, e) :: bs0, (te', e') :: bs0' ->
    FStar.Classical.or_elim #((t', r') == (te', e')) #(L.memP (t', r') bs0')
      #(fun _ -> exists (t: typ) (r: exp). L.memP (t, r) bs /\ tsim xi r r')
      (fun _ -> ())
      (fun _ -> binds_mem xi bs0 bs0' t' r')

let rec binds_nth (xi: ren) (bs bs': list (typ & exp)) (k: nat)
  : Lemma (requires tsim_binds xi bs bs')
          (ensures (match L.nth bs k, L.nth bs' k with
                    | Some (_, r), Some (_, r') -> tsim xi r r'
                    | None, None -> True
                    | _ -> False))
          (decreases bs) =
  match bs, bs' with
  | [], [] -> ()
  | _ :: bs0, _ :: bs0' -> if k = 0 then () else binds_nth xi bs0 bs0' (k - 1)

let rec binds_length (xi: ren) (bs bs': list (typ & exp))
  : Lemma (requires tsim_binds xi bs bs') (ensures L.length bs == L.length bs') (decreases bs) =
  match bs, bs' with
  | [], [] -> ()
  | _ :: bs0, _ :: bs0' -> binds_length xi bs0 bs0'

let rec exps_children (xi: ren) (ve ve': venv) (je je': jenv) (es es': list exp) (c': child)
  : Lemma (requires tsim_exps xi es es' /\ venv_rel xi ve ve' /\ jenv_rel je je' /\
                    L.memP c' (L.map (mk ve' je') es'))
          (ensures exists (c: child). L.memP c (L.map (mk ve je) es) /\ crel c c') (decreases es) =
  match es, es' with
  | e :: es0, e' :: es0' ->
    FStar.Classical.or_elim #(c' == mk ve' je' e') #(L.memP c' (L.map (mk ve' je') es0'))
      #(fun _ -> exists (c: child). L.memP c (L.map (mk ve je) es) /\ crel c c')
      (fun _ -> crel_intro xi ve je e ve' je' e')
      (fun _ -> exps_children xi ve ve' je je' es0 es0' c')

let rec rhs_children (xi: ren) (ve ve': venv) (je je': jenv) (bs bs': list (typ & exp)) (c': child)
  : Lemma (requires tsim_binds xi bs bs' /\ venv_rel xi ve ve' /\ jenv_rel je je' /\
                    L.memP c' (L.map (rhs_child ve' je') bs'))
          (ensures exists (c: child).
                     L.memP c (L.map (rhs_child ve je) bs) /\ crel c c')
          (decreases bs) =
  match bs, bs' with
  | (_, e) :: bs0, (_, e') :: bs0' ->
    FStar.Classical.or_elim #(c' == mk ve' je' e')
      #(L.memP c' (L.map (rhs_child ve' je') bs0'))
      #(fun _ -> exists (c: child).
                   L.memP c (L.map (rhs_child ve je) bs) /\ crel c c')
      (fun _ -> crel_intro xi ve je e ve' je' e')
      (fun _ -> rhs_children xi ve ve' je je' bs0 bs0' c')

let rec cells_children (xi: ren) (ve ve': venv) (je je': jenv) (th th': list (key & exp))
  (c': child)
  : Lemma (requires tsim_cells xi th th' /\ venv_rel xi ve ve' /\ jenv_rel je je' /\
                    L.memP c' (L.map (cell_child ve' je') th'))
          (ensures exists (c: child).
                     L.memP c (L.map (cell_child ve je) th) /\ crel c c')
          (decreases th) =
  match th, th' with
  | (_, e) :: th0, (_, e') :: th0' ->
    FStar.Classical.or_elim #(c' == mk ve' je' e')
      #(L.memP c' (L.map (cell_child ve' je') th0'))
      #(fun _ -> exists (c: child).
                   L.memP c (L.map (cell_child ve je) th) /\ crel c c')
      (fun _ -> crel_intro xi ve je e ve' je' e')
      (fun _ -> cells_children xi ve ve' je je' th0 th0' c')

let rec clause_children_rel (xi: ren) (ve ve': venv) (je je': jenv) (cs cs': list clause)
  (c': child)
  : Lemma (requires tsim_cls xi cs cs' /\ venv_rel xi ve ve' /\ jenv_rel je je' /\
                    L.memP c' (clause_children ve' je' cs'))
          (ensures exists (c: child). L.memP c (clause_children ve je cs) /\ crel c c')
          (decreases cs) =
  match cs, cs' with
  | CFull _ _ _ _ b :: cs0, CFull _ _ _ _ b' :: cs0' ->
    FStar.Classical.or_elim #(c' == mk (VNone :: VNone :: ve') je' b')
      #(L.memP c' (clause_children ve' je' cs0'))
      #(fun _ -> exists (c: child). L.memP c (clause_children ve je cs) /\ crel c c')
      (fun _ ->
        venv_cons xi (up_ren xi) VNone VNone ve ve';
        venv_cons (up_ren xi) (upn_ren 2 xi) VNone VNone (VNone :: ve) (VNone :: ve');
        crel_intro (upn_ren 2 xi) (VNone :: VNone :: ve) je b (VNone :: VNone :: ve') je' b')
      (fun _ -> clause_children_rel xi ve ve' je je' cs0 cs0' c')
  | CFast _ _ _ b :: cs0, CFast _ _ _ b' :: cs0' ->
    FStar.Classical.or_elim #(c' == mk (VNone :: ve') je' b')
      #(L.memP c' (clause_children ve' je' cs0'))
      #(fun _ -> exists (c: child). L.memP c (clause_children ve je cs) /\ crel c c')
      (fun _ ->
        venv_cons xi (up_ren xi) VNone VNone ve ve';
        crel_intro (up_ren xi) (VNone :: ve) je b (VNone :: ve') je' b')
      (fun _ -> clause_children_rel xi ve ve' je je' cs0 cs0' c')

(* The entry a `bind` pushes. *)
let bind_entry_rel (xc: ren) (cve cve': venv) (je je': jenv) (es es': list exp) (o: occ)
  : Lemma (requires venv_rel xc cve cve' /\ jenv_rel je je' /\ tsim_exps xc es es')
          (ensures ent_rel (bind_entry cve je es o) (bind_entry cve' je' es' o)) =
  exps_nth xc es es' (occ_root o);
  match L.nth es (occ_root o), L.nth es' (occ_root o) with
  | Some e, Some e' ->
    introduce exists (xi: ren). venv_rel xi cve cve' /\ tsim xi e e' with xc and ()
  | _ -> ()

(* A decision tree of related `case`s: the case's scrutinees and
   environment, and the tree's own environment and renaming. *)
let dtrel (xc: ren) (cve: venv) (es: list exp) (cve': venv) (es': list exp) (je je': jenv) : prop =
  venv_rel xc cve cve' /\ jenv_rel je je' /\ tsim_exps xc es es'

let rec dt_children_rel (xc xt: ren) (cve: venv) (es: list exp) (cve': venv) (es': list exp)
  (ve ve': venv) (je je': jenv) (dt dt': dtree) (c': child)
  : Lemma (requires dtrel xc cve es cve' es' je je' /\ venv_rel xt ve ve' /\ tsim_dt xt dt dt' /\
                    L.memP c' (dt_children cve' es' ve' je' dt'))
          (ensures exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
          (decreases dt) =
  match dt, dt' with
  | DLeaf e, DLeaf e' -> crel_intro xt ve je e ve' je' e'
  | DBind o dt0, DBind _ dt0' ->
    bind_entry_rel xc cve cve' je je' es es' o;
    venv_cons xt (up_ren xt) (bind_entry cve je es o) (bind_entry cve' je' es' o) ve ve';
    dt_children_rel xc (up_ren xt) cve es cve' es' (bind_entry cve je es o :: ve)
      (bind_entry cve' je' es' o :: ve') je je' dt0 dt0' c'
  | DSwitchCtor _ bs df, DSwitchCtor _ bs' df' | DSwitchKey _ bs df, DSwitchKey _ bs' df' ->
    LP.append_memP (brs_children cve' es' ve' je' bs') (odt_children cve' es' ve' je' df') c';
    FStar.Classical.or_elim #(L.memP c' (brs_children cve' es' ve' je' bs'))
      #(L.memP c' (odt_children cve' es' ve' je' df'))
      #(fun _ -> exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
      (fun _ ->
        brs_children_rel xc xt cve es cve' es' ve ve' je je' bs bs' c';
        eliminate exists (c: child). L.memP c (brs_children cve es ve je bs) /\ crel c c'
        with LP.append_memP (brs_children cve es ve je bs) (odt_children cve es ve je df) c)
      (fun _ ->
        odt_children_rel xc xt cve es cve' es' ve ve' je je' df df' c';
        eliminate exists (c: child). L.memP c (odt_children cve es ve je df) /\ crel c c'
        with LP.append_memP (brs_children cve es ve je bs) (odt_children cve es ve je df) c)
  | DSwitchLit _ bs df, DSwitchLit _ bs' df' ->
    LP.append_memP (brs_children cve' es' ve' je' bs') (dt_children cve' es' ve' je' df') c';
    FStar.Classical.or_elim #(L.memP c' (brs_children cve' es' ve' je' bs'))
      #(L.memP c' (dt_children cve' es' ve' je' df'))
      #(fun _ -> exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
      (fun _ ->
        brs_children_rel xc xt cve es cve' es' ve ve' je je' bs bs' c';
        eliminate exists (c: child). L.memP c (brs_children cve es ve je bs) /\ crel c c'
        with LP.append_memP (brs_children cve es ve je bs) (dt_children cve es ve je df) c)
      (fun _ ->
        dt_children_rel xc xt cve es cve' es' ve ve' je je' df df' c';
        eliminate exists (c: child). L.memP c (dt_children cve es ve je df) /\ crel c c'
        with LP.append_memP (brs_children cve es ve je bs) (dt_children cve es ve je df) c)
  | DGuard e dt1 dt2, DGuard e' dt1' dt2' ->
    let l1 = dt_children cve es ve je dt1 in
    let l2 = dt_children cve es ve je dt2 in
    let l1' = dt_children cve' es' ve' je' dt1' in
    let l2' = dt_children cve' es' ve' je' dt2' in
    LP.append_memP l1' l2' c';
    FStar.Classical.or_elim #(c' == mk ve' je' e') #(L.memP c' (L.append l1' l2'))
      #(fun _ -> exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
      (fun _ -> crel_intro xt ve je e ve' je' e')
      (fun _ ->
        FStar.Classical.or_elim #(L.memP c' l1') #(L.memP c' l2')
          #(fun _ -> exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
          (fun _ ->
            dt_children_rel xc xt cve es cve' es' ve ve' je je' dt1 dt1' c';
            eliminate exists (c: child). L.memP c l1 /\ crel c c'
            with LP.append_memP l1 l2 c)
          (fun _ ->
            dt_children_rel xc xt cve es cve' es' ve ve' je je' dt2 dt2' c';
            eliminate exists (c: child). L.memP c l2 /\ crel c c'
            with LP.append_memP l1 l2 c))

and odt_children_rel (xc xt: ren) (cve: venv) (es: list exp) (cve': venv) (es': list exp)
  (ve ve': venv) (je je': jenv) (df df': option dtree) (c': child)
  : Lemma (requires dtrel xc cve es cve' es' je je' /\ venv_rel xt ve ve' /\ tsim_odt xt df df' /\
                    L.memP c' (odt_children cve' es' ve' je' df'))
          (ensures exists (c: child). L.memP c (odt_children cve es ve je df) /\ crel c c')
          (decreases df) =
  match df, df' with
  | Some dt, Some dt' -> dt_children_rel xc xt cve es cve' es' ve ve' je je' dt dt' c'

and brs_children_rel (#lb: eqtype) (xc xt: ren) (cve: venv) (es: list exp) (cve': venv)
  (es': list exp) (ve ve': venv) (je je': jenv) (bs bs': list (lb & dtree)) (c': child)
  : Lemma (requires dtrel xc cve es cve' es' je je' /\ venv_rel xt ve ve' /\ tsim_brs xt bs bs' /\
                    L.memP c' (brs_children cve' es' ve' je' bs'))
          (ensures exists (c: child). L.memP c (brs_children cve es ve je bs) /\ crel c c')
          (decreases bs) =
  match bs, bs' with
  | (_, dt) :: bs0, (_, dt') :: bs0' ->
    let l1 = dt_children cve es ve je dt in
    let l2 = brs_children cve es ve je bs0 in
    LP.append_memP (dt_children cve' es' ve' je' dt') (brs_children cve' es' ve' je' bs0') c';
    FStar.Classical.or_elim #(L.memP c' (dt_children cve' es' ve' je' dt'))
      #(L.memP c' (brs_children cve' es' ve' je' bs0'))
      #(fun _ -> exists (c: child). L.memP c (brs_children cve es ve je bs) /\ crel c c')
      (fun _ ->
        dt_children_rel xc xt cve es cve' es' ve ve' je je' dt dt' c';
        eliminate exists (c: child). L.memP c l1 /\ crel c c'
        with LP.append_memP l1 l2 c)
      (fun _ ->
        brs_children_rel xc xt cve es cve' es' ve ve' je je' bs0 bs0' c';
        eliminate exists (c: child). L.memP c l2 /\ crel c c'
        with LP.append_memP l1 l2 c)

let has_rel (l: list child) (c': child) : prop = exists (c: child). L.memP c l /\ crel c c'

let app_rel (l1 l2 l1' l2': list child) (c': child)
  : Lemma (requires L.memP c' (L.append l1' l2') /\
                    (L.memP c' l1' ==> has_rel l1 c') /\ (L.memP c' l2' ==> has_rel l2 c'))
          (ensures has_rel (L.append l1 l2) c') =
  LP.append_memP l1' l2' c';
  introduce forall (c: child). L.memP c l1 \/ L.memP c l2 ==> L.memP c (L.append l1 l2)
  with LP.append_memP l1 l2 c

let cons_rel (x: child) (l: list child) (x': child) (l': list child) (c': child)
  : Lemma (requires L.memP c' (x' :: l') /\ (c' == x' ==> crel x x') /\
                    (L.memP c' l' ==> has_rel l c'))
          (ensures has_rel (x :: l) c') = ()

let one_child (x x' c': child)
  : Lemma (requires L.memP c' [x'] /\ crel x x') (ensures has_rel [x] c') =
  assert (L.memP x [x])

let two_child (x y x' y' c': child)
  : Lemma (requires L.memP c' [x'; y'] /\ crel x x' /\ crel y y') (ensures has_rel [x; y] c') =
  FStar.Classical.or_elim #(c' == x') #(L.memP c' [y']) #(fun _ -> has_rel [x; y] c')
    (fun _ -> assert (L.memP x [x; y]))
    (fun _ -> assert (L.memP y [x; y]))

(* The immediate subexpressions of related terms. *)
let children_letrec (ve: venv) (je: jenv) (bs: list (typ & exp)) (b: exp)
  : Lemma (children ve je (ELetRec bs b) ==
           L.append (L.map (rhs_child (push_rec ve je bs) je) bs) [mk (push_rec ve je bs) je b]) =
  assert (children ve je (ELetRec bs b) ==
          L.append (L.map (rhs_child (push_rec ve je bs) je) bs) [mk (push_rec ve je bs) je b])
    by (T.norm [delta_only [`%children; `%rhs_child]; iota; zeta]; T.trefl ())

let children_region_open (ve: venv) (je: jenv) (a: atom) (th: list (key & exp)) (b: exp)
  : Lemma (children ve je (ERegionOpen a th b) ==
           L.append (L.map (cell_child ve je) th) [mk ve je b]) =
  assert (children ve je (ERegionOpen a th b)
      == L.append (L.map (cell_child ve je) th) [mk ve je b])
    by (T.norm [delta_only [`%children; `%cell_child]; iota; zeta]; T.trefl ())

let children_rel_x (xi: ren) (ve: venv) (je: jenv) (e: exp) (ve': venv) (je': jenv) (e': exp)
  (c': child)
  : Lemma (requires jenv_rel je je' /\ venv_rel xi ve ve' /\ tsim xi e e' /\
                    L.memP c' (children ve' je' e'))
          (ensures has_rel (children ve je e) c') =
  let one (b b': exp) : Lemma (requires tsim xi b b' /\ L.memP c' [mk ve' je' b'])
                              (ensures has_rel [mk ve je b] c') =
    crel_intro xi ve je b ve' je' b';
    one_child (mk ve je b) (mk ve' je' b') c'
  in
  let two (b1 b2 b1' b2': exp)
    : Lemma (requires tsim xi b1 b1' /\ tsim xi b2 b2' /\ L.memP c' [mk ve' je' b1'; mk ve' je' b2'])
            (ensures has_rel [mk ve je b1; mk ve je b2] c') =
    crel_intro xi ve je b1 ve' je' b1';
    crel_intro xi ve je b2 ve' je' b2';
    two_child (mk ve je b1) (mk ve je b2) (mk ve' je' b1') (mk ve' je' b2') c'
  in
  match e, e' with
  | ELam _ _ b, ELam _ _ b' ->
    venv_cons xi (up_ren xi) VNone VNone ve ve';
    crel_intro (up_ren xi) (VNone :: ve) je b (VNone :: ve') je' b';
    one_child (mk (VNone :: ve) je b) (mk (VNone :: ve') je' b') c'
  | ETyLam _ b, ETyLam _ b' -> one b b'
  | ETyApp b _, ETyApp b' _ -> one b b'
  | ECLam _ b, ECLam _ b' -> one b b'
  | ECApp b, ECApp b' -> one b b'
  | ESelect _ b, ESelect _ b' -> one b b'
  | ERestrict _ b, ERestrict _ b' -> one b b'
  | EInject _ _ b, EInject _ _ b' -> one b b'
  | EWeaken _ _ b, EWeaken _ _ b' -> one b b'
  | EAbsurd _ b, EAbsurd _ b' -> one b b'
  | EPerform _ _ _ b, EPerform _ _ _ b' -> one b b'
  | EOpenEff _ b, EOpenEff _ b' -> one b b'
  | EWriteCell _ _ b, EWriteCell _ _ b' -> one b b'
  | EOpenEffC _ b, EOpenEffC _ b' -> one b b'
  | EFill _ b, EFill _ b' -> one b b'
  | EApp e1 e2, EApp e1' e2' -> two e1 e2 e1' e2'
  | EExtend _ e1 e2, EExtend _ e1' e2' -> two e1 e2 e1' e2'
  | EUpdate _ e1 e2, EUpdate _ e1' e2' -> two e1 e2 e1' e2'
  | EMerge e1 e2, EMerge e1' e2' -> two e1 e2 e1' e2'
  | ELet _ e1 e2, ELet _ e1' e2' ->
    crel_intro xi ve je e1 ve' je' e1';
    introduce exists (x: ren). venv_rel x ve ve' /\ tsim x e1 e1' with xi and ();
    venv_cons xi (up_ren xi) (VLat ve je e1) (VLat ve' je' e1') ve ve';
    crel_intro (up_ren xi) (push_let ve je e1) je e2 (push_let ve' je' e1') je' e2';
    two_child (mk ve je e1) (mk (push_let ve je e1) je e2) (mk ve' je' e1')
      (mk (push_let ve' je' e1') je' e2') c'
  | ELetRec bs b, ELetRec bs' b' ->
    let n = L.length bs in
    children_letrec ve je bs b; children_letrec ve' je' bs' b';
    push_rec_rel xi ve ve' je je' bs bs';
    let pv = push_rec ve je bs in
    let pv' = push_rec ve' je' bs' in
    crel_intro (upn_ren n xi) pv je b pv' je' b';
    FStar.Classical.move_requires (rhs_children (upn_ren n xi) pv pv' je je' bs bs') c';
    FStar.Classical.move_requires (one_child (mk pv je b) (mk pv' je' b')) c';
    app_rel (L.map (rhs_child pv je) bs) [mk pv je b]
      (L.map (rhs_child pv' je') bs') [mk pv' je' b'] c'
  | ECase es dt, ECase es' dt' | EMatch es dt, EMatch es' dt' ->
    FStar.Classical.move_requires (exps_children xi ve ve' je je' es es') c';
    FStar.Classical.move_requires
      (dt_children_rel xi xi ve es ve' es' ve ve' je je' dt dt') c';
    app_rel (L.map (mk ve je) es) (dt_children ve es ve je dt)
      (L.map (mk ve' je') es') (dt_children ve' es' ve' je' dt') c'
  | ELetJoin ts _ e1 e2, ELetJoin ts' _ e1' e2' ->
    join_def_rel xi ve ve' je je' ts ts' e1 e2 e1' e2';
    join_scope_rel (join_def ve je ts e1 e2) (join_def ve' je' ts' e1' e2') c'
  | EJump _ es, EJump _ es' -> exps_children xi ve ve' je je' es es' c'
  | EHandle b h, EHandle b' h' ->
    crel_intro xi ve je b ve' je' b';
    venv_cons xi (up_ren xi) VNone VNone ve ve';
    crel_intro (up_ren xi) (VNone :: ve) je h.h_ret (VNone :: ve') je' h'.h_ret;
    FStar.Classical.move_requires
      (clause_children_rel xi ve ve' je je' h.h_clauses h'.h_clauses) c';
    FStar.Classical.move_requires
      (cons_rel (mk (VNone :: ve) je h.h_ret) (clause_children ve je h.h_clauses)
        (mk (VNone :: ve') je' h'.h_ret) (clause_children ve' je' h'.h_clauses)) c';
    cons_rel (mk ve je b) (mk (VNone :: ve) je h.h_ret :: clause_children ve je h.h_clauses)
      (mk ve' je' b') (mk (VNone :: ve') je' h'.h_ret :: clause_children ve' je' h'.h_clauses) c'
  | ERegion _ es b, ERegion _ es' b' ->
    FStar.Classical.move_requires (one b) b';
    FStar.Classical.move_requires (exps_children xi ve ve' je je' es es') c';
    app_rel (L.map (mk ve je) es) [mk ve je b] (L.map (mk ve' je') es') [mk ve' je' b'] c'
  | ERegionOpen a th b, ERegionOpen a' th' b' ->
    children_region_open ve je a th b; children_region_open ve' je' a' th' b';
    FStar.Classical.move_requires (one b) b';
    FStar.Classical.move_requires (cells_children xi ve ve' je je' th th') c';
    app_rel (L.map (cell_child ve je) th) [mk ve je b]
      (L.map (cell_child ve' je') th') [mk ve' je' b'] c'
  | _ -> ()

let children_rel (c c' c1': child)
  : Lemma (requires crel c c' /\ L.memP c1' (children c'.cv c'.cj c'.ce))
          (ensures has_rel (children c.cv c.cj c.ce) c1') =
  eliminate exists (xi: ren). venv_rel xi c.cv c'.cv /\ tsim xi c.ce c'.ce
  with children_rel_x xi c.cv c.cj c.ce c'.cv c'.cj c'.ce c1'

let rec sim_sub (#c' #s': child) (p: sub c' s') (c: child)
  : Lemma (requires crel c c') (ensures exists (s: child). crel s s' /\ ex (sub c s))
          (decreases p) =
  match p with
  | SubHere _ -> ex_intro (SubHere c)
  | SubChild #_ #c1' #_ _ p1 ->
    children_rel c c' c1';
    eliminate exists (c1: child). L.memP c1 (children c.cv c.cj c.ce) /\ crel c1 c1'
    with (sim_sub p1 c1;
          eliminate exists (s: child). crel s s' /\ ex (sub c1 s)
          with (ex_map #(sub c1 s) #(sub c s) (fun q1 -> SubChild #c #c1 #s () q1)))

(* The parts a rule reads off a form. *)

let through_rel (xi: ren) (e e': exp)
  : Lemma (requires tsim xi e e' /\ Some? (through e'))
          (ensures Some? (through e) /\ tsim xi (Some?.v (through e)) (Some?.v (through e'))) = ()

let takes_rel (xi: ren) (e e': exp)
  : Lemma (requires tsim xi e e' /\ Some? (takes e'))
          (ensures Some? (takes e) /\ tsim xi (Some?.v (takes e)) (Some?.v (takes e'))) = ()

let pair_rel (xi: ren) (a b a' b' x': exp)
  : Lemma (requires tsim xi a a' /\ tsim xi b b' /\ L.memP x' [a'; b'])
          (ensures exists (x: exp). L.memP x [a; b] /\ tsim xi x x') =
  FStar.Classical.or_elim #(x' == a') #(L.memP x' [b'])
    #(fun _ -> exists (x: exp). L.memP x [a; b] /\ tsim xi x x')
    (fun _ -> assert (L.memP a [a; b]))
    (fun _ -> assert (L.memP b [a; b]))

let one_rel (xi: ren) (a a' x': exp)
  : Lemma (requires tsim xi a a' /\ L.memP x' [a'])
          (ensures exists (x: exp). L.memP x [a] /\ tsim xi x x') =
  assert (L.memP a [a])

let builds_rel (xi: ren) (e e' b': exp)
  : Lemma (requires tsim xi e e' /\ L.memP b' (builds e'))
          (ensures exists (b: exp). L.memP b (builds e) /\ tsim xi b b') =
  match e, e' with
  | EExtend _ e1 e2, EExtend _ e1' e2' | EUpdate _ e1 e2, EUpdate _ e1' e2'
  | EMerge e1 e2, EMerge e1' e2' -> pair_rel xi e1 e2 e1' e2' b'
  | EInject _ _ b, EInject _ _ b0' -> one_rel xi b b0' b'
  | _ -> ()

let rec decompose_rel (xi: ren) (e e': exp)
  : Lemma (requires tsim xi e e')
          (ensures (match decompose_global_app e, decompose_global_app e' with
                    | Some (q, _, args), Some (q', _, args') ->
                      q == q' /\ value_count args == value_count args'
                    | None, None -> True
                    | _ -> False))
          (decreases e) =
  match e, e' with
  | EApp f v, EApp f' v' ->
    decompose_rel xi f f';
    (match decompose_global_app f, decompose_global_app f' with
     | Some (_, _, args), Some (_, _, args') ->
       value_count_append args [SVal v]; value_count_append args' [SVal v']
     | _ -> ())
  | ETyApp f t, ETyApp f' t' ->
    decompose_rel xi f f';
    (match decompose_global_app f, decompose_global_app f' with
     | Some (_, _, args), Some (_, _, args') ->
       value_count_append args [STy t]; value_count_append args' [STy t']
     | _ -> ())
  | ECApp f, ECApp f' ->
    decompose_rel xi f f';
    (match decompose_global_app f, decompose_global_app f' with
     | Some (_, _, args), Some (_, _, args') ->
       value_count_append args [SConstr]; value_count_append args' [SConstr]
     | _ -> ())
  | _ -> ()

let spine_app_rel (sg: sig) (g g': group) (xi: ren) (e e': exp)
  : Lemma (requires tsim xi e e' /\ (forall (q: qname). g.gmem q == g'.gmem q))
          (ensures spine_app sg g e == spine_app sg g' e') =
  decompose_rel xi e e'

let spine_parts_rel (sg: sig) (g g': group) (xi: ren) (e e' b': exp)
  : Lemma (requires tsim xi e e' /\ (forall (q: qname). g.gmem q == g'.gmem q) /\
                    L.memP b' (spine_parts sg g' e'))
          (ensures exists (b: exp). L.memP b (spine_parts sg g e) /\ tsim xi b b') =
  spine_app_rel sg g g' xi e e';
  match e, e' with
  | EApp f v, EApp f' v' -> if spine_app sg g e then pair_rel xi f v f' v' b'
  | _ -> ()

let default_parts_rel (sg: sig) (g g': group) (xi: ren) (e e' b': exp)
  : Lemma (requires tsim xi e e' /\ (forall (q: qname). g.gmem q == g'.gmem q) /\
                    L.memP b' (default_parts sg g' e'))
          (ensures exists (b: exp). L.memP b (default_parts sg g e) /\ tsim xi b b') =
  spine_app_rel sg g g' xi e e';
  match e, e' with
  | EApp f v, EApp f' v' -> if not (spine_app sg g e) then pair_rel xi f v f' v' b'
  | EPerform _ _ _ b, EPerform _ _ _ b0' | EWriteCell _ _ b, EWriteCell _ _ b0'
  | EFill _ b, EFill _ b0' -> one_rel xi b b0' b'
  | _ -> ()

let scrut_rel (xi: ren) (e e': exp)
  : Lemma (requires tsim xi e e' /\ Some? (scrutinised e'))
          (ensures Some? (scrutinised e) /\
                   tsim_exps xi (fst (Some?.v (scrutinised e))) (fst (Some?.v (scrutinised e'))) /\
                   tsim_dt xi (snd (Some?.v (scrutinised e))) (snd (Some?.v (scrutinised e')))) = ()

let is_whole_rel (xi: ren) (e e': exp)
  : Lemma (requires tsim xi e e') (ensures is_whole e == is_whole e') = ()

let rec brs_snd_mem (#lb: eqtype) (xi: ren) (bs bs': list (lb & dtree)) (s': dtree)
  : Lemma (requires tsim_brs xi bs bs' /\ L.memP s' (L.map snd bs'))
          (ensures exists (s: dtree). L.memP s (L.map snd bs) /\ tsim_dt xi s s') (decreases bs) =
  match bs, bs' with
  | (_, dt) :: bs0, (_, dt') :: bs0' ->
    FStar.Classical.or_elim #(s' == dt') #(L.memP s' (L.map snd bs0'))
      #(fun _ -> exists (s: dtree). L.memP s (L.map snd bs) /\ tsim_dt xi s s')
      (fun _ -> ())
      (fun _ -> brs_snd_mem xi bs0 bs0' s')

let has_dt (xi: ren) (l: list dtree) (s': dtree) : prop =
  exists (s: dtree). L.memP s l /\ tsim_dt xi s s'

let app_dt (xi: ren) (l1 l2 l1' l2': list dtree) (s': dtree)
  : Lemma (requires L.memP s' (L.append l1' l2') /\
                    (L.memP s' l1' ==> has_dt xi l1 s') /\ (L.memP s' l2' ==> has_dt xi l2 s'))
          (ensures has_dt xi (L.append l1 l2) s') =
  LP.append_memP l1' l2' s';
  introduce forall (s: dtree). L.memP s l1 \/ L.memP s l2 ==> L.memP s (L.append l1 l2)
  with LP.append_memP l1 l2 s

let one_dt (xi: ren) (x x' s': dtree)
  : Lemma (requires tsim_dt xi x x' /\ L.memP s' [x']) (ensures has_dt xi [x] s') =
  assert (L.memP x [x])

let odt_list_rel (xi: ren) (df df': option dtree) (s': dtree)
  : Lemma (requires tsim_odt xi df df' /\ L.memP s' (match df' with Some d -> [d] | None -> []))
          (ensures has_dt xi (match df with Some d -> [d] | None -> []) s') =
  match df, df' with
  | Some d, Some d' -> one_dt xi d d' s'
  | _ -> ()

let switch_rel (xi: ren) (dt dt' s': dtree)
  : Lemma (requires tsim_dt xi dt dt' /\ L.memP s' (switch_subtrees dt'))
          (ensures has_dt xi (switch_subtrees dt) s') =
  match dt, dt' with
  | DSwitchCtor _ bs df, DSwitchCtor _ bs' df' ->
    FStar.Classical.move_requires (brs_snd_mem xi bs bs') s';
    FStar.Classical.move_requires (odt_list_rel xi df df') s';
    app_dt xi (L.map snd bs) (match df with Some d -> [d] | None -> [])
      (L.map snd bs') (match df' with Some d -> [d] | None -> []) s'
  | DSwitchKey _ bs df, DSwitchKey _ bs' df' ->
    FStar.Classical.move_requires (brs_snd_mem xi bs bs') s';
    FStar.Classical.move_requires (odt_list_rel xi df df') s';
    app_dt xi (L.map snd bs) (match df with Some d -> [d] | None -> [])
      (L.map snd bs') (match df' with Some d -> [d] | None -> []) s'
  | DSwitchLit _ bs df, DSwitchLit _ bs' df' ->
    FStar.Classical.move_requires (brs_snd_mem xi bs bs') s';
    FStar.Classical.move_requires (one_dt xi df df') s';
    app_dt xi (L.map snd bs) [df] (L.map snd bs') [df'] s'
  | _ -> ()

let join_arg_rel (xi: ren) (d d': jentry) (p: nat) (es es': list exp)
  : Lemma (requires jent_rel d d' /\ tsim_exps xi es es' /\ Some? (join_arg d' p es'))
          (ensures Some? (join_arg d p es) /\
                   tsim xi (Some?.v (join_arg d p es)) (Some?.v (join_arg d' p es'))) =
  match d, d' with
  | JDef _ _ n _ _, JDef _ _ _ _ _ -> if p < n then exps_nth xi es es' (n - 1 - p)

let ent_inv_mem (v: ventry) (k: nat) : Lemma (requires ent_rel v (VMem k)) (ensures v == VMem k) =
  match v with
  | VMem _ -> ()
  | _ -> ()

let jump_target (d0 d0': jentry) (p: nat) (s: child) (ve3': venv) (je3': jenv) (j: nat)
  (es': list exp) (a': exp)
  : Lemma (requires jent_rel d0 d0' /\ crel s (mk ve3' je3' (EJump j es')) /\
                    j + L.length (join_jenv d0') == L.length je3' /\ join_arg d0' p es' == Some a')
          (ensures EJump? s.ce /\
                   s == mk s.cv s.cj (EJump j (EJump?._1 s.ce)) /\
                   j + L.length (join_jenv d0) == L.length s.cj /\
                   Some? (join_arg d0 p (EJump?._1 s.ce)) /\
                   crel3 s.cv s.cj (Some?.v (join_arg d0 p (EJump?._1 s.ce))) ve3' je3' a') =
  join_jenv_length d0 d0';
  jenv_length s.cj je3';
  eliminate exists (x3: ren). venv_rel x3 s.cv ve3' /\ tsim x3 s.ce (EJump j es')
  with (match s with
        | { cv = ve3; cj = je3; ce = EJump _ es } ->
          join_arg_rel x3 d0 d0' p es es';
          crel_intro x3 ve3 je3 (Some?.v (join_arg d0 p es)) ve3' je3' a'
        | _ -> ())

(* The target of a jump that hands an argument to a join parameter. *)
let join_arg_case (xi: ren) (ve ve': venv) (i: nat) (d0': jentry) (p: nat) (c': child)
  (ve3': venv) (je3': jenv) (j: nat) (es': list exp) (a': exp)
  (sb': sub c' (mk ve3' je3' (EJump j es')))
  : Lemma (requires venv_rel xi ve ve' /\ vlook ve' (xi i) == VArg d0' p /\
                    L.memP c' (join_scope d0') /\ j + L.length (join_jenv d0') == L.length je3' /\
                    join_arg d0' p es' == Some a')
          (ensures VArg? (vlook ve i) /\ VArg?.p (vlook ve i) == p /\
                   (exists (c: child) (ve3: venv) (je3: jenv) (es: list exp) (a: exp).
                      L.memP c (join_scope (VArg?.d (vlook ve i))) /\
                      ex (sub c (mk ve3 je3 (EJump j es))) /\
                      j + L.length (join_jenv (VArg?.d (vlook ve i))) == L.length je3 /\
                      join_arg (VArg?.d (vlook ve i)) p es == Some a /\
                      crel3 ve3 je3 a ve3' je3' a')) =
  venv_lookup xi ve ve' i;
  match vlook ve i with
  | VArg d0 _ ->
    join_scope_rel d0 d0' c';
    join_jenv_length d0 d0';
    eliminate exists (c: child). L.memP c (join_scope d0) /\ crel c c'
    with (sim_sub sb' c;
          eliminate exists (s: child). crel s (mk ve3' je3' (EJump j es')) /\ ex (sub c s)
          with (jump_target d0 d0' p s ve3' je3' j es' a';
                introduce exists (c: child) (ve3: venv) (je3: jenv) (es: list exp) (a: exp).
                  L.memP c (join_scope d0) /\ ex (sub c (mk ve3 je3 (EJump j es))) /\
                  j + L.length (join_jenv d0) == L.length je3 /\ join_arg d0 p es == Some a /\
                  crel3 ve3 je3 a ve3' je3' a'
                with c s.cv s.cj (EJump?._1 s.ce) (Some?.v (join_arg d0 p (EJump?._1 s.ce)))
                and ()))
  | _ -> ()

let tsim_var_inv (xi: ren) (e e': exp)
  : Lemma (requires tsim xi e e' /\ EVar? e') (ensures EVar? e /\ EVar?._0 e' == xi (EVar?._0 e)) =
  match e with
  | EVar _ -> ()
  | _ -> ()

(* A member of a nested group, read through its variable. *)
let local_rec_case (xi: ren) (ve ve': venv) (i: nat) (ve2': venv) (je2': jenv)
  (bs': list (typ & exp)) (k: nat) (r': exp)
  : Lemma (requires venv_rel xi ve ve' /\ vlook ve' (xi i) == VRec ve2' je2' bs' k /\
                    Some? (L.nth bs' k) /\ snd (Some?.v (L.nth bs' k)) == r')
          (ensures VRec? (vlook ve i) /\ VRec?.k (vlook ve i) == k /\
                   Some? (L.nth (VRec?.bs (vlook ve i)) k) /\
                   crel3 (push_rec (VRec?.ve (vlook ve i)) (VRec?.je (vlook ve i))
                       (VRec?.bs (vlook ve i)))
                     (VRec?.je (vlook ve i)) (snd (Some?.v (L.nth (VRec?.bs (vlook ve i)) k)))
                     (push_rec ve2' je2' bs') je2' r') =
  venv_lookup xi ve ve' i;
  match vlook ve i with
  | VRec ve2 je2 bs _ ->
    let n = L.length bs in
    eliminate exists (x2: ren). venv_rel x2 ve2 ve2' /\ tsim_binds (upn_ren n x2) bs bs'
    with (push_rec_rel x2 ve2 ve2' je2 je2' bs bs';
          binds_nth (upn_ren n x2) bs bs' k;
          let Some (_, r) = L.nth bs k in
          crel_intro (upn_ren n x2) (push_rec ve2 je2 bs) je2 r (push_rec ve2' je2' bs') je2' r')
  | _ -> ()

(* The simulation. *)

let rec sim_imm (#sg: sig) (#g': group) (#ve': venv) (#je': jenv) (#e': exp) (#m: nat)
  (d': reads_imm sg g' ve' je' e' m) (g: group) (ve: venv) (je: jenv) (e: exp)
  : Lemma (requires grel g g' /\ crel3 ve je e ve' je' e')
          (ensures ex (reads_imm sg g ve je e m)) (decreases d') =
  eliminate exists (xi: ren). venv_rel xi ve ve' /\ tsim xi e e'
  with match d' with
  | IMember _ ->
    (match e with
     | EVar i ->
       venv_lookup xi ve ve' i; ent_inv_mem (vlook ve i) m;
       ex_intro #(reads_imm sg g ve je (EVar i) m) (IMember ())
     | _ -> ())
  | IMemberGlobal _ ->
    (match e with
     | EGlobal q ks -> ex_intro #(reads_imm sg g ve je (EGlobal q ks) m) (IMemberGlobal ())
     | _ -> ())
  | IThrough _ d1' ->
    through_rel xi e e';
    let b = Some?.v (through e) in
    crel_intro xi ve je b ve' je' (Some?.v (through e'));
    sim_imm d1' g ve je b;
    ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> IThrough () d1)
  | IBuild #_ #_ #_ #_ #_ #b' _ d1' ->
    builds_rel xi e e' b';
    eliminate exists (b: exp). L.memP b (builds e) /\ tsim xi b b'
    with (crel_intro xi ve je b ve' je' b';
          sim_imm d1' g ve je b;
          ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> IBuild () d1))
  | ITake _ d1' ->
    takes_rel xi e e';
    let b = Some?.v (takes e) in
    crel_intro xi ve je b ve' je' (Some?.v (takes e'));
    sim_imm d1' g ve je b;
    ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> ITake () d1)
  | ISpine #_ #_ #_ #_ #_ #b' _ d1' ->
    spine_parts_rel sg g g' xi e e' b';
    eliminate exists (b: exp). L.memP b (spine_parts sg g e) /\ tsim xi b b'
    with (crel_intro xi ve je b ve' je' b';
          sim_imm d1' g ve je b;
          ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> ISpine () d1))
  | IDefault #_ #_ #_ #_ #_ #b' _ d1' ->
    default_parts_rel sg g g' xi e e' b';
    eliminate exists (b: exp). L.memP b (default_parts sg g e) /\ tsim xi b b'
    with (crel_intro xi ve je b ve' je' b';
          sim_imm d1' g ve je b;
          ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> IDefault () d1))
  | IDefaultLat #_ #_ #_ #_ #_ #b' _ d1' ->
    default_parts_rel sg g g' xi e e' b';
    eliminate exists (b: exp). L.memP b (default_parts sg g e) /\ tsim xi b b'
    with (crel_intro xi ve je b ve' je' b';
          sim_lat d1' g ve je b;
          ex_map #(reads_lat sg g ve je b m) #(reads_imm sg g ve je e m)
            (fun d1 -> IDefaultLat () d1))
  | ILetBound d1' ->
    (match e, e' with
     | ELet t e1 e2, ELet _ e1' _ ->
       crel_intro xi ve je e1 ve' je' e1';
       sim_imm d1' g ve je e1;
       ex_map #(reads_imm sg g ve je e1 m) #(reads_imm sg g ve je (ELet t e1 e2) m)
         (fun d1 -> ILetBound d1)
     | _ -> ())
  | ILetBody d1' ->
    (match e, e' with
     | ELet t e1 e2, ELet _ e1' e2' ->
       introduce exists (x: ren). venv_rel x ve ve' /\ tsim x e1 e1' with xi and ();
       venv_cons xi (up_ren xi) (VLat ve je e1) (VLat ve' je' e1') ve ve';
       crel_intro (up_ren xi) (push_let ve je e1) je e2 (push_let ve' je' e1') je' e2';
       sim_imm d1' g (push_let ve je e1) je e2;
       ex_map #(reads_imm sg g (push_let ve je e1) je e2 m) #(reads_imm sg g ve je (ELet t e1 e2) m)
         (fun d1 -> ILetBody d1)
     | _ -> ())
  | ILetRecRhs #_ #_ #_ #_ #_ #_ #t' #r' _ d1' ->
    (match e, e' with
     | ELetRec bs b, ELetRec bs' _ ->
       let n = L.length bs in
       push_rec_rel xi ve ve' je je' bs bs';
       binds_mem (upn_ren n xi) bs bs' t' r';
       eliminate exists (t: typ) (r: exp). L.memP (t, r) bs /\ tsim (upn_ren n xi) r r'
       with (crel_intro (upn_ren n xi) (push_rec ve je bs) je r (push_rec ve' je' bs') je' r';
             sim_imm d1' g (push_rec ve je bs) je r;
             ex_map #(reads_imm sg g (push_rec ve je bs) je r m)
               #(reads_imm sg g ve je (ELetRec bs b) m)
                 (fun d1 -> ILetRecRhs #sg #g #ve #je #bs #b #t #r #m () d1))
     | _ -> ())
  | ILetRecBody d1' ->
    (match e, e' with
     | ELetRec bs b, ELetRec bs' b' ->
       let n = L.length bs in
       push_rec_rel xi ve ve' je je' bs bs';
       crel_intro (upn_ren n xi) (push_rec ve je bs) je b (push_rec ve' je' bs') je' b';
       sim_imm d1' g (push_rec ve je bs) je b;
       ex_map #(reads_imm sg g (push_rec ve je bs) je b m) #(reads_imm sg g ve je (ELetRec bs b) m)
         (fun d1 -> ILetRecBody d1)
     | _ -> ())
  | ICaseScrut #_ #_ #_ #_ #_ #_ #_ #b' _ _ d1' ->
    scrut_rel xi e e';
    let Some (es, dt) = scrutinised e in
    let Some (es', _) = scrutinised e' in
    exps_mem xi es es' b';
    eliminate exists (b: exp). L.memP b es /\ tsim xi b b'
    with (crel_intro xi ve je b ve' je' b';
          sim_imm d1' g ve je b;
          ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m)
            (fun d1 -> ICaseScrut #sg #g #ve #je #e #es #dt #b #m () () d1))
  | ICaseTree _ d1' ->
    scrut_rel xi e e';
    let Some (es, dt) = scrutinised e in
    sim_imm_dt d1' g ve es ve je dt xi xi;
    ex_map #(reads_imm_dt sg g ve es ve je dt m) #(reads_imm sg g ve je e m)
      (fun d1 -> ICaseTree #sg #g #ve #je #e #es #dt #m () d1)
  | ILetJoin d1' ->
    (match e, e' with
     | ELetJoin ts t e1 e2, ELetJoin ts' _ e1' e2' ->
       join_def_rel xi ve ve' je je' ts ts' e1 e2 e1' e2';
       let je1 = join_def ve je ts e1 e2 :: je in
       crel_intro xi ve je1 e2 ve' (join_def ve' je' ts' e1' e2' :: je') e2';
       sim_imm d1' g ve je1 e2;
       ex_map #(reads_imm sg g ve je1 e2 m) #(reads_imm sg g ve je (ELetJoin ts t e1 e2) m)
         (fun d1 -> ILetJoin d1)
     | _ -> ())
  | IJumpArg #_ #_ #_ #_ #_ #_ #b' _ d1' ->
    (match e, e' with
     | EJump j es, EJump _ es' ->
       exps_mem xi es es' b';
       eliminate exists (b: exp). L.memP b es /\ tsim xi b b'
       with (crel_intro xi ve je b ve' je' b';
             sim_imm d1' g ve je b;
             ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je (EJump j es) m)
               (fun d1 -> IJumpArg #sg #g #ve #je #j #es #b #m () d1))
     | _ -> ())
  | IJumpBody #_ #_ #_ #_ #_ #_ #d0' _ d1' ->
    (match e, e' with
     | EJump j es, EJump _ _ ->
       jenv_lookup je je' j;
       let Some d0 = jlook je j in
       join_body_rel d0 d0';
       sim_imm d1' g (join_body d0).cv (join_body d0).cj (join_body d0).ce;
       ex_map #(reads_imm sg g (join_body d0).cv (join_body d0).cj (join_body d0).ce m)
         #(reads_imm sg g ve je (EJump j es) m)
           (fun d1 -> IJumpBody #sg #g #ve #je #j #es #d0 #m () d1)
     | _ -> ())
  | IWhole #_ #_ #_ #_ #_ #c' #s' _ _ sb' d1' ->
    is_whole_rel xi e e';
    crel_intro xi ve je e ve' je' e';
    children_rel (mk ve je e) (mk ve' je' e') c';
    eliminate exists (c: child). L.memP c (children ve je e) /\ crel c c'
    with (sim_sub sb' c;
          eliminate exists (s: child). crel s s' /\ ex (sub c s)
          with (sim_imm d1' g s.cv s.cj s.ce;
                ex_map2 #(sub c s) #(reads_imm sg g s.cv s.cj s.ce m) #(reads_imm sg g ve je e m)
                  (fun sb d1 -> IWhole #sg #g #ve #je #e #c #s #m () () sb d1)))
  | IWholeLat #_ #_ #_ #_ #_ #c' #s' _ _ sb' d1' ->
    is_whole_rel xi e e';
    crel_intro xi ve je e ve' je' e';
    children_rel (mk ve je e) (mk ve' je' e') c';
    eliminate exists (c: child). L.memP c (children ve je e) /\ crel c c'
    with (sim_sub sb' c;
          eliminate exists (s: child). crel s s' /\ ex (sub c s)
          with (sim_lat d1' g s.cv s.cj s.ce;
                ex_map2 #(sub c s) #(reads_lat sg g s.cv s.cj s.ce m) #(reads_imm sg g ve je e m)
                  (fun sb d1 -> IWholeLat #sg #g #ve #je #e #c #s #m () () sb d1)))

and sim_lat (#sg: sig) (#g': group) (#ve': venv) (#je': jenv) (#e': exp) (#m: nat)
  (d': reads_lat sg g' ve' je' e' m) (g: group) (ve: venv) (je: jenv) (e: exp)
  : Lemma (requires grel g g' /\ crel3 ve je e ve' je' e')
          (ensures ex (reads_lat sg g ve je e m)) (decreases d') =
  eliminate exists (xi: ren). venv_rel xi ve ve' /\ tsim xi e e'
  with match d' with
  | LMember #_ #_ #_ #_ #_ #k #r' _ _ d1' ->
    (match e with
     | EVar i ->
       venv_lookup xi ve ve' i; ent_inv_mem (vlook ve i) k;
       eliminate exists (r: exp). rhs g k == Some r /\ crel3 g.genv [] r g'.genv [] r'
       with (sim_lat d1' g g.genv [] r;
             ex_map #(reads_lat sg g g.genv [] r m) #(reads_lat sg g ve je (EVar i) m)
               (fun d1 -> LMember #sg #g #ve #je #i #k #r #m () () d1))
     | _ -> ())
  | LMemberGlobal #_ #_ #_ #_ #_ #_ #k #r' _ _ d1' ->
    (match e with
     | EGlobal q ks ->
       eliminate exists (r: exp). rhs g k == Some r /\ crel3 g.genv [] r g'.genv [] r'
       with (sim_lat d1' g g.genv [] r;
             ex_map #(reads_lat sg g g.genv [] r m) #(reads_lat sg g ve je (EGlobal q ks) m)
               (fun d1 -> LMemberGlobal #sg #g #ve #je #q #ks #k #r #m () () d1))
     | _ -> ())
  | LLocal #_ #_ #_ #_ #_ #ve2' #je2' #e2' _ d1' ->
    (match e with
     | EVar i ->
       venv_lookup xi ve ve' i;
       (match vlook ve i with
        | VLat ve2 je2 e2 ->
          sim_lat d1' g ve2 je2 e2;
          ex_map #(reads_lat sg g ve2 je2 e2 m) #(reads_lat sg g ve je (EVar i) m)
            (fun d1 -> LLocal #sg #g #ve #je #i #ve2 #je2 #e2 #m () d1)
        | _ -> ())
     | _ -> ())
  | LLocalRec #_ #_ #_ #_ #_ #ve2' #je2' #bs' #k #t' #r' _ _ d1' ->
    tsim_var_inv xi e e';
    let EVar i = e in
    local_rec_case xi ve ve' i ve2' je2' bs' k r';
    let VRec ve2 je2 bs _ = vlook ve i in
    let Some (t, r) = L.nth bs k in
    sim_lat d1' g (push_rec ve2 je2 bs) je2 r;
    ex_map #(reads_lat sg g (push_rec ve2 je2 bs) je2 r m) #(reads_lat sg g ve je (EVar i) m)
      (fun d1 -> LLocalRec #sg #g #ve #je #i #ve2 #je2 #bs #k #t #r #m () () d1)
  | LJoinArg #_ #_ #_ #_ #_ #d0' #p #c' #ve3' #je3' #j #es' #a' #_ _ _ sb' _ _ d1' ->
    tsim_var_inv xi e e';
    let EVar i = e in
    join_arg_case xi ve ve' i d0' p c' ve3' je3' j es' a' sb';
    let d0 = VArg?.d (vlook ve i) in
    eliminate exists (c: child) (ve3: venv) (je3: jenv) (es: list exp) (a: exp).
      L.memP c (join_scope d0) /\ ex (sub c (mk ve3 je3 (EJump j es))) /\
      j + L.length (join_jenv d0) == L.length je3 /\ join_arg d0 p es == Some a /\
      crel3 ve3 je3 a ve3' je3' a'
    with (sim_lat d1' g ve3 je3 a;
          ex_map2 #(sub c (mk ve3 je3 (EJump j es))) #(reads_lat sg g ve3 je3 a m)
            #(reads_lat sg g ve je (EVar i) m)
            (fun sb d1 -> LJoinArg #sg #g #ve #je #i #d0 #p #c #ve3 #je3 #j #es #a #m
               () () sb () () d1))
  | LLam d1' ->
    (match e, e' with
     | ELam t r b, ELam _ _ b' ->
       venv_cons xi (up_ren xi) VNone VNone ve ve';
       crel_intro (up_ren xi) (VNone :: ve) je b (VNone :: ve') je' b';
       sim_imm d1' g (VNone :: ve) je b;
       ex_map #(reads_imm sg g (VNone :: ve) je b m) #(reads_lat sg g ve je (ELam t r b) m)
         (fun d1 -> LLam d1)
     | _ -> ())
  | LLamLat d1' ->
    (match e, e' with
     | ELam t r b, ELam _ _ b' ->
       venv_cons xi (up_ren xi) VNone VNone ve ve';
       crel_intro (up_ren xi) (VNone :: ve) je b (VNone :: ve') je' b';
       sim_lat d1' g (VNone :: ve) je b;
       ex_map #(reads_lat sg g (VNone :: ve) je b m) #(reads_lat sg g ve je (ELam t r b) m)
         (fun d1 -> LLamLat d1)
     | _ -> ())
  | LThrough _ d1' ->
    through_rel xi e e';
    let b = Some?.v (through e) in
    crel_intro xi ve je b ve' je' (Some?.v (through e'));
    sim_lat d1' g ve je b;
    ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LThrough () d1)
  | LBuild #_ #_ #_ #_ #_ #b' _ d1' ->
    builds_rel xi e e' b';
    eliminate exists (b: exp). L.memP b (builds e) /\ tsim xi b b'
    with (crel_intro xi ve je b ve' je' b';
          sim_lat d1' g ve je b;
          ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LBuild () d1))
  | LTake _ d1' ->
    takes_rel xi e e';
    let b = Some?.v (takes e) in
    crel_intro xi ve je b ve' je' (Some?.v (takes e'));
    sim_lat d1' g ve je b;
    ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LTake () d1)
  | LSpine #_ #_ #_ #_ #_ #b' _ d1' ->
    spine_parts_rel sg g g' xi e e' b';
    eliminate exists (b: exp). L.memP b (spine_parts sg g e) /\ tsim xi b b'
    with (crel_intro xi ve je b ve' je' b';
          sim_lat d1' g ve je b;
          ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LSpine () d1))
  | LDefault #_ #_ #_ #_ #_ #b' _ d1' ->
    default_parts_rel sg g g' xi e e' b';
    eliminate exists (b: exp). L.memP b (default_parts sg g e) /\ tsim xi b b'
    with (crel_intro xi ve je b ve' je' b';
          sim_lat d1' g ve je b;
          ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LDefault () d1))
  | LLet d1' ->
    (match e, e' with
     | ELet t e1 e2, ELet _ e1' e2' ->
       introduce exists (x: ren). venv_rel x ve ve' /\ tsim x e1 e1' with xi and ();
       venv_cons xi (up_ren xi) (VLat ve je e1) (VLat ve' je' e1') ve ve';
       crel_intro (up_ren xi) (push_let ve je e1) je e2 (push_let ve' je' e1') je' e2';
       sim_lat d1' g (push_let ve je e1) je e2;
       ex_map #(reads_lat sg g (push_let ve je e1) je e2 m) #(reads_lat sg g ve je (ELet t e1 e2) m)
         (fun d1 -> LLet d1)
     | _ -> ())
  | LLetRec d1' ->
    (match e, e' with
     | ELetRec bs b, ELetRec bs' b' ->
       let n = L.length bs in
       push_rec_rel xi ve ve' je je' bs bs';
       crel_intro (upn_ren n xi) (push_rec ve je bs) je b (push_rec ve' je' bs') je' b';
       sim_lat d1' g (push_rec ve je bs) je b;
       ex_map #(reads_lat sg g (push_rec ve je bs) je b m) #(reads_lat sg g ve je (ELetRec bs b) m)
         (fun d1 -> LLetRec d1)
     | _ -> ())
  | LCase _ d1' ->
    scrut_rel xi e e';
    let Some (es, dt) = scrutinised e in
    sim_lat_dt d1' g ve es ve je dt xi xi;
    ex_map #(reads_lat_dt sg g ve es ve je dt m) #(reads_lat sg g ve je e m)
      (fun d1 -> LCase #sg #g #ve #je #e #es #dt #m () d1)
  | LLetJoin d1' ->
    (match e, e' with
     | ELetJoin ts t e1 e2, ELetJoin ts' _ e1' e2' ->
       join_def_rel xi ve ve' je je' ts ts' e1 e2 e1' e2';
       let je1 = join_def ve je ts e1 e2 :: je in
       crel_intro xi ve je1 e2 ve' (join_def ve' je' ts' e1' e2' :: je') e2';
       sim_lat d1' g ve je1 e2;
       ex_map #(reads_lat sg g ve je1 e2 m) #(reads_lat sg g ve je (ELetJoin ts t e1 e2) m)
         (fun d1 -> LLetJoin d1)
     | _ -> ())
  | LJump #_ #_ #_ #_ #_ #_ #d0' _ d1' ->
    (match e, e' with
     | EJump j es, EJump _ _ ->
       jenv_lookup je je' j;
       let Some d0 = jlook je j in
       join_body_rel d0 d0';
       sim_lat d1' g (join_body d0).cv (join_body d0).cj (join_body d0).ce;
       ex_map #(reads_lat sg g (join_body d0).cv (join_body d0).cj (join_body d0).ce m)
         #(reads_lat sg g ve je (EJump j es) m) (fun d1 -> LJump #sg #g #ve #je #j #es #d0 #m () d1)
     | _ -> ())
  | LWhole #_ #_ #_ #_ #_ #c' #s' _ _ sb' d1' ->
    is_whole_rel xi e e';
    crel_intro xi ve je e ve' je' e';
    children_rel (mk ve je e) (mk ve' je' e') c';
    eliminate exists (c: child). L.memP c (children ve je e) /\ crel c c'
    with (sim_sub sb' c;
          eliminate exists (s: child). crel s s' /\ ex (sub c s)
          with (sim_lat d1' g s.cv s.cj s.ce;
                ex_map2 #(sub c s) #(reads_lat sg g s.cv s.cj s.ce m) #(reads_lat sg g ve je e m)
                  (fun sb d1 -> LWhole #sg #g #ve #je #e #c #s #m () () sb d1)))

and sim_imm_dt (#sg: sig) (#g': group) (#cve': venv) (#es': list exp) (#ve': venv) (#je': jenv)
  (#dt': dtree) (#m: nat)
  (d': reads_imm_dt sg g' cve' es' ve' je' dt' m) (g: group) (cve: venv) (es: list exp) (ve: venv)
  (je: jenv) (dt: dtree) (xc xt: ren)
  : Lemma (requires grel g g' /\ dtrel xc cve es cve' es' je je' /\ venv_rel xt ve ve' /\
                    tsim_dt xt dt dt')
          (ensures ex (reads_imm_dt sg g cve es ve je dt m)) (decreases d') =
  match d' with
  | ITLeaf d1' ->
    (match dt, dt' with
     | DLeaf e, DLeaf e' ->
       crel_intro xt ve je e ve' je' e';
       sim_imm d1' g ve je e;
       ex_map #(reads_imm sg g ve je e m) #(reads_imm_dt sg g cve es ve je (DLeaf e) m)
         (fun d1 -> ITLeaf d1)
     | _ -> ())
  | ITBind d1' ->
    (match dt, dt' with
     | DBind o dt0, DBind _ dt0' ->
       bind_entry_rel xc cve cve' je je' es es' o;
       let v = bind_entry cve je es o in
       venv_cons xt (up_ren xt) v (bind_entry cve' je' es' o) ve ve';
       sim_imm_dt d1' g cve es (v :: ve) je dt0 xc (up_ren xt);
       ex_map #(reads_imm_dt sg g cve es (v :: ve) je dt0 m)
         #(reads_imm_dt sg g cve es ve je (DBind o dt0) m) (fun d1 -> ITBind d1)
     | _ -> ())
  | ITSwitch #_ #_ #_ #_ #_ #_ #_ #s' _ d1' ->
    switch_rel xt dt dt' s';
    eliminate exists (s: dtree). L.memP s (switch_subtrees dt) /\ tsim_dt xt s s'
    with (sim_imm_dt d1' g cve es ve je s xc xt;
          ex_map #(reads_imm_dt sg g cve es ve je s m) #(reads_imm_dt sg g cve es ve je dt m)
            (fun d1 -> ITSwitch #sg #g #cve #es #ve #je #dt #s #m () d1))
  | ITGuard d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard e' _ _ ->
       crel_intro xt ve je e ve' je' e';
       sim_imm d1' g ve je e;
       ex_map #(reads_imm sg g ve je e m) #(reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m)
         (fun d1 -> ITGuard d1)
     | _ -> ())
  | ITGuardYes d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard _ dt1' _ ->
       sim_imm_dt d1' g cve es ve je dt1 xc xt;
       ex_map #(reads_imm_dt sg g cve es ve je dt1 m)
         #(reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m) (fun d1 -> ITGuardYes d1)
     | _ -> ())
  | ITGuardNo d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard _ _ dt2' ->
       sim_imm_dt d1' g cve es ve je dt2 xc xt;
       ex_map #(reads_imm_dt sg g cve es ve je dt2 m)
         #(reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m) (fun d1 -> ITGuardNo d1)
     | _ -> ())

and sim_lat_dt (#sg: sig) (#g': group) (#cve': venv) (#es': list exp) (#ve': venv) (#je': jenv)
  (#dt': dtree) (#m: nat)
  (d': reads_lat_dt sg g' cve' es' ve' je' dt' m) (g: group) (cve: venv) (es: list exp) (ve: venv)
  (je: jenv) (dt: dtree) (xc xt: ren)
  : Lemma (requires grel g g' /\ dtrel xc cve es cve' es' je je' /\ venv_rel xt ve ve' /\
                    tsim_dt xt dt dt')
          (ensures ex (reads_lat_dt sg g cve es ve je dt m)) (decreases d') =
  match d' with
  | LTLeaf d1' ->
    (match dt, dt' with
     | DLeaf e, DLeaf e' ->
       crel_intro xt ve je e ve' je' e';
       sim_lat d1' g ve je e;
       ex_map #(reads_lat sg g ve je e m) #(reads_lat_dt sg g cve es ve je (DLeaf e) m)
         (fun d1 -> LTLeaf d1)
     | _ -> ())
  | LTBind d1' ->
    (match dt, dt' with
     | DBind o dt0, DBind _ dt0' ->
       bind_entry_rel xc cve cve' je je' es es' o;
       let v = bind_entry cve je es o in
       venv_cons xt (up_ren xt) v (bind_entry cve' je' es' o) ve ve';
       sim_lat_dt d1' g cve es (v :: ve) je dt0 xc (up_ren xt);
       ex_map #(reads_lat_dt sg g cve es (v :: ve) je dt0 m)
         #(reads_lat_dt sg g cve es ve je (DBind o dt0) m) (fun d1 -> LTBind d1)
     | _ -> ())
  | LTSwitch #_ #_ #_ #_ #_ #_ #_ #s' _ d1' ->
    switch_rel xt dt dt' s';
    eliminate exists (s: dtree). L.memP s (switch_subtrees dt) /\ tsim_dt xt s s'
    with (sim_lat_dt d1' g cve es ve je s xc xt;
          ex_map #(reads_lat_dt sg g cve es ve je s m) #(reads_lat_dt sg g cve es ve je dt m)
            (fun d1 -> LTSwitch #sg #g #cve #es #ve #je #dt #s #m () d1))
  | LTGuardYes d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard _ dt1' _ ->
       sim_lat_dt d1' g cve es ve je dt1 xc xt;
       ex_map #(reads_lat_dt sg g cve es ve je dt1 m)
         #(reads_lat_dt sg g cve es ve je (DGuard e dt1 dt2) m) (fun d1 -> LTGuardYes d1)
     | _ -> ())
  | LTGuardNo d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard _ _ dt2' ->
       sim_lat_dt d1' g cve es ve je dt2 xc xt;
       ex_map #(reads_lat_dt sg g cve es ve je dt2 m)
         #(reads_lat_dt sg g cve es ve je (DGuard e dt1 dt2) m) (fun d1 -> LTGuardNo d1)
     | _ -> ())

(* Local groups. *)

let rec member_env_pre (n: nat)
  : Lemma (ensures pre_rel (member_env n) (member_env n) /\ L.length (member_env n) == n)
          (decreases n) =
  if n = 0 then () else member_env_pre (n - 1)

let member_env_rel (n: nat) (xi: ren)
  : Lemma (venv_rel (upn_ren n xi) (member_env n) (member_env n)) =
  member_env_pre n;
  LP.append_l_nil (member_env n);
  venv_append xi (member_env n) (member_env n) [] []

let rec rhs_nth (xi: ren) (bs bs': list (typ & exp)) (k: nat)
  : Lemma (requires tsim_binds xi bs bs')
          (ensures (match L.nth (L.map snd bs) k, L.nth (L.map snd bs') k with
                    | Some r, Some r' -> tsim xi r r'
                    | None, None -> True
                    | _ -> False))
          (decreases bs) =
  match bs, bs' with
  | [], [] -> ()
  | _ :: bs0, _ :: bs0' -> if k = 0 then () else rhs_nth xi bs0 bs0' (k - 1)

let local_grel (xi: ren) (bs bs': list (typ & exp))
  : Lemma (requires L.length bs' == L.length bs /\ tsim_binds (upn_ren (L.length bs) xi) bs bs')
          (ensures grel (local_group bs) (local_group bs')) =
  let n = L.length bs in
  let g = local_group bs in
  let g' = local_group bs' in
  member_env_rel n xi;
  introduce forall (k: nat) (r': exp). rhs g' k == Some r' ==>
    (exists (r: exp). rhs g k == Some r /\ crel3 g.genv [] r g'.genv [] r')
  with introduce _ ==> _
  with (rhs_nth (upn_ren n xi) bs bs' k;
           let Some r = rhs g k in
           crel_intro (upn_ren n xi) g.genv [] r g'.genv [] r')

(* Initialization safety. A group whose members are related to those of a
   safe group, under the members' binders lifted past any renaming, is
   safe. *)

let init_safe_tsim (sg: sig) (xi: ren) (bs bs': list (typ & exp))
  : Lemma (requires init_safe_letrec sg bs /\ L.length bs' == L.length bs /\
                    tsim_binds (upn_ren (L.length bs) xi) bs bs')
          (ensures init_safe_letrec sg bs') =
  let g = local_group bs in
  let g' = local_group bs' in
  local_grel xi bs bs';
  introduce forall (i: nat) (r': exp) (m: nat) (d': reads_imm sg g' g'.genv [] r' m).
    rhs g' i == Some r' ==> m < i
  with introduce _ ==> _
  with (eliminate exists (r: exp). rhs g i == Some r /\ crel3 g.genv [] r g'.genv [] r'
           with (sim_imm d' g g.genv [] r;
                 eliminate exists (d: reads_imm sg g g.genv [] r m). True
                 with ()))

let init_safe_sub_ty sg sigma bs =
  let n = L.length bs in
  tsim_binds_sub_ty (upn_ren n id_ren) sigma bs;
  init_safe_tsim sg id_ren bs (sub_ty_binds sigma bs)

let init_safe_ren_ty sg xi bs =
  ren_ty_binds_as_sub xi bs;
  init_safe_sub_ty sg (ren_tsub xi) bs

let init_safe_ren_tm sg xi bs =
  let n = L.length bs in
  tsim_binds_ren_tm (upn_ren n xi) bs;
  init_safe_tsim sg xi bs (ren_tm_binds (upn_ren n xi) bs)
