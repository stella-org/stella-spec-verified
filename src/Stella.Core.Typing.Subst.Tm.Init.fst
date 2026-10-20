(* Proof structure.

   The simulation is that of `Stella.Core.Init.Sim`. A substitution split
   at the cutoff `c` (`split`) is the identity below `c` and puts an inert
   term at and above it; it relates a term to its image,
   `ssim c e (sub_tm σ e)` (`ssim_sub_tm`). `upn_esub |bs| σ`, `σ` with no
   free jump, is split at `|bs|`, which gives `init_safe_sub_tm` by
   `init_safe_ssim`.

   The lifts of a term substitution under the binders of each sort keep a
   split (`split_up`, `split_ty`, `split_jp`). A lift shifts the
   substitutes past the new binders, so it keeps them inert: a term
   renaming that fixes the local variables and sends the variables beyond
   the cutoff beyond the new one (`iner_ren_tm`), a type renaming
   (`iner_ren_ty`), and a join renaming that keeps the local join points
   local (`iner_ren_jp`) each keep a term inert. With no environment
   variable, `iner` is `jps_below_exp` (`iner_jps`). *)
module Stella.Core.Typing.Subst.Tm.Init
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Scope
open Stella.Core.Init
open Stella.Core.Init.Sim
module L = FStar.List.Tot

(* With no environment variable, `iner` is `jps_below_exp`. *)
let rec iner_jps (k q: nat) (e: exp)
  : Lemma (ensures iner k 0 q e == jps_below_exp q e) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> iner_jps (k + 1) q b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    iner_jps k q e1; iner_jps k q e2
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> iner_jps k q b
  | ELet _ e1 e2 -> iner_jps k q e1; iner_jps (k + 1) q e2
  | ELetRec bs b -> iner_jps_binds (k + L.length bs) q bs; iner_jps (k + L.length bs) q b
  | ECase es dt | EMatch es dt -> iner_jps_exps k q es; iner_jps_dt k q dt
  | ELetJoin ts _ e1 e2 -> iner_jps (k + L.length ts) (q + 1) e1; iner_jps k (q + 1) e2
  | EJump _ es -> iner_jps_exps k q es
  | EHandle b h -> iner_jps k q b; iner_jps (k + 1) q h.h_ret; iner_jps_cls k q h.h_clauses
  | ERegion _ es b -> iner_jps_exps k q es; iner_jps k q b
  | ERegionOpen _ th b -> iner_jps_cells k q th; iner_jps k q b

and iner_jps_exps (k q: nat) (es: list exp)
  : Lemma (ensures iner_exps k 0 q es == jps_below_exps q es) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> iner_jps k q e; iner_jps_exps k q es

and iner_jps_binds (k q: nat) (bs: list (typ & exp))
  : Lemma (ensures iner_binds k 0 q bs == jps_below_binds q bs) (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, e) = pa in iner_jps k q e; iner_jps_binds k q bs

and iner_jps_cells (k q: nat) (th: list (key & exp))
  : Lemma (ensures iner_cells k 0 q th == jps_below_cells q th) (decreases th) =
  match th with
  | [] -> ()
  | pa :: th -> let (_, e) = pa in iner_jps k q e; iner_jps_cells k q th

and iner_jps_dt (k q: nat) (dt: dtree)
  : Lemma (ensures iner_dt k 0 q dt == jps_below_dt q dt) (decreases dt) =
  match dt with
  | DLeaf e -> iner_jps k q e
  | DBind _ dt -> iner_jps_dt (k + 1) q dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df -> iner_jps_brs k q bs; iner_jps_odt k q df
  | DSwitchLit _ bs df -> iner_jps_brs k q bs; iner_jps_dt k q df
  | DGuard e dt1 dt2 -> iner_jps k q e; iner_jps_dt k q dt1; iner_jps_dt k q dt2

and iner_jps_odt (k q: nat) (df: option dtree)
  : Lemma (ensures iner_odt k 0 q df == jps_below_odt q df) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> iner_jps_dt k q dt

and iner_jps_brs (#lb: eqtype) (k q: nat) (bs: list (lb & dtree))
  : Lemma (ensures iner_brs k 0 q bs == jps_below_brs q bs) (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, dt) = pa in iner_jps_dt k q dt; iner_jps_brs k q bs

and iner_jps_cls (k q: nat) (cs: list clause)
  : Lemma (ensures iner_cls k 0 q cs == jps_below_cls q cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> iner_jps (k + 2) q b; iner_jps_cls k q cs
  | CFast _ _ _ b :: cs -> iner_jps (k + 1) q b; iner_jps_cls k q cs

(* A term renaming that fixes the local variables and sends the variables
   beyond `c` beyond `c'`. *)
let rok (k c c': nat) (xi: ren) : prop =
  (forall (i: nat). i < k ==> xi i == i) /\ (forall (i: nat). i >= k + c ==> xi i >= k + c')

let rok_up (n k c c': nat) (xi: ren)
  : Lemma (requires rok k c c' xi) (ensures rok (k + n) c c' (upn_ren n xi)) =
  introduce forall (i: nat). i < k + n ==> upn_ren n xi i == i
  with introduce _ ==> _ with (if i < n then () else assert (xi (i - n) == i - n));
  introduce forall (i: nat). i >= k + n + c ==> upn_ren n xi i >= k + n + c'
  with introduce _ ==> _ with assert (xi (i - n) >= k + c')

let rec iner_ren_tm (k c c' q: nat) (xi: ren) (e: exp)
  : Lemma (requires iner k c q e /\ rok k c c' xi) (ensures iner k c' q (ren_tm xi e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> rok_up 1 k c c' xi; iner_ren_tm (k + 1) c c' q (up_ren xi) b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    iner_ren_tm k c c' q xi e1; iner_ren_tm k c c' q xi e2
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> iner_ren_tm k c c' q xi b
  | ELet _ e1 e2 ->
    iner_ren_tm k c c' q xi e1; rok_up 1 k c c' xi; iner_ren_tm (k + 1) c c' q (up_ren xi) e2
  | ELetRec bs b ->
    let n = L.length bs in
    rok_up n k c c' xi;
    iner_ren_tm_binds (k + n) c c' q (upn_ren n xi) bs; iner_ren_tm (k + n) c c' q (upn_ren n xi) b
  | ECase es dt | EMatch es dt -> iner_ren_tm_exps k c c' q xi es; iner_ren_tm_dt k c c' q xi dt
  | ELetJoin ts _ e1 e2 ->
    let n = L.length ts in
    rok_up n k c c' xi;
    iner_ren_tm (k + n) c c' (q + 1) (upn_ren n xi) e1; iner_ren_tm k c c' (q + 1) xi e2
  | EJump _ es -> iner_ren_tm_exps k c c' q xi es
  | EHandle b h ->
    iner_ren_tm k c c' q xi b; rok_up 1 k c c' xi; iner_ren_tm (k + 1) c c' q (up_ren xi) h.h_ret;
    iner_ren_tm_cls k c c' q xi h.h_clauses
  | ERegion _ es b -> iner_ren_tm_exps k c c' q xi es; iner_ren_tm k c c' q xi b
  | ERegionOpen _ th b -> iner_ren_tm_cells k c c' q xi th; iner_ren_tm k c c' q xi b

and iner_ren_tm_exps (k c c' q: nat) (xi: ren) (es: list exp)
  : Lemma (requires iner_exps k c q es /\ rok k c c' xi)
          (ensures iner_exps k c' q (ren_tm_exps xi es)) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> iner_ren_tm k c c' q xi e; iner_ren_tm_exps k c c' q xi es

and iner_ren_tm_binds (k c c' q: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (requires iner_binds k c q bs /\ rok k c c' xi)
          (ensures iner_binds k c' q (ren_tm_binds xi bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, e) = pa in iner_ren_tm k c c' q xi e; iner_ren_tm_binds k c c' q xi bs

and iner_ren_tm_cells (k c c' q: nat) (xi: ren) (th: list (key & exp))
  : Lemma (requires iner_cells k c q th /\ rok k c c' xi)
          (ensures iner_cells k c' q (ren_tm_cells xi th)) (decreases th) =
  match th with
  | [] -> ()
  | pa :: th -> let (_, e) = pa in iner_ren_tm k c c' q xi e; iner_ren_tm_cells k c c' q xi th

and iner_ren_tm_dt (k c c' q: nat) (xi: ren) (dt: dtree)
  : Lemma (requires iner_dt k c q dt /\ rok k c c' xi)
          (ensures iner_dt k c' q (ren_tm_dt xi dt)) (decreases dt) =
  match dt with
  | DLeaf e -> iner_ren_tm k c c' q xi e
  | DBind _ dt -> rok_up 1 k c c' xi; iner_ren_tm_dt (k + 1) c c' q (up_ren xi) dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    iner_ren_tm_brs k c c' q xi bs; iner_ren_tm_odt k c c' q xi df
  | DSwitchLit _ bs df -> iner_ren_tm_brs k c c' q xi bs; iner_ren_tm_dt k c c' q xi df
  | DGuard e dt1 dt2 ->
    iner_ren_tm k c c' q xi e; iner_ren_tm_dt k c c' q xi dt1; iner_ren_tm_dt k c c' q xi dt2

and iner_ren_tm_odt (k c c' q: nat) (xi: ren) (df: option dtree)
  : Lemma (requires iner_odt k c q df /\ rok k c c' xi)
          (ensures iner_odt k c' q (ren_tm_odt xi df)) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> iner_ren_tm_dt k c c' q xi dt

and iner_ren_tm_brs (#lb: eqtype) (k c c' q: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (requires iner_brs k c q bs /\ rok k c c' xi)
          (ensures iner_brs k c' q (ren_tm_brs xi bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, dt) = pa in iner_ren_tm_dt k c c' q xi dt; iner_ren_tm_brs k c c' q xi bs

and iner_ren_tm_cls (k c c' q: nat) (xi: ren) (cs: list clause)
  : Lemma (requires iner_cls k c q cs /\ rok k c c' xi)
          (ensures iner_cls k c' q (ren_tm_cls xi cs)) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs ->
    rok_up 2 k c c' xi; iner_ren_tm (k + 2) c c' q (upn_ren 2 xi) b; iner_ren_tm_cls k c c' q xi cs
  | CFast _ _ _ b :: cs ->
    rok_up 1 k c c' xi; iner_ren_tm (k + 1) c c' q (up_ren xi) b; iner_ren_tm_cls k c c' q xi cs

(* A type renaming changes no term variable and no jump. *)
let rec iner_ren_ty (k c q: nat) (xi: ren) (e: exp)
  : Lemma (ensures iner k c q (ren_ty_exp xi e) == iner k c q e) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> iner_ren_ty (k + 1) c q xi b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    iner_ren_ty k c q xi e1; iner_ren_ty k c q xi e2
  | ETyLam _ b -> iner_ren_ty k c q (up_ren xi) b
  | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> iner_ren_ty k c q xi b
  | ELet _ e1 e2 -> iner_ren_ty k c q xi e1; iner_ren_ty (k + 1) c q xi e2
  | ELetRec bs b ->
    iner_ren_ty_binds (k + L.length bs) c q xi bs; iner_ren_ty (k + L.length bs) c q xi b
  | ECase es dt | EMatch es dt -> iner_ren_ty_exps k c q xi es; iner_ren_ty_dt k c q xi dt
  | ELetJoin ts _ e1 e2 ->
    iner_ren_ty (k + L.length ts) c (q + 1) xi e1; iner_ren_ty k c (q + 1) xi e2
  | EJump _ es -> iner_ren_ty_exps k c q xi es
  | EHandle b h ->
    iner_ren_ty k c q xi b; iner_ren_ty (k + 1) c q xi h.h_ret; iner_ren_ty_cls k c q xi h.h_clauses
  | ERegion _ es b -> iner_ren_ty_exps k c q xi es; iner_ren_ty k c q xi b
  | ERegionOpen _ th b -> iner_ren_ty_cells k c q xi th; iner_ren_ty k c q xi b

and iner_ren_ty_exps (k c q: nat) (xi: ren) (es: list exp)
  : Lemma (ensures iner_exps k c q (ren_ty_exps xi es) == iner_exps k c q es) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> iner_ren_ty k c q xi e; iner_ren_ty_exps k c q xi es

and iner_ren_ty_binds (k c q: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures iner_binds k c q (ren_ty_binds xi bs) == iner_binds k c q bs) (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, e) = pa in iner_ren_ty k c q xi e; iner_ren_ty_binds k c q xi bs

and iner_ren_ty_cells (k c q: nat) (xi: ren) (th: list (key & exp))
  : Lemma (ensures iner_cells k c q (ren_ty_cells xi th) == iner_cells k c q th) (decreases th) =
  match th with
  | [] -> ()
  | pa :: th -> let (_, e) = pa in iner_ren_ty k c q xi e; iner_ren_ty_cells k c q xi th

and iner_ren_ty_dt (k c q: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures iner_dt k c q (ren_ty_dt xi dt) == iner_dt k c q dt) (decreases dt) =
  match dt with
  | DLeaf e -> iner_ren_ty k c q xi e
  | DBind _ dt -> iner_ren_ty_dt (k + 1) c q xi dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    iner_ren_ty_brs k c q xi bs; iner_ren_ty_odt k c q xi df
  | DSwitchLit _ bs df -> iner_ren_ty_brs k c q xi bs; iner_ren_ty_dt k c q xi df
  | DGuard e dt1 dt2 ->
    iner_ren_ty k c q xi e; iner_ren_ty_dt k c q xi dt1; iner_ren_ty_dt k c q xi dt2

and iner_ren_ty_odt (k c q: nat) (xi: ren) (df: option dtree)
  : Lemma (ensures iner_odt k c q (ren_ty_odt xi df) == iner_odt k c q df) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> iner_ren_ty_dt k c q xi dt

and iner_ren_ty_brs (#lb: eqtype) (k c q: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures iner_brs k c q (ren_ty_brs xi bs) == iner_brs k c q bs) (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, dt) = pa in iner_ren_ty_dt k c q xi dt; iner_ren_ty_brs k c q xi bs

and iner_ren_ty_cls (k c q: nat) (xi: ren) (cs: list clause)
  : Lemma (ensures iner_cls k c q (ren_ty_cls xi cs) == iner_cls k c q cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs -> iner_ren_ty (k + 2) c q (upn_ren nb xi) b; iner_ren_ty_cls k c q xi cs
  | CFast _ nb _ b :: cs -> iner_ren_ty (k + 1) c q (upn_ren nb xi) b; iner_ren_ty_cls k c q xi cs

(* A join renaming that keeps the local join points local. *)
let jok (q: nat) (xi: ren) : prop = forall (j: nat). j < q ==> xi j < q

let jok_up (q: nat) (xi: ren) : Lemma (requires jok q xi) (ensures jok (q + 1) (up_ren xi)) =
  introduce forall (j: nat). j < q + 1 ==> up_ren xi j < q + 1
  with introduce _ ==> _ with (if j = 0 then () else assert (xi (j - 1) < q))

let rec iner_ren_jp (k c q: nat) (xi: ren) (e: exp)
  : Lemma (requires iner k c q e /\ jok q xi) (ensures iner k c q (ren_jp xi e)) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> iner_ren_jp (k + 1) c q xi b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    iner_ren_jp k c q xi e1; iner_ren_jp k c q xi e2
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> iner_ren_jp k c q xi b
  | ELet _ e1 e2 -> iner_ren_jp k c q xi e1; iner_ren_jp (k + 1) c q xi e2
  | ELetRec bs b ->
    iner_ren_jp_binds (k + L.length bs) c q xi bs; iner_ren_jp (k + L.length bs) c q xi b
  | ECase es dt | EMatch es dt -> iner_ren_jp_exps k c q xi es; iner_ren_jp_dt k c q xi dt
  | ELetJoin ts _ e1 e2 ->
    jok_up q xi;
    iner_ren_jp (k + L.length ts) c (q + 1) (up_ren xi) e1; iner_ren_jp k c (q + 1) (up_ren xi) e2
  | EJump _ es -> iner_ren_jp_exps k c q xi es
  | EHandle b h ->
    iner_ren_jp k c q xi b; iner_ren_jp (k + 1) c q xi h.h_ret; iner_ren_jp_cls k c q xi h.h_clauses
  | ERegion _ es b -> iner_ren_jp_exps k c q xi es; iner_ren_jp k c q xi b
  | ERegionOpen _ th b -> iner_ren_jp_cells k c q xi th; iner_ren_jp k c q xi b

and iner_ren_jp_exps (k c q: nat) (xi: ren) (es: list exp)
  : Lemma (requires iner_exps k c q es /\ jok q xi) (ensures iner_exps k c q (ren_jp_exps xi es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> iner_ren_jp k c q xi e; iner_ren_jp_exps k c q xi es

and iner_ren_jp_binds (k c q: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (requires iner_binds k c q bs /\ jok q xi) (ensures iner_binds k c q (ren_jp_binds xi bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, e) = pa in iner_ren_jp k c q xi e; iner_ren_jp_binds k c q xi bs

and iner_ren_jp_cells (k c q: nat) (xi: ren) (th: list (key & exp))
  : Lemma (requires iner_cells k c q th /\ jok q xi) (ensures iner_cells k c q (ren_jp_cells xi th))
          (decreases th) =
  match th with
  | [] -> ()
  | pa :: th -> let (_, e) = pa in iner_ren_jp k c q xi e; iner_ren_jp_cells k c q xi th

and iner_ren_jp_dt (k c q: nat) (xi: ren) (dt: dtree)
  : Lemma (requires iner_dt k c q dt /\ jok q xi) (ensures iner_dt k c q (ren_jp_dt xi dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> iner_ren_jp k c q xi e
  | DBind _ dt -> iner_ren_jp_dt (k + 1) c q xi dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    iner_ren_jp_brs k c q xi bs; iner_ren_jp_odt k c q xi df
  | DSwitchLit _ bs df -> iner_ren_jp_brs k c q xi bs; iner_ren_jp_dt k c q xi df
  | DGuard e dt1 dt2 ->
    iner_ren_jp k c q xi e; iner_ren_jp_dt k c q xi dt1; iner_ren_jp_dt k c q xi dt2

and iner_ren_jp_odt (k c q: nat) (xi: ren) (df: option dtree)
  : Lemma (requires iner_odt k c q df /\ jok q xi) (ensures iner_odt k c q (ren_jp_odt xi df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> iner_ren_jp_dt k c q xi dt

and iner_ren_jp_brs (#lb: eqtype) (k c q: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (requires iner_brs k c q bs /\ jok q xi) (ensures iner_brs k c q (ren_jp_brs xi bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, dt) = pa in iner_ren_jp_dt k c q xi dt; iner_ren_jp_brs k c q xi bs

and iner_ren_jp_cls (k c q: nat) (xi: ren) (cs: list clause)
  : Lemma (requires iner_cls k c q cs /\ jok q xi) (ensures iner_cls k c q (ren_jp_cls xi cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> iner_ren_jp (k + 2) c q xi b; iner_ren_jp_cls k c q xi cs
  | CFast _ _ _ b :: cs -> iner_ren_jp (k + 1) c q xi b; iner_ren_jp_cls k c q xi cs

(* A substitution split at `c`: the identity below, inert at `c` above. *)
let split (c: nat) (sigma: esub) : prop =
  (forall (i: nat). i < c ==> sigma i == EVar i) /\ (forall (i: nat). i >= c ==> inert c (sigma i))

let split_up (n c: nat) (sigma: esub)
  : Lemma (requires split c sigma) (ensures split (c + n) (upn_esub n sigma)) =
  introduce forall (i: nat). i < c + n ==> upn_esub n sigma i == EVar i
  with introduce _ ==> _ with (if i < n then () else assert (sigma (i - n) == EVar (i - n)));
  introduce forall (i: nat). i >= c + n ==> inert (c + n) (upn_esub n sigma i)
  with introduce _ ==> _
  with iner_ren_tm 0 c (c + n) 0 (shift n) (sigma (i - n))

let split_ty (m c: nat) (sigma: esub)
  : Lemma (requires split c sigma) (ensures split c (tyup_esub m sigma)) =
  introduce forall (i: nat). i >= c ==> inert c (tyup_esub m sigma i)
  with introduce _ ==> _ with iner_ren_ty 0 c 0 (shift m) (sigma i)

let split_jp (c: nat) (sigma: esub)
  : Lemma (requires split c sigma) (ensures split c (jup_esub sigma)) =
  introduce forall (i: nat). i >= c ==> inert c (jup_esub sigma i)
  with introduce _ ==> _ with iner_ren_jp 0 c 0 (shift 1) (sigma i)

let rec ssim_sub_tm (c: nat) (sigma: esub) (e: exp)
  : Lemma (requires split c sigma) (ensures ssim c e (sub_tm sigma e)) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> split_up 1 c sigma; ssim_sub_tm (c + 1) (up_esub sigma) b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    ssim_sub_tm c sigma e1; ssim_sub_tm c sigma e2
  | ETyLam _ b -> split_ty 1 c sigma; ssim_sub_tm c (tyup_esub 1 sigma) b
  | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> ssim_sub_tm c sigma b
  | ELet _ e1 e2 ->
    ssim_sub_tm c sigma e1; split_up 1 c sigma; ssim_sub_tm (c + 1) (up_esub sigma) e2
  | ELetRec bs b ->
    let n = L.length bs in
    split_up n c sigma;
    ssim_sub_tm_binds (c + n) (upn_esub n sigma) bs; ssim_sub_tm (c + n) (upn_esub n sigma) b
  | ECase es dt | EMatch es dt -> ssim_sub_tm_exps c sigma es; ssim_sub_tm_dt c sigma dt
  | ELetJoin ts _ e1 e2 ->
    let n = L.length ts in
    split_jp c sigma;
    split_up n c (jup_esub sigma);
    ssim_sub_tm (c + n) (upn_esub n (jup_esub sigma)) e1; ssim_sub_tm c (jup_esub sigma) e2
  | EJump _ es -> ssim_sub_tm_exps c sigma es
  | EHandle b h ->
    ssim_sub_tm c sigma b; split_up 1 c sigma; ssim_sub_tm (c + 1) (up_esub sigma) h.h_ret;
    ssim_sub_tm_cls c sigma h.h_clauses
  | ERegion _ es b -> ssim_sub_tm_exps c sigma es; ssim_sub_tm c sigma b
  | ERegionOpen _ th b -> ssim_sub_tm_cells c sigma th; ssim_sub_tm c sigma b

and ssim_sub_tm_exps (c: nat) (sigma: esub) (es: list exp)
  : Lemma (requires split c sigma) (ensures ssim_exps c es (sub_tm_exps sigma es)) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ssim_sub_tm c sigma e; ssim_sub_tm_exps c sigma es

and ssim_sub_tm_binds (c: nat) (sigma: esub) (bs: list (typ & exp))
  : Lemma (requires split c sigma)
          (ensures ssim_binds c bs (sub_tm_binds sigma bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, e) = pa in ssim_sub_tm c sigma e; ssim_sub_tm_binds c sigma bs

and ssim_sub_tm_cells (c: nat) (sigma: esub) (th: list (key & exp))
  : Lemma (requires split c sigma)
          (ensures ssim_cells c th (sub_tm_cells sigma th)) (decreases th) =
  match th with
  | [] -> ()
  | pa :: th -> let (_, e) = pa in ssim_sub_tm c sigma e; ssim_sub_tm_cells c sigma th

and ssim_sub_tm_dt (c: nat) (sigma: esub) (dt: dtree)
  : Lemma (requires split c sigma) (ensures ssim_dt c dt (sub_tm_dt sigma dt)) (decreases dt) =
  match dt with
  | DLeaf e -> ssim_sub_tm c sigma e
  | DBind _ dt -> split_up 1 c sigma; ssim_sub_tm_dt (c + 1) (up_esub sigma) dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    ssim_sub_tm_brs c sigma bs; ssim_sub_tm_odt c sigma df
  | DSwitchLit _ bs df -> ssim_sub_tm_brs c sigma bs; ssim_sub_tm_dt c sigma df
  | DGuard e dt1 dt2 ->
    ssim_sub_tm c sigma e; ssim_sub_tm_dt c sigma dt1; ssim_sub_tm_dt c sigma dt2

and ssim_sub_tm_odt (c: nat) (sigma: esub) (df: option dtree)
  : Lemma (requires split c sigma) (ensures ssim_odt c df (sub_tm_odt sigma df)) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ssim_sub_tm_dt c sigma dt

and ssim_sub_tm_brs (#lb: eqtype) (c: nat) (sigma: esub) (bs: list (lb & dtree))
  : Lemma (requires split c sigma) (ensures ssim_brs c bs (sub_tm_brs sigma bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | pa :: bs -> let (_, dt) = pa in ssim_sub_tm_dt c sigma dt; ssim_sub_tm_brs c sigma bs

and ssim_sub_tm_cls (c: nat) (sigma: esub) (cs: list clause)
  : Lemma (requires split c sigma) (ensures ssim_cls c cs (sub_tm_cls sigma cs)) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    split_ty nb c sigma; split_up 2 c (tyup_esub nb sigma);
    ssim_sub_tm (c + 2) (upn_esub 2 (tyup_esub nb sigma)) b; ssim_sub_tm_cls c sigma cs
  | CFast _ nb _ b :: cs ->
    split_ty nb c sigma; split_up 1 c (tyup_esub nb sigma);
    ssim_sub_tm (c + 1) (up_esub (tyup_esub nb sigma)) b; ssim_sub_tm_cls c sigma cs

let init_safe_sub_tm sg sigma bs =
  let n = L.length bs in
  introduce forall (i: nat). i >= 0 ==> inert 0 (sigma i)
  with introduce _ ==> _ with iner_jps 0 0 (sigma i);
  split_up n 0 sigma;
  ssim_sub_tm_binds n (upn_esub n sigma) bs;
  init_safe_ssim sg bs (sub_tm_binds (upn_esub n sigma) bs)
