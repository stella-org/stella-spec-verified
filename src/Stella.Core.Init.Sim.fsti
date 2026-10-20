(**
 * Initialization safety is invariant under the maps of a group that keep
 * its shape (spec 10; design §5): a type substitution, a type renaming, a
 * kind instantiation, a term renaming and a term substitution under the
 * group's members.
 *
 * The judgement of `Stella.Core.Init` reads no type and no kind: it reads
 * the shape of a term, its term variables and join indices, the positions
 * of the members, and the declared scheme of a chain's head
 * (`Stella.Core.Spine.global_scheme`), which depends on the head's name
 * alone. Each of these maps keeps the shape of the group and its term
 * variables below a cutoff, the members, and replaces every other term
 * variable by a term that reads nothing of the group (`ssim`). A group
 * related so to a safe group is safe (`init_safe_ssim`).
 *
 *   - A type substitution, a type renaming and a kind instantiation keep
 *     every term variable.
 *   - A term renaming lifted past the members fixes them and sends every
 *     variable bound outside the group beyond them.
 *   - A term substitution lifted past the members fixes them and puts a
 *     substitute where a variable bound outside the group stood.
 *)
module Stella.Core.Init.Sim
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Init
module L = FStar.List.Tot

(** * Inert terms *)

(** `iner k c q e`: under `k` local term binders, every term variable of
    `e` is local (`< k`) or beyond the `c` variables of the environment
    (`>= k + c`), and every jump of `e` targets one of the `q` local join
    points. *)
let rec iner (k c q: nat) (e: exp) : Tot bool (decreases e) =
  match e with
  | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> true
  | EVar i -> i < k || i >= k + c
  | ELam _ _ b -> iner (k + 1) c q b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> iner k c q e1 && iner k c q e2
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> iner k c q b
  | ELet _ e1 e2 -> iner k c q e1 && iner (k + 1) c q e2
  | ELetRec bs b -> iner_binds (k + L.length bs) c q bs && iner (k + L.length bs) c q b
  | ECase es dt | EMatch es dt -> iner_exps k c q es && iner_dt k c q dt
  | ELetJoin ts _ e1 e2 -> iner (k + L.length ts) c (q + 1) e1 && iner k c (q + 1) e2
  | EJump j es -> j < q && iner_exps k c q es
  | EHandle b h -> iner k c q b && iner (k + 1) c q h.h_ret && iner_cls k c q h.h_clauses
  | ERegion _ es b -> iner_exps k c q es && iner k c q b
  | ERegionOpen _ th b -> iner_cells k c q th && iner k c q b

and iner_exps (k c q: nat) (es: list exp) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> iner k c q e && iner_exps k c q es

and iner_binds (k c q: nat) (bs: list (typ & exp)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | pa :: bs -> let (_, e) = pa in iner k c q e && iner_binds k c q bs

and iner_cells (k c q: nat) (th: list (key & exp)) : Tot bool (decreases th) =
  match th with
  | [] -> true
  | pa :: th -> let (_, e) = pa in iner k c q e && iner_cells k c q th

and iner_dt (k c q: nat) (dt: dtree) : Tot bool (decreases dt) =
  match dt with
  | DLeaf e -> iner k c q e
  | DBind _ dt -> iner_dt (k + 1) c q dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df -> iner_brs k c q bs && iner_odt k c q df
  | DSwitchLit _ bs df -> iner_brs k c q bs && iner_dt k c q df
  | DGuard e dt1 dt2 -> iner k c q e && iner_dt k c q dt1 && iner_dt k c q dt2

and iner_odt (k c q: nat) (df: option dtree) : Tot bool (decreases df) =
  match df with
  | None -> true
  | Some dt -> iner_dt k c q dt

and iner_brs (#lb: eqtype) (k c q: nat) (bs: list (lb & dtree)) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | pa :: bs -> let (_, dt) = pa in iner_dt k c q dt && iner_brs k c q bs

and iner_cls (k c q: nat) (cs: list clause) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | CFull _ _ _ _ b :: cs -> iner (k + 2) c q b && iner_cls k c q cs
  | CFast _ _ _ b :: cs -> iner (k + 1) c q b && iner_cls k c q cs

(** A term that stands, at cutoff `c`, for a variable at or beyond `c`: no
    term variable below `c` and no free jump. A variable at or beyond `c`
    is one. With `c = 0` it is a term with no free join index
    (`Stella.Core.Scope.jps_below_exp 0`). *)
let inert (c: nat) (e: exp) : bool = iner 0 c 0 e

(** * Related terms *)

(** `ssim c e e'`: `e'` is `e` with every type and kind replaced
    arbitrarily, every term variable below the cutoff `c` kept, and every
    variable at or beyond `c` replaced by an inert term (`inert c`), the
    cutoff growing by the term binders as the variables of the group
    shift. *)
let rec ssim (c: nat) (e e': exp) : Tot bool (decreases e) =
  match e, e' with
  | EVar i, _ -> if i < c then (match e' with EVar i' -> i' = i | _ -> false) else inert c e'
  | EGlobal q _, EGlobal q' _ -> q = q'
  | ELit _, ELit _ | ERecEmpty, ERecEmpty | EReadCell _ _, EReadCell _ _ | EForce _, EForce _
  | EOpaque _ _, EOpaque _ _ -> true
  | ELam _ _ b, ELam _ _ b' -> ssim (c + 1) b b'
  | EApp e1 e2, EApp e1' e2' | EExtend _ e1 e2, EExtend _ e1' e2'
  | EUpdate _ e1 e2, EUpdate _ e1' e2' | EMerge e1 e2, EMerge e1' e2' ->
    ssim c e1 e1' && ssim c e2 e2'
  | ETyLam _ b, ETyLam _ b' | ETyApp b _, ETyApp b' _ | ECLam _ b, ECLam _ b' | ECApp b, ECApp b'
  | ESelect _ b, ESelect _ b' | ERestrict _ b, ERestrict _ b' | EInject _ _ b, EInject _ _ b'
  | EWeaken _ _ b, EWeaken _ _ b' | EAbsurd _ b, EAbsurd _ b' | EPerform _ _ _ b, EPerform _ _ _ b'
  | EOpenEff _ b, EOpenEff _ b' | EWriteCell _ _ b, EWriteCell _ _ b'
  | EOpenEffC _ b, EOpenEffC _ b' | EFill _ b, EFill _ b' -> ssim c b b'
  | ELet _ e1 e2, ELet _ e1' e2' -> ssim c e1 e1' && ssim (c + 1) e2 e2'
  | ELetRec bs b, ELetRec bs' b' ->
    L.length bs = L.length bs' &&
    ssim_binds (c + L.length bs) bs bs' && ssim (c + L.length bs) b b'
  | ECase es dt, ECase es' dt' | EMatch es dt, EMatch es' dt' ->
    ssim_exps c es es' && ssim_dt c dt dt'
  | ELetJoin ts _ e1 e2, ELetJoin ts' _ e1' e2' ->
    L.length ts = L.length ts' && ssim (c + L.length ts) e1 e1' && ssim c e2 e2'
  | EJump j es, EJump j' es' -> j = j' && ssim_exps c es es'
  | EHandle b h, EHandle b' h' ->
    ssim c b b' && ssim (c + 1) h.h_ret h'.h_ret && ssim_cls c h.h_clauses h'.h_clauses
  | ERegion _ es b, ERegion _ es' b' -> ssim_exps c es es' && ssim c b b'
  | ERegionOpen _ th b, ERegionOpen _ th' b' -> ssim_cells c th th' && ssim c b b'
  | _ -> false

and ssim_exps (c: nat) (es es': list exp) : Tot bool (decreases es) =
  match es, es' with
  | [], [] -> true
  | e :: es, e' :: es' -> ssim c e e' && ssim_exps c es es'
  | _ -> false

and ssim_binds (c: nat) (bs bs': list (typ & exp)) : Tot bool (decreases bs) =
  match bs, bs' with
  | [], [] -> true
  | pa :: bs, pb :: bs' -> let (_, e) = pa in let (_, e') = pb in ssim c e e' && ssim_binds c bs bs'
  | _ -> false

and ssim_cells (c: nat) (th th': list (key & exp)) : Tot bool (decreases th) =
  match th, th' with
  | [], [] -> true
  | pa :: th, pb :: th' -> let (_, e) = pa in let (_, e') = pb in ssim c e e' && ssim_cells c th th'
  | _ -> false

and ssim_dt (c: nat) (dt dt': dtree) : Tot bool (decreases dt) =
  match dt, dt' with
  | DLeaf e, DLeaf e' -> ssim c e e'
  | DBind o dt, DBind o' dt' -> o = o' && ssim_dt (c + 1) dt dt'
  | DSwitchCtor _ bs df, DSwitchCtor _ bs' df' | DSwitchKey _ bs df, DSwitchKey _ bs' df' ->
    ssim_brs c bs bs' && ssim_odt c df df'
  | DSwitchLit _ bs df, DSwitchLit _ bs' df' -> ssim_brs c bs bs' && ssim_dt c df df'
  | DGuard e dt1 dt2, DGuard e' dt1' dt2' ->
    ssim c e e' && ssim_dt c dt1 dt1' && ssim_dt c dt2 dt2'
  | _ -> false

and ssim_odt (c: nat) (df df': option dtree) : Tot bool (decreases df) =
  match df, df' with
  | None, None -> true
  | Some dt, Some dt' -> ssim_dt c dt dt'
  | _ -> false

and ssim_brs (#lb: eqtype) (c: nat) (bs bs': list (lb & dtree)) : Tot bool (decreases bs) =
  match bs, bs' with
  | [], [] -> true
  | pa :: bs, pb :: bs' ->
    let (_, dt) = pa in let (_, dt') = pb in ssim_dt c dt dt' && ssim_brs c bs bs'
  | _ -> false

and ssim_cls (c: nat) (cs cs': list clause) : Tot bool (decreases cs) =
  match cs, cs' with
  | [], [] -> true
  | CFull _ _ _ _ b :: cs, CFull _ _ _ _ b' :: cs' -> ssim (c + 2) b b' && ssim_cls c cs cs'
  | CFast _ _ _ b :: cs, CFast _ _ _ b' :: cs' -> ssim (c + 1) b b' && ssim_cls c cs cs'
  | _ -> false

(** * Initialization safety *)

(** The members of `letrec bs` are its innermost `|bs|` term variables. A
    group related at that cutoff to a safe group is safe. *)
val init_safe_ssim (sg: sig) (bs bs': list (typ & exp))
  : Lemma (requires init_safe_letrec sg bs /\ ssim_binds (L.length bs) bs bs')
          (ensures init_safe_letrec sg bs')
