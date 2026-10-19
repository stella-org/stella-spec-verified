(* Proof structure.

   Maps of chains: each map sends `EApp`, `ETyApp`, `ECApp` and `EGlobal`
   to themselves, so the view of the image is the image of the view, by
   induction on the chain (as `Stella.Core.Spine.decompose_sub_ty_exp`).

   Cursors under the maps: a step reads the shape of the remainder, which a
   kind instantiation keeps (`as_function_kinst`), and a type argument,
   which goes into the accumulated substitution. So the image cursor
   reaches the image remainder with the image substitution pointwise, from
   the identity substitution, which every map fixes. The instance then
   commutes by `kinst_sub_ty` / `rmap_sub_ty`. The start of the image
   cursor is the declared scheme instantiated at the image kinds, which
   is the image of the instantiated scheme by `kinst_ty_comp`, the scheme
   having its kind variables below `|κ̄|` (`check_kvs_below`). A declared
   scheme is kinded with no region in scope, so it has no region
   reference (`rfree`), and neither has any part of it that a cursor
   reaches; a region map fixes it.

   Saturated constructor chains: the instantiated constructor scheme is
   `foralls κ̄' (pure_arrows τ̄' (T [[κ̄]] ā))`. A cursor that reaches a
   saturated remainder consumes one type argument per `forall`
   (`walk_foralls`) and then one value argument per arrow
   (`walk_arrows`), and stops at `T [[κ̄]] ā`, the only saturated
   remainder. The substitution is then `σ̄` consed in order
   (`scons_all`), which instantiates `ā` to `σ̄` and agrees with
   `inst_foralls`, the instantiation `ctor_fields` reads. *)
module Stella.Core.Spine.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.Region.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
module L = FStar.List.Tot

(* Kind variables in scope. *)

let rec qkinds_below (n: nat) (kl: list kind)
  : Lemma (requires qkinds_wf n kl) (ensures kinds_below n kl) (decreases kl) =
  match kl with
  | [] -> ()
  | _ :: kl' -> qkinds_below n kl'

let rec synth_kind_kvs (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires Some? (synth_kind sg g t)) (ensures kvs_below g.nk t) (decreases %[t; 0]) =
  match t with
  | TCon _ kl -> qkinds_below g.nk kl
  | TApp t1 t2 ->
    synth_kind_kvs sg g t1;
    let Some (KArrow k1 _) = synth_kind sg g t1 in
    check_kvs sg g t2 k1
  | TForall k t1 -> check_kvs sg (push_tvar g k) t1 KType
  | TConstr c t1 -> constr_ok_kvs sg g c; check_kvs sg (add_assump g c) t1 KType
  | _ -> ()

and check_kvs (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg g t k) (ensures kvs_below g.nk t) (decreases %[t; 1]) =
  match t with
  | TRowEmpty -> ()
  | TRowExt en r -> let KRow e = k in entry_ok_kvs sg g en e; check_kvs sg g r k
  | TRowUnion r1 r2 -> check_kvs sg g r1 k; check_kvs sg g r2 k
  | _ -> synth_kind_kvs sg g t

and entry_ok_kvs (sg: sig) (g: ctx) (en: entry) (e: elt_kind)
  : Lemma (requires entry_ok sg g en e) (ensures kvs_below_ent g.nk en) (decreases en) =
  match en with
  | EntTy _ t -> check_kvs sg g t KType
  | EntEff _ q ts -> check_tys_kvs sg g ts (Some?.v (sg.effects q)).eff_params
  | EntRegion _ -> ()

and check_tys_kvs (sg: sig) (g: ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ts ks) (ensures kvs_below_tys g.nk ts) (decreases ts) =
  match ts, ks with
  | [], [] -> ()
  | t :: ts', k :: ks' -> check_kvs sg g t k; check_tys_kvs sg g ts' ks'

and constr_ok_kvs (sg: sig) (g: ctx) (c: constr)
  : Lemma (requires constr_ok sg g c) (ensures kvs_below_constr g.nk c) (decreases c) =
  match c with
  | CLacks _ r ->
    if check sg g r (KRow EType) then check_kvs sg g r (KRow EType)
    else check_kvs sg g r (KRow EEffect)
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_kvs sg g r1 (KRow EType);
      check_kvs sg g r2 (KRow EType)
    end else begin
      check_kvs sg g r1 (KRow EEffect);
      check_kvs sg g r2 (KRow EEffect)
    end

let check_kvs_below sg g t k = check_kvs sg g t k

(* Composition. *)

let rec kinst_kinds_comp (ks ks0: list kind) (kl: list kind)
  : Lemma (requires kinds_below (L.length ks0) kl)
          (ensures kinst_kinds ks (kinst_kinds ks0 kl) == kinst_kinds (kinst_kinds ks ks0) kl)
          (decreases kl) =
  match kl with
  | [] -> ()
  | k :: kl' -> kinst_kind_comp ks ks0 k; kinst_kinds_comp ks ks0 kl'

let rec kinst_comp (ks ks0: list kind) (t: typ)
  : Lemma (requires kvs_below (L.length ks0) t)
          (ensures kinst_ty ks (kinst_ty ks0 t) == kinst_ty (kinst_kinds ks ks0) t) (decreases t) =
  match t with
  | TVar _ | TRowEmpty -> ()
  | TCon _ kl -> kinst_kinds_comp ks ks0 kl
  | TApp t1 t2 | TRowUnion t1 t2 -> kinst_comp ks ks0 t1; kinst_comp ks ks0 t2
  | TForall k b -> kinst_kind_comp ks ks0 k; kinst_comp ks ks0 b
  | TConstr c b -> kinst_comp_constr ks ks0 c; kinst_comp ks ks0 b
  | TRowExt en r -> kinst_comp_ent ks ks0 en; kinst_comp ks ks0 r

and kinst_comp_ent (ks ks0: list kind) (en: entry)
  : Lemma (requires kvs_below_ent (L.length ks0) en)
          (ensures kinst_ent ks (kinst_ent ks0 en) == kinst_ent (kinst_kinds ks ks0) en)
          (decreases en) =
  match en with
  | EntTy _ t -> kinst_comp ks ks0 t
  | EntEff _ _ ts -> kinst_comp_tys ks ks0 ts
  | EntRegion _ -> ()

and kinst_comp_constr (ks ks0: list kind) (c: constr)
  : Lemma (requires kvs_below_constr (L.length ks0) c)
          (ensures kinst_constr ks (kinst_constr ks0 c) == kinst_constr (kinst_kinds ks ks0) c)
          (decreases c) =
  match c with
  | CLacks _ t -> kinst_comp ks ks0 t
  | CDisj t1 t2 -> kinst_comp ks ks0 t1; kinst_comp ks ks0 t2

and kinst_comp_tys (ks ks0: list kind) (ts: list typ)
  : Lemma (requires kvs_below_tys (L.length ks0) ts)
          (ensures kinst_tys ks (kinst_tys ks0 ts) == kinst_tys (kinst_kinds ks ks0) ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> kinst_comp ks ks0 t; kinst_comp_tys ks ks0 ts'

let kinst_ty_comp ks ks0 t = kinst_comp ks ks0 t

let kinst_constr_comp ks ks0 c = kinst_comp_constr ks ks0 c

(* Chains under the maps. *)

let rec decompose_kinst (ks: list kind) (e: exp)
  : Lemma (ensures decompose_global_app (kinst_exp ks e) ==
                   (match decompose_global_app e with
                    | Some (q, kl, args) -> Some (q, kinst_kinds ks kl, L.map (kinst_arg ks) args)
                    | None -> None))
          (decreases e) =
  match e with
  | EApp f v ->
    decompose_kinst ks f;
    (match decompose_global_app f with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (kinst_arg ks) args [SVal v]
     | None -> ())
  | ETyApp f t ->
    decompose_kinst ks f;
    (match decompose_global_app f with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (kinst_arg ks) args [STy t]
     | None -> ())
  | ECApp f ->
    decompose_kinst ks f;
    (match decompose_global_app f with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (kinst_arg ks) args [SConstr]
     | None -> ())
  | _ -> ()

let rec decompose_rmap (f: nat -> region_ref -> region_ref) (d: nat) (e: exp)
  : Lemma (ensures decompose_global_app (rmap_exp f d e) ==
                   (match decompose_global_app e with
                    | Some (q, kl, args) -> Some (q, kl, L.map (rmap_arg f d) args)
                    | None -> None))
          (decreases e) =
  match e with
  | EApp h v ->
    decompose_rmap f d h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (rmap_arg f d) args [SVal v]
     | None -> ())
  | ETyApp h t ->
    decompose_rmap f d h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (rmap_arg f d) args [STy t]
     | None -> ())
  | ECApp h ->
    decompose_rmap f d h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (rmap_arg f d) args [SConstr]
     | None -> ())
  | _ -> ()

let rec decompose_ren_tm (xi: ren) (e: exp)
  : Lemma (ensures decompose_global_app (ren_tm xi e) ==
                   (match decompose_global_app e with
                    | Some (q, kl, args) -> Some (q, kl, L.map (val_arg (ren_tm xi)) args)
                    | None -> None))
          (decreases e) =
  match e with
  | EApp h v ->
    decompose_ren_tm xi h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (val_arg (ren_tm xi)) args [SVal v]
     | None -> ())
  | ETyApp h t ->
    decompose_ren_tm xi h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (val_arg (ren_tm xi)) args [STy t]
     | None -> ())
  | ECApp h ->
    decompose_ren_tm xi h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (val_arg (ren_tm xi)) args [SConstr]
     | None -> ())
  | _ -> ()

let rec decompose_ren_jp (xi: ren) (e: exp)
  : Lemma (ensures decompose_global_app (ren_jp xi e) ==
                   (match decompose_global_app e with
                    | Some (q, kl, args) -> Some (q, kl, L.map (val_arg (ren_jp xi)) args)
                    | None -> None))
          (decreases e) =
  match e with
  | EApp h v ->
    decompose_ren_jp xi h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (val_arg (ren_jp xi)) args [SVal v]
     | None -> ())
  | ETyApp h t ->
    decompose_ren_jp xi h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (val_arg (ren_jp xi)) args [STy t]
     | None -> ())
  | ECApp h ->
    decompose_ren_jp xi h;
    (match decompose_global_app h with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (val_arg (ren_jp xi)) args [SConstr]
     | None -> ())
  | _ -> ()

let rec cursor_val_args (sg: sig) (fv: exp -> exp) (t: typ) (th: tsub) (args: list spine_arg)
  : Lemma (ensures cursor sg t th (L.map (val_arg fv) args) == cursor sg t th args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    match cursor_step sg t th a with
    | Some (t', th') -> cursor_val_args sg fv t' th' args'
    | None -> ()

let spine_cursor_val_args (sg: sig) (fv: exp -> exp) (q: qname) (ks: list kind)
  (args: list spine_arg)
  : Lemma (spine_cursor sg q ks (L.map (val_arg fv) args) == spine_cursor sg q ks args) =
  match global_scheme sg q with
  | Some (_, nk, t) -> if L.length ks = nk then cursor_val_args sg fv (kinst_ty ks t) tvar args
  | None -> ()

let chain_cursor_ren_tm sg xi e =
  decompose_ren_tm xi e;
  match decompose_global_app e with
  | Some (q, ks, args) -> spine_cursor_val_args sg (ren_tm xi) q ks args
  | None -> ()

let chain_cursor_ren_jp sg xi e =
  decompose_ren_jp xi e;
  match decompose_global_app e with
  | Some (q, ks, args) -> spine_cursor_val_args sg (ren_jp xi) q ks args
  | None -> ()

(* The declared scheme of a global. *)

let global_scheme_ok (sg: sig) (q: qname) (c: global_class) (nk: nat) (t: typ)
  : Lemma (requires sig_wf sg /\ global_scheme sg q == Some (c, nk, t)) (ensures scheme_ok sg nk t) =
  match sg.ctors q, sg.foreigns q with
  | Some ci, _ -> assert (scheme_ok sg ci.ct_nk ci.ct_ty)
  | None, Some fi -> assert (scheme_ok sg fi.fr_nk fi.fr_ty)

let rec kinst_kinds_length (ks kl: list kind)
  : Lemma (ensures L.length (kinst_kinds ks kl) == L.length kl) (decreases kl) =
  match kl with
  | [] -> ()
  | _ :: kl' -> kinst_kinds_length ks kl'

(* Cursors under kind instantiation. *)

(* `kinst_ty` is unfolded one application node at a time. *)
let as_function_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (as_function sg (kinst_ty ks t) ==
           (match as_function sg t with
            | Some (t1, r, t2) -> Some (kinst_ty ks t1, kinst_ty ks r, kinst_ty ks t2)
            | None -> None)) =
  match t with
  | TApp f t2 ->
    assert (kinst_ty ks t == TApp (kinst_ty ks f) (kinst_ty ks t2));
    (match f with
     | TApp g r ->
       assert (kinst_ty ks f == TApp (kinst_ty ks g) (kinst_ty ks r));
       (match g with
        | TApp h t1 ->
          assert (kinst_ty ks g == TApp (kinst_ty ks h) (kinst_ty ks t1));
          (match h with
           | TCon _ kl -> (match kl with [] -> () | _ :: _ -> ())
           | _ -> ())
        | _ -> ())
     | _ -> ())
  | _ -> ()

let rec cursor_kinst (sg: sig) (ks: list kind) (t: typ) (th th': tsub) (args: list spine_arg)
  : Lemma (requires (forall (i: nat). th' i == kinst_ty ks (th i)) /\ Some? (cursor sg t th args))
          (ensures (let Some (t1, th1) = cursor sg t th args in
                    match cursor sg (kinst_ty ks t) th' (L.map (kinst_arg ks) args) with
                    | Some (t1', th1') ->
                      t1' == kinst_ty ks t1 /\ (forall (i: nat). th1' i == kinst_ty ks (th1 i))
                    | None -> False))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    match a, t with
    | STy s, TForall _ body ->
      introduce forall (i: nat). scons (kinst_ty ks s) th' i == kinst_ty ks (scons s th i)
      with (if i = 0 then () else ());
      cursor_kinst sg ks body (scons s th) (scons (kinst_ty ks s) th') args'
    | SConstr, TConstr _ body -> cursor_kinst sg ks body th th' args'
    | SVal _, _ ->
      as_function_kinst sg ks t;
      let Some (_, _, t2) = as_function sg t in
      cursor_kinst sg ks t2 th th' args'

let chain_cursor_kinst sg ks e t th =
  decompose_kinst ks e;
  let Some (q, kl, args) = decompose_global_app e in
  let Some (c, nk, t0) = global_scheme sg q in
  global_scheme_ok sg q c nk t0;
  check_kvs_below sg (decl_ctx nk) t0 KType;
  kinst_ty_comp ks kl t0;
  kinst_kinds_length ks kl;
  cursor_kinst sg ks (kinst_ty kl t0) tvar tvar args;
  let Some (t', th') = cursor sg (kinst_ty (kinst_kinds ks kl) t0) tvar (L.map (kinst_arg ks) args) in
  kinst_sub_ty ks th th' t;
  introduce forall (t1 r t2: typ). as_function sg t == Some (t1, r, t2) ==>
    as_function sg t' == Some (kinst_ty ks t1, kinst_ty ks r, kinst_ty ks t2) /\
    sub_ty th' (kinst_ty ks t1) == kinst_ty ks (sub_ty th t1) /\
    sub_ty th' (kinst_ty ks r) == kinst_ty ks (sub_ty th r) /\
    sub_ty th' (kinst_ty ks t2) == kinst_ty ks (sub_ty th t2)
  with introduce _ ==> _
  with begin
    as_function_kinst sg ks t;
    kinst_sub_ty ks th th' t1;
    kinst_sub_ty ks th th' r;
    kinst_sub_ty ks th th' t2
  end;
  introduce forall (c: constr) (b: typ). t == TConstr c b ==>
    sub_constr th' (kinst_constr ks c) == kinst_constr ks (sub_constr th c)
  with introduce _ ==> _
  with kinst_sub_constr ks th th' c

(* Region-free types. *)

let no_region_key (k: key) : bool = not (RegionKey? k)

let rec rfree (t: typ) : Tot bool (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> true
  | TApp t1 t2 | TRowUnion t1 t2 -> rfree t1 && rfree t2
  | TForall _ b -> rfree b
  | TConstr c b -> rfree_constr c && rfree b
  | TRowExt en r -> rfree_ent en && rfree r

and rfree_ent (en: entry) : Tot bool (decreases en) =
  match en with
  | EntTy k t -> no_region_key k && rfree t
  | EntEff _ _ ts -> rfree_tys ts
  | EntRegion _ -> false

and rfree_constr (c: constr) : Tot bool (decreases c) =
  match c with
  | CLacks k t -> no_region_key k && rfree t
  | CDisj t1 t2 -> rfree t1 && rfree t2

and rfree_tys (ts: list typ) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | t :: ts -> rfree t && rfree_tys ts

let no_atoms (l: list atom) : prop = forall (a: atom). ~(L.mem a l)

let rec lc_rfree (t: typ)
  : Lemma (requires lc_ty_at 0 t /\ no_atoms (frn_ty t)) (ensures rfree t) (decreases t) =
  match t with
  | TApp t1 t2 | TRowUnion t1 t2 -> lc_rfree t1; lc_rfree t2
  | TForall _ b -> lc_rfree b
  | TConstr c b -> lc_rfree_constr c; lc_rfree b
  | TRowExt en r -> lc_rfree_ent en; lc_rfree r
  | _ -> ()

and lc_rfree_ent (en: entry)
  : Lemma (requires lc_ent_at 0 en /\ no_atoms (frn_ent en)) (ensures rfree_ent en) (decreases en) =
  match en with
  | EntTy k t ->
    (match k with RegionKey (RFree a) -> assert (L.mem a (frn_ent en)) | _ -> ());
    lc_rfree t
  | EntEff _ _ ts -> lc_rfree_tys ts
  | EntRegion r -> (match r with RFree a -> assert (L.mem a (frn_ent en)) | _ -> ())

and lc_rfree_constr (c: constr)
  : Lemma (requires lc_constr_at 0 c /\ no_atoms (frn_constr c)) (ensures rfree_constr c)
          (decreases c) =
  match c with
  | CLacks k t ->
    (match k with RegionKey (RFree a) -> assert (L.mem a (frn_constr c)) | _ -> ());
    lc_rfree t
  | CDisj t1 t2 -> lc_rfree t1; lc_rfree t2

and lc_rfree_tys (ts: list typ)
  : Lemma (requires lc_tys_at 0 ts /\ no_atoms (frn_tys ts)) (ensures rfree_tys ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> lc_rfree t; lc_rfree_tys ts'

let rec rfree_kinst (ks: list kind) (t: typ)
  : Lemma (requires rfree t) (ensures rfree (kinst_ty ks t)) (decreases t) =
  match t with
  | TApp t1 t2 | TRowUnion t1 t2 -> rfree_kinst ks t1; rfree_kinst ks t2
  | TForall _ b -> rfree_kinst ks b
  | TConstr c b -> rfree_kinst_constr ks c; rfree_kinst ks b
  | TRowExt en r -> rfree_kinst_ent ks en; rfree_kinst ks r
  | _ -> ()

and rfree_kinst_ent (ks: list kind) (en: entry)
  : Lemma (requires rfree_ent en) (ensures rfree_ent (kinst_ent ks en)) (decreases en) =
  match en with
  | EntTy _ t -> rfree_kinst ks t
  | EntEff _ _ ts -> rfree_kinst_tys ks ts
  | EntRegion _ -> ()

and rfree_kinst_constr (ks: list kind) (c: constr)
  : Lemma (requires rfree_constr c) (ensures rfree_constr (kinst_constr ks c)) (decreases c) =
  match c with
  | CLacks _ t -> rfree_kinst ks t
  | CDisj t1 t2 -> rfree_kinst ks t1; rfree_kinst ks t2

and rfree_kinst_tys (ks: list kind) (ts: list typ)
  : Lemma (requires rfree_tys ts) (ensures rfree_tys (kinst_tys ks ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> rfree_kinst ks t; rfree_kinst_tys ks ts'

let rec rfree_rmap (g: region_ref -> region_ref) (t: typ)
  : Lemma (requires rfree t) (ensures rmap_ty g t == t) (decreases t) =
  match t with
  | TApp t1 t2 | TRowUnion t1 t2 -> rfree_rmap g t1; rfree_rmap g t2
  | TForall _ b -> rfree_rmap g b
  | TConstr c b -> rfree_rmap_constr g c; rfree_rmap g b
  | TRowExt en r -> rfree_rmap_ent g en; rfree_rmap g r
  | _ -> ()

and rfree_rmap_ent (g: region_ref -> region_ref) (en: entry)
  : Lemma (requires rfree_ent en) (ensures rmap_ent g en == en) (decreases en) =
  match en with
  | EntTy _ t -> rfree_rmap g t
  | EntEff _ _ ts -> rfree_rmap_tys g ts
  | EntRegion _ -> ()

and rfree_rmap_constr (g: region_ref -> region_ref) (c: constr)
  : Lemma (requires rfree_constr c) (ensures rmap_constr g c == c) (decreases c) =
  match c with
  | CLacks _ t -> rfree_rmap g t
  | CDisj t1 t2 -> rfree_rmap g t1; rfree_rmap g t2

and rfree_rmap_tys (g: region_ref -> region_ref) (ts: list typ)
  : Lemma (requires rfree_tys ts) (ensures rmap_tys g ts == ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> rfree_rmap g t; rfree_rmap_tys g ts'

(* A declared scheme, kinded with no region in scope, is region-free. *)
let scheme_rfree (sg: sig) (nk: nat) (t: typ)
  : Lemma (requires scheme_ok sg nk t) (ensures rfree t) =
  check_lc sg (decl_ctx nk) t KType;
  lc_rfree t

(* Cursors under region maps. *)

let rec cursor_rmap (sg: sig) (f: nat -> region_ref -> region_ref) (d: nat) (t: typ)
  (th th': tsub) (args: list spine_arg)
  : Lemma (requires rfree t /\ (forall (i: nat). th' i == rmap_ty (f d) (th i)) /\
                    Some? (cursor sg t th args))
          (ensures (let Some (t1, th1) = cursor sg t th args in
                    rfree t1 /\
                    (match cursor sg t th' (L.map (rmap_arg f d) args) with
                     | Some (t1', th1') ->
                       t1' == t1 /\ (forall (i: nat). th1' i == rmap_ty (f d) (th1 i))
                     | None -> False)))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    match a, t with
    | STy s, TForall _ body ->
      introduce forall (i: nat). scons (rmap_ty (f d) s) th' i == rmap_ty (f d) (scons s th i)
      with (if i = 0 then () else ());
      cursor_rmap sg f d body (scons s th) (scons (rmap_ty (f d) s) th') args'
    | SConstr, TConstr _ body -> cursor_rmap sg f d body th th' args'
    | SVal _, _ ->
      let Some (_, _, t2) = as_function sg t in
      cursor_rmap sg f d t2 th th' args'

let chain_cursor_rmap sg f d e t th =
  decompose_rmap f d e;
  let Some (q, kl, args) = decompose_global_app e in
  let Some (c, nk, t0) = global_scheme sg q in
  global_scheme_ok sg q c nk t0;
  scheme_rfree sg nk t0;
  rfree_kinst kl t0;
  cursor_rmap sg f d (kinst_ty kl t0) tvar tvar args;
  let Some (_, th') = cursor sg (kinst_ty kl t0) tvar (L.map (rmap_arg f d) args) in
  let g = f d in
  rfree_rmap g t;
  rmap_sub_ty g th th' t;
  introduce forall (t1 r t2: typ). as_function sg t == Some (t1, r, t2) ==>
    sub_ty th' t1 == rmap_ty g (sub_ty th t1) /\
    sub_ty th' r == rmap_ty g (sub_ty th r) /\
    sub_ty th' t2 == rmap_ty g (sub_ty th t2)
  with introduce _ ==> _
  with begin
    let TApp (TApp (TApp h _) _) _ = t in
    assert (rfree (TApp (TApp h t1) r) /\ rfree t2);
    assert (rfree (TApp h t1) /\ rfree r);
    rfree_rmap g t1; rmap_sub_ty g th th' t1;
    rfree_rmap g r; rmap_sub_ty g th th' r;
    rfree_rmap g t2; rmap_sub_ty g th th' t2
  end;
  introduce forall (c: constr) (b: typ). t == TConstr c b ==>
    sub_constr th' c == rmap_constr g (sub_constr th c)
  with introduce _ ==> _
  with begin
    assert (rfree_constr c);
    rfree_rmap_constr g c;
    rmap_sub_constr g th th' c
  end

(* The domains of a chain. *)

let rec cursor_domains_snoc sg t th args a =
  match args with
  | [] ->
    (match cursor_step sg t th a with
     | Some _ -> L.append_l_nil (arg_domain sg t th a)
     | None -> L.append_l_nil (arg_domain sg t th a))
  | b :: args' ->
    match cursor_step sg t th b with
    | Some (t1, th1) ->
      cursor_domains_snoc sg t1 th1 args' a;
      L.append_assoc (arg_domain sg t th b) (cursor_domains sg t1 th1 args')
        (match cursor sg t1 th1 args' with
         | Some (t', th') -> arg_domain sg t' th' a
         | None -> [])
    | None -> L.append_l_nil (arg_domain sg t th b)

let rec value_args_snoc (args: list spine_arg) (a: spine_arg)
  : Lemma (ensures value_args (L.append args [a]) ==
                   L.append (value_args args) (match a with SVal v -> [v] | _ -> []))
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: args' -> value_args_snoc args' a

let chain_domains_apply_arg sg e a =
  decompose_apply_arg e a;
  let Some (q, ks, args) = decompose_global_app e in
  value_args_snoc args a;
  match global_scheme sg q with
  | Some (_, nk, t) -> if L.length ks = nk then cursor_domains_snoc sg (kinst_ty ks t) tvar args a
  | None -> ()

(* The instantiated constructor scheme. *)

let rec kinst_foralls (ks: list kind) (ps: list kind) (t: typ)
  : Lemma (ensures kinst_ty ks (foralls ps t) == foralls (kinst_kinds ks ps) (kinst_ty ks t))
          (decreases ps) =
  match ps with
  | [] -> ()
  | _ :: ps' -> kinst_foralls ks ps' t

let rec kinst_pure_arrows (ks: list kind) (fs: list typ) (t: typ)
  : Lemma (ensures kinst_ty ks (pure_arrows fs t) == pure_arrows (kinst_tys ks fs) (kinst_ty ks t))
          (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs' ->
    kinst_pure_arrows ks fs' t;
    (* one application node at a time *)
    let h = TCon prim_function [] in
    let x = pure_arrows fs' t in
    assert (kinst_ty ks h == h);
    assert (kinst_ty ks (TApp h f) == TApp h (kinst_ty ks f));
    assert (kinst_ty ks (TApp (TApp h f) TRowEmpty) == TApp (TApp h (kinst_ty ks f)) TRowEmpty);
    assert (kinst_ty ks (TApp (TApp (TApp h f) TRowEmpty) x) ==
            TApp (TApp (TApp h (kinst_ty ks f)) TRowEmpty) (kinst_ty ks x))

let rec kinst_tapps (ks: list kind) (h: typ) (ts: list typ)
  : Lemma (ensures kinst_ty ks (tapps h ts) == tapps (kinst_ty ks h) (kinst_tys ks ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> kinst_tapps ks (TApp h t) ts'

let rec kinst_type_vars (ks: list kind) (n: nat)
  : Lemma (ensures kinst_tys ks (type_vars n) == type_vars n) (decreases n) =
  if n = 0 then () else kinst_type_vars ks (n - 1)

let rec kinst_tys_length (ks: list kind) (ts: list typ)
  : Lemma (ensures L.length (kinst_tys ks ts) == L.length ts) (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts' -> kinst_tys_length ks ts'

let rec drop (#a: Type) (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then l else match l with [] -> [] | _ :: l -> drop (n - 1) l

let rec drop_index (#a: Type) (i: nat) (l: list a)
  : Lemma (requires i < L.length l) (ensures drop i l == L.index l i :: drop (i + 1) l)
          (decreases i) =
  if i = 0 then () else drop_index (i - 1) (L.tl l)

let rec drop_length (#a: Type) (l: list a)
  : Lemma (ensures drop (L.length l) l == []) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l' -> drop_length l'

let rec kinst_kvars_from (ks: list kind) (i m: nat)
  : Lemma (requires i + m == L.length ks) (ensures kinst_kinds ks (kvars_from i m) == drop i ks)
          (decreases m) =
  if m = 0 then drop_length ks
  else begin
    kinst_kvars_from ks (i + 1) (m - 1);
    drop_index i ks
  end

(* A remainder headed by a constructor other than a function type
   constructor is no arrow. *)

let rec tapps_head (h: typ) (ts: list typ)
  : Lemma (requires TCon? h \/ TApp? h)
          (ensures (TCon? (tapps h ts) \/ TApp? (tapps h ts)) /\ ty_head (tapps h ts) == ty_head h)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> tapps_head (TApp h t) ts'

let headed_no_arrow (sg: sig) (t: typ) (q: qname)
  : Lemma (requires (TCon? t \/ TApp? t) /\ ty_head t == Some q /\ not (is_function_tycon sg q))
          (ensures as_function sg t == None /\ fun_args sg t == [] /\ saturated sg t) =
  match t with
  | TApp (TApp (TApp h a) b) _ ->
    assert (ty_head t == ty_head (TApp (TApp h a) b));
    assert (ty_head (TApp (TApp h a) b) == ty_head (TApp h a));
    assert (ty_head (TApp h a) == ty_head h)
  | _ -> ()

let function_tycon (sg: sig)
  : Lemma (requires prim_wf sg) (ensures is_function_tycon sg prim_function) = ()

(* The cursor through the binders of the parameters and through the
   arrows of the fields. *)

let rec scons_all (ss: list typ) (th: tsub) : Tot tsub (decreases ss) =
  match ss with
  | [] -> th
  | s :: ss -> scons_all ss (scons s th)

let rec ty_prefix (args: list spine_arg) : Tot (list typ) (decreases args) =
  match args with
  | STy t :: args -> t :: ty_prefix args
  | _ -> []

let rec after_tys (args: list spine_arg) : Tot (list spine_arg) (decreases args) =
  match args with
  | STy _ :: args -> after_tys args
  | _ -> args

let rec split_tys (args: list spine_arg)
  : Lemma (ensures args == L.append (L.map STy (ty_prefix args)) (after_tys args)) (decreases args) =
  match args with
  | STy _ :: args' -> split_tys args'
  | _ -> ()

let rec walk_foralls (sg: sig) (kps: list kind) (b: typ) (th: tsub) (args: list spine_arg)
  (t1: typ) (th1: tsub)
  : Lemma (requires cursor sg (foralls kps b) th args == Some (t1, th1) /\ saturated sg t1 /\
                    not (TForall? b))
          (ensures L.length (ty_prefix args) == L.length kps /\
                   cursor sg b (scons_all (ty_prefix args) th) (after_tys args) == Some (t1, th1) /\
                   cursor_domains sg (foralls kps b) th args ==
                   cursor_domains sg b (scons_all (ty_prefix args) th) (after_tys args))
          (decreases kps) =
  match kps with
  | [] -> (match args with STy _ :: _ -> () | _ -> ())
  | _ :: kps' ->
    match args with
    | STy s :: args' -> walk_foralls sg kps' b (scons s th) args' t1 th1
    | _ -> ()

let rec walk_arrows (sg: sig) (fs: list typ) (res: typ) (th: tsub) (args: list spine_arg)
  (t1: typ) (th1: tsub)
  : Lemma (requires prim_wf sg /\ cursor sg (pure_arrows fs res) th args == Some (t1, th1) /\
                    saturated sg t1 /\ saturated sg res)
          (ensures args == L.map SVal (value_args args) /\ L.length (value_args args) == L.length fs /\
                   t1 == res /\ th1 == th /\
                   cursor_domains sg (pure_arrows fs res) th args == L.map (sub_ty th) fs)
          (decreases fs) =
  function_tycon sg;
  match fs with
  | [] -> (match args with [] -> () | _ :: _ -> ())
  | f :: fs' ->
    as_function_fun_ty sg prim_function f TRowEmpty (pure_arrows fs' res);
    match args with
    | SVal _ :: args' -> walk_arrows sg fs' res th args' t1 th1
    | _ -> ()

(* The instantiation `ctor_fields` reads. *)

let rec inst_sub_foralls (kps: list kind) (b: typ) (th: tsub) (ss: list typ)
  : Lemma (requires L.length ss == L.length kps)
          (ensures inst_foralls (sub_ty th (foralls kps b)) ss == Some (sub_ty (scons_all ss th) b))
          (decreases kps) =
  match kps, ss with
  | [], [] -> ()
  | _ :: kps', s :: ss' ->
    cursor_instance_forall s th (foralls kps' b);
    inst_sub_foralls kps' b (scons s th) ss'

let rec sub_pure_arrows (sigma: tsub) (fs: list typ) (t: typ)
  : Lemma (ensures sub_ty sigma (pure_arrows fs t) == pure_arrows (L.map (sub_ty sigma) fs) (sub_ty sigma t))
          (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs' ->
    sub_pure_arrows sigma fs' t;
    (* one application node at a time *)
    let h = TCon prim_function [] in
    let x = pure_arrows fs' t in
    assert (sub_ty sigma h == h);
    assert (sub_ty sigma (TApp h f) == TApp h (sub_ty sigma f));
    assert (sub_ty sigma (TApp (TApp h f) TRowEmpty) == TApp (TApp h (sub_ty sigma f)) TRowEmpty);
    assert (sub_ty sigma (TApp (TApp (TApp h f) TRowEmpty) x) ==
            TApp (TApp (TApp h (sub_ty sigma f)) TRowEmpty) (sub_ty sigma x))

let rec fun_args_pure_arrows (sg: sig) (fs: list typ) (t: typ)
  : Lemma (requires prim_wf sg) (ensures fun_args sg (pure_arrows fs t) == L.append fs (fun_args sg t))
          (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs' -> function_tycon sg; fun_args_pure_arrows sg fs' t

let rec sub_tapps (sigma: tsub) (h: typ) (ts: list typ)
  : Lemma (ensures sub_ty sigma (tapps h ts) == tapps (sub_ty sigma h) (L.map (sub_ty sigma) ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> sub_tapps sigma (TApp h t) ts'

(* `σ̄` consed in order: the variable `i` below `|σ̄|` is the
   `(|σ̄| - 1 - i)`-th of `σ̄`, the last written being index 0. *)
let rec scons_all_at (ss: list typ) (th: tsub) (i: nat)
  : Lemma (ensures scons_all ss th i ==
                   (if i < L.length ss then L.index ss (L.length ss - 1 - i) else th (i - L.length ss)))
          (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' -> scons_all_at ss' (scons s th) i

let rec sub_type_vars (ss: list typ) (th: tsub) (m: nat)
  : Lemma (requires m <= L.length ss)
          (ensures L.map (sub_ty (scons_all ss th)) (type_vars m) == drop (L.length ss - m) ss)
          (decreases m) =
  if m = 0 then drop_length ss
  else begin
    sub_type_vars ss th (m - 1);
    scons_all_at ss th (m - 1);
    drop_index (L.length ss - m) ss
  end

let rec spine_args_shape (ss: list typ) (vs: list exp)
  : Lemma (ensures ty_args (L.append (L.map STy ss) (L.map SVal vs)) == ss /\
                   value_args (L.append (L.map STy ss) (L.map SVal vs)) == vs)
          (decreases ss) =
  match ss with
  | [] ->
    let rec aux (vs: list exp)
      : Lemma (ensures ty_args (L.map SVal vs) == [] /\ value_args (L.map SVal vs) == vs)
              (decreases vs) =
      match vs with [] -> () | _ :: vs' -> aux vs'
    in
    aux vs
  | _ :: ss' -> spine_args_shape ss' vs

let rec value_args_after_tys (args: list spine_arg)
  : Lemma (ensures value_args (after_tys args) == value_args args) (decreases args) =
  match args with
  | STy _ :: args' -> value_args_after_tys args'
  | _ -> ()

let ctor_chain_saturated sg e c ks args ci t th =
  let Some ti = sg.tycons ci.ct_owner in
  assert (ctor_ok sg c ci);
  let fs0 = ctor_decl_fields ti ci.ct_ty in
  let ps = arg_kinds ti.tc_kind in
  let n = L.length ps in
  let nk = ti.tc_nk in
  let owner = ci.ct_owner in
  assert (global_scheme sg c == Some (GCtor, nk, ci.ct_ty));
  assert (L.length ks == nk);
  (* The instantiated scheme. *)
  let res0 = tapps (TCon owner (kind_vars nk)) (type_vars n) in
  let res = tapps (TCon owner ks) (type_vars n) in
  let kfs = kinst_tys ks fs0 in
  let kps = kinst_kinds ks ps in
  let b = pure_arrows kfs res in
  kinst_foralls ks ps (pure_arrows fs0 res0);
  kinst_pure_arrows ks fs0 res0;
  kinst_tapps ks (TCon owner (kind_vars nk)) (type_vars n);
  kinst_type_vars ks n;
  kinst_kvars_from ks 0 nk;
  assert (kinst_ty ks ci.ct_ty == foralls kps b);
  kinst_kinds_length ks ps;
  kinst_tys_length ks fs0;
  (* The remainder at the end. *)
  tapps_head (TCon owner ks) (type_vars n);
  headed_no_arrow sg res owner;
  assert (not (TForall? b));
  (* The walk. *)
  walk_foralls sg kps b tvar args t th;
  let ss = ty_prefix args in
  let theta = scons_all ss tvar in
  walk_arrows sg kfs res theta (after_tys args) t th;
  split_tys args;
  value_args_after_tys args;
  spine_args_shape ss (value_args args);
  (* The instance. *)
  sub_tapps theta (TCon owner ks) (type_vars n);
  sub_type_vars ss tvar n;
  (* The fields. *)
  sub_ty_tvar (foralls kps b);
  inst_sub_foralls kps b tvar ss;
  sub_pure_arrows theta kfs res;
  tapps_head (TCon owner ks) (L.map (sub_ty theta) (type_vars n));
  headed_no_arrow sg (sub_ty theta res) owner;
  fun_args_pure_arrows sg (L.map (sub_ty theta) kfs) (sub_ty theta res);
  L.append_l_nil (L.map (sub_ty theta) kfs)
