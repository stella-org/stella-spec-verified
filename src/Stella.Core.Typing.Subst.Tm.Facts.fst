(* Proof structure.

   Values: by induction on the value, as in
   `Stella.Core.Typing.Rename.Facts`. A value is no variable, so the
   substitution keeps its head form; a chain is read through its view,
   which the substitution maps argument by argument
   (`Stella.Core.Spine.decompose_sub_tm`), and whose cursor does not read
   the value arguments (`cursor_val_args`). The value at an occurrence
   follows the projection path through the same forms.

   Region names: a mutual induction over the term classes, as `sub_tm`
   itself is defined; a variable has no atom, and every other node keeps
   its own atoms. *)
module Stella.Core.Typing.Subst.Tm.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Tm
open Stella.Core.Region
open Stella.Core.Region.Lemmas
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* Chains. *)

let rec map_sub_tm_arg (sigma: esub) (args: list spine_arg)
  : Lemma (ensures L.map (sub_tm_arg sigma) args == L.map (val_arg (sub_tm sigma)) args)
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: args -> map_sub_tm_arg sigma args

let value_head_sub_tm (sg: sig) (sigma: esub) (e: exp)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures V.value_head sg (sub_tm sigma e) == V.value_head sg e) =
  decompose_sub_tm sigma e;
  let Some (q, ks, args) = decompose_global_app e in
  map_sub_tm_arg sigma args;
  match global_scheme sg q with
  | Some (_, nk, t) ->
    if L.length ks = nk then cursor_val_args sg (sub_tm sigma) (kinst_ty ks t) tvar args
  | None -> ()

let ctor_chain_decompose (sg: sig) (e: exp)
  : Lemma (requires V.value_head sg e) (ensures Some? (decompose_global_app e)) = ()

(* Values. *)

let rec value_form_sub_tm sg sigma e
  : Lemma (requires value_form sg e) (ensures value_form sg (sub_tm sigma e))
          (decreases %[e; 1]) =
  match e with
  | ETyLam _ v -> value_form_sub_tm sg (tyup_esub 1 sigma) v
  | ECLam _ v | EInject _ _ v -> value_form_sub_tm sg sigma v
  | EExtend _ v1 v2 -> value_form_sub_tm sg sigma v1; value_form_sub_tm sg sigma v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ctor_chain_form_sub_tm sg sigma e
  | _ -> ()

and ctor_chain_form_sub_tm (sg: sig) (sigma: esub) (e: exp)
  : Lemma (requires ctor_chain_form sg e) (ensures ctor_chain_form sg (sub_tm sigma e))
          (decreases %[e; 0]) =
  match e with
  | EApp f v -> ctor_chain_form_sub_tm sg sigma f; value_form_sub_tm sg sigma v
  | ETyApp f _ | ECApp f -> ctor_chain_form_sub_tm sg sigma f
  | _ -> ()

let rec is_value_sub_tm sg sigma e
  : Lemma (requires V.is_value sg e) (ensures V.is_value sg (sub_tm sigma e))
          (decreases %[e; 1]) =
  match e with
  | ETyLam _ v -> is_value_sub_tm sg (tyup_esub 1 sigma) v
  | ECLam _ v | EInject _ _ v | EWeaken _ _ v | EOpenEff _ v -> is_value_sub_tm sg sigma v
  | EExtend _ v1 v2 -> is_value_sub_tm sg sigma v1; is_value_sub_tm sg sigma v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ ->
    ctor_chain_decompose sg e;
    value_head_sub_tm sg sigma e;
    chain_values_sub_tm sg sigma e
  | _ -> ()

and chain_values_sub_tm (sg: sig) (sigma: esub) (e: exp)
  : Lemma (requires V.chain_values sg e) (ensures V.chain_values sg (sub_tm sigma e))
          (decreases %[e; 0]) =
  match e with
  | EApp f v -> chain_values_sub_tm sg sigma f; is_value_sub_tm sg sigma v
  | ETyApp f _ | ECApp f -> chain_values_sub_tm sg sigma f
  | _ -> ()

let rec values_sub_tm sg sigma es =
  match es with
  | [] -> ()
  | e :: es -> is_value_sub_tm sg sigma e; values_sub_tm sg sigma es

(* Occurrences. *)

let rec nth_sub_tm_exps (sigma: esub) (es: list exp) (i: nat) (v: exp)
  : Lemma (requires L.nth es i == Some v)
          (ensures L.nth (sub_tm_exps sigma es) i == Some (sub_tm sigma v)) (decreases es) =
  match es with
  | _ :: es -> if i = 0 then () else nth_sub_tm_exps sigma es (i - 1) v

let rec value_args_sub_tm (sigma: esub) (args: list spine_arg)
  : Lemma (ensures value_args (L.map (sub_tm_arg sigma) args) ==
                   sub_tm_exps sigma (value_args args))
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: args -> value_args_sub_tm sigma args

let ctor_field_sub_tm (sg: sig) (sigma: esub) (q: qname) (j: nat) (v0 v: exp)
  : Lemma (requires ctor_field sg q j v0 == Some v)
          (ensures ctor_field sg q j (sub_tm sigma v0) == Some (sub_tm sigma v)) =
  decompose_sub_tm sigma v0;
  let Some (_, _, args) = decompose_global_app v0 in
  value_args_sub_tm sigma args;
  nth_sub_tm_exps sigma (value_args args) j v

let rec record_field_sub_tm (sigma: esub) (k: key) (v0 v: exp)
  : Lemma (requires record_field k v0 == Some v)
          (ensures record_field k (sub_tm sigma v0) == Some (sub_tm sigma v)) (decreases v0) =
  match v0 with
  | EExtend k' _ v2 -> if k' = k then () else record_field_sub_tm sigma k v2 v

let rec variant_payload_sub_tm (sigma: esub) (k: key) (v0 v: exp)
  : Lemma (requires variant_payload k v0 == Some v)
          (ensures variant_payload k (sub_tm sigma v0) == Some (sub_tm sigma v)) (decreases v0) =
  match v0 with
  | EInject _ _ _ -> ()
  | EWeaken _ _ v1 -> variant_payload_sub_tm sigma k v1 v

let rec proj_sub_tm sg sigma th o v
  : Lemma (requires proj sg th o == Some v)
          (ensures proj sg (sub_tm_exps sigma th) o == Some (sub_tm sigma v)) (decreases o) =
  match o with
  | OScrut i -> nth_sub_tm_exps sigma th i v
  | OCtor o' q j ->
    let Some v0 = proj sg th o' in
    proj_sub_tm sg sigma th o' v0;
    ctor_field_sub_tm sg sigma q j v0 v
  | ORecord o' k ->
    let Some v0 = proj sg th o' in
    proj_sub_tm sg sigma th o' v0;
    record_field_sub_tm sigma k v0 v
  | OVariant o' k ->
    let Some v0 = proj sg th o' in
    proj_sub_tm sg sigma th o' v0;
    variant_payload_sub_tm sigma k v0 v

(* Region names. *)

let rec frn_sub_tm' (sigma: esub) (e: exp)
  : Lemma (ensures forall (a: atom). L.mem a (frn_exp e) ==> L.mem a (frn_exp (sub_tm sigma e)))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> frn_sub_tm' (up_esub sigma) b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    frn_sub_tm' sigma e1; frn_sub_tm' sigma e2
  | ETyLam _ b -> frn_sub_tm' (tyup_esub 1 sigma) b
  | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> frn_sub_tm' sigma b
  | ELet _ e1 e2 -> frn_sub_tm' sigma e1; frn_sub_tm' (up_esub sigma) e2
  | ELetRec bs b ->
    frn_sub_tm_binds (upn_esub (L.length bs) sigma) bs;
    frn_sub_tm' (upn_esub (L.length bs) sigma) b
  | ECase es dt | EMatch es dt -> frn_sub_tm_exps sigma es; frn_sub_tm_dt sigma dt
  | ELetJoin ts _ e1 e2 ->
    frn_sub_tm' (upn_esub (L.length ts) (jup_esub sigma)) e1; frn_sub_tm' (jup_esub sigma) e2
  | EJump _ es -> frn_sub_tm_exps sigma es
  | EHandle b h ->
    frn_sub_tm' sigma b; frn_sub_tm' (up_esub sigma) h.h_ret; frn_sub_tm_cls sigma h.h_clauses
  | ERegion _ es b -> frn_sub_tm_exps sigma es; frn_sub_tm' sigma b
  | ERegionOpen _ th b -> frn_sub_tm_cells sigma th; frn_sub_tm' sigma b

and frn_sub_tm_exps (sigma: esub) (es: list exp)
  : Lemma (ensures forall (a: atom). L.mem a (frn_exps es) ==>
                     L.mem a (frn_exps (sub_tm_exps sigma es)))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> frn_sub_tm' sigma e; frn_sub_tm_exps sigma es

and frn_sub_tm_binds (sigma: esub) (bs: list (typ & exp))
  : Lemma (ensures forall (a: atom). L.mem a (frn_binds bs) ==>
                     L.mem a (frn_binds (sub_tm_binds sigma bs)))
          (decreases bs) =
  match bs with
  | [] -> ()
  | p :: bs0 ->
    let (_, e) = p in
    frn_sub_tm' sigma e; frn_sub_tm_binds sigma bs0

and frn_sub_tm_cells (sigma: esub) (th: list (key & exp))
  : Lemma (ensures forall (a: atom). L.mem a (frn_cells th) ==>
                     L.mem a (frn_cells (sub_tm_cells sigma th)))
          (decreases th) =
  match th with
  | [] -> ()
  | p :: th0 ->
    let (_, e) = p in
    frn_sub_tm' sigma e; frn_sub_tm_cells sigma th0

and frn_sub_tm_dt (sigma: esub) (dt: dtree)
  : Lemma (ensures forall (a: atom). L.mem a (frn_dt dt) ==> L.mem a (frn_dt (sub_tm_dt sigma dt)))
          (decreases dt) =
  match dt with
  | DLeaf e -> frn_sub_tm' sigma e
  | DBind _ dt -> frn_sub_tm_dt (up_esub sigma) dt
  | DSwitchCtor _ bs df -> frn_sub_tm_brs sigma bs; frn_sub_tm_odt sigma df
  | DSwitchLit _ bs df -> frn_sub_tm_brs sigma bs; frn_sub_tm_dt sigma df
  | DSwitchKey _ bs df -> frn_sub_tm_kbrs sigma bs; frn_sub_tm_odt sigma df
  | DGuard e dt1 dt2 -> frn_sub_tm' sigma e; frn_sub_tm_dt sigma dt1; frn_sub_tm_dt sigma dt2

and frn_sub_tm_odt (sigma: esub) (df: option dtree)
  : Lemma (ensures forall (a: atom). L.mem a (frn_odt df) ==>
                     L.mem a (frn_odt (sub_tm_odt sigma df)))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> frn_sub_tm_dt sigma dt

and frn_sub_tm_brs (#lb: eqtype) (sigma: esub) (bs: list (lb & dtree))
  : Lemma (ensures forall (a: atom). L.mem a (frn_brs bs) ==>
                     L.mem a (frn_brs (sub_tm_brs sigma bs)))
          (decreases bs) =
  match bs with
  | [] -> ()
  | p :: bs0 ->
    let (_, dt) = p in
    frn_sub_tm_dt sigma dt; frn_sub_tm_brs sigma bs0

and frn_sub_tm_kbrs (sigma: esub) (bs: list (key & dtree))
  : Lemma (ensures forall (a: atom). L.mem a (frn_kbrs bs) ==>
                     L.mem a (frn_kbrs (sub_tm_brs sigma bs)))
          (decreases bs) =
  match bs with
  | [] -> ()
  | p :: bs0 ->
    let (_, dt) = p in
    frn_sub_tm_dt sigma dt; frn_sub_tm_kbrs sigma bs0

and frn_sub_tm_cls (sigma: esub) (cs: list clause)
  : Lemma (ensures forall (a: atom). L.mem a (frn_cls cs) ==>
                     L.mem a (frn_cls (sub_tm_cls sigma cs)))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    frn_sub_tm' (upn_esub 2 (tyup_esub nb sigma)) b; frn_sub_tm_cls sigma cs
  | CFast _ nb _ b :: cs -> frn_sub_tm' (up_esub (tyup_esub nb sigma)) b; frn_sub_tm_cls sigma cs

let frn_sub_tm sigma e a = frn_sub_tm' sigma e

let lc_ren_tm xi e =
  ren_tm_as_sub xi e;
  lc_sub_tm 0 (ren_esub xi) e

(* Forms. *)

let rec sub_tm_binds_fst sigma bs =
  match bs with
  | [] -> ()
  | _ :: bs -> sub_tm_binds_fst sigma bs

let rec clause_ops_sub_tm sigma cs =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ _ :: cs | CFast _ _ _ _ :: cs -> clause_ops_sub_tm sigma cs
