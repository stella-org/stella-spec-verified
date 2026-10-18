module Stella.Core.Init.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Init
module L = FStar.List.Tot

let rec value_count_append (a1 a2: list spine_arg)
  : Lemma (ensures value_count (L.append a1 a2) == value_count a1 + value_count a2)
          (decreases a1) =
  match a1 with
  | [] -> ()
  | _ :: a1 -> value_count_append a1 a2

(* A function type is `TCon q []` applied three times; kind instantiation
   keeps an empty kind vector empty and a non-empty one non-empty. *)
let rec decl_arity_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (ensures decl_arity sg (kinst_ty ks t) == decl_arity sg t) (decreases t) =
  match t with
  | TForall _ b | TConstr _ b -> decl_arity_kinst sg ks b
  | TApp (TApp (TApp (TCon _ kl) _) _) t2 ->
    (match kl with
     | [] -> decl_arity_kinst sg ks t2
     | _ :: _ -> ())
  | TApp (TApp (TApp _ _) _) _ -> ()
  | TApp (TApp _ _) _ -> ()
  | _ -> ()

let rec cursor_arity (sg: sig) (t: typ) (th: tsub) (args: list spine_arg)
  : Lemma (requires Some? (cursor sg t th args))
          (ensures (match cursor sg t th args with
                   | Some (t', _) -> decl_arity sg t == value_count args + decl_arity sg t'
                   | None -> True))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    match cursor_step sg t th a with
    | Some (t1, th1) -> cursor_arity sg t1 th1 rest
    | None -> ()

let saturated_arity (sg: sig) (t: typ)
  : Lemma (requires saturated sg t) (ensures decl_arity sg t == 0) =
  ()

let spine_cursor_arity (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg)
  : Lemma (requires Some? (spine_cursor sg q ks args))
          (ensures (match spine_cursor sg q ks args with
                   | Some (t', _) -> global_arity sg q == Some (value_count args + decl_arity sg t')
                   | None -> True)) =
  let Some (_, _, t) = global_scheme sg q in
  decl_arity_kinst sg ks t;
  cursor_arity sg (kinst_ty ks t) tvar args

let spine_saturated_arity (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg)
  : Lemma (requires spine_saturated sg q ks args)
          (ensures global_arity sg q == Some (value_count args)) =
  spine_cursor_arity sg q ks args;
  let Some (t', _) = spine_cursor sg q ks args in
  saturated_arity sg t'

(* `EApp (recompose q ks args) v` is the chain `recompose q ks (args @ [SVal v])`. *)
let decompose_app_recompose (q: qname) (ks: list kind) (args: list spine_arg) (v: exp)
  : Lemma (decompose_global_app (EApp (recompose q ks args) v) ==
           Some (q, ks, L.append args [SVal v])) =
  decompose_recompose q ks args

let spine_app_cursor (sg: sig) (g: group) (q: qname) (ks: list kind)
                     (args: list spine_arg) (v: exp)
  : Lemma (requires None? (g.gmem q) /\ Some? (spine_cursor sg q ks (L.append args [SVal v])))
          (ensures spine_app sg g (EApp (recompose q ks args) v)) =
  decompose_app_recompose q ks args v;
  spine_cursor_arity sg q ks (L.append args [SVal v])

let over_applied_default (sg: sig) (g: group) (q: qname) (ks: list kind)
                         (args: list spine_arg) (v: exp)
  : Lemma (requires spine_saturated sg q ks args)
          (ensures not (spine_app sg g (EApp (recompose q ks args) v)) /\
                   default_parts sg g (EApp (recompose q ks args) v) == [recompose q ks args; v]) =
  decompose_app_recompose q ks args v;
  value_count_append args [SVal v];
  spine_saturated_arity sg q ks args

let imm_nothing (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                (d: reads_imm sg g ve je e m)
  : Lemma (requires reads_nothing_now e) (ensures False) =
  match d with
  | IThrough _ _ | IBuild _ _ | ITake _ _ | ISpine _ _ | IDefault _ _ | IDefaultLat _ _
  | ICaseScrut _ _ _ | ICaseTree _ _ | IWhole _ _ _ _ | IWholeLat _ _ _ _ -> ()

let lat_nothing (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                (d: reads_lat sg g ve je e m)
  : Lemma (requires holds_nothing e) (ensures False) =
  match d with
  | LThrough _ _ | LBuild _ _ | LTake _ _ | LSpine _ _ | LDefault _ _
  | LCase _ _ | LWhole _ _ _ _ -> ()

let imm_var (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
            (i: nat) (d: reads_imm sg g ve je e m)
  : Lemma (requires e == EVar i) (ensures vlook ve i == VMem m) =
  match d with
  | IMember _ -> ()
  | IThrough _ _ | IBuild _ _ | ITake _ _ | ISpine _ _ | IDefault _ _ | IDefaultLat _ _
  | ICaseScrut _ _ _ | ICaseTree _ _ | IWhole _ _ _ _ | IWholeLat _ _ _ _ -> ()

let imm_global (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
               (q: qname) (ks: list kind) (d: reads_imm sg g ve je e m)
  : Lemma (requires e == EGlobal q ks) (ensures g.gmem q == Some m) =
  match d with
  | IMemberGlobal _ -> ()
  | IThrough _ _ | IBuild _ _ | ITake _ _ | ISpine _ _ | IDefault _ _ | IDefaultLat _ _
  | ICaseScrut _ _ _ | ICaseTree _ _ | IWhole _ _ _ _ | IWholeLat _ _ _ _ -> ()

let imm_spine_app (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                  (f v: exp)
                  (nf: (reads_imm sg g ve je f m -> Lemma False))
                  (nv: (reads_imm sg g ve je v m -> Lemma False))
                  (d: reads_imm sg g ve je e m)
  : Lemma (requires e == EApp f v /\ spine_app sg g e) (ensures False) =
  match d with
  | ISpine #_ #_ #_ #_ #_ #b _ d' ->
    if b = f then nf (coerce_eq () d') else nv (coerce_eq () d')
  | IThrough _ _ | IBuild _ _ | ITake _ _ | IDefault _ _ | IDefaultLat _ _
  | ICaseScrut _ _ _ | ICaseTree _ _ | IWhole _ _ _ _ | IWholeLat _ _ _ _ -> ()

let imm_through (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                (b: exp)
                (nb: (reads_imm sg g ve je b m -> Lemma False))
                (d: reads_imm sg g ve je e m)
  : Lemma (requires through e == Some b) (ensures False) =
  match d with
  | IThrough _ d' -> nb (coerce_eq () d')
  | IMember _ | IMemberGlobal _ | IBuild _ _ | ITake _ _ | ISpine _ _ | IDefault _ _
  | IDefaultLat _ _ | ICaseScrut _ _ _ | ICaseTree _ _ | IWhole _ _ _ _ | IWholeLat _ _ _ _ -> ()

let imm_build (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
              (nb: (b: exp{L.memP b (builds e)} -> reads_imm sg g ve je b m -> Lemma False))
              (d: reads_imm sg g ve je e m)
  : Lemma (requires Cons? (builds e)) (ensures False) =
  match d with
  | IBuild #_ #_ #_ #_ #_ #b _ d' -> nb b d'
  | IMember _ | IMemberGlobal _ | IThrough _ _ | ITake _ _ | ISpine _ _ | IDefault _ _
  | IDefaultLat _ _ | ICaseScrut _ _ _ | ICaseTree _ _ | IWhole _ _ _ _ | IWholeLat _ _ _ _ -> ()

let rec nth_memP (#a: Type) (l: list a) (i: nat) (x: a)
  : Lemma (requires L.nth l i == Some x) (ensures L.memP x l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> if i = 0 then () else nth_memP l (i - 1) x

let function_group_safe (sg: sig) (g: group)
  : Lemma (requires forall (r: exp). L.memP r g.grhs ==> ELam? r)
          (ensures init_safe sg g) =
  introduce forall (i: nat) (r: exp) (m: nat) (d: reads_imm sg g g.genv [] r m).
              rhs g i == Some r ==> m < i
  with introduce rhs g i == Some r ==> m < i
       with (nth_memP g.grhs i r; imm_nothing d)
