(* The proofs of the length lemmas of `Stella.Core.Subst`. *)
module Stella.Core.Subst
open Stella.Core.Syntax
module L = FStar.List.Tot

let rec ren_tys_length (xi: ren) (l: list typ)
  : Lemma (ensures L.length (ren_tys xi l) == L.length l) (decreases l)
          [SMTPat (L.length (ren_tys xi l))] =
  match l with [] -> () | _ :: l -> ren_tys_length xi l

let rec sub_tys_length (sigma: tsub) (l: list typ)
  : Lemma (ensures L.length (sub_tys sigma l) == L.length l) (decreases l)
          [SMTPat (L.length (sub_tys sigma l))] =
  match l with [] -> () | _ :: l -> sub_tys_length sigma l

let rec ren_ty_binds_length (xi: ren) (l: list (typ & exp))
  : Lemma (ensures L.length (ren_ty_binds xi l) == L.length l) (decreases l)
          [SMTPat (L.length (ren_ty_binds xi l))] =
  match l with [] -> () | _ :: l -> ren_ty_binds_length xi l

let rec sub_ty_binds_length (sigma: tsub) (l: list (typ & exp))
  : Lemma (ensures L.length (sub_ty_binds sigma l) == L.length l) (decreases l)
          [SMTPat (L.length (sub_ty_binds sigma l))] =
  match l with [] -> () | _ :: l -> sub_ty_binds_length sigma l

let rec ren_tm_binds_length (xi: ren) (l: list (typ & exp))
  : Lemma (ensures L.length (ren_tm_binds xi l) == L.length l) (decreases l)
          [SMTPat (L.length (ren_tm_binds xi l))] =
  match l with [] -> () | _ :: l -> ren_tm_binds_length xi l

let rec ren_jp_binds_length (xi: ren) (l: list (typ & exp))
  : Lemma (ensures L.length (ren_jp_binds xi l) == L.length l) (decreases l)
          [SMTPat (L.length (ren_jp_binds xi l))] =
  match l with [] -> () | _ :: l -> ren_jp_binds_length xi l

let rec sub_tm_binds_length (sigma: esub) (l: list (typ & exp))
  : Lemma (ensures L.length (sub_tm_binds sigma l) == L.length l) (decreases l)
          [SMTPat (L.length (sub_tm_binds sigma l))] =
  match l with [] -> () | _ :: l -> sub_tm_binds_length sigma l
