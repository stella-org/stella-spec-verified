(* The proofs of the lemmas of `Stella.Core.Region`. *)
module Stella.Core.Region
open Stella.Core.Syntax
module L = FStar.List.Tot

let rec rmap_tys_length (f: region_ref -> region_ref) (l: list typ)
  : Lemma (ensures L.length (rmap_tys f l) == L.length l) (decreases l)
          [SMTPat (L.length (rmap_tys f l))] =
  match l with [] -> () | _ :: l -> rmap_tys_length f l

let rec rmap_binds_length (f: nat -> region_ref -> region_ref) (d: nat) (l: list (typ & exp))
  : Lemma (ensures L.length (rmap_binds f d l) == L.length l) (decreases l)
          [SMTPat (L.length (rmap_binds f d l))] =
  match l with [] -> () | _ :: l -> rmap_binds_length f d l

let mem_append (a: atom) (l1 l2: list atom)
  : Lemma (L.mem a (l1 @ l2) = (L.mem a l1 || L.mem a l2)) [SMTPat (L.mem a (l1 @ l2))] =
  FStar.List.Tot.Properties.append_mem l1 l2 a
