module Stella.Core.Kinding
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Context
module L = FStar.List.Tot

let rec qkind_kind_wf (nk: nat) (k: kind)
  : Lemma (requires qkind nk k) (ensures kind_wf nk k) (decreases k) =
  match k with
  | KArrow k1 k2 -> qkind_kind_wf nk k1; qkind_kind_wf nk k2
  | _ -> ()
