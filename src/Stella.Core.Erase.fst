module Stella.Core.Erase
open Stella.Core.Syntax
open Stella.Core.Rows
module L = FStar.List.Tot

let rec erase_exps_map (es: list exp) : Lemma (ensures erase_exps es == L.map erase es) (decreases es) =
  match es with
  | [] -> ()
  | _ :: es' -> erase_exps_map es'
