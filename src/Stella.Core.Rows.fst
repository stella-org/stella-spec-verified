(* Injectivity of the encodings: `enc_* x r1 == enc_* y r2` implies
   `x == y /\ r1 == r2`, by induction on `x`. Equal tags select the same
   constructor, and the fields are then peeled off left to right, each
   field's induction hypothesis also equating the tokens that follow it. *)
module Stella.Core.Rows
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.OrdSet
module L = FStar.List.Tot
module U32 = FStar.UInt32

let char_code_inj (c1 c2: FStar.Char.char)
  : Lemma (requires FStar.Char.int_of_char c1 == FStar.Char.int_of_char c2) (ensures c1 == c2) =
  U32.v_inj (FStar.Char.u32_of_char c1) (FStar.Char.u32_of_char c2)

let rec enc_chars_inj (x y: list FStar.Char.char) (r1 r2: tokens)
  : Lemma (requires enc_chars x r1 == enc_chars y r2) (ensures x == y /\ r1 == r2) (decreases x) =
  match x, y with
  | c1 :: x, c2 :: y -> char_code_inj c1 c2; enc_chars_inj x y r1 r2
  | _ -> ()

let enc_string_inj (x y: string) (r1 r2: tokens)
  : Lemma (requires enc_string x r1 == enc_string y r2) (ensures x == y /\ r1 == r2) =
  enc_chars_inj (FStar.String.list_of_string x) (FStar.String.list_of_string y) r1 r2;
  FStar.String.string_of_list_of_string x;
  FStar.String.string_of_list_of_string y

let rec enc_strings_inj (x y: list string) (r1 r2: tokens)
  : Lemma (requires enc_strings x r1 == enc_strings y r2) (ensures x == y /\ r1 == r2)
          (decreases x) =
  match x, y with
  | s1 :: x, s2 :: y ->
    enc_string_inj s1 s2 (enc_strings x r1) (enc_strings y r2); enc_strings_inj x y r1 r2
  | _ -> ()

let enc_qname_inj (x y: qname) (r1 r2: tokens)
  : Lemma (requires enc_qname x r1 == enc_qname y r2) (ensures x == y /\ r1 == r2) =
  enc_strings_inj x.qmod y.qmod (enc_string x.qid r1) (enc_string y.qid r2);
  enc_string_inj x.qid y.qid r1 r2

let rec enc_kind_inj (x y: kind) (r1 r2: tokens)
  : Lemma (requires enc_kind x r1 == enc_kind y r2) (ensures x == y /\ r1 == r2) (decreases x) =
  match x, y with
  | KArrow a1 b1, KArrow a2 b2 ->
    enc_kind_inj a1 a2 (enc_kind b1 r1) (enc_kind b2 r2); enc_kind_inj b1 b2 r1 r2
  | _ -> ()

let rec enc_kinds_inj (x y: list kind) (r1 r2: tokens)
  : Lemma (requires enc_kinds x r1 == enc_kinds y r2) (ensures x == y /\ r1 == r2)
          (decreases x) =
  match x, y with
  | k1 :: x, k2 :: y -> enc_kind_inj k1 k2 (enc_kinds x r1) (enc_kinds y r2); enc_kinds_inj x y r1 r2
  | _ -> ()

let enc_key_inj (x y: key) (r1 r2: tokens)
  : Lemma (requires enc_key x r1 == enc_key y r2) (ensures x == y /\ r1 == r2) =
  match x, y with
  | SymbolKey s1, SymbolKey s2 | TagKey s1, TagKey s2 -> enc_string_inj s1 s2 r1 r2
  | EffectKey q1, EffectKey q2 -> enc_qname_inj q1 q2 r1 r2
  | _ -> ()

let rec enc_ctyp_inj (x y: ctyp) (r1 r2: tokens)
  : Lemma (requires enc_ctyp x r1 == enc_ctyp y r2) (ensures x == y /\ r1 == r2) (decreases x) =
  match x, y with
  | CCon q1 k1, CCon q2 k2 ->
    enc_qname_inj q1 q2 (enc_kinds k1 r1) (enc_kinds k2 r2); enc_kinds_inj k1 k2 r1 r2
  | CApp a1 b1, CApp a2 b2 ->
    enc_ctyp_inj a1 a2 (enc_ctyp b1 r1) (enc_ctyp b2 r2); enc_ctyp_inj b1 b2 r1 r2
  | CForall k1 a1, CForall k2 a2 ->
    enc_kind_inj k1 k2 (enc_ctyp a1 r1) (enc_ctyp a2 r2); enc_ctyp_inj a1 a2 r1 r2
  | CConstr c1 a1, CConstr c2 a2 ->
    enc_cconstr_inj c1 c2 (enc_ctyp a1 r1) (enc_ctyp a2 r2); enc_ctyp_inj a1 a2 r1 r2
  | CRow e1 t1, CRow e2 t2 ->
    enc_centries_inj e1 e2 (enc_ctyps t1 r1) (enc_ctyps t2 r2); enc_ctyps_inj t1 t2 r1 r2
  | _ -> ()

and enc_pay_inj (x y: cpayload) (r1 r2: tokens)
  : Lemma (requires enc_pay x r1 == enc_pay y r2) (ensures x == y /\ r1 == r2) (decreases x) =
  match x, y with
  | PTy c1, PTy c2 -> enc_ctyp_inj c1 c2 r1 r2
  | PEff q1 c1, PEff q2 c2 ->
    enc_qname_inj q1 q2 (enc_ctyps c1 r1) (enc_ctyps c2 r2); enc_ctyps_inj c1 c2 r1 r2
  | _ -> ()

and enc_centry_inj (x y: key & cpayload) (r1 r2: tokens)
  : Lemma (requires enc_centry x r1 == enc_centry y r2) (ensures x == y /\ r1 == r2)
          (decreases x) =
  match x, y with
  | (k1, p1), (k2, p2) -> enc_key_inj k1 k2 (enc_pay p1 r1) (enc_pay p2 r2); enc_pay_inj p1 p2 r1 r2

and enc_centries_inj (x y: list (key & cpayload)) (r1 r2: tokens)
  : Lemma (requires enc_centries x r1 == enc_centries y r2) (ensures x == y /\ r1 == r2)
          (decreases x) =
  match x, y with
  | e1 :: x, e2 :: y ->
    enc_centry_inj e1 e2 (enc_centries x r1) (enc_centries y r2); enc_centries_inj x y r1 r2
  | _ -> ()

and enc_ctyps_inj (x y: list ctyp) (r1 r2: tokens)
  : Lemma (requires enc_ctyps x r1 == enc_ctyps y r2) (ensures x == y /\ r1 == r2)
          (decreases x) =
  match x, y with
  | c1 :: x, c2 :: y -> enc_ctyp_inj c1 c2 (enc_ctyps x r1) (enc_ctyps y r2); enc_ctyps_inj x y r1 r2
  | _ -> ()

and enc_cconstr_inj (x y: cconstr) (r1 r2: tokens)
  : Lemma (requires enc_cconstr x r1 == enc_cconstr y r2) (ensures x == y /\ r1 == r2)
          (decreases x) =
  match x, y with
  | CCLacks k1 c1, CCLacks k2 c2 ->
    enc_key_inj k1 k2 (enc_ctyp c1 r1) (enc_ctyp c2 r2); enc_ctyp_inj c1 c2 r1 r2
  | CCDisj a1 b1, CCDisj a2 b2 ->
    enc_ctyp_inj a1 a2 (enc_ctyp b1 r1) (enc_ctyp b2 r2); enc_ctyp_inj b1 b2 r1 r2
  | _ -> ()

let enc_ctyp0_injective () =
  let aux (x y: ctyp) : Lemma (enc_ctyp0 x == enc_ctyp0 y ==> x == y) =
    FStar.Classical.move_requires (enc_ctyp_inj x y []) []
  in
  FStar.Classical.forall_intro_2 aux

let enc_centry0_injective () =
  let aux (x y: centry) : Lemma (enc_centry0 x == enc_centry0 y ==> x == y) =
    FStar.Classical.move_requires (enc_centry_inj x y []) []
  in
  FStar.Classical.forall_intro_2 aux
