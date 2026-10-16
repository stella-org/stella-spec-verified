(* The order facts are proved for `lex_lt` and transferred through
   injectivity; the set facts are inductions on the lists. *)
module Stella.Core.OrdSet
module L = FStar.List.Tot

let rec lex_irrefl (a: tokens) : Lemma (not (lex_lt a a)) =
  match a with [] -> () | _ :: a -> lex_irrefl a

let rec lex_trans (a b c: tokens)
  : Lemma (requires lex_lt a b /\ lex_lt b c) (ensures lex_lt a c) (decreases a) =
  match a, b, c with
  | _ :: a, _ :: b, _ :: c -> if lex_lt a b && lex_lt b c then lex_trans a b c
  | _ -> ()

let rec lex_total (a b: tokens)
  : Lemma (requires a <> b) (ensures lex_lt a b \/ lex_lt b a) (decreases a) =
  match a, b with
  | x :: a, y :: b -> if x = y then lex_total a b
  | _ -> ()

let lt_irrefl #a o x = lex_irrefl (o x)

let lt_trans #a o x y z = lex_trans (o x) (o y) (o z)

let lt_total #a o x y = lex_total (o x) (o y)

let rec mem_insert #a o x l z =
  match l with
  | [] -> ()
  | y :: tl -> if x = y || lt o x y then () else mem_insert o x tl z

let rec mem_norm #a o l z =
  match l with
  | [] -> ()
  | x :: tl -> mem_norm o tl z; mem_insert o x (norm o tl) z

(* Every member of a sorted list's tail lies above its head. *)
let rec sorted_head_lt (#a: eqtype) (o: ord a) (x: a) (l: list a) (z: a)
  : Lemma (requires sorted o (x :: l) /\ L.mem z l) (ensures lt o x z) (decreases l) =
  match l with
  | y :: tl -> if z = y then () else (sorted_head_lt o y tl z; lt_trans o x y z)

let rec sorted_insert #a o x l =
  match l with
  | [] -> ()
  | y :: tl ->
    if x = y || lt o x y then ()
    else begin
      lt_total o x y;
      sorted_insert o x tl;
      (* the head of `insert o x tl` is `x` or the head of `tl`, both above `y` *)
      match insert o x tl with
      | h :: _ -> mem_insert o x tl h; if h = x then () else sorted_head_lt o y tl h
    end

let rec sorted_norm #a o l =
  match l with
  | [] -> ()
  | x :: tl -> sorted_norm o tl; sorted_insert o x (norm o tl)

let rec sorted_ext #a o l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | [], y :: _ -> assert (L.mem y l2)
  | x :: _, [] -> assert (L.mem x l1)
  | x :: t1, y :: t2 ->
    if x = y then begin
      let aux (z: a) : Lemma (L.mem z t1 = L.mem z t2) =
        if L.mem z t1 then (sorted_head_lt o x t1 z; lt_irrefl o z)
        else if L.mem z t2 then (sorted_head_lt o y t2 z; lt_irrefl o z)
      in
      FStar.Classical.forall_intro aux;
      sorted_ext o t1 t2
    end else begin
      (* each head is a member of the other tail, so each is above the other *)
      assert (L.mem x t2 /\ L.mem y t1);
      sorted_head_lt o y t2 x;
      sorted_head_lt o x t1 y;
      lt_trans o x y x;
      lt_irrefl o x
    end

let norm_sorted #a o l = sorted_norm o l; sorted_ext o (norm o l) l

let norm_idem #a o l = sorted_norm o l; norm_sorted o (norm o l)

let norm_ext #a o l1 l2 =
  sorted_norm o l1;
  sorted_norm o l2;
  FStar.Classical.move_requires (sorted_ext o (norm o l1)) (norm o l2)
