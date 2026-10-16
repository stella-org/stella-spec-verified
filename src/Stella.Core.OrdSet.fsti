(**
 * Finite sets as sorted, duplicate-free lists (design §2.1).
 *
 * The canonical form of a row holds two finite sets, of entries and of
 * tails. Representing each set by the strictly increasing list of its
 * elements makes set equality coincide with list equality, so canonical
 * forms stay an eqtype and type equality stays a boolean computation.
 *
 * ## The order
 *
 * An element type is ordered through an injective *encoding* into a list of
 * tokens (`tokens = list nat`), compared lexicographically (`lex_lt`). An
 * `ord a` is such an encoding. Irreflexivity, transitivity and totality are
 * proved once, for `lex_lt`, and transfer to every `ord` through
 * injectivity, so each element type only has to show that its encoding is
 * injective. The encodings of the canonical forms are in `Stella.Core.Rows`.
 *
 * ## Sets
 *
 * `norm o l` sorts `l` by insertion and drops repeated elements. The core
 * facts are
 *
 *   - `norm_ext`:    `norm o l1 == norm o l2 <==> seteq l1 l2`, where
 *                    `seteq` is equality of the membership predicates;
 *   - `norm_sorted`: `norm o l == l` when `l` is already `sorted`.
 *
 * Every later fact about the canonical form of a row reduces to membership
 * through these two.
 *)
module Stella.Core.OrdSet
module L = FStar.List.Tot

(** * Tokens and their lexicographic order *)

type tokens = list nat

(** The strict lexicographic order: a proper prefix comes first. *)
let rec lex_lt (a b: tokens) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> false
  | [], _ :: _ -> true
  | _ :: _, [] -> false
  | x :: a, y :: b -> x < y || (x = y && lex_lt a b)

(** * Orders by encoding *)

let injective (#a: Type) (f: a -> tokens) : prop =
  forall (x y: a). {:pattern f x; f y} f x == f y ==> x == y

(** An injective encoding into tokens, inducing a strict total order. *)
type ord (a: eqtype) = f: (a -> tokens){injective f}

let lt (#a: eqtype) (o: ord a) (x y: a) : bool = lex_lt (o x) (o y)

val lt_irrefl (#a: eqtype) (o: ord a) (x: a) : Lemma (not (lt o x x))

val lt_trans (#a: eqtype) (o: ord a) (x y z: a)
  : Lemma (requires lt o x y /\ lt o y z) (ensures lt o x z)

val lt_total (#a: eqtype) (o: ord a) (x y: a)
  : Lemma (requires x <> y) (ensures lt o x y \/ lt o y x)

(** * Sorted lists *)

(** Strictly increasing, hence duplicate-free. *)
let rec sorted (#a: eqtype) (o: ord a) (l: list a) : Tot bool (decreases l) =
  match l with
  | [] | [_] -> true
  | x :: y :: tl -> lt o x y && sorted o (y :: tl)

(** Insertion into a sorted list; an element already present is not added
    again. *)
let rec insert (#a: eqtype) (o: ord a) (x: a) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> [x]
  | y :: tl -> if x = y then l else if lt o x y then x :: l else y :: insert o x tl

(** The sorted, duplicate-free list of the elements of `l`. *)
let rec norm (#a: eqtype) (o: ord a) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | x :: tl -> insert o x (norm o tl)

(** * Inclusion and equality of membership *)

let incl (#a: eqtype) (l1 l2: list a) : prop = forall (z: a). L.mem z l1 ==> L.mem z l2

let seteq (#a: eqtype) (l1 l2: list a) : prop = incl l1 l2 /\ incl l2 l1

(** * Facts *)

val mem_insert (#a: eqtype) (o: ord a) (x: a) (l: list a) (z: a)
  : Lemma (L.mem z (insert o x l) = (z = x || L.mem z l))

val mem_norm (#a: eqtype) (o: ord a) (l: list a) (z: a)
  : Lemma (L.mem z (norm o l) = L.mem z l) [SMTPat (L.mem z (norm o l))]

val sorted_insert (#a: eqtype) (o: ord a) (x: a) (l: list a)
  : Lemma (requires sorted o l) (ensures sorted o (insert o x l))

val sorted_norm (#a: eqtype) (o: ord a) (l: list a) : Lemma (sorted o (norm o l))

(** Two sorted lists with the same members are equal. *)
val sorted_ext (#a: eqtype) (o: ord a) (l1 l2: list a)
  : Lemma (requires sorted o l1 /\ sorted o l2 /\ seteq l1 l2) (ensures l1 == l2)

val norm_sorted (#a: eqtype) (o: ord a) (l: list a)
  : Lemma (requires sorted o l) (ensures norm o l == l)

val norm_idem (#a: eqtype) (o: ord a) (l: list a) : Lemma (norm o (norm o l) == norm o l)

(** The core set lemma: `norm` identifies exactly the lists with the same
    members. *)
val norm_ext (#a: eqtype) (o: ord a) (l1 l2: list a)
  : Lemma (norm o l1 == norm o l2 <==> seteq l1 l2)
