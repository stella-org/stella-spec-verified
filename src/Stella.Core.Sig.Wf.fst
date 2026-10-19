(* The readings of `globals_ok` follow the lists of a data type's
   constructors and of their tags. *)
module Stella.Core.Sig.Wf
open Stella.Core.Syntax
open Stella.Core.Sig
module L = FStar.List.Tot

let rec owned_by_mem (sg: sig) (q: qname) (cs: list qname) (c: qname)
  : Lemma (requires owned_by sg q cs /\ L.mem c cs)
          (ensures Some? (sg.ctors c) /\ (Some?.v (sg.ctors c)).ct_owner == q) (decreases cs) =
  match cs with
  | c' :: cs' -> if c = c' then () else owned_by_mem sg q cs' c

let ctor_of_data sg q ti cs c =
  assert (data_ok sg q cs);
  owned_by_mem sg q cs c

let rec mem_ctor_tags (sg: sig) (cs: list qname) (c: qname) (ci: ctor_info)
  : Lemma (requires L.mem c cs /\ sg.ctors c == Some ci) (ensures L.mem ci.ct_tag (ctor_tags sg cs))
          (decreases cs) =
  match cs with
  | c' :: cs' -> if c = c' then () else mem_ctor_tags sg cs' c ci

let rec tags_distinct (sg: sig) (cs: list qname) (c1 c2: qname) (ci1 ci2: ctor_info)
  : Lemma (requires L.noRepeats (ctor_tags sg cs) /\ L.mem c1 cs /\ L.mem c2 cs /\
                    sg.ctors c1 == Some ci1 /\ sg.ctors c2 == Some ci2 /\ ci1.ct_tag == ci2.ct_tag)
          (ensures c1 == c2) (decreases cs) =
  match cs with
  | c :: cs' ->
    if c1 = c && c2 = c then ()
    else if c1 = c then mem_ctor_tags sg cs' c2 ci2
    else if c2 = c then mem_ctor_tags sg cs' c1 ci1
    else tags_distinct sg cs' c1 c2 ci1 ci2

let ctor_tags_distinct sg c1 c2 ci1 ci2 =
  assert (ctor_ok sg c1 ci1);
  assert (ctor_ok sg c2 ci2);
  let Some ti = sg.tycons ci1.ct_owner in
  let TcData cs = ti.tc_class in
  assert (data_ok sg ci1.ct_owner cs);
  tags_distinct sg cs c1 c2 ci1 ci2
