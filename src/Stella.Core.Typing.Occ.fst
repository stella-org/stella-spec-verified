(* Proof structure.

   A projection is a value by recursion on the occurrence: the value
   arguments of a value chain are values (`chain_values_view`), and so are
   the fields of a record value and the payload of a variant value.

   `occ_sound` recurses on the occurrence derivation: an entry of `Ω` is
   found in `match_typing` at the position `L.assoc` finds it, and a record
   field is read by the canonical form of the record value at the
   occurrence below. Each branch selection recurses on the branch typing
   along `L.assoc`; the branch typings of `switchKey` pair the keys of the
   branches with those of the split, so the key found in one is found in
   the other at the same position.

   A `switchKey` payload is typed at the payload of its view
   (`inv_variant`) and converted to the payload type of the split, the
   entry of each being one of the kinded row, which is sharp in a
   consistent context. In the default, the entry of the view's key is one
   of the residual (`key_split_residual`).

   The `match_typing` builders walk a list with the prefix already
   consumed, whose length is the index of the next occurrence. *)
module Stella.Core.Typing.Occ
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Sharp
open Stella.Core.Kinding.Facts
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Regularity
open Stella.Core.Typing.Inversion
open Stella.Core.Typing.Values
open Stella.Core.Typing.Keys
open Stella.Core.Typing.Canonical
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* Lists. *)

let rec nth_for_all (#a: Type) (f: a -> bool) (l: list a) (i: nat) (x: a)
  : Lemma (requires L.for_all f l /\ L.nth l i == Some x) (ensures f x) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else nth_for_all f l' (i - 1) x

let rec nth_append_len (#a: Type) (pre: list a) (x: a) (l: list a)
  : Lemma (ensures L.nth (L.append pre (x :: l)) (L.length pre) == Some x) (decreases pre) =
  match pre with
  | [] -> ()
  | _ :: pre' -> nth_append_len pre' x l

let snoc_append (#a: Type) (pre: list a) (x: a) (l: list a)
  : Lemma (L.append pre (x :: l) == L.append (L.append pre [x]) l /\
           L.length (L.append pre [x]) == L.length pre + 1) =
  LP.append_assoc pre [x] l;
  LP.append_length pre [x]

let assoc_some (#a: eqtype) (#b: Type) (x: a) (l: list (a & b))
  : Lemma (L.mem x (L.map fst l) <==> Some? (L.assoc x l)) =
  LP.assoc_mem x l

(* Projections of values. *)

let rec args_nth_value (sg: sig) (args: list spine_arg) (j: nat) (w: exp)
  : Lemma (requires V.args_values sg args /\ L.nth (value_args args) j == Some w)
          (ensures V.is_value sg w) (decreases args) =
  match args with
  | SVal _ :: args' -> if j = 0 then () else args_nth_value sg args' (j - 1) w
  | _ :: args' -> args_nth_value sg args' j w

let chain_args_values (sg: sig) (v: exp)
  : Lemma (requires V.is_value sg v /\ Some? (decompose_global_app v))
          (ensures (let Some (_, _, args) = decompose_global_app v in V.args_values sg args)) =
  match v with
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> V.chain_values_view sg v

let ctor_field_value (sg: sig) (q: qname) (j: nat) (v w: exp)
  : Lemma (requires V.is_value sg v /\ ctor_field sg q j v == Some w) (ensures V.is_value sg w) =
  chain_args_values sg v;
  let Some (_, _, args) = decompose_global_app v in
  args_nth_value sg args j w

let rec record_field_value (sg: sig) (k: key) (v w: exp)
  : Lemma (requires V.is_value sg v /\ record_field k v == Some w) (ensures V.is_value sg w)
          (decreases v) =
  match v with
  | EExtend k' _ v2 -> if k' = k then () else record_field_value sg k v2 w

let variant_payload_value (sg: sig) (k: key) (v w: exp)
  : Lemma (requires V.is_value sg v /\ variant_payload k v == Some w) (ensures V.is_value sg w) =
  variant_payload_view k v;
  let Some (k', w') = variant_view v in
  variant_view_value sg v k' w'

let rec proj_value sg th o v =
  match o with
  | OScrut i -> nth_for_all (V.is_value sg) th i v
  | OCtor o' q j ->
    let Some v' = proj sg th o' in
    proj_value sg th o' v';
    ctor_field_value sg q j v' v
  | ORecord o' k ->
    let Some v' = proj sg th o' in
    proj_value sg th o' v';
    record_field_value sg k v' v
  | OVariant o' k ->
    let Some v' = proj sg th o' in
    proj_value sg th o' v';
    variant_payload_value sg k v' v

let variant_payload_of_view k v w = variant_payload_view k v

(* Soundness of occurrences. *)

let rec match_typing_lookup #sg #ln #g #d #r #th #om hm o t
  : Pure (v: exp & typing sg ln g d v t r)
         (requires L.assoc o om == Some t)
         (ensures fun (| v, _ |) -> proj sg th o == Some v)
         (decreases hm) =
  match hm with
  | TM_Cons #_ #_ #_ #_ #_ #_ #o' #_ #_ #v' _ hv hm' ->
    if o' = o then (| v', hv |) else match_typing_lookup hm' o t

let rec occ_sound #sg #ln #g #r #th #om #o #t_o hm ho
  : Pure (v: exp & typing sg ln g [] v t_o r)
         (requires sig_ok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   L.for_all (V.is_value sg) th)
         (ensures fun (| v, _ |) -> proj sg th o == Some v /\ V.is_value sg v)
         (decreases ho) =
  match ho with
  | TO_Lookup _ ->
    let (| v, hv |) = match_typing_lookup hm o t_o in
    proj_value sg th o v;
    (| v, hv |)
  | TO_Field #_ #_ #_ #_ #k #_ #_ rr ho' _ _ ->
    let (| v0, h0 |) = occ_sound hm ho' in
    let (| w, hw |) = canonical_record_field h0 rr k t_o in
    (| w, hw |)

(* Branch selection. *)

let rec ctor_brs_select #sg #ln #g #d #om #o #ks #ss #cs #bs #t #r hb c dt
  : Pure (fs: list typ & dt_typing sg ln g d (L.append (field_occs o c 0 fs) om) dt t r)
         (requires branch (Some c) bs == Some dt)
         (ensures fun (| fs, _ |) -> L.mem c cs /\ ctor_fields sg c ks ss == Some fs)
         (decreases hb) =
  match hb with
  | TCB_Cons #_ #_ #_ #_ #_ #_ #_ #_ #_ #c' #_ #_ #_ #_ #fs' _ hdt hrest ->
    if c' = c then (| fs', hdt |) else ctor_brs_select hrest c dt

let rec lit_brs_select #sg #ln #g #d #om #lt #bs #t #r hb c dt
  : Pure (dt_typing sg ln g d om dt t r)
         (requires branch (Some c) bs == Some dt)
         (ensures fun _ -> ty_eq (lit_type c) lt)
         (decreases hb) =
  match hb with
  | TLB_Cons #_ #_ #_ #_ #_ #_ #c' #_ #_ #_ #_ _ hdt hrest ->
    if c' = c then hdt else lit_brs_select hrest c dt

let rec key_brs_select #sg #ln #g #d #om #o #kts #bs #t #r hb k dt
  : Pure (pt: typ & dt_typing sg ln g d ((OVariant o k, pt) :: om) dt t r)
         (requires branch (Some k) bs == Some dt)
         (ensures fun (| pt, _ |) -> L.assoc k kts == Some pt /\ L.mem (k, pt) kts /\
                                    check sg g pt KType)
         (decreases hb) =
  match hb with
  | TKB_Cons #_ #_ #_ #_ #_ #_ #k' #pt' #_ #_ #_ #_ #_ _ hdt hrest ->
    if k' = k then (| pt', hdt |)
    else let (| pt, hdt' |) = key_brs_select hrest k dt in (| pt, hdt' |)

let variant_payload_typing #sg #ln #g #d #v #t_o #r h vr kts vr' k w pt =
  let p = inv_variant h k w vr in
  key_split_branch vr kts vr' k pt;
  check_sharp sg g vr EType;
  typing_regular p.var_h;
  T_Conv p.var_h () ()

(* Exhaustiveness. *)

let ctor_brs_exhaustive cs bs c = assoc_some c bs

let key_split_exhaustive_key vr kts k p =
  key_split_exhaustive vr kts;
  brs_entries_keys kts (k, p)

let key_brs_exhaustive #sg #ln #g #d #om #o #kts #bs #t #r hb vr k p =
  key_split_exhaustive_key vr kts k p;
  key_brs_typing_keys hb;
  assoc_some k bs

(* Defaults. *)

let key_default_typing #sg #ln #g #d #v #t_o #r #d' #om #o #kts #bs #t #r' h hb vr vr' =
  canonical_variant h vr;
  let Some (k, w) = variant_view v in
  key_brs_typing_keys hb;
  assoc_some k bs;
  let p = inv_variant h k w vr in
  key_split_residual vr kts vr' (k, PTy (canon p.var_ty));
  typing_regular h;
  check_t_variant sg g vr;
  check_t_variant sg g vr';
  let h0 : typing sg ln g [] v (t_variant vr) r = T_Conv (value_typing h [] r) () () in
  T_VariantValue #sg #ln #g #[] #v #k #w #p.var_ty #r vr vr' h0 () p.var_h ()

(* Building `match_typing`. *)

let rec scrut_go (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (th pre: list exp)
  (i: nat) (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts)
  : Pure (match_typing sg ln g d r th (scrut_occs i ts))
         (requires th == L.append pre es /\ i == L.length pre)
         (ensures fun _ -> True)
         (decreases h) =
  match h with
  | TE_Nil sq -> TM_Nil sq
  | TE_Cons #_ #_ #_ #_ #_ #e #es' #t #ts' he hes ->
    nth_append_len pre e es';
    snoc_append pre e es';
    TM_Cons #sg #ln #g #d #r #th #(OScrut i) #t #(scrut_occs (i + 1) ts') #e ()
      he (scrut_go th (L.append pre [e]) (i + 1) hes)

let match_typing_scrut #sg #ln #g #d #r #th #ts h = scrut_go th [] 0 h

let rec fields_go (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (o: occ) (v: exp) (c: qname) (ks: list kind) (args: list spine_arg) (pre: list exp) (j: nat)
  (#es: list exp) (#fs: list typ) (h: exps_typing sg ln g d r es fs)
  : Pure (match_typing sg ln g d r th (field_occs o c j fs))
         (requires proj sg th o == Some v /\ decompose_global_app v == Some (c, ks, args) /\
                   is_ctor sg c /\ value_args args == L.append pre es /\ j == L.length pre)
         (ensures fun _ -> True)
         (decreases h) =
  match h with
  | TE_Nil sq -> TM_Nil sq
  | TE_Cons #_ #_ #_ #_ #_ #e #es' #t #fs' he hes ->
    nth_append_len pre e es';
    snoc_append pre e es';
    TM_Cons #sg #ln #g #d #r #th #(OCtor o c j) #t #(field_occs o c (j + 1) fs') #e ()
      he (fields_go o v c ks args (L.append pre [e]) (j + 1) hes)

let match_typing_fields #sg #ln #g #d #r #th o v c ks args #fs hf =
  fields_go o v c ks args [] 0 hf

let match_typing_variant #sg #ln #g #d #r #th #om hm o v k #w #pt hw =
  variant_payload_view k v;
  TM_Cons #sg #ln #g #d #r #th #(OVariant o k) #pt #om #w () hw hm

let rec match_typing_append #sg #ln #g #d #r #th #om1 #om2 h1 h2
  : Tot (match_typing sg ln g d r th (L.append om1 om2)) (decreases h1) =
  match h1 with
  | TM_Nil _ -> h2
  | TM_Cons sq hv h1' -> TM_Cons sq hv (match_typing_append h1' h2)
