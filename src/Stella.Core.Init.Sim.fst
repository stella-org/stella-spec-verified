(* Proof structure.

   A backward simulation: a derivation that the related group reads a
   member gives one that the original group reads it.

   Environments are related entry by entry (`ent_rel`, `venv_rel`,
   `jent_rel`, `jenv_rel`), and the cutoff of a term is the length of the
   variable environment it stands under, for the term judged and for the
   term of every entry. A variable at or beyond the cutoff is beyond the
   environment, at `ρ = ∅`, and reads nothing.

   The inert lemma (`inert_imm`, …) shows that an inert term reads nothing
   under the environments of the image at that point, `bv` and `bj`: every
   environment the judgement reaches from it is `bv` or `bj` with inert
   entries pushed on top (`env_ok`, `jenv_ok`), and every term reached
   mentions only those entries and the variables beyond the whole
   environment (`tri_ok`). A variable then finds `VNone` or an inert entry,
   never a member; a jump finds an inert join point; a local group has no
   global member.

   The simulation is a mutual induction on the derivation of the image. It
   first sets aside a variable at or beyond the cutoff (`outside`), whose
   image is inert and reads nothing. Every other form has an image of the
   same shape, and the parts a rule reads off a form (`through`, `builds`,
   `takes`, `spine_parts`, `default_parts`, `scrutinised`, `children` and
   the decision-tree helpers) are related parts. Two cases differ from a
   plain congruence:

   - an inert term may be a chain, so an application of a variable at or
     beyond the cutoff may read as a chain in the image; the original reads
     its parts by the default rule, which reads them now as well;
   - a subexpression of the image (`sub`) may lie within an inert term
     (`dead`). Its reads are nothing by the inert lemma, and a jump there
     targets no join point outside that term.

   Each lemma concludes that a derivation exists (`ex`), so the relations
   can be propositions. *)
module Stella.Core.Init.Sim
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Init
open Stella.Core.Init.Lemmas
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module T = FStar.Tactics.V2

(* A variable at or beyond the cutoff, whose image is inert. *)
let outside (c: nat) (e: exp) : bool =
  match e with
  | EVar i -> i >= c
  | _ -> false

(* An inert term reads nothing. The environments it is read under extend
   the base `bv`, `bj` it stands under; the entries pushed on top of the
   base are inert, and the variables of a term are local or beyond the
   whole environment. *)

let dif (a b: nat) : nat = if a >= b then a - b else 0

(* Membership in a list of one or two elements. *)
let mem1 (#a: Type) (x y: a) : Lemma (requires L.memP y [x]) (ensures y == x) = ()

let mem2 (#a: Type) (x1 x2 y: a)
  : Lemma (requires L.memP y [x1; x2]) (ensures y == x1 \/ y == x2) =
  assert (L.memP y [x1; x2] <==> (y == x1 \/ (y == x2 \/ False)))
    by (T.norm [delta_only [`%L.memP]; iota; zeta])

let mem_cons2 (#a: Type) (x1 x2 y: a) (l: list a)
  : Lemma (requires L.memP y (x1 :: x2 :: l)) (ensures y == x1 \/ y == x2 \/ L.memP y l) =
  assert (L.memP y (x1 :: x2 :: l) <==> (y == x1 \/ (y == x2 \/ L.memP y l)))
    by (T.norm [delta_only [`%L.memP]; iota; zeta])

let rec ent_ok (bv: venv) (bj: jenv) (v: ventry) : Tot prop (decreases v) =
  match v with
  | VNone -> True
  | VMem _ -> False
  | VLat ve je e ->
    env_ok bv bj ve /\ jenv_ok bv bj je /\
    iner (dif (L.length ve) (L.length bv)) (L.length bv) (dif (L.length je) (L.length bj)) e
  | VRec ve je bs _ ->
    env_ok bv bj ve /\ jenv_ok bv bj je /\
    iner_binds (dif (L.length ve) (L.length bv) + L.length bs) (L.length bv)
      (dif (L.length je) (L.length bj)) bs
  | VArg d _ -> jent_ok bv bj d

and env_ok (bv: venv) (bj: jenv) (ve: venv) : Tot prop (decreases ve) =
  ve == bv \/ (match ve with [] -> False | v :: ve1 -> ent_ok bv bj v /\ env_ok bv bj ve1)

and jent_ok (bv: venv) (bj: jenv) (d: jentry) : Tot prop (decreases d) =
  match d with
  | JDef ve je n e1 e2 ->
    env_ok bv bj ve /\ jenv_ok bv bj je /\
    iner (dif (L.length ve) (L.length bv) + n) (L.length bv)
      (dif (L.length je) (L.length bj) + 1) e1 /\
    iner (dif (L.length ve) (L.length bv)) (L.length bv) (dif (L.length je) (L.length bj) + 1) e2

and jenv_ok (bv: venv) (bj: jenv) (je: jenv) : Tot prop (decreases je) =
  je == bj \/ (match je with [] -> False | d :: je1 -> jent_ok bv bj d /\ jenv_ok bv bj je1)

let tri_ok (bv: venv) (bj: jenv) (ve: venv) (je: jenv) (e: exp) : prop =
  env_ok bv bj ve /\ jenv_ok bv bj je /\
  iner (dif (L.length ve) (L.length bv)) (L.length bv) (dif (L.length je) (L.length bj)) e

let child_ok (bv: venv) (bj: jenv) (c: child) : prop = tri_ok bv bj c.cv c.cj c.ce

let dtri_ok (bv: venv) (bj: jenv) (cve: venv) (es: list exp) (ve: venv) (je: jenv) (dt: dtree)
  : prop =
  env_ok bv bj cve /\
  iner_exps (dif (L.length cve) (L.length bv)) (L.length bv) (dif (L.length je) (L.length bj)) es /\
  env_ok bv bj ve /\ jenv_ok bv bj je /\
  iner_dt (dif (L.length ve) (L.length bv)) (L.length bv) (dif (L.length je) (L.length bj)) dt

let rec env_ok_len (bv: venv) (bj: jenv) (ve: venv)
  : Lemma (requires env_ok bv bj ve) (ensures L.length ve >= L.length bv) (decreases ve) =
  match ve with
  | [] -> ()
  | _ :: ve1 -> FStar.Classical.move_requires (env_ok_len bv bj) ve1

let rec jenv_ok_len (bv: venv) (bj: jenv) (je: jenv)
  : Lemma (requires jenv_ok bv bj je) (ensures L.length je >= L.length bj) (decreases je) =
  match je with
  | [] -> ()
  | _ :: je1 -> FStar.Classical.move_requires (jenv_ok_len bv bj) je1

let rec nth_none (#a: Type) (l: list a) (i: nat)
  : Lemma (requires i >= L.length l) (ensures L.nth l i == None) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> nth_none l (i - 1)

let rec env_lookup_ok (bv: venv) (bj: jenv) (ve: venv) (i: nat)
  : Lemma (requires env_ok bv bj ve /\ i < dif (L.length ve) (L.length bv))
          (ensures ent_ok bv bj (vlook ve i)) (decreases ve) =
  match ve with
  | v :: ve1 ->
    if i = 0 then ()
    else begin
      FStar.Classical.move_requires (env_ok_len bv bj) ve1;
      FStar.Classical.move_requires (env_lookup_ok bv bj ve1) (i - 1)
    end

(* The entry of a variable of an inert term is inert. *)
let var_ent_ok (bv: venv) (bj: jenv) (ve: venv) (je: jenv) (i: nat)
  : Lemma (requires tri_ok bv bj ve je (EVar i)) (ensures ent_ok bv bj (vlook ve i)) =
  env_ok_len bv bj ve;
  if i >= L.length ve then nth_none ve i else env_lookup_ok bv bj ve i

let rec jenv_lookup_ok (bv: venv) (bj: jenv) (je: jenv) (j: nat)
  : Lemma (requires jenv_ok bv bj je /\ j < dif (L.length je) (L.length bj) /\ Some? (jlook je j))
          (ensures jent_ok bv bj (Some?.v (jlook je j))) (decreases je) =
  match je with
  | d :: je1 ->
    if j = 0 then ()
    else begin
      assert (jenv_ok bv bj je1);
      jenv_ok_len bv bj je1;
      jenv_lookup_ok bv bj je1 (j - 1)
    end

let push_ok (bv: venv) (bj: jenv) (v: ventry) (ve: venv)
  : Lemma (requires ent_ok bv bj v /\ env_ok bv bj ve)
          (ensures env_ok bv bj (v :: ve) /\
                   dif (L.length (v :: ve)) (L.length bv) == dif (L.length ve) (L.length bv) + 1) =
  env_ok_len bv bj ve

let jpush_ok (bv: venv) (bj: jenv) (d: jentry) (je: jenv)
  : Lemma (requires jent_ok bv bj d /\ jenv_ok bv bj je)
          (ensures jenv_ok bv bj (d :: je) /\
                   dif (L.length (d :: je)) (L.length bj) == dif (L.length je) (L.length bj) + 1) =
  jenv_ok_len bv bj je

let rec rec_entries_ok (bv: venv) (bj: jenv) (ve: venv) (je: jenv) (bs: list (typ & exp)) (n: nat)
  (ve0: venv)
  : Lemma (requires ent_ok bv bj (VRec ve je bs 0) /\ env_ok bv bj ve0)
          (ensures env_ok bv bj (L.append (rec_entries ve je bs n) ve0) /\
                   L.length (L.append (rec_entries ve je bs n) ve0) == n + L.length ve0)
          (decreases n) =
  if n = 0 then () else rec_entries_ok bv bj ve je bs (n - 1) ve0

let push_rec_ok (bv: venv) (bj: jenv) (ve: venv) (je: jenv) (bs: list (typ & exp))
  : Lemma (requires ent_ok bv bj (VRec ve je bs 0))
          (ensures env_ok bv bj (push_rec ve je bs) /\
                   dif (L.length (push_rec ve je bs)) (L.length bv)
                     == dif (L.length ve) (L.length bv) + L.length bs) =
  rec_entries_ok bv bj ve je bs (L.length bs) ve;
  env_ok_len bv bj ve

let rec arg_entries_ok (bv: venv) (bj: jenv) (d: jentry) (p n: nat) (ve0: venv)
  : Lemma (requires jent_ok bv bj d /\ env_ok bv bj ve0)
          (ensures env_ok bv bj (L.append (arg_entries d p n) ve0) /\
                   L.length (L.append (arg_entries d p n) ve0) == n + L.length ve0)
          (decreases n) =
  if n = 0 then () else arg_entries_ok bv bj d (p + 1) (n - 1) ve0

let join_body_ok (bv: venv) (bj: jenv) (d: jentry)
  : Lemma (requires jent_ok bv bj d) (ensures child_ok bv bj (join_body d)) =
  match d with
  | JDef ve je n _ _ -> arg_entries_ok bv bj d 0 n ve; env_ok_len bv bj ve; jpush_ok bv bj d je

let join_cont_ok (bv: venv) (bj: jenv) (d: jentry)
  : Lemma (requires jent_ok bv bj d) (ensures child_ok bv bj (join_cont d)) =
  match d with
  | JDef ve je n _ _ -> jpush_ok bv bj d je

let join_scope_ok (bv: venv) (bj: jenv) (d: jentry) (c: child)
  : Lemma (requires jent_ok bv bj d /\ L.memP c (join_scope d)) (ensures child_ok bv bj c) =
  join_body_ok bv bj d; join_cont_ok bv bj d; mem2 (join_body d) (join_cont d) c

(* The parts of an inert form are inert. *)

let iner_through (k c q: nat) (e: exp)
  : Lemma (requires iner k c q e /\ Some? (through e)) (ensures iner k c q (Some?.v (through e))) =
  match e with
  | ETyLam _ _ | ETyApp _ _ | ECLam _ _ | ECApp _ | EOpenEff _ _ | EOpenEffC _ _ -> ()

let iner_takes (k c q: nat) (e: exp)
  : Lemma (requires iner k c q e /\ Some? (takes e)) (ensures iner k c q (Some?.v (takes e))) =
  match e with
  | ESelect _ _ | ERestrict _ _ | EWeaken _ _ _ | EAbsurd _ _ -> ()

let iner_builds (k c q: nat) (e b: exp)
  : Lemma (requires iner k c q e /\ L.memP b (builds e)) (ensures iner k c q b) =
  match e with
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> mem2 e1 e2 b
  | EInject _ _ b0 -> mem1 b0 b

let iner_spine (sg: sig) (g: group) (k c q: nat) (e b: exp)
  : Lemma (requires iner k c q e /\ L.memP b (spine_parts sg g e)) (ensures iner k c q b) =
  match e with
  | EApp f v -> mem2 f v b

let iner_default (sg: sig) (g: group) (k c q: nat) (e b: exp)
  : Lemma (requires iner k c q e /\ L.memP b (default_parts sg g e)) (ensures iner k c q b) =
  match e with
  | EApp f v -> mem2 f v b
  | EPerform _ _ _ b0 | EWriteCell _ _ b0 | EFill _ b0 -> mem1 b0 b

let iner_scrut (k c q: nat) (e: exp)
  : Lemma (requires iner k c q e /\ Some? (scrutinised e))
          (ensures iner_exps k c q (fst (Some?.v (scrutinised e))) /\
                   iner_dt k c q (snd (Some?.v (scrutinised e)))) =
  match e with
  | ECase _ _ | EMatch _ _ -> ()

let rec iner_exps_mem (k c q: nat) (es: list exp) (b: exp)
  : Lemma (requires iner_exps k c q es /\ L.memP b es) (ensures iner k c q b) (decreases es) =
  match es with
  | e :: es1 -> FStar.Classical.move_requires (iner_exps_mem k c q es1) b

let rec iner_exps_nth (k c q: nat) (es: list exp) (i: nat)
  : Lemma (requires iner_exps k c q es /\ Some? (L.nth es i))
          (ensures iner k c q (Some?.v (L.nth es i)))
          (decreases es) =
  match es with
  | e :: es1 -> if i = 0 then () else iner_exps_nth k c q es1 (i - 1)

let rec iner_binds_mem (k c q: nat) (bs: list (typ & exp)) (t: typ) (r: exp)
  : Lemma (requires iner_binds k c q bs /\ L.memP (t, r) bs) (ensures iner k c q r) (decreases bs) =
  match bs with
  | _ :: bs1 -> FStar.Classical.move_requires (iner_binds_mem k c q bs1 t) r

let rec iner_binds_nth (k c q: nat) (bs: list (typ & exp)) (i: nat)
  : Lemma (requires iner_binds k c q bs /\ Some? (L.nth bs i))
          (ensures iner k c q (snd (Some?.v (L.nth bs i)))) (decreases bs) =
  match bs with
  | _ :: bs1 -> if i = 0 then () else iner_binds_nth k c q bs1 (i - 1)

let rec iner_cells_mem (k c q: nat) (th: list (key & exp)) (kv: key & exp)
  : Lemma (requires iner_cells k c q th /\ L.memP kv th)
          (ensures iner k c q (snd kv)) (decreases th) =
  match th with
  | _ :: th1 -> FStar.Classical.move_requires (iner_cells_mem k c q th1) kv

let rec iner_brs_snd (#lb: eqtype) (k c q: nat) (bs: list (lb & dtree)) (s: dtree)
  : Lemma (requires iner_brs k c q bs /\ L.memP s (L.map snd bs)) (ensures iner_dt k c q s)
          (decreases bs) =
  match bs with
  | _ :: bs1 -> FStar.Classical.move_requires (iner_brs_snd k c q bs1) s

let iner_switch (k c q: nat) (dt s: dtree)
  : Lemma (requires iner_dt k c q dt /\ L.memP s (switch_subtrees dt)) (ensures iner_dt k c q s) =
  match dt with
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    LP.append_memP (L.map snd bs) (match df with Some d -> [d] | None -> []) s;
    FStar.Classical.move_requires (iner_brs_snd k c q bs) s
  | DSwitchLit _ bs df ->
    LP.append_memP (L.map snd bs) [df] s;
    FStar.Classical.move_requires (iner_brs_snd k c q bs) s

let iner_jump (k c q: nat) (j: nat) (es: list exp)
  : Lemma (requires iner k c q (EJump j es)) (ensures j < q /\ iner_exps k c q es) = ()

let iner_join_arg (k c q: nat) (d: jentry) (p: nat) (es: list exp)
  : Lemma (requires iner_exps k c q es /\ Some? (join_arg d p es))
          (ensures iner k c q (Some?.v (join_arg d p es))) =
  match d with
  | JDef _ _ n _ _ -> iner_exps_nth k c q es (n - 1 - p)

(* The children of an inert term are inert, and stand under at least its
   join points. *)

let rhs_child (ve: venv) (je: jenv) (be: typ & exp) : child = mk ve je (snd be)

let cell_child (ve: venv) (je: jenv) (kv: key & exp) : child = mk ve je (snd kv)

let children_letrec (ve: venv) (je: jenv) (bs: list (typ & exp)) (b: exp)
  : Lemma (children ve je (ELetRec bs b) ==
           L.append (L.map (rhs_child (push_rec ve je bs) je) bs) [mk (push_rec ve je bs) je b]) =
  assert (children ve je (ELetRec bs b) ==
          L.append (L.map (rhs_child (push_rec ve je bs) je) bs) [mk (push_rec ve je bs) je b])
    by (T.norm [delta_only [`%children; `%rhs_child]; iota; zeta]; T.trefl ())

let children_region_open (ve: venv) (je: jenv) (a: atom) (th: list (key & exp)) (b: exp)
  : Lemma (children ve je (ERegionOpen a th b) ==
           L.append (L.map (cell_child ve je) th) [mk ve je b]) =
  assert (children ve je (ERegionOpen a th b)
      == L.append (L.map (cell_child ve je) th) [mk ve je b])
    by (T.norm [delta_only [`%children; `%cell_child]; iota; zeta]; T.trefl ())

let rec dt_children_ok (bv: venv) (bj: jenv) (cve: venv) (es: list exp) (ve: venv) (je: jenv)
  (dt: dtree) (c: child)
  : Lemma (requires dtri_ok bv bj cve es ve je dt /\ L.memP c (dt_children cve es ve je dt))
          (ensures child_ok bv bj c /\ c.cj == je) (decreases dt) =
  let k = dif (L.length ve) (L.length bv) in
  let q = dif (L.length je) (L.length bj) in
  match dt with
  | DLeaf _ -> ()
  | DBind o dt0 ->
    let v = bind_entry cve je es o in
    (match L.nth es (occ_root o) with
     | Some _ -> iner_exps_nth (dif (L.length cve) (L.length bv)) (L.length bv) q es (occ_root o)
     | None -> ());
    push_ok bv bj v ve;
    dt_children_ok bv bj cve es (v :: ve) je dt0 c
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    LP.append_memP (brs_children cve es ve je bs) (odt_children cve es ve je df) c;
    FStar.Classical.move_requires (brs_children_ok bv bj cve es ve je bs) c;
    FStar.Classical.move_requires (odt_children_ok bv bj cve es ve je df) c
  | DSwitchLit _ bs df ->
    LP.append_memP (brs_children cve es ve je bs) (dt_children cve es ve je df) c;
    FStar.Classical.move_requires (brs_children_ok bv bj cve es ve je bs) c;
    FStar.Classical.move_requires (dt_children_ok bv bj cve es ve je df) c
  | DGuard e dt1 dt2 ->
    LP.append_memP (dt_children cve es ve je dt1) (dt_children cve es ve je dt2) c;
    FStar.Classical.move_requires (dt_children_ok bv bj cve es ve je dt1) c;
    FStar.Classical.move_requires (dt_children_ok bv bj cve es ve je dt2) c

and odt_children_ok (bv: venv) (bj: jenv) (cve: venv) (es: list exp) (ve: venv) (je: jenv)
  (df: option dtree) (c: child)
  : Lemma (requires env_ok bv bj cve /\
                    iner_exps (dif (L.length cve) (L.length bv)) (L.length bv)
                      (dif (L.length je) (L.length bj)) es /\
                    env_ok bv bj ve /\ jenv_ok bv bj je /\
                    iner_odt (dif (L.length ve) (L.length bv)) (L.length bv)
                      (dif (L.length je) (L.length bj)) df /\
                    L.memP c (odt_children cve es ve je df))
          (ensures child_ok bv bj c /\ c.cj == je) (decreases df) =
  match df with
  | Some dt -> dt_children_ok bv bj cve es ve je dt c

and brs_children_ok (#lb: eqtype) (bv: venv) (bj: jenv) (cve: venv) (es: list exp) (ve: venv)
  (je: jenv) (bs: list (lb & dtree)) (c: child)
  : Lemma (requires env_ok bv bj cve /\
                    iner_exps (dif (L.length cve) (L.length bv)) (L.length bv)
                      (dif (L.length je) (L.length bj)) es /\
                    env_ok bv bj ve /\ jenv_ok bv bj je /\
                    iner_brs (dif (L.length ve) (L.length bv)) (L.length bv)
                      (dif (L.length je) (L.length bj)) bs /\
                    L.memP c (brs_children cve es ve je bs))
          (ensures child_ok bv bj c /\ c.cj == je) (decreases bs) =
  match bs with
  | pa :: bs0 -> let (_, dt) = pa in
    LP.append_memP (dt_children cve es ve je dt) (brs_children cve es ve je bs0) c;
    FStar.Classical.move_requires (dt_children_ok bv bj cve es ve je dt) c;
    FStar.Classical.move_requires (brs_children_ok bv bj cve es ve je bs0) c

let rec clause_children_ok (bv: venv) (bj: jenv) (ve: venv) (je: jenv) (cs: list clause) (c: child)
  : Lemma (requires env_ok bv bj ve /\ jenv_ok bv bj je /\
                    iner_cls (dif (L.length ve) (L.length bv)) (L.length bv)
                      (dif (L.length je) (L.length bj)) cs /\
                    L.memP c (clause_children ve je cs))
          (ensures child_ok bv bj c /\ c.cj == je) (decreases cs) =
  match cs with
  | CFull _ _ _ _ _ :: cs0 ->
    push_ok bv bj VNone ve; push_ok bv bj VNone (VNone :: ve);
    FStar.Classical.move_requires (clause_children_ok bv bj ve je cs0) c
  | CFast _ _ _ _ :: cs0 ->
    push_ok bv bj VNone ve;
    FStar.Classical.move_requires (clause_children_ok bv bj ve je cs0) c

let map_mk_ok (bv: venv) (bj: jenv) (ve: venv) (je: jenv) (es: list exp) (c: child)
  : Lemma (requires env_ok bv bj ve /\ jenv_ok bv bj je /\
                    iner_exps (dif (L.length ve) (L.length bv)) (L.length bv)
                      (dif (L.length je) (L.length bj)) es /\
                    L.memP c (L.map (mk ve je) es))
          (ensures child_ok bv bj c /\ c.cj == je) =
  LP.memP_map_elim (mk ve je) c es;
  eliminate exists (b: exp). L.memP b es /\ mk ve je b == c
  with iner_exps_mem (dif (L.length ve) (L.length bv)) (L.length bv)
      (dif (L.length je) (L.length bj)) es b

let children_ok (bv: venv) (bj: jenv) (ve: venv) (je: jenv) (e: exp) (c: child)
  : Lemma (requires tri_ok bv bj ve je e /\ L.memP c (children ve je e))
          (ensures child_ok bv bj c /\ L.length c.cj >= L.length je) =
  let k = dif (L.length ve) (L.length bv) in
  let cc = L.length bv in
  let q = dif (L.length je) (L.length bj) in
  env_ok_len bv bj ve; jenv_ok_len bv bj je;
  match e with
  | ELam _ _ b -> push_ok bv bj VNone ve; mem1 (mk (VNone :: ve) je b) c
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b
  | EInject _ _ b | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b
  | EWriteCell _ _ b | EOpenEffC _ b | EFill _ b -> mem1 (mk ve je b) c
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    mem2 (mk ve je e1) (mk ve je e2) c
  | ELet _ e1 e2 ->
    push_ok bv bj (VLat ve je e1) ve; mem2 (mk ve je e1) (mk (push_let ve je e1) je e2) c
  | ELetRec bs b ->
    children_letrec ve je bs b;
    push_rec_ok bv bj ve je bs;
    let pv = push_rec ve je bs in
    LP.append_memP (L.map (rhs_child pv je) bs) [mk pv je b] c;
    FStar.Classical.move_requires (mem1 (mk pv je b)) c;
    let aux () : Lemma (requires L.memP c (L.map (rhs_child pv je) bs))
                       (ensures child_ok bv bj c /\ L.length c.cj >= L.length je) =
      LP.memP_map_elim (rhs_child pv je) c bs;
      eliminate exists (be: typ & exp). L.memP be bs /\ rhs_child pv je be == c
      with iner_binds_mem (k + L.length bs) cc q bs (fst be) (snd be)
    in
    FStar.Classical.move_requires aux ()
  | ECase es dt | EMatch es dt ->
    LP.append_memP (L.map (mk ve je) es) (dt_children ve es ve je dt) c;
    FStar.Classical.move_requires (map_mk_ok bv bj ve je es) c;
    FStar.Classical.move_requires (dt_children_ok bv bj ve es ve je dt) c
  | ELetJoin ts _ e1 e2 ->
    let d = join_def ve je ts e1 e2 in
    assert (jent_ok bv bj d);
    mem2 (join_body d) (join_cont d) c;
    join_scope_ok bv bj d c
  | EJump _ es -> map_mk_ok bv bj ve je es c
  | EHandle b h ->
    push_ok bv bj VNone ve;
    mem_cons2 (mk ve je b) (mk (VNone :: ve) je h.h_ret) c (clause_children ve je h.h_clauses);
    FStar.Classical.move_requires (clause_children_ok bv bj ve je h.h_clauses) c
  | ERegion _ es b ->
    LP.append_memP (L.map (mk ve je) es) [mk ve je b] c;
    FStar.Classical.move_requires (mem1 (mk ve je b)) c;
    FStar.Classical.move_requires (map_mk_ok bv bj ve je es) c
  | ERegionOpen a th b ->
    children_region_open ve je a th b;
    LP.append_memP (L.map (cell_child ve je) th) [mk ve je b] c;
    FStar.Classical.move_requires (mem1 (mk ve je b)) c;
    let aux () : Lemma (requires L.memP c (L.map (cell_child ve je) th))
                       (ensures child_ok bv bj c /\ L.length c.cj >= L.length je) =
      LP.memP_map_elim (cell_child ve je) c th;
      eliminate exists (kv: key & exp). L.memP kv th /\ cell_child ve je kv == c
      with iner_cells_mem k cc q th kv
    in
    FStar.Classical.move_requires aux ()
  | _ -> ()

let rec sub_ok (bv: venv) (bj: jenv) (#c #s: child) (p: sub c s)
  : Lemma (requires child_ok bv bj c) (ensures child_ok bv bj s /\ L.length s.cj >= L.length c.cj)
          (decreases p) =
  match p with
  | SubHere _ -> ()
  | SubChild #_ #c1 _ p1 -> children_ok bv bj c.cv c.cj c.ce c1; sub_ok bv bj p1

(* The children of any term stand under at least its join points. *)
let rec dt_children_cj (cve: venv) (es: list exp) (ve: venv) (je: jenv) (dt: dtree) (c: child)
  : Lemma (requires L.memP c (dt_children cve es ve je dt)) (ensures c.cj == je) (decreases dt) =
  match dt with
  | DLeaf _ -> ()
  | DBind o dt0 -> dt_children_cj cve es (bind_entry cve je es o :: ve) je dt0 c
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    LP.append_memP (brs_children cve es ve je bs) (odt_children cve es ve je df) c;
    FStar.Classical.move_requires (brs_children_cj cve es ve je bs) c;
    FStar.Classical.move_requires (odt_children_cj cve es ve je df) c
  | DSwitchLit _ bs df ->
    LP.append_memP (brs_children cve es ve je bs) (dt_children cve es ve je df) c;
    FStar.Classical.move_requires (brs_children_cj cve es ve je bs) c;
    FStar.Classical.move_requires (dt_children_cj cve es ve je df) c
  | DGuard e dt1 dt2 ->
    LP.append_memP (dt_children cve es ve je dt1) (dt_children cve es ve je dt2) c;
    FStar.Classical.move_requires (dt_children_cj cve es ve je dt1) c;
    FStar.Classical.move_requires (dt_children_cj cve es ve je dt2) c

and odt_children_cj (cve: venv) (es: list exp) (ve: venv) (je: jenv) (df: option dtree) (c: child)
  : Lemma (requires L.memP c (odt_children cve es ve je df)) (ensures c.cj == je) (decreases df) =
  match df with
  | Some dt -> dt_children_cj cve es ve je dt c

and brs_children_cj (#lb: eqtype) (cve: venv) (es: list exp) (ve: venv) (je: jenv)
  (bs: list (lb & dtree)) (c: child)
  : Lemma (requires L.memP c (brs_children cve es ve je bs)) (ensures c.cj == je) (decreases bs) =
  match bs with
  | pa :: bs0 -> let (_, dt) = pa in
    LP.append_memP (dt_children cve es ve je dt) (brs_children cve es ve je bs0) c;
    FStar.Classical.move_requires (dt_children_cj cve es ve je dt) c;
    FStar.Classical.move_requires (brs_children_cj cve es ve je bs0) c

let rec clause_children_cj (ve: venv) (je: jenv) (cs: list clause) (c: child)
  : Lemma (requires L.memP c (clause_children ve je cs)) (ensures c.cj == je) (decreases cs) =
  match cs with
  | CFull _ _ _ _ _ :: cs0 | CFast _ _ _ _ :: cs0 ->
    FStar.Classical.move_requires (clause_children_cj ve je cs0) c

let map_mk_cj (ve: venv) (je: jenv) (es: list exp) (c: child)
  : Lemma (requires L.memP c (L.map (mk ve je) es)) (ensures c.cj == je) =
  LP.memP_map_elim (mk ve je) c es

let children_cj (ve: venv) (je: jenv) (e: exp) (c: child)
  : Lemma (requires L.memP c (children ve je e)) (ensures L.length c.cj >= L.length je) =
  match e with
  | ELetRec bs b ->
    children_letrec ve je bs b;
    let pv = push_rec ve je bs in
    LP.append_memP (L.map (rhs_child pv je) bs) [mk pv je b] c;
    LP.memP_map_elim (rhs_child pv je) c bs
  | ECase es dt | EMatch es dt ->
    LP.append_memP (L.map (mk ve je) es) (dt_children ve es ve je dt) c;
    FStar.Classical.move_requires (map_mk_cj ve je es) c;
    FStar.Classical.move_requires (dt_children_cj ve es ve je dt) c
  | EJump _ es -> map_mk_cj ve je es c
  | EHandle b h ->
    mem_cons2 (mk ve je b) (mk (VNone :: ve) je h.h_ret) c (clause_children ve je h.h_clauses);
    FStar.Classical.move_requires (clause_children_cj ve je h.h_clauses) c
  | ERegion _ es b ->
    LP.append_memP (L.map (mk ve je) es) [mk ve je b] c;
    FStar.Classical.move_requires (map_mk_cj ve je es) c
  | ERegionOpen a th b ->
    children_region_open ve je a th b;
    LP.append_memP (L.map (cell_child ve je) th) [mk ve je b] c;
    LP.memP_map_elim (cell_child ve je) c th
  | ELam _ _ b -> mem1 (mk (VNone :: ve) je b) c
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b
  | EInject _ _ b | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b
  | EWriteCell _ _ b | EOpenEffC _ b | EFill _ b -> mem1 (mk ve je b) c
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    mem2 (mk ve je e1) (mk ve je e2) c
  | ELet _ e1 e2 -> mem2 (mk ve je e1) (mk (push_let ve je e1) je e2) c
  | ELetJoin ts _ e1 e2 ->
    let d = join_def ve je ts e1 e2 in
    mem2 (join_body d) (join_cont d) c
  | _ -> ()

(* The inert lemma. *)

let local (g: group) : prop = forall (q: qname). g.gmem q == None

let rec inert_imm (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
  (d: reads_imm sg g ve je e m) (bv: venv) (bj: jenv)
  : Lemma (requires local g /\ tri_ok bv bj ve je e) (ensures False) (decreases d) =
  let cc = L.length bv in
  let k = dif (L.length ve) cc in
  let q = dif (L.length je) (L.length bj) in
  env_ok_len bv bj ve; jenv_ok_len bv bj je;
  match d with
  | IMember #_ #_ #_ #_ #i _ -> var_ent_ok bv bj ve je i
  | IMemberGlobal #_ #_ #_ #_ #q0 _ -> assert (g.gmem q0 == None)
  | IThrough _ d1 -> iner_through k cc q e; inert_imm d1 bv bj
  | IBuild #_ #_ #_ #_ #_ #b _ d1 -> iner_builds k cc q e b; inert_imm d1 bv bj
  | ITake _ d1 -> iner_takes k cc q e; inert_imm d1 bv bj
  | ISpine #_ #_ #_ #_ #_ #b _ d1 -> iner_spine sg g k cc q e b; inert_imm d1 bv bj
  | IDefault #_ #_ #_ #_ #_ #b _ d1 -> iner_default sg g k cc q e b; inert_imm d1 bv bj
  | IDefaultLat #_ #_ #_ #_ #_ #b _ d1 -> iner_default sg g k cc q e b; inert_lat d1 bv bj
  | ILetBound d1 -> inert_imm d1 bv bj
  | ILetBody #_ #_ #_ #_ #_ #e1 d1 -> push_ok bv bj (VLat ve je e1) ve; inert_imm d1 bv bj
  | ILetRecRhs #_ #_ #_ #_ #bs #_ #t #r _ d1 ->
    push_rec_ok bv bj ve je bs; iner_binds_mem (k + L.length bs) cc q bs t r; inert_imm d1 bv bj
  | ILetRecBody #_ #_ #_ #_ #bs d1 -> push_rec_ok bv bj ve je bs; inert_imm d1 bv bj
  | ICaseScrut #_ #_ #_ #_ #_ #es #_ #b _ _ d1 ->
    iner_scrut k cc q e; iner_exps_mem k cc q es b; inert_imm d1 bv bj
  | ICaseTree _ d1 -> iner_scrut k cc q e; inert_imm_dt d1 bv bj
  | ILetJoin #_ #_ #_ #_ #ts #_ #e1 #e2 d1 ->
    jpush_ok bv bj (join_def ve je ts e1 e2) je; inert_imm d1 bv bj
  | IJumpArg #_ #_ #_ #_ #_ #es #b _ d1 -> iner_exps_mem k cc q es b; inert_imm d1 bv bj
  | IJumpBody #_ #_ #_ #_ #j #_ #d0 _ d1 ->
    jenv_lookup_ok bv bj je j; join_body_ok bv bj d0; inert_imm d1 bv bj
  | IWhole #_ #_ #_ #_ #_ #c #_ _ _ sb d1 ->
    children_ok bv bj ve je e c; sub_ok bv bj sb; inert_imm d1 bv bj
  | IWholeLat #_ #_ #_ #_ #_ #c #_ _ _ sb d1 ->
    children_ok bv bj ve je e c; sub_ok bv bj sb; inert_lat d1 bv bj

and inert_lat (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
  (d: reads_lat sg g ve je e m) (bv: venv) (bj: jenv)
  : Lemma (requires local g /\ tri_ok bv bj ve je e) (ensures False) (decreases d) =
  let cc = L.length bv in
  let k = dif (L.length ve) cc in
  let q = dif (L.length je) (L.length bj) in
  env_ok_len bv bj ve; jenv_ok_len bv bj je;
  match d with
  | LMember #_ #_ #_ #_ #i _ _ _ -> var_ent_ok bv bj ve je i
  | LMemberGlobal #_ #_ #_ #_ #q0 _ _ _ -> assert (g.gmem q0 == None)
  | LLocal #_ #_ #_ #_ #i _ d1 -> var_ent_ok bv bj ve je i; inert_lat d1 bv bj
  | LLocalRec #_ #_ #_ #_ #i #ve2 #je2 #bs #k0 _ _ d1 ->
    var_ent_ok bv bj ve je i;
    push_rec_ok bv bj ve2 je2 bs;
    env_ok_len bv bj ve2;
    iner_binds_nth (dif (L.length ve2) cc + L.length bs)
        cc (dif (L.length je2) (L.length bj)) bs k0;
    inert_lat d1 bv bj
  | LJoinArg #_ #_ #_ #_ #i #d0 #p #c #ve3 #je3 #j #es #a _ _ sb _ _ d1 ->
    var_ent_ok bv bj ve je i;
    join_scope_ok bv bj d0 c;
    sub_ok bv bj sb;
    assert (child_ok bv bj (mk ve3 je3 (EJump j es)));
    assert (tri_ok bv bj ve3 je3 (EJump j es));
    env_ok_len bv bj ve3; jenv_ok_len bv bj je3;
    iner_jump (dif (L.length ve3) cc) cc (dif (L.length je3) (L.length bj)) j es;
    iner_join_arg (dif (L.length ve3) cc) cc (dif (L.length je3) (L.length bj)) d0 p es;
    inert_lat d1 bv bj
  | LLam d1 -> push_ok bv bj VNone ve; inert_imm d1 bv bj
  | LLamLat d1 -> push_ok bv bj VNone ve; inert_lat d1 bv bj
  | LThrough _ d1 -> iner_through k cc q e; inert_lat d1 bv bj
  | LBuild #_ #_ #_ #_ #_ #b _ d1 -> iner_builds k cc q e b; inert_lat d1 bv bj
  | LTake _ d1 -> iner_takes k cc q e; inert_lat d1 bv bj
  | LSpine #_ #_ #_ #_ #_ #b _ d1 -> iner_spine sg g k cc q e b; inert_lat d1 bv bj
  | LDefault #_ #_ #_ #_ #_ #b _ d1 -> iner_default sg g k cc q e b; inert_lat d1 bv bj
  | LLet #_ #_ #_ #_ #_ #e1 d1 -> push_ok bv bj (VLat ve je e1) ve; inert_lat d1 bv bj
  | LLetRec #_ #_ #_ #_ #bs d1 -> push_rec_ok bv bj ve je bs; inert_lat d1 bv bj
  | LCase _ d1 -> iner_scrut k cc q e; inert_lat_dt d1 bv bj
  | LLetJoin #_ #_ #_ #_ #ts #_ #e1 #e2 d1 ->
    jpush_ok bv bj (join_def ve je ts e1 e2) je; inert_lat d1 bv bj
  | LJump #_ #_ #_ #_ #j #_ #d0 _ d1 ->
    jenv_lookup_ok bv bj je j; join_body_ok bv bj d0; inert_lat d1 bv bj
  | LWhole #_ #_ #_ #_ #_ #c #_ _ _ sb d1 ->
    children_ok bv bj ve je e c; sub_ok bv bj sb; inert_lat d1 bv bj

and inert_imm_dt (#sg: sig) (#g: group) (#cve: venv) (#es: list exp) (#ve: venv) (#je: jenv)
  (#dt: dtree) (#m: nat) (d: reads_imm_dt sg g cve es ve je dt m) (bv: venv) (bj: jenv)
  : Lemma (requires local g /\ dtri_ok bv bj cve es ve je dt) (ensures False) (decreases d) =
  let cc = L.length bv in
  let q = dif (L.length je) (L.length bj) in
  match d with
  | ITLeaf d1 -> inert_imm d1 bv bj
  | ITBind #_ #_ #_ #_ #_ #_ #o d1 ->
    (match L.nth es (occ_root o) with
     | Some _ -> iner_exps_nth (dif (L.length cve) cc) cc q es (occ_root o)
     | None -> ());
    push_ok bv bj (bind_entry cve je es o) ve;
    inert_imm_dt d1 bv bj
  | ITSwitch #_ #_ #_ #_ #_ #_ #_ #s _ d1 ->
    iner_switch (dif (L.length ve) cc) cc q dt s; inert_imm_dt d1 bv bj
  | ITGuard d1 -> inert_imm d1 bv bj
  | ITGuardYes d1 -> inert_imm_dt d1 bv bj
  | ITGuardNo d1 -> inert_imm_dt d1 bv bj

and inert_lat_dt (#sg: sig) (#g: group) (#cve: venv) (#es: list exp) (#ve: venv) (#je: jenv)
  (#dt: dtree) (#m: nat) (d: reads_lat_dt sg g cve es ve je dt m) (bv: venv) (bj: jenv)
  : Lemma (requires local g /\ dtri_ok bv bj cve es ve je dt) (ensures False) (decreases d) =
  let cc = L.length bv in
  let q = dif (L.length je) (L.length bj) in
  match d with
  | LTLeaf d1 -> inert_lat d1 bv bj
  | LTBind #_ #_ #_ #_ #_ #_ #o d1 ->
    (match L.nth es (occ_root o) with
     | Some _ -> iner_exps_nth (dif (L.length cve) cc) cc q es (occ_root o)
     | None -> ());
    push_ok bv bj (bind_entry cve je es o) ve;
    inert_lat_dt d1 bv bj
  | LTSwitch #_ #_ #_ #_ #_ #_ #_ #s _ d1 ->
    iner_switch (dif (L.length ve) cc) cc q dt s; inert_lat_dt d1 bv bj
  | LTGuardYes d1 -> inert_lat_dt d1 bv bj
  | LTGuardNo d1 -> inert_lat_dt d1 bv bj


(* Related environments: entry by entry, each entry's term related at the
   length of its own environment. *)

let rec ent_rel (v v': ventry) : Tot prop (decreases v) =
  match v, v' with
  | VNone, VNone -> True
  | VMem k, VMem k' -> k == k'
  | VLat ve je e, VLat ve' je' e' -> venv_rel ve ve' /\ jenv_rel je je' /\ ssim (L.length ve) e e'
  | VRec ve je bs k, VRec ve' je' bs' k' ->
    k == k' /\ L.length bs' == L.length bs /\ venv_rel ve ve' /\ jenv_rel je je' /\
    ssim_binds (L.length ve + L.length bs) bs bs'
  | VArg d p, VArg d' p' -> p == p' /\ jent_rel d d'
  | _ -> False

and venv_rel (ve ve': venv) : Tot prop (decreases ve) =
  match ve, ve' with
  | [], [] -> True
  | v :: ve, v' :: ve' -> ent_rel v v' /\ venv_rel ve ve'
  | _ -> False

and jent_rel (d d': jentry) : Tot prop (decreases d) =
  match d, d' with
  | JDef ve je n e1 e2, JDef ve' je' n' e1' e2' ->
    n == n' /\ venv_rel ve ve' /\ jenv_rel je je' /\ ssim (L.length ve + n) e1 e1' /\
    ssim (L.length ve) e2 e2'

and jenv_rel (je je': jenv) : Tot prop (decreases je) =
  match je, je' with
  | [], [] -> True
  | d :: je, d' :: je' -> jent_rel d d' /\ jenv_rel je je'
  | _ -> False

let crel3 (ve: venv) (je: jenv) (e: exp) (ve': venv) (je': jenv) (e': exp) : prop =
  venv_rel ve ve' /\ jenv_rel je je' /\ ssim (L.length ve) e e'

let crel (c c': child) : prop = crel3 c.cv c.cj c.ce c'.cv c'.cj c'.ce

(* Related local groups: no global member, related right-hand sides. *)
let grel (g g': group) : prop =
  local g /\ local g' /\
  (forall (k: nat) (r': exp). rhs g' k == Some r' ==>
     (exists (r: exp). rhs g k == Some r /\ crel3 g.genv [] r g'.genv [] r'))

(* A child of the image within an inert term: inert under a base standing
   under at least `lo` join points. *)
let dead (lo: nat) (s': child) : prop =
  exists (bv: venv) (bj: jenv). L.length bj >= lo /\ child_ok bv bj s'

(* Existence of a derivation. *)
let ex (a: Type) : prop = exists (x: a). True

let ex_intro (#a: Type) (x: a) : Lemma (ex a) = introduce exists (y: a). True with x and ()

let ex_map (#a #b: Type) (f: a -> b) : Lemma (requires ex a) (ensures ex b) =
  eliminate exists (x: a). True
    with introduce exists (y: b). True with (f x) and ()

let ex_map2 (#a #b #c: Type) (f: a -> b -> c) : Lemma (requires ex a /\ ex b) (ensures ex c) =
  eliminate exists (x: a). True
    with
  eliminate exists (y: b). True
    with
  introduce exists (z: c). True with (f x y) and ()

(* Lookups. *)

let rec venv_len (ve ve': venv)
  : Lemma (requires venv_rel ve ve') (ensures L.length ve == L.length ve') (decreases ve) =
  match ve, ve' with
  | [], [] -> ()
  | _ :: ve0, _ :: ve0' -> venv_len ve0 ve0'

let rec venv_lookup (ve ve': venv) (i: nat)
  : Lemma (requires venv_rel ve ve') (ensures ent_rel (vlook ve i) (vlook ve' i)) (decreases ve) =
  match ve, ve' with
  | [], [] -> ()
  | _ :: ve0, _ :: ve0' -> if i = 0 then () else venv_lookup ve0 ve0' (i - 1)

let rec jenv_lookup (je je': jenv) (j: nat)
  : Lemma (requires jenv_rel je je')
          (ensures (match jlook je j, jlook je' j with
                    | Some d, Some d' -> jent_rel d d'
                    | None, None -> True
                    | _ -> False))
          (decreases je) =
  match je, je' with
  | [], [] -> ()
  | _ :: je0, _ :: je0' -> if j = 0 then () else jenv_lookup je0 je0' (j - 1)

let rec jenv_length (je je': jenv)
  : Lemma (requires jenv_rel je je') (ensures L.length je == L.length je') (decreases je) =
  match je, je' with
  | [], [] -> ()
  | _ :: je0, _ :: je0' -> jenv_length je0 je0'

(* Pushing entries. *)

let rec pre_rel (p p': venv) : Tot prop (decreases p) =
  match p, p' with
  | [], [] -> True
  | v :: p, v' :: p' -> ent_rel v v' /\ pre_rel p p'
  | _ -> False

let rec venv_append (p p': venv) (ve ve': venv)
  : Lemma (requires pre_rel p p' /\ venv_rel ve ve')
          (ensures venv_rel (L.append p ve) (L.append p' ve') /\
                   L.length (L.append p ve) == L.length p + L.length ve)
          (decreases p) =
  match p, p' with
  | [], [] -> ()
  | _ :: p0, _ :: p0' -> venv_append p0 p0' ve ve'

let rec rec_entries_rel (ve ve': venv) (je je': jenv) (bs bs': list (typ & exp)) (n: nat)
  : Lemma (requires ent_rel (VRec ve je bs 0) (VRec ve' je' bs' 0))
          (ensures pre_rel (rec_entries ve je bs n) (rec_entries ve' je' bs' n) /\
                   L.length (rec_entries ve je bs n) == n)
          (decreases n) =
  if n = 0 then () else rec_entries_rel ve ve' je je' bs bs' (n - 1)

let push_rec_rel (ve ve': venv) (je je': jenv) (bs bs': list (typ & exp))
  : Lemma (requires venv_rel ve ve' /\ jenv_rel je je' /\ L.length bs' == L.length bs /\
                    ssim_binds (L.length ve + L.length bs) bs bs')
          (ensures venv_rel (push_rec ve je bs) (push_rec ve' je' bs') /\
                   L.length (push_rec ve je bs) == L.length ve + L.length bs) =
  assert (ent_rel (VRec ve je bs 0) (VRec ve' je' bs' 0));
  rec_entries_rel ve ve' je je' bs bs' (L.length bs);
  venv_append (rec_entries ve je bs (L.length bs)) (rec_entries ve' je' bs' (L.length bs)) ve ve'

let rec arg_entries_rel (d d': jentry) (p n: nat)
  : Lemma (requires jent_rel d d')
          (ensures pre_rel (arg_entries d p n) (arg_entries d' p n) /\
                   L.length (arg_entries d p n) == n)
          (decreases n) =
  if n = 0 then () else arg_entries_rel d d' (p + 1) (n - 1)

let join_def_rel (ve ve': venv) (je je': jenv) (ts ts': list typ) (e1 e2 e1' e2': exp)
  : Lemma (requires venv_rel ve ve' /\ jenv_rel je je' /\ L.length ts == L.length ts' /\
                    ssim (L.length ve + L.length ts) e1 e1' /\ ssim (L.length ve) e2 e2')
          (ensures jent_rel (join_def ve je ts e1 e2) (join_def ve' je' ts' e1' e2')) = ()

let join_body_rel (d d': jentry)
  : Lemma (requires jent_rel d d') (ensures crel (join_body d) (join_body d')) =
  match d, d' with
  | JDef ve je n e1 e2, JDef ve' je' _ e1' e2' ->
    arg_entries_rel d d' 0 n;
    venv_append (arg_entries d 0 n) (arg_entries d' 0 n) ve ve'

let join_cont_rel (d d': jentry)
  : Lemma (requires jent_rel d d') (ensures crel (join_cont d) (join_cont d')) = ()

let join_scope_rel (d d': jentry) (c': child)
  : Lemma (requires jent_rel d d' /\ L.memP c' (join_scope d'))
          (ensures exists (c: child). L.memP c (join_scope d) /\ crel c c') =
  join_body_rel d d';
  join_cont_rel d d';
  FStar.Classical.or_elim #(c' == join_body d') #(L.memP c' [join_cont d'])
    #(fun _ -> exists (c: child). L.memP c (join_scope d) /\ crel c c')
    (fun _ -> assert (L.memP (join_body d) (join_scope d)))
    (fun _ -> assert (L.memP (join_cont d) (join_scope d)))

let join_jenv_length (d d': jentry)
  : Lemma (requires jent_rel d d') (ensures L.length (join_jenv d) == L.length (join_jenv d')) =
  match d, d' with
  | JDef _ je _ _ _, JDef _ je' _ _ _ -> jenv_length je je'

let join_scope_cj (d: jentry) (c: child)
  : Lemma (requires L.memP c (join_scope d)) (ensures L.length c.cj == L.length (join_jenv d)) =
  mem2 (join_body d) (join_cont d) c

(* Lists of related terms. *)

let rec exps_nth (c: nat) (es es': list exp) (k: nat)
  : Lemma (requires ssim_exps c es es')
          (ensures (match L.nth es k, L.nth es' k with
                    | Some e, Some e' -> ssim c e e'
                    | None, None -> True
                    | _ -> False))
          (decreases es) =
  match es, es' with
  | [], [] -> ()
  | _ :: es0, _ :: es0' -> if k = 0 then () else exps_nth c es0 es0' (k - 1)

let rec exps_mem (c: nat) (es es': list exp) (b': exp)
  : Lemma (requires ssim_exps c es es' /\ L.memP b' es')
          (ensures exists (b: exp). L.memP b es /\ ssim c b b') (decreases es) =
  match es, es' with
  | e :: es0, e' :: es0' ->
    FStar.Classical.or_elim #(b' == e') #(L.memP b' es0')
      #(fun _ -> exists (b: exp). L.memP b es /\ ssim c b b')
      (fun _ -> ())
      (fun _ -> exps_mem c es0 es0' b')

let rec binds_mem (c: nat) (bs bs': list (typ & exp)) (t': typ) (r': exp)
  : Lemma (requires ssim_binds c bs bs' /\ L.memP (t', r') bs')
          (ensures exists (t: typ) (r: exp). L.memP (t, r) bs /\ ssim c r r') (decreases bs) =
  match bs, bs' with
  | (t, e) :: bs0, (te', e') :: bs0' ->
    FStar.Classical.or_elim #((t', r') == (te', e')) #(L.memP (t', r') bs0')
      #(fun _ -> exists (t: typ) (r: exp). L.memP (t, r) bs /\ ssim c r r')
      (fun _ -> ())
      (fun _ -> binds_mem c bs0 bs0' t' r')

let rec binds_nth (c: nat) (bs bs': list (typ & exp)) (k: nat)
  : Lemma (requires ssim_binds c bs bs')
          (ensures (match L.nth bs k, L.nth bs' k with
                    | Some (_, r), Some (_, r') -> ssim c r r'
                    | None, None -> True
                    | _ -> False))
          (decreases bs) =
  match bs, bs' with
  | [], [] -> ()
  | _ :: bs0, _ :: bs0' -> if k = 0 then () else binds_nth c bs0 bs0' (k - 1)

let rec exps_children (ve ve': venv) (je je': jenv) (es es': list exp) (c': child)
  : Lemma (requires ssim_exps (L.length ve) es es' /\ venv_rel ve ve' /\ jenv_rel je je' /\
                    L.memP c' (L.map (mk ve' je') es'))
          (ensures exists (c: child). L.memP c (L.map (mk ve je) es) /\ crel c c') (decreases es) =
  match es, es' with
  | e :: es0, e' :: es0' ->
    FStar.Classical.or_elim #(c' == mk ve' je' e') #(L.memP c' (L.map (mk ve' je') es0'))
      #(fun _ -> exists (c: child). L.memP c (L.map (mk ve je) es) /\ crel c c')
      (fun _ -> assert (crel (mk ve je e) (mk ve' je' e')))
      (fun _ -> exps_children ve ve' je je' es0 es0' c')

let rec rhs_children (ve ve': venv) (je je': jenv) (bs bs': list (typ & exp)) (c': child)
  : Lemma (requires ssim_binds (L.length ve) bs bs' /\ venv_rel ve ve' /\ jenv_rel je je' /\
                    L.memP c' (L.map (rhs_child ve' je') bs'))
          (ensures exists (c: child).
                     L.memP c (L.map (rhs_child ve je) bs) /\ crel c c')
          (decreases bs) =
  match bs, bs' with
  | pa :: bs0, pb :: bs0' -> let (_, e) = pa in let (_, e') = pb in
    FStar.Classical.or_elim #(c' == mk ve' je' e')
      #(L.memP c' (L.map (rhs_child ve' je') bs0'))
      #(fun _ -> exists (c: child).
                   L.memP c (L.map (rhs_child ve je) bs) /\ crel c c')
      (fun _ -> assert (crel (mk ve je e) (mk ve' je' e')))
      (fun _ -> rhs_children ve ve' je je' bs0 bs0' c')

let rec cells_children (ve ve': venv) (je je': jenv) (th th': list (key & exp)) (c': child)
  : Lemma (requires ssim_cells (L.length ve) th th' /\ venv_rel ve ve' /\ jenv_rel je je' /\
                    L.memP c' (L.map (cell_child ve' je') th'))
          (ensures exists (c: child).
                     L.memP c (L.map (cell_child ve je) th) /\ crel c c')
          (decreases th) =
  match th, th' with
  | pa :: th0, pb :: th0' -> let (_, e) = pa in let (_, e') = pb in
    FStar.Classical.or_elim #(c' == mk ve' je' e')
      #(L.memP c' (L.map (cell_child ve' je') th0'))
      #(fun _ -> exists (c: child).
                   L.memP c (L.map (cell_child ve je) th) /\ crel c c')
      (fun _ -> assert (crel (mk ve je e) (mk ve' je' e')))
      (fun _ -> cells_children ve ve' je je' th0 th0' c')

let rec clause_children_rel (ve ve': venv) (je je': jenv) (cs cs': list clause) (c': child)
  : Lemma (requires ssim_cls (L.length ve) cs cs' /\ venv_rel ve ve' /\ jenv_rel je je' /\
                    L.memP c' (clause_children ve' je' cs'))
          (ensures exists (c: child). L.memP c (clause_children ve je cs) /\ crel c c')
          (decreases cs) =
  match cs, cs' with
  | CFull _ _ _ _ b :: cs0, CFull _ _ _ _ b' :: cs0' ->
    FStar.Classical.or_elim #(c' == mk (VNone :: VNone :: ve') je' b')
      #(L.memP c' (clause_children ve' je' cs0'))
      #(fun _ -> exists (c: child). L.memP c (clause_children ve je cs) /\ crel c c')
      (fun _ -> assert (crel (mk (VNone :: VNone :: ve) je b) (mk (VNone :: VNone :: ve') je' b')))
      (fun _ -> clause_children_rel ve ve' je je' cs0 cs0' c')
  | CFast _ _ _ b :: cs0, CFast _ _ _ b' :: cs0' ->
    FStar.Classical.or_elim #(c' == mk (VNone :: ve') je' b')
      #(L.memP c' (clause_children ve' je' cs0'))
      #(fun _ -> exists (c: child). L.memP c (clause_children ve je cs) /\ crel c c')
      (fun _ -> assert (crel (mk (VNone :: ve) je b) (mk (VNone :: ve') je' b')))
      (fun _ -> clause_children_rel ve ve' je je' cs0 cs0' c')

(* The entry a `bind` pushes. *)
let bind_entry_rel (cve cve': venv) (je je': jenv) (es es': list exp) (o: occ)
  : Lemma (requires venv_rel cve cve' /\ jenv_rel je je' /\ ssim_exps (L.length cve) es es')
          (ensures ent_rel (bind_entry cve je es o) (bind_entry cve' je' es' o)) =
  exps_nth (L.length cve) es es' (occ_root o)

let dtrel (cve: venv) (es: list exp) (cve': venv) (es': list exp) (je je': jenv) : prop =
  venv_rel cve cve' /\ jenv_rel je je' /\ ssim_exps (L.length cve) es es'

let rec dt_children_rel (cve: venv) (es: list exp) (cve': venv) (es': list exp)
  (ve ve': venv) (je je': jenv) (dt dt': dtree) (c': child)
  : Lemma (requires dtrel cve es cve' es' je je' /\ venv_rel ve ve' /\
                    ssim_dt (L.length ve) dt dt' /\ L.memP c' (dt_children cve' es' ve' je' dt'))
          (ensures exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
          (decreases dt) =
  match dt, dt' with
  | DLeaf e, DLeaf e' -> assert (crel (mk ve je e) (mk ve' je' e'))
  | DBind o dt0, DBind _ dt0' ->
    bind_entry_rel cve cve' je je' es es' o;
    dt_children_rel cve es cve' es' (bind_entry cve je es o :: ve)
      (bind_entry cve' je' es' o :: ve') je je' dt0 dt0' c'
  | DSwitchCtor _ bs df, DSwitchCtor _ bs' df' | DSwitchKey _ bs df, DSwitchKey _ bs' df' ->
    LP.append_memP (brs_children cve' es' ve' je' bs') (odt_children cve' es' ve' je' df') c';
    FStar.Classical.or_elim #(L.memP c' (brs_children cve' es' ve' je' bs'))
      #(L.memP c' (odt_children cve' es' ve' je' df'))
      #(fun _ -> exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
      (fun _ ->
        brs_children_rel cve es cve' es' ve ve' je je' bs bs' c';
        eliminate exists (c: child). L.memP c (brs_children cve es ve je bs) /\ crel c c'
        with LP.append_memP (brs_children cve es ve je bs) (odt_children cve es ve je df) c)
      (fun _ ->
        odt_children_rel cve es cve' es' ve ve' je je' df df' c';
        eliminate exists (c: child). L.memP c (odt_children cve es ve je df) /\ crel c c'
        with LP.append_memP (brs_children cve es ve je bs) (odt_children cve es ve je df) c)
  | DSwitchLit _ bs df, DSwitchLit _ bs' df' ->
    LP.append_memP (brs_children cve' es' ve' je' bs') (dt_children cve' es' ve' je' df') c';
    FStar.Classical.or_elim #(L.memP c' (brs_children cve' es' ve' je' bs'))
      #(L.memP c' (dt_children cve' es' ve' je' df'))
      #(fun _ -> exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
      (fun _ ->
        brs_children_rel cve es cve' es' ve ve' je je' bs bs' c';
        eliminate exists (c: child). L.memP c (brs_children cve es ve je bs) /\ crel c c'
        with LP.append_memP (brs_children cve es ve je bs) (dt_children cve es ve je df) c)
      (fun _ ->
        dt_children_rel cve es cve' es' ve ve' je je' df df' c';
        eliminate exists (c: child). L.memP c (dt_children cve es ve je df) /\ crel c c'
        with LP.append_memP (brs_children cve es ve je bs) (dt_children cve es ve je df) c)
  | DGuard e dt1 dt2, DGuard e' dt1' dt2' ->
    let l1 = dt_children cve es ve je dt1 in
    let l2 = dt_children cve es ve je dt2 in
    let l1' = dt_children cve' es' ve' je' dt1' in
    let l2' = dt_children cve' es' ve' je' dt2' in
    LP.append_memP l1' l2' c';
    FStar.Classical.or_elim #(c' == mk ve' je' e') #(L.memP c' (L.append l1' l2'))
      #(fun _ -> exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
      (fun _ -> assert (crel (mk ve je e) (mk ve' je' e')))
      (fun _ ->
        FStar.Classical.or_elim #(L.memP c' l1') #(L.memP c' l2')
          #(fun _ -> exists (c: child). L.memP c (dt_children cve es ve je dt) /\ crel c c')
          (fun _ ->
            dt_children_rel cve es cve' es' ve ve' je je' dt1 dt1' c';
            eliminate exists (c: child). L.memP c l1 /\ crel c c'
            with LP.append_memP l1 l2 c)
          (fun _ ->
            dt_children_rel cve es cve' es' ve ve' je je' dt2 dt2' c';
            eliminate exists (c: child). L.memP c l2 /\ crel c c'
            with LP.append_memP l1 l2 c))

and odt_children_rel (cve: venv) (es: list exp) (cve': venv) (es': list exp)
  (ve ve': venv) (je je': jenv) (df df': option dtree) (c': child)
  : Lemma (requires dtrel cve es cve' es' je je' /\ venv_rel ve ve' /\
                    ssim_odt (L.length ve) df df' /\ L.memP c' (odt_children cve' es' ve' je' df'))
          (ensures exists (c: child). L.memP c (odt_children cve es ve je df) /\ crel c c')
          (decreases df) =
  match df, df' with
  | Some dt, Some dt' -> dt_children_rel cve es cve' es' ve ve' je je' dt dt' c'

and brs_children_rel (#lb: eqtype) (cve: venv) (es: list exp) (cve': venv)
  (es': list exp) (ve ve': venv) (je je': jenv) (bs bs': list (lb & dtree)) (c': child)
  : Lemma (requires dtrel cve es cve' es' je je' /\ venv_rel ve ve' /\
                    ssim_brs (L.length ve) bs bs' /\ L.memP c' (brs_children cve' es' ve' je' bs'))
          (ensures exists (c: child). L.memP c (brs_children cve es ve je bs) /\ crel c c')
          (decreases bs) =
  match bs, bs' with
  | pa :: bs0, pb :: bs0' -> let (_, dt) = pa in let (_, dt') = pb in
    let l1 = dt_children cve es ve je dt in
    let l2 = brs_children cve es ve je bs0 in
    LP.append_memP (dt_children cve' es' ve' je' dt') (brs_children cve' es' ve' je' bs0') c';
    FStar.Classical.or_elim #(L.memP c' (dt_children cve' es' ve' je' dt'))
      #(L.memP c' (brs_children cve' es' ve' je' bs0'))
      #(fun _ -> exists (c: child). L.memP c (brs_children cve es ve je bs) /\ crel c c')
      (fun _ ->
        dt_children_rel cve es cve' es' ve ve' je je' dt dt' c';
        eliminate exists (c: child). L.memP c l1 /\ crel c c'
        with LP.append_memP l1 l2 c)
      (fun _ ->
        brs_children_rel cve es cve' es' ve ve' je je' bs0 bs0' c';
        eliminate exists (c: child). L.memP c l2 /\ crel c c'
        with LP.append_memP l1 l2 c)

let has_rel (l: list child) (c': child) : prop = exists (c: child). L.memP c l /\ crel c c'

let app_rel (l1 l2 l1' l2': list child) (c': child)
  : Lemma (requires L.memP c' (L.append l1' l2') /\
                    (L.memP c' l1' ==> has_rel l1 c') /\ (L.memP c' l2' ==> has_rel l2 c'))
          (ensures has_rel (L.append l1 l2) c') =
  LP.append_memP l1' l2' c';
  introduce forall (c: child). L.memP c l1 \/ L.memP c l2 ==> L.memP c (L.append l1 l2)
  with LP.append_memP l1 l2 c

let cons_rel (x: child) (l: list child) (x': child) (l': list child) (c': child)
  : Lemma (requires L.memP c' (x' :: l') /\ (c' == x' ==> crel x x') /\
                    (L.memP c' l' ==> has_rel l c'))
          (ensures has_rel (x :: l) c') = ()

let one_child (x x' c': child)
  : Lemma (requires L.memP c' [x'] /\ crel x x') (ensures has_rel [x] c') =
  assert (L.memP x [x])

let two_child (x y x' y' c': child)
  : Lemma (requires L.memP c' [x'; y'] /\ crel x x' /\ crel y y') (ensures has_rel [x; y] c') =
  FStar.Classical.or_elim #(c' == x') #(L.memP c' [y']) #(fun _ -> has_rel [x; y] c')
    (fun _ -> assert (L.memP x [x; y]))
    (fun _ -> assert (L.memP y [x; y]))

(* The immediate subexpressions of related terms, the original being no
   variable at or beyond the cutoff. *)
let children_rel_x (ve: venv) (je: jenv) (e: exp) (ve': venv) (je': jenv) (e': exp) (c': child)
  : Lemma (requires crel3 ve je e ve' je' e' /\ not (outside (L.length ve) e) /\
                    L.memP c' (children ve' je' e'))
          (ensures has_rel (children ve je e) c') =
  let n0 = L.length ve in
  venv_len ve ve';
  let one (b b': exp) : Lemma (requires ssim n0 b b' /\ L.memP c' [mk ve' je' b'])
                              (ensures has_rel [mk ve je b] c') =
    one_child (mk ve je b) (mk ve' je' b') c'
  in
  let two (b1 b2 b1' b2': exp)
    : Lemma (requires ssim n0 b1 b1' /\ ssim n0 b2 b2' /\
                      L.memP c' [mk ve' je' b1'; mk ve' je' b2'])
            (ensures has_rel [mk ve je b1; mk ve je b2] c') =
    two_child (mk ve je b1) (mk ve je b2) (mk ve' je' b1') (mk ve' je' b2') c'
  in
  match e, e' with
  | ELam _ _ b, ELam _ _ b' ->
    one_child (mk (VNone :: ve) je b) (mk (VNone :: ve') je' b') c'
  | ETyLam _ b, ETyLam _ b' -> one b b'
  | ETyApp b _, ETyApp b' _ -> one b b'
  | ECLam _ b, ECLam _ b' -> one b b'
  | ECApp b, ECApp b' -> one b b'
  | ESelect _ b, ESelect _ b' -> one b b'
  | ERestrict _ b, ERestrict _ b' -> one b b'
  | EInject _ _ b, EInject _ _ b' -> one b b'
  | EWeaken _ _ b, EWeaken _ _ b' -> one b b'
  | EAbsurd _ b, EAbsurd _ b' -> one b b'
  | EPerform _ _ _ b, EPerform _ _ _ b' -> one b b'
  | EOpenEff _ b, EOpenEff _ b' -> one b b'
  | EWriteCell _ _ b, EWriteCell _ _ b' -> one b b'
  | EOpenEffC _ b, EOpenEffC _ b' -> one b b'
  | EFill _ b, EFill _ b' -> one b b'
  | EApp e1 e2, EApp e1' e2' -> two e1 e2 e1' e2'
  | EExtend _ e1 e2, EExtend _ e1' e2' -> two e1 e2 e1' e2'
  | EUpdate _ e1 e2, EUpdate _ e1' e2' -> two e1 e2 e1' e2'
  | EMerge e1 e2, EMerge e1' e2' -> two e1 e2 e1' e2'
  | ELet _ e1 e2, ELet _ e1' e2' ->
    assert (crel (mk (push_let ve je e1) je e2) (mk (push_let ve' je' e1') je' e2'));
    two_child (mk ve je e1) (mk (push_let ve je e1) je e2) (mk ve' je' e1')
      (mk (push_let ve' je' e1') je' e2') c'
  | ELetRec bs b, ELetRec bs' b' ->
    children_letrec ve je bs b; children_letrec ve' je' bs' b';
    push_rec_rel ve ve' je je' bs bs';
    let pv = push_rec ve je bs in
    let pv' = push_rec ve' je' bs' in
    assert (crel (mk pv je b) (mk pv' je' b'));
    FStar.Classical.move_requires (rhs_children pv pv' je je' bs bs') c';
    FStar.Classical.move_requires (one_child (mk pv je b) (mk pv' je' b')) c';
    app_rel (L.map (rhs_child pv je) bs) [mk pv je b]
      (L.map (rhs_child pv' je') bs') [mk pv' je' b'] c'
  | ECase es dt, ECase es' dt' | EMatch es dt, EMatch es' dt' ->
    FStar.Classical.move_requires (exps_children ve ve' je je' es es') c';
    FStar.Classical.move_requires
      (dt_children_rel ve es ve' es' ve ve' je je' dt dt') c';
    app_rel (L.map (mk ve je) es) (dt_children ve es ve je dt)
      (L.map (mk ve' je') es') (dt_children ve' es' ve' je' dt') c'
  | ELetJoin ts _ e1 e2, ELetJoin ts' _ e1' e2' ->
    join_def_rel ve ve' je je' ts ts' e1 e2 e1' e2';
    join_scope_rel (join_def ve je ts e1 e2) (join_def ve' je' ts' e1' e2') c'
  | EJump _ es, EJump _ es' -> exps_children ve ve' je je' es es' c'
  | EHandle b h, EHandle b' h' ->
    assert (crel (mk ve je b) (mk ve' je' b'));
    assert (crel (mk (VNone :: ve) je h.h_ret) (mk (VNone :: ve') je' h'.h_ret));
    FStar.Classical.move_requires
      (clause_children_rel ve ve' je je' h.h_clauses h'.h_clauses) c';
    FStar.Classical.move_requires
      (cons_rel (mk (VNone :: ve) je h.h_ret) (clause_children ve je h.h_clauses)
        (mk (VNone :: ve') je' h'.h_ret) (clause_children ve' je' h'.h_clauses)) c';
    cons_rel (mk ve je b) (mk (VNone :: ve) je h.h_ret :: clause_children ve je h.h_clauses)
      (mk ve' je' b') (mk (VNone :: ve') je' h'.h_ret :: clause_children ve' je' h'.h_clauses) c'
  | ERegion _ es b, ERegion _ es' b' ->
    FStar.Classical.move_requires (one b) b';
    FStar.Classical.move_requires (exps_children ve ve' je je' es es') c';
    app_rel (L.map (mk ve je) es) [mk ve je b] (L.map (mk ve' je') es') [mk ve' je' b'] c'
  | ERegionOpen a th b, ERegionOpen a' th' b' ->
    children_region_open ve je a th b; children_region_open ve' je' a' th' b';
    FStar.Classical.move_requires (one b) b';
    FStar.Classical.move_requires (cells_children ve ve' je je' th th') c';
    app_rel (L.map (cell_child ve je) th) [mk ve je b]
      (L.map (cell_child ve' je') th') [mk ve' je' b'] c'
  | _ -> ()

(* A variable at or beyond the cutoff stands for an inert term, which is
   inert under the environments of the image. *)
let outside_dead (ve: venv) (je: jenv) (e: exp) (ve': venv) (je': jenv) (e': exp)
  : Lemma (requires crel3 ve je e ve' je' e' /\ outside (L.length ve) e)
          (ensures tri_ok ve' je' ve' je' e') =
  venv_len ve ve'

let rec sim_sub (#c' #s': child) (p: sub c' s') (c: child)
  : Lemma (requires crel c c')
          (ensures (exists (s: child). crel s s' /\ ex (sub c s)) \/ dead (L.length c'.cj) s')
          (decreases p) =
  if outside (L.length c.cv) c.ce then begin
    outside_dead c.cv c.cj c.ce c'.cv c'.cj c'.ce;
    sub_ok c'.cv c'.cj p;
    introduce exists (bv: venv) (bj: jenv). L.length bj >= L.length c'.cj /\ child_ok bv bj s'
    with c'.cv c'.cj and ()
  end else
  match p with
  | SubHere _ -> ex_intro (SubHere c)
  | SubChild #_ #c1' #_ _ p1 ->
    children_rel_x c.cv c.cj c.ce c'.cv c'.cj c'.ce c1';
    children_cj c'.cv c'.cj c'.ce c1';
    eliminate exists (c1: child). L.memP c1 (children c.cv c.cj c.ce) /\ crel c1 c1'
    with (sim_sub p1 c1;
          FStar.Classical.or_elim #(exists (s: child). crel s s' /\ ex (sub c1 s))
            #(dead (L.length c1'.cj) s')
            #(fun _ -> (exists (s: child). crel s s' /\ ex (sub c s)) \/ dead (L.length c'.cj) s')
            (fun _ ->
              eliminate exists (s: child). crel s s' /\ ex (sub c1 s)
              with (ex_map #(sub c1 s) #(sub c s) (fun q1 -> SubChild #c #c1 #s () q1)))
            (fun _ -> ()))

(* The parts a rule reads off a form. *)

let through_rel (n: nat) (e e': exp)
  : Lemma (requires ssim n e e' /\ not (outside n e) /\ Some? (through e'))
          (ensures Some? (through e) /\ ssim n (Some?.v (through e)) (Some?.v (through e'))) = ()

let takes_rel (n: nat) (e e': exp)
  : Lemma (requires ssim n e e' /\ not (outside n e) /\ Some? (takes e'))
          (ensures Some? (takes e) /\ ssim n (Some?.v (takes e)) (Some?.v (takes e'))) = ()

let pair_rel (n: nat) (a b a' b' x': exp)
  : Lemma (requires ssim n a a' /\ ssim n b b' /\ L.memP x' [a'; b'])
          (ensures exists (x: exp). L.memP x [a; b] /\ ssim n x x') =
  FStar.Classical.or_elim #(x' == a') #(L.memP x' [b'])
    #(fun _ -> exists (x: exp). L.memP x [a; b] /\ ssim n x x')
    (fun _ -> assert (L.memP a [a; b]))
    (fun _ -> assert (L.memP b [a; b]))

let one_rel (n: nat) (a a' x': exp)
  : Lemma (requires ssim n a a' /\ L.memP x' [a'])
          (ensures exists (x: exp). L.memP x [a] /\ ssim n x x') =
  assert (L.memP a [a])

let builds_rel (n: nat) (e e' b': exp)
  : Lemma (requires ssim n e e' /\ not (outside n e) /\ L.memP b' (builds e'))
          (ensures exists (b: exp). L.memP b (builds e) /\ ssim n b b') =
  match e, e' with
  | EExtend _ e1 e2, EExtend _ e1' e2' | EUpdate _ e1 e2, EUpdate _ e1' e2'
  | EMerge e1 e2, EMerge e1' e2' -> pair_rel n e1 e2 e1' e2' b'
  | EInject _ _ b, EInject _ _ b0' -> one_rel n b b0' b'
  | _ -> ()

(* A chain of the original is a chain of the image with the same head and
   the same number of value arguments. The image of a variable at or
   beyond the cutoff may be a chain, at the head of an application of the
   original, so the converse fails. *)
let rec decompose_rel (n: nat) (e e': exp)
  : Lemma (requires ssim n e e' /\ Some? (decompose_global_app e))
          (ensures (match decompose_global_app e, decompose_global_app e' with
                    | Some (q, _, args), Some (q', _, args') ->
                      q == q' /\ value_count args == value_count args'
                    | _ -> False))
          (decreases e) =
  match e, e' with
  | EApp f v, EApp f' v' ->
    decompose_rel n f f';
    (match decompose_global_app f, decompose_global_app f' with
     | Some (_, _, args), Some (_, _, args') ->
       value_count_append args [SVal v]; value_count_append args' [SVal v']
     | _ -> ())
  | ETyApp f t, ETyApp f' t' ->
    decompose_rel n f f';
    (match decompose_global_app f, decompose_global_app f' with
     | Some (_, _, args), Some (_, _, args') ->
       value_count_append args [STy t]; value_count_append args' [STy t']
     | _ -> ())
  | ECApp f, ECApp f' ->
    decompose_rel n f f';
    (match decompose_global_app f, decompose_global_app f' with
     | Some (_, _, args), Some (_, _, args') ->
       value_count_append args [SConstr]; value_count_append args' [SConstr]
     | _ -> ())
  | _ -> ()

let spine_app_rel (sg: sig) (g g': group) (n: nat) (e e': exp)
  : Lemma (requires ssim n e e' /\ local g /\ local g' /\ spine_app sg g e)
          (ensures spine_app sg g' e') =
  match decompose_global_app e with
  | Some _ -> decompose_rel n e e'
  | None -> ()

(* An application read as part of a chain in the image is read by the
   default rule or as part of a chain in the original; both read the
   parts now. *)
let spine_parts_rel (sg: sig) (g g': group) (n: nat) (e e' b': exp)
  : Lemma (requires ssim n e e' /\ not (outside n e) /\ L.memP b' (spine_parts sg g' e'))
          (ensures exists (b: exp).
               (L.memP b (spine_parts sg g e) \/ L.memP b (default_parts sg g e)) /\
                     ssim n b b') =
  match e, e' with
  | EApp f v, EApp f' v' -> pair_rel n f v f' v' b'
  | _ -> ()

let default_parts_rel (sg: sig) (g g': group) (n: nat) (e e' b': exp)
  : Lemma (requires ssim n e e' /\ not (outside n e) /\ local g /\ local g' /\
                    L.memP b' (default_parts sg g' e'))
          (ensures exists (b: exp). L.memP b (default_parts sg g e) /\ ssim n b b') =
  FStar.Classical.move_requires (spine_app_rel sg g g' n e) e';
  match e, e' with
  | EApp f v, EApp f' v' -> pair_rel n f v f' v' b'
  | EPerform _ _ _ b, EPerform _ _ _ b0' | EWriteCell _ _ b, EWriteCell _ _ b0'
  | EFill _ b, EFill _ b0' -> one_rel n b b0' b'
  | _ -> ()

let scrut_rel (n: nat) (e e': exp)
  : Lemma (requires ssim n e e' /\ not (outside n e) /\ Some? (scrutinised e'))
          (ensures Some? (scrutinised e) /\
                   ssim_exps n (fst (Some?.v (scrutinised e))) (fst (Some?.v (scrutinised e'))) /\
                   ssim_dt n (snd (Some?.v (scrutinised e))) (snd (Some?.v (scrutinised e')))) = ()

let is_whole_rel (n: nat) (e e': exp)
  : Lemma (requires ssim n e e' /\ not (outside n e)) (ensures is_whole e == is_whole e') = ()

let rec brs_snd_mem (#lb: eqtype) (n: nat) (bs bs': list (lb & dtree)) (s': dtree)
  : Lemma (requires ssim_brs n bs bs' /\ L.memP s' (L.map snd bs'))
          (ensures exists (s: dtree). L.memP s (L.map snd bs) /\ ssim_dt n s s') (decreases bs) =
  match bs, bs' with
  | pa :: bs0, pb :: bs0' -> let (_, dt) = pa in let (_, dt') = pb in
    FStar.Classical.or_elim #(s' == dt') #(L.memP s' (L.map snd bs0'))
      #(fun _ -> exists (s: dtree). L.memP s (L.map snd bs) /\ ssim_dt n s s')
      (fun _ -> ())
      (fun _ -> brs_snd_mem n bs0 bs0' s')

let has_dt (n: nat) (l: list dtree) (s': dtree) : prop =
  exists (s: dtree). L.memP s l /\ ssim_dt n s s'

let app_dt (n: nat) (l1 l2 l1' l2': list dtree) (s': dtree)
  : Lemma (requires L.memP s' (L.append l1' l2') /\
                    (L.memP s' l1' ==> has_dt n l1 s') /\ (L.memP s' l2' ==> has_dt n l2 s'))
          (ensures has_dt n (L.append l1 l2) s') =
  LP.append_memP l1' l2' s';
  introduce forall (s: dtree). L.memP s l1 \/ L.memP s l2 ==> L.memP s (L.append l1 l2)
  with LP.append_memP l1 l2 s

let one_dt (n: nat) (x x' s': dtree)
  : Lemma (requires ssim_dt n x x' /\ L.memP s' [x']) (ensures has_dt n [x] s') =
  assert (L.memP x [x])

let odt_list_rel (n: nat) (df df': option dtree) (s': dtree)
  : Lemma (requires ssim_odt n df df' /\ L.memP s' (match df' with Some d -> [d] | None -> []))
          (ensures has_dt n (match df with Some d -> [d] | None -> []) s') =
  match df, df' with
  | Some d, Some d' -> one_dt n d d' s'
  | _ -> ()

let switch_rel (n: nat) (dt dt' s': dtree)
  : Lemma (requires ssim_dt n dt dt' /\ L.memP s' (switch_subtrees dt'))
          (ensures has_dt n (switch_subtrees dt) s') =
  match dt, dt' with
  | DSwitchCtor _ bs df, DSwitchCtor _ bs' df' ->
    FStar.Classical.move_requires (brs_snd_mem n bs bs') s';
    FStar.Classical.move_requires (odt_list_rel n df df') s';
    app_dt n (L.map snd bs) (match df with Some d -> [d] | None -> [])
      (L.map snd bs') (match df' with Some d -> [d] | None -> []) s'
  | DSwitchKey _ bs df, DSwitchKey _ bs' df' ->
    FStar.Classical.move_requires (brs_snd_mem n bs bs') s';
    FStar.Classical.move_requires (odt_list_rel n df df') s';
    app_dt n (L.map snd bs) (match df with Some d -> [d] | None -> [])
      (L.map snd bs') (match df' with Some d -> [d] | None -> []) s'
  | DSwitchLit _ bs df, DSwitchLit _ bs' df' ->
    FStar.Classical.move_requires (brs_snd_mem n bs bs') s';
    FStar.Classical.move_requires (one_dt n df df') s';
    app_dt n (L.map snd bs) [df] (L.map snd bs') [df'] s'
  | _ -> ()

let join_arg_rel (n: nat) (d d': jentry) (p: nat) (es es': list exp)
  : Lemma (requires jent_rel d d' /\ ssim_exps n es es' /\ Some? (join_arg d' p es'))
          (ensures Some? (join_arg d p es) /\
                   ssim n (Some?.v (join_arg d p es)) (Some?.v (join_arg d' p es'))) =
  match d, d' with
  | JDef _ _ k _ _, JDef _ _ _ _ _ -> if p < k then exps_nth n es es' (k - 1 - p)

let ent_inv_mem (v: ventry) (k: nat) : Lemma (requires ent_rel v (VMem k)) (ensures v == VMem k) =
  match v with
  | VMem _ -> ()
  | _ -> ()

(* A jump of the image in a related child: an inert term has no free
   jump, so the original is a jump too. *)
let jump_target (d0 d0': jentry) (p: nat) (s: child) (ve3': venv) (je3': jenv) (j: nat)
  (es': list exp) (a': exp)
  : Lemma (requires jent_rel d0 d0' /\ crel s (mk ve3' je3' (EJump j es')) /\
                    j + L.length (join_jenv d0') == L.length je3' /\ join_arg d0' p es' == Some a')
          (ensures EJump? s.ce /\
                   s == mk s.cv s.cj (EJump j (EJump?._1 s.ce)) /\
                   j + L.length (join_jenv d0) == L.length s.cj /\
                   Some? (join_arg d0 p (EJump?._1 s.ce)) /\
                   crel3 s.cv s.cj (Some?.v (join_arg d0 p (EJump?._1 s.ce))) ve3' je3' a') =
  join_jenv_length d0 d0';
  jenv_length s.cj je3';
  match s with
  | { cv = ve3; cj = je3; ce = EJump _ es } -> join_arg_rel (L.length ve3) d0 d0' p es es'
  | _ -> ()

(* A jump within an inert term targets no join point outside it. *)
let dead_jump (lo: nat) (ve3': venv) (je3': jenv) (j: nat) (es': list exp)
  : Lemma (requires dead lo (mk ve3' je3' (EJump j es')) /\ j + lo == L.length je3')
          (ensures False) =
  eliminate exists (bv: venv) (bj: jenv).
      L.length bj >= lo /\ child_ok bv bj (mk ve3' je3' (EJump j es'))
  with (jenv_ok_len bv bj je3';
        iner_jump (dif (L.length ve3') (L.length bv)) (L.length bv)
          (dif (L.length je3') (L.length bj))
          j es')

(* The target of a jump that hands an argument to a join parameter. *)
let join_arg_case (ve ve': venv) (i: nat) (d0': jentry) (p: nat) (c': child)
  (ve3': venv) (je3': jenv) (j: nat) (es': list exp) (a': exp)
  (sb': sub c' (mk ve3' je3' (EJump j es')))
  : Lemma (requires venv_rel ve ve' /\ vlook ve' i == VArg d0' p /\
                    L.memP c' (join_scope d0') /\ j + L.length (join_jenv d0') == L.length je3' /\
                    join_arg d0' p es' == Some a')
          (ensures VArg? (vlook ve i) /\ VArg?.p (vlook ve i) == p /\
                   (exists (c: child) (ve3: venv) (je3: jenv) (es: list exp) (a: exp).
                      L.memP c (join_scope (VArg?.d (vlook ve i))) /\
                      ex (sub c (mk ve3 je3 (EJump j es))) /\
                      j + L.length (join_jenv (VArg?.d (vlook ve i))) == L.length je3 /\
                      join_arg (VArg?.d (vlook ve i)) p es == Some a /\
                      crel3 ve3 je3 a ve3' je3' a')) =
  venv_lookup ve ve' i;
  match vlook ve i with
  | VArg d0 _ ->
    join_scope_rel d0 d0' c';
    join_jenv_length d0 d0';
    join_scope_cj d0' c';
    eliminate exists (c: child). L.memP c (join_scope d0) /\ crel c c'
    with (sim_sub sb' c;
          FStar.Classical.or_elim
            #(exists (s: child). crel s (mk ve3' je3' (EJump j es')) /\ ex (sub c s))
            #(dead (L.length c'.cj) (mk ve3' je3' (EJump j es')))
            #(fun _ -> exists (c: child) (ve3: venv) (je3: jenv) (es: list exp) (a: exp).
                  L.memP c (join_scope d0) /\ ex (sub c (mk ve3 je3 (EJump j es))) /\
                  j + L.length (join_jenv d0) == L.length je3 /\ join_arg d0 p es == Some a /\
                  crel3 ve3 je3 a ve3' je3' a')
            (fun _ ->
              eliminate exists (s: child). crel s (mk ve3' je3' (EJump j es')) /\ ex (sub c s)
              with (jump_target d0 d0' p s ve3' je3' j es' a';
                    introduce exists (c: child) (ve3: venv) (je3: jenv) (es: list exp) (a: exp).
                      L.memP c (join_scope d0) /\ ex (sub c (mk ve3 je3 (EJump j es))) /\
                      j + L.length (join_jenv d0) == L.length je3 /\ join_arg d0 p es == Some a /\
                      crel3 ve3 je3 a ve3' je3' a'
                    with c s.cv s.cj (EJump?._1 s.ce) (Some?.v (join_arg d0 p (EJump?._1 s.ce)))
                    and ()))
            (fun _ -> dead_jump (L.length c'.cj) ve3' je3' j es'))
  | _ -> ()

let ssim_var_inv (n: nat) (e e': exp)
  : Lemma (requires ssim n e e' /\ not (outside n e) /\ EVar? e')
          (ensures EVar? e /\ EVar?._0 e' == EVar?._0 e /\ EVar?._0 e < n) =
  match e with
  | EVar _ -> ()
  | _ -> ()

(* A member of a nested group, read through its variable. *)
let local_rec_case (ve ve': venv) (i: nat) (ve2': venv) (je2': jenv)
  (bs': list (typ & exp)) (k: nat) (r': exp)
  : Lemma (requires venv_rel ve ve' /\ vlook ve' i == VRec ve2' je2' bs' k /\
                    Some? (L.nth bs' k) /\ snd (Some?.v (L.nth bs' k)) == r')
          (ensures VRec? (vlook ve i) /\ VRec?.k (vlook ve i) == k /\
                   Some? (L.nth (VRec?.bs (vlook ve i)) k) /\
                   crel3 (push_rec (VRec?.ve (vlook ve i)) (VRec?.je (vlook ve i))
                       (VRec?.bs (vlook ve i)))
                     (VRec?.je (vlook ve i)) (snd (Some?.v (L.nth (VRec?.bs (vlook ve i)) k)))
                     (push_rec ve2' je2' bs') je2' r') =
  venv_lookup ve ve' i;
  match vlook ve i with
  | VRec ve2 je2 bs _ ->
    push_rec_rel ve2 ve2' je2 je2' bs bs';
    binds_nth (L.length ve2 + L.length bs) bs bs' k
  | _ -> ()

(* The simulation. *)

let rec sim_imm (#sg: sig) (#g': group) (#ve': venv) (#je': jenv) (#e': exp) (#m: nat)
  (d': reads_imm sg g' ve' je' e' m) (g: group) (ve: venv) (je: jenv) (e: exp)
  : Lemma (requires grel g g' /\ crel3 ve je e ve' je' e')
          (ensures ex (reads_imm sg g ve je e m)) (decreases d') =
  let n = L.length ve in
  venv_len ve ve';
  if outside n e then begin
    outside_dead ve je e ve' je' e';
    inert_imm d' ve' je'
  end else
  match d' with
  | IMember _ ->
    ssim_var_inv n e e';
    let EVar i = e in
    venv_lookup ve ve' i; ent_inv_mem (vlook ve i) m;
    ex_intro #(reads_imm sg g ve je (EVar i) m) (IMember ())
  | IMemberGlobal #_ #_ #_ #_ #q0 _ -> assert (g'.gmem q0 == None)
  | IThrough _ d1' ->
    through_rel n e e';
    let b = Some?.v (through e) in
    sim_imm d1' g ve je b;
    ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> IThrough () d1)
  | IBuild #_ #_ #_ #_ #_ #b' _ d1' ->
    builds_rel n e e' b';
    eliminate exists (b: exp). L.memP b (builds e) /\ ssim n b b'
    with (sim_imm d1' g ve je b;
          ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> IBuild () d1))
  | ITake _ d1' ->
    takes_rel n e e';
    let b = Some?.v (takes e) in
    sim_imm d1' g ve je b;
    ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> ITake () d1)
  | ISpine #_ #_ #_ #_ #_ #b' _ d1' ->
    spine_parts_rel sg g g' n e e' b';
    eliminate exists (b: exp).
      (L.memP b (spine_parts sg g e) \/ L.memP b (default_parts sg g e)) /\ ssim n b b'
    with (sim_imm d1' g ve je b;
          FStar.Classical.or_elim #(L.memP b (spine_parts sg g e))
              #(L.memP b (default_parts sg g e))
            #(fun _ -> ex (reads_imm sg g ve je e m))
            (fun _ -> ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m)
                       (fun d1 -> ISpine () d1))
            (fun _ -> ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m)
                       (fun d1 -> IDefault () d1)))
  | IDefault #_ #_ #_ #_ #_ #b' _ d1' ->
    default_parts_rel sg g g' n e e' b';
    eliminate exists (b: exp). L.memP b (default_parts sg g e) /\ ssim n b b'
    with (sim_imm d1' g ve je b;
          ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m) (fun d1 -> IDefault () d1))
  | IDefaultLat #_ #_ #_ #_ #_ #b' _ d1' ->
    default_parts_rel sg g g' n e e' b';
    eliminate exists (b: exp). L.memP b (default_parts sg g e) /\ ssim n b b'
    with (sim_lat d1' g ve je b;
          ex_map #(reads_lat sg g ve je b m) #(reads_imm sg g ve je e m)
            (fun d1 -> IDefaultLat () d1))
  | ILetBound d1' ->
    (match e, e' with
     | ELet t e1 e2, ELet _ e1' _ ->
       sim_imm d1' g ve je e1;
       ex_map #(reads_imm sg g ve je e1 m) #(reads_imm sg g ve je (ELet t e1 e2) m)
         (fun d1 -> ILetBound d1)
     | _ -> ())
  | ILetBody d1' ->
    (match e, e' with
     | ELet t e1 e2, ELet _ e1' e2' ->
       assert (crel3 (push_let ve je e1) je e2 (push_let ve' je' e1') je' e2');
       sim_imm d1' g (push_let ve je e1) je e2;
       ex_map #(reads_imm sg g (push_let ve je e1) je e2 m) #(reads_imm sg g ve je (ELet t e1 e2) m)
         (fun d1 -> ILetBody d1)
     | _ -> ())
  | ILetRecRhs #_ #_ #_ #_ #_ #_ #t' #r' _ d1' ->
    (match e, e' with
     | ELetRec bs b, ELetRec bs' _ ->
       let k = L.length bs in
       push_rec_rel ve ve' je je' bs bs';
       binds_mem (n + k) bs bs' t' r';
       eliminate exists (t: typ) (r: exp). L.memP (t, r) bs /\ ssim (n + k) r r'
       with (sim_imm d1' g (push_rec ve je bs) je r;
             ex_map #(reads_imm sg g (push_rec ve je bs) je r m)
               #(reads_imm sg g ve je (ELetRec bs b) m)
                 (fun d1 -> ILetRecRhs #sg #g #ve #je #bs #b #t #r #m () d1))
     | _ -> ())
  | ILetRecBody d1' ->
    (match e, e' with
     | ELetRec bs b, ELetRec bs' b' ->
       push_rec_rel ve ve' je je' bs bs';
       sim_imm d1' g (push_rec ve je bs) je b;
       ex_map #(reads_imm sg g (push_rec ve je bs) je b m) #(reads_imm sg g ve je (ELetRec bs b) m)
         (fun d1 -> ILetRecBody d1)
     | _ -> ())
  | ICaseScrut #_ #_ #_ #_ #_ #_ #_ #b' _ _ d1' ->
    scrut_rel n e e';
    let Some (es, dt) = scrutinised e in
    let Some (es', _) = scrutinised e' in
    exps_mem n es es' b';
    eliminate exists (b: exp). L.memP b es /\ ssim n b b'
    with (sim_imm d1' g ve je b;
          ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je e m)
            (fun d1 -> ICaseScrut #sg #g #ve #je #e #es #dt #b #m () () d1))
  | ICaseTree _ d1' ->
    scrut_rel n e e';
    let Some (es, dt) = scrutinised e in
    sim_imm_dt d1' g ve es ve je dt;
    ex_map #(reads_imm_dt sg g ve es ve je dt m) #(reads_imm sg g ve je e m)
      (fun d1 -> ICaseTree #sg #g #ve #je #e #es #dt #m () d1)
  | ILetJoin d1' ->
    (match e, e' with
     | ELetJoin ts t e1 e2, ELetJoin ts' _ e1' e2' ->
       join_def_rel ve ve' je je' ts ts' e1 e2 e1' e2';
       let je1 = join_def ve je ts e1 e2 :: je in
       sim_imm d1' g ve je1 e2;
       ex_map #(reads_imm sg g ve je1 e2 m) #(reads_imm sg g ve je (ELetJoin ts t e1 e2) m)
         (fun d1 -> ILetJoin d1)
     | _ -> ())
  | IJumpArg #_ #_ #_ #_ #_ #_ #b' _ d1' ->
    (match e, e' with
     | EJump j es, EJump _ es' ->
       exps_mem n es es' b';
       eliminate exists (b: exp). L.memP b es /\ ssim n b b'
       with (sim_imm d1' g ve je b;
             ex_map #(reads_imm sg g ve je b m) #(reads_imm sg g ve je (EJump j es) m)
               (fun d1 -> IJumpArg #sg #g #ve #je #j #es #b #m () d1))
     | _ -> ())
  | IJumpBody #_ #_ #_ #_ #_ #_ #d0' _ d1' ->
    (match e, e' with
     | EJump j es, EJump _ _ ->
       jenv_lookup je je' j;
       let Some d0 = jlook je j in
       join_body_rel d0 d0';
       sim_imm d1' g (join_body d0).cv (join_body d0).cj (join_body d0).ce;
       ex_map #(reads_imm sg g (join_body d0).cv (join_body d0).cj (join_body d0).ce m)
         #(reads_imm sg g ve je (EJump j es) m)
           (fun d1 -> IJumpBody #sg #g #ve #je #j #es #d0 #m () d1)
     | _ -> ())
  | IWhole #_ #_ #_ #_ #_ #c' #s' _ _ sb' d1' ->
    is_whole_rel n e e';
    children_rel_x ve je e ve' je' e' c';
    eliminate exists (c: child). L.memP c (children ve je e) /\ crel c c'
    with (sim_sub sb' c;
          FStar.Classical.or_elim #(exists (s: child). crel s s' /\ ex (sub c s))
            #(dead (L.length c'.cj) s') #(fun _ -> ex (reads_imm sg g ve je e m))
            (fun _ ->
              eliminate exists (s: child). crel s s' /\ ex (sub c s)
              with (sim_imm d1' g s.cv s.cj s.ce;
                    ex_map2 #(sub c s) #(reads_imm sg g s.cv s.cj s.ce m)
                      #(reads_imm sg g ve je e m)
                      (fun sb d1 -> IWhole #sg #g #ve #je #e #c #s #m () () sb d1)))
            (fun _ ->
              eliminate exists (bv: venv) (bj: jenv).
                  L.length bj >= L.length c'.cj /\ child_ok bv bj s'
              with inert_imm d1' bv bj))
  | IWholeLat #_ #_ #_ #_ #_ #c' #s' _ _ sb' d1' ->
    is_whole_rel n e e';
    children_rel_x ve je e ve' je' e' c';
    eliminate exists (c: child). L.memP c (children ve je e) /\ crel c c'
    with (sim_sub sb' c;
          FStar.Classical.or_elim #(exists (s: child). crel s s' /\ ex (sub c s))
            #(dead (L.length c'.cj) s') #(fun _ -> ex (reads_imm sg g ve je e m))
            (fun _ ->
              eliminate exists (s: child). crel s s' /\ ex (sub c s)
              with (sim_lat d1' g s.cv s.cj s.ce;
                    ex_map2 #(sub c s) #(reads_lat sg g s.cv s.cj s.ce m)
                      #(reads_imm sg g ve je e m)
                      (fun sb d1 -> IWholeLat #sg #g #ve #je #e #c #s #m () () sb d1)))
            (fun _ ->
              eliminate exists (bv: venv) (bj: jenv).
                  L.length bj >= L.length c'.cj /\ child_ok bv bj s'
              with inert_lat d1' bv bj))

and sim_lat (#sg: sig) (#g': group) (#ve': venv) (#je': jenv) (#e': exp) (#m: nat)
  (d': reads_lat sg g' ve' je' e' m) (g: group) (ve: venv) (je: jenv) (e: exp)
  : Lemma (requires grel g g' /\ crel3 ve je e ve' je' e')
          (ensures ex (reads_lat sg g ve je e m)) (decreases d') =
  let n = L.length ve in
  venv_len ve ve';
  if outside n e then begin
    outside_dead ve je e ve' je' e';
    inert_lat d' ve' je'
  end else
  match d' with
  | LMember #_ #_ #_ #_ #_ #k #r' _ _ d1' ->
    ssim_var_inv n e e';
    let EVar i = e in
    venv_lookup ve ve' i; ent_inv_mem (vlook ve i) k;
    eliminate exists (r: exp). rhs g k == Some r /\ crel3 g.genv [] r g'.genv [] r'
    with (sim_lat d1' g g.genv [] r;
          ex_map #(reads_lat sg g g.genv [] r m) #(reads_lat sg g ve je (EVar i) m)
            (fun d1 -> LMember #sg #g #ve #je #i #k #r #m () () d1))
  | LMemberGlobal #_ #_ #_ #_ #q0 _ _ _ -> assert (g'.gmem q0 == None)
  | LLocal #_ #_ #_ #_ #_ #ve2' #je2' #e2' _ d1' ->
    ssim_var_inv n e e';
    let EVar i = e in
    venv_lookup ve ve' i;
    (match vlook ve i with
     | VLat ve2 je2 e2 ->
       sim_lat d1' g ve2 je2 e2;
       ex_map #(reads_lat sg g ve2 je2 e2 m) #(reads_lat sg g ve je (EVar i) m)
         (fun d1 -> LLocal #sg #g #ve #je #i #ve2 #je2 #e2 #m () d1)
     | _ -> ())
  | LLocalRec #_ #_ #_ #_ #_ #ve2' #je2' #bs' #k #t' #r' _ _ d1' ->
    ssim_var_inv n e e';
    let EVar i = e in
    local_rec_case ve ve' i ve2' je2' bs' k r';
    let VRec ve2 je2 bs _ = vlook ve i in
    let Some (t, r) = L.nth bs k in
    sim_lat d1' g (push_rec ve2 je2 bs) je2 r;
    ex_map #(reads_lat sg g (push_rec ve2 je2 bs) je2 r m) #(reads_lat sg g ve je (EVar i) m)
      (fun d1 -> LLocalRec #sg #g #ve #je #i #ve2 #je2 #bs #k #t #r #m () () d1)
  | LJoinArg #_ #_ #_ #_ #_ #d0' #p #c' #ve3' #je3' #j #es' #a' #_ _ _ sb' _ _ d1' ->
    ssim_var_inv n e e';
    let EVar i = e in
    join_arg_case ve ve' i d0' p c' ve3' je3' j es' a' sb';
    let d0 = VArg?.d (vlook ve i) in
    eliminate exists (c: child) (ve3: venv) (je3: jenv) (es: list exp) (a: exp).
      L.memP c (join_scope d0) /\ ex (sub c (mk ve3 je3 (EJump j es))) /\
      j + L.length (join_jenv d0) == L.length je3 /\ join_arg d0 p es == Some a /\
      crel3 ve3 je3 a ve3' je3' a'
    with (sim_lat d1' g ve3 je3 a;
          ex_map2 #(sub c (mk ve3 je3 (EJump j es))) #(reads_lat sg g ve3 je3 a m)
            #(reads_lat sg g ve je (EVar i) m)
            (fun sb d1 -> LJoinArg #sg #g #ve #je #i #d0 #p #c #ve3 #je3 #j #es #a #m
               () () sb () () d1))
  | LLam d1' ->
    (match e, e' with
     | ELam t r b, ELam _ _ b' ->
       sim_imm d1' g (VNone :: ve) je b;
       ex_map #(reads_imm sg g (VNone :: ve) je b m) #(reads_lat sg g ve je (ELam t r b) m)
         (fun d1 -> LLam d1)
     | _ -> ())
  | LLamLat d1' ->
    (match e, e' with
     | ELam t r b, ELam _ _ b' ->
       sim_lat d1' g (VNone :: ve) je b;
       ex_map #(reads_lat sg g (VNone :: ve) je b m) #(reads_lat sg g ve je (ELam t r b) m)
         (fun d1 -> LLamLat d1)
     | _ -> ())
  | LThrough _ d1' ->
    through_rel n e e';
    let b = Some?.v (through e) in
    sim_lat d1' g ve je b;
    ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LThrough () d1)
  | LBuild #_ #_ #_ #_ #_ #b' _ d1' ->
    builds_rel n e e' b';
    eliminate exists (b: exp). L.memP b (builds e) /\ ssim n b b'
    with (sim_lat d1' g ve je b;
          ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LBuild () d1))
  | LTake _ d1' ->
    takes_rel n e e';
    let b = Some?.v (takes e) in
    sim_lat d1' g ve je b;
    ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LTake () d1)
  | LSpine #_ #_ #_ #_ #_ #b' _ d1' ->
    spine_parts_rel sg g g' n e e' b';
    eliminate exists (b: exp).
      (L.memP b (spine_parts sg g e) \/ L.memP b (default_parts sg g e)) /\ ssim n b b'
    with (sim_lat d1' g ve je b;
          FStar.Classical.or_elim #(L.memP b (spine_parts sg g e))
              #(L.memP b (default_parts sg g e))
            #(fun _ -> ex (reads_lat sg g ve je e m))
            (fun _ -> ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m)
                       (fun d1 -> LSpine () d1))
            (fun _ -> ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m)
                       (fun d1 -> LDefault () d1)))
  | LDefault #_ #_ #_ #_ #_ #b' _ d1' ->
    default_parts_rel sg g g' n e e' b';
    eliminate exists (b: exp). L.memP b (default_parts sg g e) /\ ssim n b b'
    with (sim_lat d1' g ve je b;
          ex_map #(reads_lat sg g ve je b m) #(reads_lat sg g ve je e m) (fun d1 -> LDefault () d1))
  | LLet d1' ->
    (match e, e' with
     | ELet t e1 e2, ELet _ e1' e2' ->
       assert (crel3 (push_let ve je e1) je e2 (push_let ve' je' e1') je' e2');
       sim_lat d1' g (push_let ve je e1) je e2;
       ex_map #(reads_lat sg g (push_let ve je e1) je e2 m) #(reads_lat sg g ve je (ELet t e1 e2) m)
         (fun d1 -> LLet d1)
     | _ -> ())
  | LLetRec d1' ->
    (match e, e' with
     | ELetRec bs b, ELetRec bs' b' ->
       push_rec_rel ve ve' je je' bs bs';
       sim_lat d1' g (push_rec ve je bs) je b;
       ex_map #(reads_lat sg g (push_rec ve je bs) je b m) #(reads_lat sg g ve je (ELetRec bs b) m)
         (fun d1 -> LLetRec d1)
     | _ -> ())
  | LCase _ d1' ->
    scrut_rel n e e';
    let Some (es, dt) = scrutinised e in
    sim_lat_dt d1' g ve es ve je dt;
    ex_map #(reads_lat_dt sg g ve es ve je dt m) #(reads_lat sg g ve je e m)
      (fun d1 -> LCase #sg #g #ve #je #e #es #dt #m () d1)
  | LLetJoin d1' ->
    (match e, e' with
     | ELetJoin ts t e1 e2, ELetJoin ts' _ e1' e2' ->
       join_def_rel ve ve' je je' ts ts' e1 e2 e1' e2';
       let je1 = join_def ve je ts e1 e2 :: je in
       sim_lat d1' g ve je1 e2;
       ex_map #(reads_lat sg g ve je1 e2 m) #(reads_lat sg g ve je (ELetJoin ts t e1 e2) m)
         (fun d1 -> LLetJoin d1)
     | _ -> ())
  | LJump #_ #_ #_ #_ #_ #_ #d0' _ d1' ->
    (match e, e' with
     | EJump j es, EJump _ _ ->
       jenv_lookup je je' j;
       let Some d0 = jlook je j in
       join_body_rel d0 d0';
       sim_lat d1' g (join_body d0).cv (join_body d0).cj (join_body d0).ce;
       ex_map #(reads_lat sg g (join_body d0).cv (join_body d0).cj (join_body d0).ce m)
         #(reads_lat sg g ve je (EJump j es) m) (fun d1 -> LJump #sg #g #ve #je #j #es #d0 #m () d1)
     | _ -> ())
  | LWhole #_ #_ #_ #_ #_ #c' #s' _ _ sb' d1' ->
    is_whole_rel n e e';
    children_rel_x ve je e ve' je' e' c';
    eliminate exists (c: child). L.memP c (children ve je e) /\ crel c c'
    with (sim_sub sb' c;
          FStar.Classical.or_elim #(exists (s: child). crel s s' /\ ex (sub c s))
            #(dead (L.length c'.cj) s') #(fun _ -> ex (reads_lat sg g ve je e m))
            (fun _ ->
              eliminate exists (s: child). crel s s' /\ ex (sub c s)
              with (sim_lat d1' g s.cv s.cj s.ce;
                    ex_map2 #(sub c s) #(reads_lat sg g s.cv s.cj s.ce m)
                      #(reads_lat sg g ve je e m)
                      (fun sb d1 -> LWhole #sg #g #ve #je #e #c #s #m () () sb d1)))
            (fun _ ->
              eliminate exists (bv: venv) (bj: jenv).
                  L.length bj >= L.length c'.cj /\ child_ok bv bj s'
              with inert_lat d1' bv bj))

and sim_imm_dt (#sg: sig) (#g': group) (#cve': venv) (#es': list exp) (#ve': venv) (#je': jenv)
  (#dt': dtree) (#m: nat)
  (d': reads_imm_dt sg g' cve' es' ve' je' dt' m) (g: group) (cve: venv) (es: list exp) (ve: venv)
  (je: jenv) (dt: dtree)
  : Lemma (requires grel g g' /\ dtrel cve es cve' es' je je' /\ venv_rel ve ve' /\
                    ssim_dt (L.length ve) dt dt')
          (ensures ex (reads_imm_dt sg g cve es ve je dt m)) (decreases d') =
  match d' with
  | ITLeaf d1' ->
    (match dt, dt' with
     | DLeaf e, DLeaf e' ->
       sim_imm d1' g ve je e;
       ex_map #(reads_imm sg g ve je e m) #(reads_imm_dt sg g cve es ve je (DLeaf e) m)
         (fun d1 -> ITLeaf d1)
     | _ -> ())
  | ITBind d1' ->
    (match dt, dt' with
     | DBind o dt0, DBind _ dt0' ->
       bind_entry_rel cve cve' je je' es es' o;
       let v = bind_entry cve je es o in
       sim_imm_dt d1' g cve es (v :: ve) je dt0;
       ex_map #(reads_imm_dt sg g cve es (v :: ve) je dt0 m)
         #(reads_imm_dt sg g cve es ve je (DBind o dt0) m) (fun d1 -> ITBind d1)
     | _ -> ())
  | ITSwitch #_ #_ #_ #_ #_ #_ #_ #s' _ d1' ->
    switch_rel (L.length ve) dt dt' s';
    eliminate exists (s: dtree). L.memP s (switch_subtrees dt) /\ ssim_dt (L.length ve) s s'
    with (sim_imm_dt d1' g cve es ve je s;
          ex_map #(reads_imm_dt sg g cve es ve je s m) #(reads_imm_dt sg g cve es ve je dt m)
            (fun d1 -> ITSwitch #sg #g #cve #es #ve #je #dt #s #m () d1))
  | ITGuard d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard e' _ _ ->
       sim_imm d1' g ve je e;
       ex_map #(reads_imm sg g ve je e m) #(reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m)
         (fun d1 -> ITGuard d1)
     | _ -> ())
  | ITGuardYes d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard _ dt1' _ ->
       sim_imm_dt d1' g cve es ve je dt1;
       ex_map #(reads_imm_dt sg g cve es ve je dt1 m)
         #(reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m) (fun d1 -> ITGuardYes d1)
     | _ -> ())
  | ITGuardNo d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard _ _ dt2' ->
       sim_imm_dt d1' g cve es ve je dt2;
       ex_map #(reads_imm_dt sg g cve es ve je dt2 m)
         #(reads_imm_dt sg g cve es ve je (DGuard e dt1 dt2) m) (fun d1 -> ITGuardNo d1)
     | _ -> ())

and sim_lat_dt (#sg: sig) (#g': group) (#cve': venv) (#es': list exp) (#ve': venv) (#je': jenv)
  (#dt': dtree) (#m: nat)
  (d': reads_lat_dt sg g' cve' es' ve' je' dt' m) (g: group) (cve: venv) (es: list exp) (ve: venv)
  (je: jenv) (dt: dtree)
  : Lemma (requires grel g g' /\ dtrel cve es cve' es' je je' /\ venv_rel ve ve' /\
                    ssim_dt (L.length ve) dt dt')
          (ensures ex (reads_lat_dt sg g cve es ve je dt m)) (decreases d') =
  match d' with
  | LTLeaf d1' ->
    (match dt, dt' with
     | DLeaf e, DLeaf e' ->
       sim_lat d1' g ve je e;
       ex_map #(reads_lat sg g ve je e m) #(reads_lat_dt sg g cve es ve je (DLeaf e) m)
         (fun d1 -> LTLeaf d1)
     | _ -> ())
  | LTBind d1' ->
    (match dt, dt' with
     | DBind o dt0, DBind _ dt0' ->
       bind_entry_rel cve cve' je je' es es' o;
       let v = bind_entry cve je es o in
       sim_lat_dt d1' g cve es (v :: ve) je dt0;
       ex_map #(reads_lat_dt sg g cve es (v :: ve) je dt0 m)
         #(reads_lat_dt sg g cve es ve je (DBind o dt0) m) (fun d1 -> LTBind d1)
     | _ -> ())
  | LTSwitch #_ #_ #_ #_ #_ #_ #_ #s' _ d1' ->
    switch_rel (L.length ve) dt dt' s';
    eliminate exists (s: dtree). L.memP s (switch_subtrees dt) /\ ssim_dt (L.length ve) s s'
    with (sim_lat_dt d1' g cve es ve je s;
          ex_map #(reads_lat_dt sg g cve es ve je s m) #(reads_lat_dt sg g cve es ve je dt m)
            (fun d1 -> LTSwitch #sg #g #cve #es #ve #je #dt #s #m () d1))
  | LTGuardYes d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard _ dt1' _ ->
       sim_lat_dt d1' g cve es ve je dt1;
       ex_map #(reads_lat_dt sg g cve es ve je dt1 m)
         #(reads_lat_dt sg g cve es ve je (DGuard e dt1 dt2) m) (fun d1 -> LTGuardYes d1)
     | _ -> ())
  | LTGuardNo d1' ->
    (match dt, dt' with
     | DGuard e dt1 dt2, DGuard _ _ dt2' ->
       sim_lat_dt d1' g cve es ve je dt2;
       ex_map #(reads_lat_dt sg g cve es ve je dt2 m)
         #(reads_lat_dt sg g cve es ve je (DGuard e dt1 dt2) m) (fun d1 -> LTGuardNo d1)
     | _ -> ())

(* Local groups. *)

let rec member_env_pre (n: nat)
  : Lemma (ensures pre_rel (member_env n) (member_env n) /\ L.length (member_env n) == n)
          (decreases n) =
  if n = 0 then () else member_env_pre (n - 1)

let member_env_rel (n: nat)
  : Lemma (venv_rel (member_env n) (member_env n) /\ L.length (member_env n) == n) =
  member_env_pre n;
  LP.append_l_nil (member_env n);
  venv_append (member_env n) (member_env n) [] []

let rec rhs_nth (n: nat) (bs bs': list (typ & exp)) (k: nat)
  : Lemma (requires ssim_binds n bs bs')
          (ensures (match L.nth (L.map snd bs) k, L.nth (L.map snd bs') k with
                    | Some r, Some r' -> ssim n r r'
                    | None, None -> True
                    | _ -> False))
          (decreases bs) =
  match bs, bs' with
  | [], [] -> ()
  | _ :: bs0, _ :: bs0' -> if k = 0 then () else rhs_nth n bs0 bs0' (k - 1)

let local_grel (bs bs': list (typ & exp))
  : Lemma (requires L.length bs' == L.length bs /\ ssim_binds (L.length bs) bs bs')
          (ensures grel (local_group bs) (local_group bs')) =
  let n = L.length bs in
  let g = local_group bs in
  let g' = local_group bs' in
  member_env_rel n;
  introduce forall (k: nat) (r': exp). rhs g' k == Some r' ==>
    (exists (r: exp). rhs g k == Some r /\ crel3 g.genv [] r g'.genv [] r')
  with introduce _ ==> _
  with rhs_nth n bs bs' k


let rec ssim_binds_length (c: nat) (bs bs': list (typ & exp))
  : Lemma (requires ssim_binds c bs bs') (ensures L.length bs' == L.length bs) (decreases bs) =
  match bs, bs' with
  | [], [] -> ()
  | _ :: bs0, _ :: bs0' -> ssim_binds_length c bs0 bs0'

let init_safe_ssim sg bs bs' =
  let g = local_group bs in
  let g' = local_group bs' in
  ssim_binds_length (L.length bs) bs bs';
  local_grel bs bs';
  introduce forall (i: nat) (r': exp) (m: nat) (d': reads_imm sg g' g'.genv [] r' m).
    rhs g' i == Some r' ==> m < i
  with introduce _ ==> _
  with (eliminate exists (r: exp). rhs g i == Some r /\ crel3 g.genv [] r g'.genv [] r'
           with (sim_imm d' g g.genv [] r;
                 eliminate exists (d: reads_imm sg g g.genv [] r m). True
                 with ()))
