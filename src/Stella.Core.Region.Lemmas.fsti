(**
 * Region names against the σ-calculus operations, and the locally nameless
 * facts about `open` and `close` (design §1.3, §3.1).
 *
 *   - Renamings of every sort leave region references alone: `lc_*`
 *     is invariant under `ren_ty`, `ren_tm`, `ren_jp`, and `rmap_*` commutes
 *     with them.
 *   - Substitutions preserve local closure when the substitutes are locally
 *     closed (`lc_sub_ty`, `lc_sub_ty_exp`, `lc_sub_tm`), and commute with a
 *     region map that fixes the substitutes (`rmap_sub_ty_exp`,
 *     `rmap_sub_tm`); for `open_region` the substitutes need only be `lc`.
 *   - `open_region` turns a body that is locally closed under its binder
 *     into a locally closed term (`lc_open_exp`), and `open` and `close` are
 *     inverse: `close ∘ open` for a fresh atom, `open ∘ close` on a locally
 *     closed term.
 *
 * A family over types is exported at every class (`typ`, `entry`, `constr`,
 * `list typ`, layouts); a family over terms at `exp` and `dtree`.
 *)
module Stella.Core.Region.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
module L = FStar.List.Tot

(** * Types *)

val lc_mono_ty (n: nat) (m: nat) (t: typ)
  : Lemma (requires n <= m /\ lc_ty_at n t)
          (ensures lc_ty_at m t)

val lc_mono_ent (n: nat) (m: nat) (en: entry)
  : Lemma (requires n <= m /\ lc_ent_at n en)
          (ensures lc_ent_at m en)

val lc_mono_constr (n: nat) (m: nat) (cn: constr)
  : Lemma (requires n <= m /\ lc_constr_at n cn)
          (ensures lc_constr_at m cn)

val lc_mono_tys (n: nat) (m: nat) (ts: list typ)
  : Lemma (requires n <= m /\ lc_tys_at n ts)
          (ensures lc_tys_at m ts)

val lc_mono_layout (n: nat) (m: nat) (l: list (key & typ))
  : Lemma (requires n <= m /\ lc_layout_at n l)
          (ensures lc_layout_at m l)

val lc_ren_ty (n: nat) (xi: ren) (t: typ)
  : Lemma (ensures lc_ty_at n (ren_ty xi t) == lc_ty_at n t)

val lc_ren_ent (n: nat) (xi: ren) (en: entry)
  : Lemma (ensures lc_ent_at n (ren_ent xi en) == lc_ent_at n en)

val lc_ren_constr (n: nat) (xi: ren) (cn: constr)
  : Lemma (ensures lc_constr_at n (ren_constr xi cn) == lc_constr_at n cn)

val lc_ren_tys (n: nat) (xi: ren) (ts: list typ)
  : Lemma (ensures lc_tys_at n (ren_tys xi ts) == lc_tys_at n ts)

val lc_ren_layout (n: nat) (xi: ren) (l: list (key & typ))
  : Lemma (ensures lc_layout_at n (ren_layout xi l) == lc_layout_at n l)

val lc_sub_ty (n: nat) (sigma: tsub) (t: typ)
  : Lemma (requires lc_ty_at n t /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_ty_at n (sub_ty sigma t))

val lc_sub_ent (n: nat) (sigma: tsub) (en: entry)
  : Lemma (requires lc_ent_at n en /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_ent_at n (sub_ent sigma en))

val lc_sub_constr (n: nat) (sigma: tsub) (cn: constr)
  : Lemma (requires lc_constr_at n cn /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_constr_at n (sub_constr sigma cn))

val lc_sub_tys (n: nat) (sigma: tsub) (ts: list typ)
  : Lemma (requires lc_tys_at n ts /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_tys_at n (sub_tys sigma ts))

val lc_sub_layout (n: nat) (sigma: tsub) (l: list (key & typ))
  : Lemma (requires lc_layout_at n l /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_layout_at n (sub_layout sigma l))

val rmap_ren_ty (g: region_ref -> region_ref) (xi: ren) (t: typ)
  : Lemma (ensures rmap_ty g (ren_ty xi t) == ren_ty xi (rmap_ty g t))

val rmap_ren_ent (g: region_ref -> region_ref) (xi: ren) (en: entry)
  : Lemma (ensures rmap_ent g (ren_ent xi en) == ren_ent xi (rmap_ent g en))

val rmap_ren_constr (g: region_ref -> region_ref) (xi: ren) (cn: constr)
  : Lemma (ensures rmap_constr g (ren_constr xi cn) == ren_constr xi (rmap_constr g cn))

val rmap_ren_tys (g: region_ref -> region_ref) (xi: ren) (ts: list typ)
  : Lemma (ensures rmap_tys g (ren_tys xi ts) == ren_tys xi (rmap_tys g ts))

val rmap_ren_layout (g: region_ref -> region_ref) (xi: ren) (l: list (key & typ))
  : Lemma (ensures rmap_layout g (ren_layout xi l) == ren_layout xi (rmap_layout g l))

val rmap_sub_ty (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_ty g (sub_ty sigma t) == sub_ty theta (rmap_ty g t))

val rmap_sub_ent (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_ent g (sub_ent sigma en) == sub_ent theta (rmap_ent g en))

val rmap_sub_constr (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_constr g (sub_constr sigma cn) == sub_constr theta (rmap_constr g cn))

val rmap_sub_tys (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_tys g (sub_tys sigma ts) == sub_tys theta (rmap_tys g ts))

val rmap_sub_layout (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_layout g (sub_layout sigma l) == sub_layout theta (rmap_layout g l))

val open_close_ty (a: atom) (d: nat) (t: typ)
  : Lemma (requires lc_ty_at d t)
          (ensures rmap_ty (open_rr a d) (rmap_ty (close_rr a d) t) == t)

val open_close_ent (a: atom) (d: nat) (en: entry)
  : Lemma (requires lc_ent_at d en)
          (ensures rmap_ent (open_rr a d) (rmap_ent (close_rr a d) en) == en)

val open_close_constr (a: atom) (d: nat) (cn: constr)
  : Lemma (requires lc_constr_at d cn)
          (ensures rmap_constr (open_rr a d) (rmap_constr (close_rr a d) cn) == cn)

val open_close_tys (a: atom) (d: nat) (ts: list typ)
  : Lemma (requires lc_tys_at d ts)
          (ensures rmap_tys (open_rr a d) (rmap_tys (close_rr a d) ts) == ts)

val open_close_layout (a: atom) (d: nat) (l: list (key & typ))
  : Lemma (requires lc_layout_at d l)
          (ensures rmap_layout (open_rr a d) (rmap_layout (close_rr a d) l) == l)

val close_open_ty (a: atom) (d: nat) (t: typ)
  : Lemma (requires not (L.mem a (frn_ty t)))
          (ensures rmap_ty (close_rr a d) (rmap_ty (open_rr a d) t) == t)

val close_open_ent (a: atom) (d: nat) (en: entry)
  : Lemma (requires not (L.mem a (frn_ent en)))
          (ensures rmap_ent (close_rr a d) (rmap_ent (open_rr a d) en) == en)

val close_open_constr (a: atom) (d: nat) (cn: constr)
  : Lemma (requires not (L.mem a (frn_constr cn)))
          (ensures rmap_constr (close_rr a d) (rmap_constr (open_rr a d) cn) == cn)

val close_open_tys (a: atom) (d: nat) (ts: list typ)
  : Lemma (requires not (L.mem a (frn_tys ts)))
          (ensures rmap_tys (close_rr a d) (rmap_tys (open_rr a d) ts) == ts)

val close_open_layout (a: atom) (d: nat) (l: list (key & typ))
  : Lemma (requires not (L.mem a (frn_layout l)))
          (ensures rmap_layout (close_rr a d) (rmap_layout (open_rr a d) l) == l)

val lc_open_ty (a: atom) (d: nat) (t: typ)
  : Lemma (requires lc_ty_at (d + 1) t)
          (ensures lc_ty_at d (rmap_ty (open_rr a d) t))

val lc_open_ent (a: atom) (d: nat) (en: entry)
  : Lemma (requires lc_ent_at (d + 1) en)
          (ensures lc_ent_at d (rmap_ent (open_rr a d) en))

val lc_open_constr (a: atom) (d: nat) (cn: constr)
  : Lemma (requires lc_constr_at (d + 1) cn)
          (ensures lc_constr_at d (rmap_constr (open_rr a d) cn))

val lc_open_tys (a: atom) (d: nat) (ts: list typ)
  : Lemma (requires lc_tys_at (d + 1) ts)
          (ensures lc_tys_at d (rmap_tys (open_rr a d) ts))

val lc_open_layout (a: atom) (d: nat) (l: list (key & typ))
  : Lemma (requires lc_layout_at (d + 1) l)
          (ensures lc_layout_at d (rmap_layout (open_rr a d) l))

val open_lc_ty (a: atom) (d: nat) (t: typ)
  : Lemma (requires lc_ty_at d t)
          (ensures rmap_ty (open_rr a d) t == t)

val open_lc_ent (a: atom) (d: nat) (en: entry)
  : Lemma (requires lc_ent_at d en)
          (ensures rmap_ent (open_rr a d) en == en)

val open_lc_constr (a: atom) (d: nat) (cn: constr)
  : Lemma (requires lc_constr_at d cn)
          (ensures rmap_constr (open_rr a d) cn == cn)

val open_lc_tys (a: atom) (d: nat) (ts: list typ)
  : Lemma (requires lc_tys_at d ts)
          (ensures rmap_tys (open_rr a d) ts == ts)

val open_lc_layout (a: atom) (d: nat) (l: list (key & typ))
  : Lemma (requires lc_layout_at d l)
          (ensures rmap_layout (open_rr a d) l == l)

(** * Occurrences *)

val lc_mono_occ (n m: nat) (o: occ)
  : Lemma (requires n <= m /\ lc_occ_at n o) (ensures lc_occ_at m o)

val lc_open_occ (a: atom) (d: nat) (o: occ)
  : Lemma (requires lc_occ_at (d + 1) o) (ensures lc_occ_at d (rmap_occ (open_rr a d) o))

val open_lc_occ (a: atom) (d: nat) (o: occ)
  : Lemma (requires lc_occ_at d o) (ensures rmap_occ (open_rr a d) o == o)

val open_close_occ (a: atom) (d: nat) (o: occ)
  : Lemma (requires lc_occ_at d o)
          (ensures rmap_occ (open_rr a d) (rmap_occ (close_rr a d) o) == o)

val close_open_occ (a: atom) (d: nat) (o: occ)
  : Lemma (requires not (L.mem a (frn_occ o)))
          (ensures rmap_occ (close_rr a d) (rmap_occ (open_rr a d) o) == o)

(** * Terms: local closure is monotone *)

val lc_mono_exp (n: nat) (m: nat) (e: exp)
  : Lemma (requires n <= m /\ lc_exp_at n e)
          (ensures lc_exp_at m e)

val lc_mono_dt (n: nat) (m: nat) (dt: dtree)
  : Lemma (requires n <= m /\ lc_dt_at n dt)
          (ensures lc_dt_at m dt)

(** * Terms: open and close *)

val lc_open_exp (a: atom) (d: nat) (e: exp)
  : Lemma (requires lc_exp_at (d + 1) e)
          (ensures lc_exp_at d (rmap_exp (open_rr a) d e))

val lc_open_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires lc_dt_at (d + 1) dt)
          (ensures lc_dt_at d (rmap_dt (open_rr a) d dt))

val open_lc_exp (a: atom) (d: nat) (e: exp)
  : Lemma (requires lc_exp_at d e)
          (ensures rmap_exp (open_rr a) d e == e)

val open_lc_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires lc_dt_at d dt)
          (ensures rmap_dt (open_rr a) d dt == dt)

val open_close_exp (a: atom) (d: nat) (e: exp)
  : Lemma (requires lc_exp_at d e)
          (ensures rmap_exp (open_rr a) d (rmap_exp (close_rr a) d e) == e)

val open_close_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires lc_dt_at d dt)
          (ensures rmap_dt (open_rr a) d (rmap_dt (close_rr a) d dt) == dt)

val close_open_exp (a: atom) (d: nat) (e: exp)
  : Lemma (requires not (L.mem a (frn_exp e)))
          (ensures rmap_exp (close_rr a) d (rmap_exp (open_rr a) d e) == e)

val close_open_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires not (L.mem a (frn_dt dt)))
          (ensures rmap_dt (close_rr a) d (rmap_dt (open_rr a) d dt) == dt)

(** `open_region` makes a locally closed body locally closed, and the
    corresponding facts for the whole of a region body. *)
val lc_open_region (a: atom) (e: exp)
  : Lemma (requires lc_exp_at 1 e) (ensures lc_exp (open_region a e))

val close_open_region (a: atom) (e: exp)
  : Lemma (requires not (L.mem a (frn_exp e))) (ensures close_region a (open_region a e) == e)

val open_close_region (a: atom) (e: exp)
  : Lemma (requires lc_exp e) (ensures open_region a (close_region a e) == e)

(** * Terms: renamings do not touch regions *)

val rmap_ren_tm (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (e: exp)
  : Lemma (ensures rmap_exp f d (ren_tm xi e) == ren_tm xi (rmap_exp f d e))

val rmap_ren_tm_dt (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures rmap_dt f d (ren_tm_dt xi dt) == ren_tm_dt xi (rmap_dt f d dt))

val rmap_ren_jp (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (e: exp)
  : Lemma (ensures rmap_exp f d (ren_jp xi e) == ren_jp xi (rmap_exp f d e))

val rmap_ren_jp_dt (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures rmap_dt f d (ren_jp_dt xi dt) == ren_jp_dt xi (rmap_dt f d dt))

val lc_ren_tm (n: nat) (xi: ren) (e: exp)
  : Lemma (ensures lc_exp_at n (ren_tm xi e) == lc_exp_at n e)

val lc_ren_tm_dt (n: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures lc_dt_at n (ren_tm_dt xi dt) == lc_dt_at n dt)

val lc_ren_jp (n: nat) (xi: ren) (e: exp)
  : Lemma (ensures lc_exp_at n (ren_jp xi e) == lc_exp_at n e)

val lc_ren_jp_dt (n: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures lc_dt_at n (ren_jp_dt xi dt) == lc_dt_at n dt)

(** * Terms: type substitution *)

val rmap_sub_ty_exp (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub) (e: exp)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_exp f d (sub_ty_exp sigma e) == sub_ty_exp sigma (rmap_exp f d e))

val rmap_sub_ty_dt (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub) (dt: dtree)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_dt f d (sub_ty_dt sigma dt) == sub_ty_dt sigma (rmap_dt f d dt))

val rmap_ren_ty_exp (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (e: exp)
  : Lemma (rmap_exp f d (ren_ty_exp xi e) == ren_ty_exp xi (rmap_exp f d e))

val lc_sub_ty_exp (n: nat) (sigma: tsub) (e: exp)
  : Lemma (requires lc_exp_at n e /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_exp_at n (sub_ty_exp sigma e))

val lc_sub_ty_dt (n: nat) (sigma: tsub) (dt: dtree)
  : Lemma (requires lc_dt_at n dt /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_dt_at n (sub_ty_dt sigma dt))

val lc_ren_ty_exp (n: nat) (xi: ren) (e: exp)
  : Lemma (requires lc_exp_at n e) (ensures lc_exp_at n (ren_ty_exp xi e))

(** * Terms: term substitution *)

val rmap_sub_tm (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub) (e: exp)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_exp f d (sub_tm sigma e) == sub_tm sigma (rmap_exp f d e))

val rmap_sub_tm_dt (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub) (dt: dtree)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_dt f d (sub_tm_dt sigma dt) == sub_tm_dt sigma (rmap_dt f d dt))

val lc_sub_tm (n: nat) (sigma: esub) (e: exp)
  : Lemma (requires lc_exp_at n e /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_exp_at n (sub_tm sigma e))

val lc_sub_tm_dt (n: nat) (sigma: esub) (dt: dtree)
  : Lemma (requires lc_dt_at n dt /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_dt_at n (sub_tm_dt sigma dt))

(** * Opening commutes with the substitutions of locally closed terms *)

val open_region_sub_ty (d: nat) (a: atom) (sigma: tsub) (t: typ)
  : Lemma (requires forall (i: nat). lc_ty (sigma i))
          (ensures open_region_ty d a (sub_ty sigma t) == sub_ty sigma (open_region_ty d a t))

val open_region_sub_ty_exp (d: nat) (a: atom) (sigma: tsub) (e: exp)
  : Lemma (requires forall (i: nat). lc_ty (sigma i))
          (ensures open_region_at d a (sub_ty_exp sigma e)
                   == sub_ty_exp sigma (open_region_at d a e))

val open_region_sub_tm (d: nat) (a: atom) (sigma: esub) (e: exp)
  : Lemma (requires forall (i: nat). lc_exp (sigma i))
          (ensures open_region_at d a (sub_tm sigma e) == sub_tm sigma (open_region_at d a e))

val open_region_ren_ty_exp (d: nat) (a: atom) (xi: ren) (e: exp)
  : Lemma (open_region_at d a (ren_ty_exp xi e) == ren_ty_exp xi (open_region_at d a e))

val open_region_ren_tm (d: nat) (a: atom) (xi: ren) (e: exp)
  : Lemma (open_region_at d a (ren_tm xi e) == ren_tm xi (open_region_at d a e))

val open_region_ren_jp (d: nat) (a: atom) (xi: ren) (e: exp)
  : Lemma (open_region_at d a (ren_jp xi e) == ren_jp xi (open_region_at d a e))
