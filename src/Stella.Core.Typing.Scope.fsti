(**
 * Syntactic closedness of well-typed terms (design §1, §4.2, §4.3).
 *
 * A term typed in `Γ` and `Δ` mentions only what `Γ` and `Δ` have in
 * scope (`exp_scoped g |Δ| e`):
 *
 *   - every free type variable is below `|g.tvars|`;
 *   - every free term variable is below `|g.vars|`;
 *   - it is `Stella.Core.Value.jp_scoped |Δ|`, so every free join index is
 *     below `|Δ|` (`Stella.Core.Scope.jp_scoped_jps_below`);
 *   - it is locally closed for regions, `lc_exp`;
 *   - every atom it names is a region of `g`, `frn_exp e ⊆ rdom g`.
 *
 * The ambient row of the derivation is in scope too: locally closed, with
 * its atoms in `rdom g` (`row_scoped`). The list, chain, branch and clause
 * judgements have the same conclusion for their terms, and occurrences
 * typed against an `Ω` in scope are in scope.
 *
 * The hypothesis on `Γ` is that it is well formed, `wf_ctx`. No typing
 * rule kinds the layouts of `Γ_R`, and `readCell` and `writeCell` name
 * their key from a layout; `wf_ctx` makes the keys of every layout in
 * scope structural (`wf_ctx_layouts_struct`), so such a key names no
 * region. The layout a `region` enters has structural keys by its kinding
 * premise.
 *
 * Join-point scoping needs no hypothesis (`typing_jp_scoped`): the bound
 * `|Δ|` comes from the premise of `jump` and the `Δ` each rule gives its
 * premises, whatever `Γ` is. So do its consequences, the bound on the free
 * join indices (`typing_jps_below`) and the invariance of a typed value
 * under join renamings (`typing_value_ren_jp`).
 *
 * A region body is typed opened with every fresh atom; one of them, outside
 * `rdom g` and the atoms of the body, gives the scope of the body itself
 * (`Stella.Core.Scope.rmap_scope`, `lc_open_inv`, `frn_open_incl`).
 *)
module Stella.Core.Typing.Scope
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
open Stella.Core.Kinding.Keys
open Stella.Core.Scope
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Scope predicates *)

(** Every layout of `rs` has structural keys. *)
let rec layouts_struct (rs: list (atom & layout)) : Tot bool (decreases rs) =
  match rs with
  | [] -> true
  | (_, l) :: rs -> keys_struct (L.map fst l) && layouts_struct rs

(** Every key of `ks` is locally closed and names regions of `g`. *)
let rec keys_scoped (g: ctx) (ks: list key) : Tot prop (decreases ks) =
  match ks with
  | [] -> True
  | k :: ks -> lc_key 0 k /\ in_rdom (frn_key k) g /\ keys_scoped g ks

(** An occurrence in scope. Occurrences hold no variable; their keys may
    name regions. *)
let occ_scoped (g: ctx) (o: occ) : prop = lc_occ_at 0 o /\ in_rdom (frn_occ o) g

(** Every occurrence of `Ω` is in scope. *)
let rec octx_scoped (g: ctx) (om: octx) : Tot prop (decreases om) =
  match om with
  | [] -> True
  | (o, _) :: om -> occ_scoped g o /\ octx_scoped g om

(** A row, or any type, in scope for regions. *)
let row_scoped (g: ctx) (r: typ) : prop = lc_ty r /\ in_rdom (frn_ty r) g

let exp_scoped (g: ctx) (nj: nat) (e: exp) : prop =
  tvs_below_exp (L.length g.tvars) e /\ vars_below_exp (L.length g.vars) e /\
  V.jp_scoped nj e /\ lc_exp e /\ in_rdom (frn_exp e) g

let exps_scoped (g: ctx) (nj: nat) (es: list exp) : prop =
  tvs_below_exps (L.length g.tvars) es /\ vars_below_exps (L.length g.vars) es /\
  V.jp_scoped_exps nj es /\ lc_exps_at 0 es /\ in_rdom (frn_exps es) g

let binds_scoped (g: ctx) (bs: list (typ & exp)) : prop =
  tvs_below_binds (L.length g.tvars) bs /\ vars_below_binds (L.length g.vars) bs /\
  V.jp_scoped_binds 0 bs /\ lc_binds_at 0 bs /\ in_rdom (frn_binds bs) g

let cells_scoped (g: ctx) (th: list (key & exp)) : prop =
  tvs_below_cells (L.length g.tvars) th /\ vars_below_cells (L.length g.vars) th /\
  V.jp_scoped_cells 0 th /\ lc_cells_at 0 th /\ in_rdom (frn_cells th) g

let dt_scoped (g: ctx) (nj: nat) (dt: dtree) : prop =
  tvs_below_dt (L.length g.tvars) dt /\ vars_below_dt (L.length g.vars) dt /\
  V.jp_scoped_dt nj dt /\ lc_dt_at 0 dt /\ in_rdom (frn_dt dt) g

(** The branches of a `switchCtor` or a `switchLit`, whose labels hold no
    region. *)
let brs_scoped (#lb: eqtype) (g: ctx) (nj: nat) (bs: list (lb & dtree)) : prop =
  tvs_below_brs (L.length g.tvars) bs /\ vars_below_brs (L.length g.vars) bs /\
  V.jp_scoped_brs nj bs /\ lc_brs_at 0 bs /\ in_rdom (frn_brs bs) g

(** The branches of a `switchKey`, keys included. *)
let kbrs_scoped (g: ctx) (nj: nat) (bs: list (key & dtree)) : prop =
  tvs_below_brs (L.length g.tvars) bs /\ vars_below_brs (L.length g.vars) bs /\
  V.jp_scoped_brs nj bs /\ lc_kbrs_at 0 bs /\ in_rdom (frn_kbrs bs) g

(** Clauses discard `Δ`. *)
let cls_scoped (g: ctx) (cs: list clause) : prop =
  tvs_below_cls (L.length g.tvars) cs /\ vars_below_cls (L.length g.vars) cs /\
  V.jp_scoped_cls 0 cs /\ lc_cls_at 0 cs /\ in_rdom (frn_cls cs) g

(** * Structural keys *)

(** A layout kinded as a `Row Type` row has structural keys. *)
val layout_row_struct (sg: sig) (g: ctx) (l: layout)
  : Lemma (requires check sg g (layout_row l) (KRow EType)) (ensures keys_struct (L.map fst l))

(** The layouts of a well-formed context have structural keys. *)
val wf_ctx_layouts_struct (sg: sig) (g: ctx)
  : Lemma (requires wf_ctx sg g) (ensures layouts_struct g.regions)

val push_vars_regions (g: ctx) (ts: list typ) : Lemma ((push_vars g ts).regions == g.regions)

(** * Occurrences *)

val occ_typing_scoped (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t)
  : Lemma (requires octx_scoped g om) (ensures occ_scoped g o)

(** * Closedness of the judgements *)

val typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r)
  : Lemma (requires wf_ctx sg g)
          (ensures exp_scoped g (L.length d) e /\ row_scoped g r)

val exps_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d r es ts)
  : Lemma (requires wf_ctx sg g)
          (ensures exps_scoped g (L.length d) es /\ row_scoped g r)

val chain_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e)
  : Lemma (requires wf_ctx sg g)
          (ensures exp_scoped g (L.length d) e /\ row_scoped g r)

val binds_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs)
  : Lemma (requires wf_ctx sg g) (ensures binds_scoped g bs)

(** The cells of `region⟨a⟩` against a layout of `Γ_R`. *)
val cells_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#th: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g th lay)
  : Lemma (requires wf_ctx sg g /\ keys_struct (L.map fst lay))
          (ensures cells_scoped g th)

(** The values of a `match` in scope put every occurrence they justify in
    scope. *)
val match_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om)
  : Lemma (requires wf_ctx sg g /\ lc_exps_at 0 th /\ in_rdom (frn_exps th) g)
          (ensures octx_scoped g om /\ row_scoped g r)

val dt_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d om dt t r)
  : Lemma (requires wf_ctx sg g /\ octx_scoped g om)
          (ensures dt_scoped g (L.length d) dt /\ row_scoped g r)

val ctor_brs_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ)
  (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r)
  : Lemma (requires wf_ctx sg g /\ octx_scoped g om /\ occ_scoped g o)
          (ensures brs_scoped g (L.length d) bs /\ row_scoped g r)

val lit_brs_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r)
  : Lemma (requires wf_ctx sg g /\ octx_scoped g om)
          (ensures brs_scoped g (L.length d) bs /\ row_scoped g r)

(** The keys of the branches are those of `kts`, which the split of a kinded
    row puts in scope. *)
val key_brs_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r)
  : Lemma (requires wf_ctx sg g /\ octx_scoped g om /\ occ_scoped g o /\
                    keys_scoped g (L.map fst kts))
          (ensures kbrs_scoped g (L.length d) bs /\ row_scoped g r)

val clauses_typing_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause)
  (h: clauses_typing sg ln g ei ts r b cs)
  : Lemma (requires wf_ctx sg g) (ensures cls_scoped g cs)

(** * Join-point scoping, in every context *)

(** A typed term is `jp_scoped |Δ|`, with no hypothesis on `Γ`. *)
val typing_jp_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r)
  : Lemma (V.jp_scoped (L.length d) e)

val exps_typing_jp_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d r es ts)
  : Lemma (V.jp_scoped_exps (L.length d) es)

val dt_typing_jp_scoped (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d om dt t r)
  : Lemma (V.jp_scoped_dt (L.length d) dt)

(** * Consequences *)

(** The free join indices of a typed term are below `|Δ|`. *)
val typing_jps_below (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ)
  (h: typing sg ln g d e t r)
  : Lemma (jps_below_exp (L.length d) e)

(** A typed value has no free join index, so every join renaming fixes
    it. *)
val typing_value_ren_jp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp)
  (#t #r: typ)
  (h: typing sg ln g d v t r) (xi: ren)
  : Lemma (requires V.is_value sg v)
          (ensures V.jp_scoped 0 v /\ ren_jp xi v == v)
