(**
 * Typing through an evaluation context (spec 06 §Evaluation contexts,
 * §Join points; design §4.3, §7).
 *
 * A derivation of `f[e]`, `f` a frame (`Stella.Core.Semantics.Ctx`), is
 * split into a derivation of its hole `e` and a way to put back any term
 * typed as the hole was (`plug1_typing`). The hole stands under `Δ = []`,
 * except in the continuation of `letjoin j (x̄ : τ̄) : τ = e1 in []`,
 * where it stands under `j` in front of the `Δ` of the `letjoin`, at the
 * type `τ` and the row of the `letjoin` (`hole_jctx`). Its row is the row
 * of `f[e]`, up to type equality, except under `openEffC`, `handle`, an
 * open region and `fill`, whose rules type the hole at a row of their own
 * (`hole_row`).
 *
 * The term put back may be typed in a context that extends the context of
 * `f[e]` in place (`Stella.Core.Typing.Weaken.ctx_weaker`), as the reduct
 * of a hole that opens a region is typed with the region added to `Γ_R`:
 * the other premises of the frame's rule are weakened to that context,
 * and `f[e']` is typed there.
 *
 * ## Chains
 *
 * When `e` is no value, the rule of the frame's form is the only rule
 * that types `f[e]` up to conversion (`T_VariantValue` types values
 * only), and it types the hole by a premise. The four frames of a chain,
 * `e Ev`, `Ev v`, `Ev [τ]` and `Ev [•]`, have a second rule: when `f[e]` is a chain headed by a
 * constructor or a foreign, `T_Chain` types it at its cursor
 * `⟨ σ ; θ ⟩` (`Stella.Core.Spine.chain_cursor`), also when the hole is
 * no value, as in `Just [Int] ((λx : Int. x) 1)`. The hole is then
 *
 *   - in `e Ev`, a value argument, typed at the instance `θ0(τ1)` of the
 *     domain it meets, under `Δ = []` and at the row of the chain;
 *   - in `Ev v`, `Ev [τ]` and `Ev [•]`, the prefix of the chain, typed by
 *     `T_Chain` at the instance of its own cursor.
 *
 * Putting back a prefix rebuilds the chain from the new prefix, which
 * needs the chain's cursor to be what it was. The new term must keep the
 * cursor of `f[e]` (`cursor_kept`), which says nothing where `f[e]` has no
 * cursor, so nothing outside these four frames. A step keeps the cursor of
 * every chain that is no saturated foreign chain (`step_chain_cursor`),
 * and of every `f[e]` whose hole steps (`step_plug1_cursor_kept`).
 *
 * ## Tail contexts
 *
 * Through a tail context `Tl` (`tl_frames`) the hole stands under one join
 * point per frame, innermost first, in front of the `Δ` of `Tl[e]`
 * (`tl_typing`): the join index `|Tl|` of the hole is the first join point
 * of that `Δ`, the one a `jump` reaches through `Tl` in the join rule
 * (spec 06 §Join points).
 *
 * ## Inversions
 *
 * The reference to a top-level value (`inv_global`), a `jump`
 * (`inv_jump`) and a saturated foreign chain (`foreign_redex_typing`)
 * are inverted for the head rules that reduce them.
 *
 * The lemmas that rebuild a derivation (`plug1_typing`, `tl_typing`,
 * `foreign_redex_typing`) convert it to the type and the row asked for,
 * which takes the regularity of `Stella.Core.Typing.Regularity`, and so a
 * well-formed `Σ` and `Γ`. The inversions of a global and of a `jump`
 * need neither.
 *)
module Stella.Core.Typing.Plug
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Weaken
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Keeping the cursor *)

(** `b` keeps the cursor of `a`: if `a` is a chain with a cursor, `b` is a
    chain with the same cursor. *)
let cursor_kept (sg: sig) (a b: exp) : prop =
  Some? (chain_cursor sg a) ==>
  (Some? (decompose_global_app b) /\ chain_cursor sg b == chain_cursor sg a)

(** The cursor does not read the value arguments: replacing the last one
    keeps whether the term is a chain, and its cursor. *)
val chain_cursor_replace_val (sg: sig) (fn x y: exp)
  : Lemma (Some? (decompose_global_app (EApp fn x)) == Some? (decompose_global_app (EApp fn y)) /\
           chain_cursor sg (EApp fn x) == chain_cursor sg (EApp fn y))

(** A step keeps the cursor of a chain that is no saturated foreign chain:
    the only head rule that rewrites a chain with a cursor is the foreign
    rule, since a constructor or a foreign has no definition to unfold, and
    a step inside the chain rewrites a value argument, which the cursor
    does not read, or a prefix, whose cursor it keeps. *)
val step_chain_cursor (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#e': exp) (s: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (requires Some? (chain_cursor sg e) /\ not (V.foreign_redex sg e))
          (ensures Some? (decompose_global_app e') /\ chain_cursor sg e' == chain_cursor sg e)

(** A frame around a non-value is no saturated foreign chain of values. In
    `e Ev` the hole is a value argument, which such a chain has only values
    for. In `Ev v`, `Ev [τ]` and `Ev [•]` the hole is a prefix with one more
    argument position, which in such a chain is an unsaturated foreign
    chain of values, a value. *)
val plug1_not_foreign_redex (sg: sig) (f: frame) (e: exp)
  : Lemma (requires not (V.is_value sg e)) (ensures not (V.foreign_redex sg (plug1 f e)))

(** A step of the hole keeps the cursor of the term the frame `f` builds
    around it, which is how `plug1_typing` puts a reduct back. *)
val step_plug1_cursor_kept (#sg: sig) (#gi: genv) (#ra: list atom) (#st: store) (#e: exp)
  (#ra': list atom) (#st': store) (#e': exp) (f: frame) (s: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (cursor_kept sg (plug1 f e) (plug1 f e'))

(** * One frame *)

(** The `Δ` of the hole of `f`, given the `Δ` and the type `t` of `f[e]`
    and the type `ht` and the row `hr` of the hole: the continuation of
    `letjoin` adds its join point, at the type `τ' ≡ t` the `letjoin`
    writes, which is the type of the hole, and at the row of the hole.
    Every other hole stands under `Δ = []`. *)
let hole_jctx (f: frame) (d: jctx) (t: typ) (hd: jctx) (ht hr: typ) : prop =
  match f with
  | FLetJoin ts t' _ -> hd == (ts, t', hr) :: d /\ ht == t' /\ ty_eq t' t
  | _ -> hd == []

(** The row `hr` of the hole of `f`, given the row `r` of `f[e]`. It is `r`,
    up to type equality, but under four frames: `openEffC [ρ'] e` at
    `( ρ0 | ρ' ) ≡ r` has its operand at `ρ0`, `handle e with h` its handled
    computation at `r` with the element `h` removes, an open region `a` its
    body at `r` with `region a`, and `fill ν e` its initializer at `()`. *)
let hole_row (f: frame) (r hr: typ) : prop =
  match f with
  | FOpenEffC r' -> ty_eq (TRowUnion hr r') r
  | FHandle h -> ty_eq hr (TRowExt h.h_ent r)
  | FRegionOpen a _ -> ty_eq hr (TRowExt (EntRegion (RFree a)) r)
  | FFill _ -> hr == TRowEmpty
  | _ -> ty_eq hr r

(** Putting a term typed as the hole back into `f`, at the judgement of
    `f[e]`, when it keeps the cursor of `f[e]`. The term may be typed in
    any context `g'` that extends `g` in place (`ctx_weaker`), such as
    `Γ_R` with a region added: the frame's other premises are weakened to
    `g'`, and the frame is rebuilt there. *)
let plug1_fill (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (f: frame) (e: exp) (t r: typ)
  (hd: jctx) (ht hr: typ) : Type =
  g': ctx -> e': exp -> typing sg ln g' hd e' ht hr ->
  Pure (typing sg ln g' d (plug1 f e') t r)
       (requires ctx_weaker g g' /\ cursor_kept sg (plug1 f e) (plug1 f e'))
       (ensures fun _ -> True)

(** A derivation of `f[e]` at `Γ; Δ ⊢ f[e] : τ ! ρ`, split at the hole:
    the hole's derivation, under `hd`, at `ht` and `hr`, and the way to put
    a term back. *)
noeq type plug1_inv (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (f: frame) (e: exp) (t r: typ) = {
  hd: jctx;
  ht: typ;
  hr: typ;
  hole: typing sg ln g hd e ht hr;
  hole_ctx: squash (hole_jctx f d t hd ht hr /\ hole_row f r hr);
  fill: plug1_fill sg ln g d f e t r hd ht hr;
}

(** Every derivation of `f[e]`, for any frame `f`, splits at the hole when
    `e` or `f[e]` is no value (`Stella.Core.Semantics.Ctx.plug1_not_value`
    gives the second from the first). *)
val plug1_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#f: frame) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d (plug1 f e) t r)
  : Pure (plug1_inv sg ln g d f e t r)
         (requires sig_ok sg /\ wf_ctx sg g /\
                   (not (V.is_value sg e) \/ not (V.is_value sg (plug1 f e))))
         (ensures fun _ -> True)

(** * Tail contexts *)

(** `pre` holds one join point per frame of the tail context `fs`, in the
    same order, with the parameter types and the result type the frame's
    `letjoin` writes. *)
let rec tl_jctx (fs: list frame) (pre: jctx) : Tot prop (decreases fs) =
  match fs, pre with
  | [], [] -> True
  | FLetJoin ts t' _ :: fs, (ts', t'', _) :: pre -> ts' == ts /\ t'' == t' /\ tl_jctx fs pre
  | _ -> False

val tl_jctx_length (fs: list frame) (pre: jctx)
  : Lemma (requires tl_jctx fs pre) (ensures L.length pre == L.length fs)

(** A derivation of `Tl[e]` split at the hole, which stands under the join
    points `pre` of `Tl` in front of `Δ`, at the type and the row of
    `Tl[e]` up to type equality. *)
noeq type tl_inv (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (fs: list frame) (e: exp) (t r: typ) = {
  pre: jctx;
  tl_t: typ;
  tl_r: typ;
  tl_hole: typing sg ln g (L.append pre d) e tl_t tl_r;
  tl_pre: squash (tl_jctx fs pre /\ L.length pre == L.length fs /\ ty_eq tl_t t /\ ty_eq tl_r r);
  tl_fill: e': exp -> typing sg ln g (L.append pre d) e' tl_t tl_r -> typing sg ln g d (plug fs e') t r;
}

(** Every derivation of `Tl[e]` splits at the hole. No `letjoin` is a
    chain, so every term typed as the hole is put back. *)
val tl_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#fs: list frame) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d (plug fs e) t r)
  : Pure (tl_inv sg ln g d fs e t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ tl_frames fs)
         (ensures fun _ -> True)

(** The join point at index `n` of `pre @ Δ`: in `pre` below `|pre|`, in
    `Δ` from there. *)
val nth_append (pre d: jctx) (n: nat)
  : Lemma (L.nth (L.append pre d) n ==
           (if n < L.length pre then L.nth pre n else L.nth d (n - L.length pre)))

(** * Inversions *)

(** A reference `M.x [[κ̄]]` to a top-level value has the declared type
    `σ[k̄ := κ̄]` of `M.x`, up to type equality, with as many well-formed
    quantifiable kinds as `M.x` has kind variables: `T_Global` is the only
    rule, since `M.x` heads no chain. *)
val inv_global (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#q: qname) (#ks: list kind)
  (#t #r: typ) (h: typing sg ln g d (EGlobal q ks) t r) (vi: value_info)
  : Lemma (requires value_scheme sg q == Some vi)
          (ensures ty_eq t (kinst_ty ks vi.vl_ty) /\ L.length ks == vi.vl_nk /\ qkinds_wf g.nk ks)

(** The premises of `T_Jump` for `jump n (ē)` at `τ ! ρ`: the join point
    `(τ̄, τ', ρ')` at index `n` of `Δ`, with `τ' ≡ τ` and `ρ' ≡ ρ`, and the
    arguments at `τ̄`, under `Δ = []`, at `ρ'`. *)
noeq type jump_inv (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (n: nat) (es: list exp) (t r: typ) = {
  j_ts: list typ;
  j_t: typ;
  j_r: typ;
  j_args: exps_typing sg ln g [] j_r es j_ts;
  j_facts: squash (L.nth d n == Some (j_ts, j_t, j_r) /\ ty_eq j_t t /\ ty_eq j_r r);
}

val inv_jump (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#n: nat) (#es: list exp) (#t #r: typ)
  (h: typing sg ln g d (EJump n es) t r)
  : Pure (jump_inv sg ln g d n es t r) (requires True) (ensures fun _ -> True)

(** A saturated chain of values of a foreign, typed anywhere, is typed at
    the instance `θ(σ)` of its cursor under `Δ = []` at the row `()`, the
    judgement condition (3) of conformance reads
    (`Stella.Core.Semantics.Env.foreign_call_ok`), and its type is that
    instance up to type equality. The chain is normalized
    (`Stella.Core.Typing.Chain.chain_normal`) and its value arguments are
    retyped at `()` (`Stella.Core.Typing.Values.value_chain_typing`). *)
val foreign_redex_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (s: typ) (th: tsub)
  : Pure (typing sg ln g [] e (sub_ty th s) TRowEmpty)
         (requires sig_ok sg /\ wf_ctx sg g /\ V.foreign_redex sg e /\
                   chain_cursor sg e == Some (s, th))
         (ensures fun _ -> ty_eq t (sub_ty th s))

(** The same, as `typed`. *)
val foreign_redex_typed (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (s: typ) (th: tsub)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g /\ V.foreign_redex sg e /\
                    chain_cursor sg e == Some (s, th))
          (ensures typed sg ln g e (sub_ty th s) /\ ty_eq t (sub_ty th s))
