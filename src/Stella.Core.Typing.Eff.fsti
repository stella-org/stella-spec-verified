(**
 * Typing the redexes of the rules of operations and handlers (spec 05
 * §Effects; spec 06 §Operations and handlers, §Where a handler finishes,
 * §Evaluation contexts).
 *
 * ## Plugging a context
 *
 * A derivation of `Ev[e]`, `Ev` a list of frames and `e` no value, splits
 * at the hole (`plug_typing`): the hole's derivation, under a `Δ`, at a
 * type and a row of its own, and a way to put back any term typed as the
 * hole was, frame by frame (`Stella.Core.Typing.Plug.plug1_typing`). A
 * frame of a chain puts back only a term that keeps the chain's cursor.
 * The cursor reads the spine of the chain but not its value arguments, so
 * `plug_typing` puts back any term with the same spine as the hole
 * (`spine_like`), such as a variable in place of a `perform`, since
 * neither is a chain.
 *
 * The hole's row is related to the row of `Ev[e]` frame by frame
 * (`Stella.Core.Typing.hole_row`). Through an `Ev_k` (`ev_k k fs`)
 * every effect entry of key `k` of the hole's row is one of the outer row
 * (`eff_entries_in`): `openEffC` types its operand at a part of the outer
 * row, a `handle` of another key adds an entry of another key, an open
 * region adds a region entry, `fill` types its operand at `()`, which has
 * no entry, and every other frame keeps the row.
 *
 * ## The handled `perform`
 *
 * `handle e with h` is typed by `T_Handle` alone up to conversion
 * (`inv_handle`), and `perform k.op [σ̄] v` by `T_Perform` alone
 * (`inv_perform`). When `e = Ev_k[perform k.op [σ̄] v]` and `k` is the key
 * of `h`'s element `E τ̄`, the entry `k : E' τ̄'` that the `perform` reads
 * in its row is an entry of the row `( E τ̄ | ρ )` of the handled
 * computation, which has the entry `k : E τ̄` too. A kinded row in a
 * consistent context is sharp (`Stella.Core.Kinding.Sharp.check_sharp`),
 * so `E' = E` and `τ̄' ≡ τ̄` (`handled_entry`): the `perform` is one of
 * `E`'s operations, at the arguments the handler's clauses are typed at.
 *
 * ## Resuming
 *
 * The continuation and the `let` of a `fast` clause rebuild
 * `handle Ev_k[y] with h` under the binder of `y`
 * (`Stella.Core.Semantics.Step.resume`). Its derivation is the redex's
 * weakened past that binder, split at the hole, with `y : τ'` put in the
 * hole, `τ'` being the type the `perform` has (`resume_typing`).
 *
 * ## Clauses
 *
 * The clause a rule selects (`Stella.Core.Semantics.Step.clause_of`) has
 * the premises `TCL_Full` or `TCL_Fast` gives it in the handler's
 * derivation (`full_clause_typing`, `fast_clause_typing`).
 *)
module Stella.Core.Typing.Eff
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Prim
open Stella.Core.Typing
open Stella.Core.Typing.Plug
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Terms with the same spine *)

(** A spine argument with the term of a value argument forgotten. *)
let arg_shape (a: spine_arg) : spine_arg =
  match a with
  | SVal _ -> SVal ERecEmpty
  | _ -> a

(** `b` has the spine of `a`: neither is a chain, or both are chains of
    the same head whose arguments agree but for the value arguments. *)
let spine_like (a b: exp) : prop =
  match decompose_global_app a, decompose_global_app b with
  | None, None -> True
  | Some (q, ks, args), Some (q', ks', args') ->
    q == q' /\ ks == ks' /\ L.map arg_shape args == L.map arg_shape args'
  | _ -> False

(** Two terms that are no chains have the same spine. *)
val spine_like_atoms (a b: exp)
  : Lemma (requires None? (decompose_global_app a) /\ None? (decompose_global_app b))
          (ensures spine_like a b)

(** A frame keeps the relation. *)
val spine_like_plug1 (f: frame) (a b: exp)
  : Lemma (requires spine_like a b) (ensures spine_like (plug1 f a) (plug1 f b))

(** Terms of the same spine have the same cursor. *)
val spine_like_cursor (sg: sig) (a b: exp)
  : Lemma (requires spine_like a b) (ensures cursor_kept sg a b)

(** * Plugging a context *)

(** Every effect entry of key `k` of the row `hr` is one of `r`. *)
let eff_entries_in (k: key) (hr r: typ) : prop =
  forall (q: qname) (cs: list ctyp). {:pattern L.mem (k, PEff q cs) (row_entries (canon hr))}
    L.mem (k, PEff q cs) (row_entries (canon hr)) ==> L.mem (k, PEff q cs) (row_entries (canon r))

(** A frame that is no `handle` of key `k` keeps the effect entries of key
    `k` of its hole's row in its own. *)
val hole_row_eff (f: frame) (k: key) (r hr: typ)
  : Lemma (requires hole_row f r hr /\ not_handle_of k f) (ensures eff_entries_in k hr r)

(** Putting a term with the hole's spine, typed as the hole, back into
    `fs`. *)
let plug_fill (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (fs: list frame) (e: exp) (t r: typ)
  (hd: jctx) (ht hr: typ) : Type =
  e': exp -> typing sg ln g hd e' ht hr ->
  Pure (typing sg ln g d (plug fs e') t r) (requires spine_like e e') (ensures fun _ -> True)

(** A derivation of `Ev[e]` split at the hole: the hole's derivation under
    `p_d`, at `p_t` and `p_r`, the effect entries of every key `k` the
    context is an `Ev_k` for, and the way to put a term back. *)
noeq type plug_inv (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (fs: list frame) (e: exp) (t r: typ) = {
  p_d: jctx;
  p_t: typ;
  p_r: typ;
  p_hole: typing sg ln g p_d e p_t p_r;
  p_rows: squash (forall (k: key). {:pattern ev_k k fs} ev_k k fs ==> eff_entries_in k p_r r);
  p_fill: plug_fill sg ln g d fs e t r p_d p_t p_r;
}

(** Every derivation of `Ev[e]`, `e` no value, splits at the hole. *)
val plug_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#fs: list frame) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d (plug fs e) t r)
  : Pure (plug_inv sg ln g d fs e t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ not (V.is_value sg e))
         (ensures fun _ -> True)

(** * `handle` and `perform` *)

(** The premises of `T_Handle` for `handle e with h` at `τ ! ρ`: the
    answer type `hi_b ≡ τ` and the outer row `hi_r ≡ ρ`. *)
noeq type handle_inv (sg: sig) (ln: lctx) (g: ctx) (e: exp) (h: handler) (t r: typ) = {
  hi_b: typ;
  hi_r: typ;
  hi_lbl: option string;
  hi_q: qname;
  hi_ts: list typ;
  hi_ei: effect_info;
  hi_body: typing sg ln g [] e h.h_ret_ty (TRowExt h.h_ent hi_r);
  hi_ret: typing sg ln (push_var g h.h_ret_ty) [] h.h_ret hi_b hi_r;
  hi_cls: clauses_typing sg ln g hi_ei hi_ts hi_r hi_b h.h_clauses;
  hi_facts: squash (h.h_ent == EntEff hi_lbl hi_q hi_ts /\ sg.effects hi_q == Some hi_ei /\
                    check sg g (TRowExt h.h_ent hi_r) (KRow EEffect) /\
                    check sg g h.h_ret_ty KType /\
                    check sg g hi_b KType /\ check sg g hi_r (KRow EEffect) /\
                    clauses_cover hi_ei h.h_clauses /\ ty_eq hi_b t /\ ty_eq hi_r r);
}

(** `T_Handle` is the only rule that types `handle e with h`, up to
    conversion. *)
val inv_handle (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#h: handler) (#t #r: typ)
  (hh: typing sg ln g d (EHandle e h) t r)
  : Pure (handle_inv sg ln g e h t r) (requires True) (ensures fun _ -> True)

(** `T_Handle` from its premises, with the handled computation replaced
    by any term typed as it was, under any `Δ`. *)
val handle_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#e: exp) (#h: handler) (#t #r: typ)
  (hi: handle_inv sg ln g e h t r) (d: jctx) (e': exp)
  (he: typing sg ln g [] e' h.h_ret_ty (TRowExt h.h_ent hi.hi_r))
  : typing sg ln g d (EHandle e' h) hi.hi_b hi.hi_r

(** The premises of `T_Perform` for `perform k.op [σ̄] v` at `τ ! ρ`: the
    entry `k : E τ̄` read in `ρ`, the operation's signature, and the
    argument at the instance of its type, at a row `pf_r ≡ ρ`; the
    instance of the result type is `τ` up to type equality. *)
noeq type perform_inv (sg: sig) (ln: lctx) (g: ctx) (k: key) (op: opname) (ss: list typ)
  (v: exp) (t r: typ) = {
  pf_q: qname;
  pf_ts: list typ;
  pf_ei: effect_info;
  pf_os: op_sig;
  pf_r: typ;
  pf_arg: typing sg ln g [] v (op_inst pf_ts ss pf_os.arg) pf_r;
  pf_facts: squash (L.mem (k, PEff pf_q (canon_tys pf_ts)) (row_entries (canon r)) /\
                    sg.effects pf_q == Some pf_ei /\ op_of pf_ei op == Some pf_os /\
                    check_tys sg g pf_ts pf_ei.eff_params /\ check_tys sg g ss pf_os.binders /\
                    ty_eq (op_inst pf_ts ss pf_os.res) t /\ ty_eq pf_r r);
}

(** `T_Perform` is the only rule that types `perform k.op [σ̄] v`, up to
    conversion. *)
val inv_perform (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: key) (#op: opname)
  (#ss: list typ) (#v: exp) (#t #r: typ) (h: typing sg ln g d (EPerform k op ss v) t r)
  : Pure (perform_inv sg ln g k op ss v t r) (requires True) (ensures fun _ -> True)

(** The entry the `perform` reads in the hole's row of an `Ev_k` inside a
    `handle` of key `k` and element `E τ̄` is `k : E τ̄`, up to type
    equality of the arguments. *)
val handled_entry (sg: sig) (g: ctx) (en: entry) (r0 pr: typ) (k: key)
  (lbl: option string) (q q': qname) (ts ts': list typ)
  : Lemma (requires check sg g (TRowExt en r0) (KRow EEffect) /\ not (inconsistent (hyps g)) /\
                    en == EntEff lbl q ts /\ ent_key en == k /\
                    eff_entries_in k pr (TRowExt en r0) /\
                    L.mem (k, PEff q' (canon_tys ts')) (row_entries (canon pr)))
          (ensures q' == q /\ canon_tys ts' == canon_tys ts)

(** * Resuming *)

(** `handle Ev_k[y] with h` under `y : τ'`, `τ'` the type of the
    `perform`, at the type and the row of the redex up to type
    equality. *)
val resume_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#fs: list frame) (#k: key) (#op: opname)
  (#ss: list typ) (#v: exp) (#hd: handler) (#b #r0: typ)
  (h: typing sg ln g [] (EHandle (plug fs (EPerform k op ss v)) hd) b r0)
  (lbl: option string) (q: qname) (ts: list typ) (ei: effect_info) (os: op_sig)
  (tp: typ) (d0: jctx) (b' r': typ)
  : Pure (typing sg ln (push_var g tp) d0 (resume fs hd) b' r')
         (requires sig_ok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\ ev_k k fs /\
                   hd.h_ent == EntEff lbl q ts /\ handler_key hd == k /\
                   sg.effects q == Some ei /\ op_of ei op == Some os /\
                   check sg g tp KType /\ ty_eq tp (op_inst ts ss os.res) /\
                   ty_eq b' b /\ ty_eq r' r0 /\
                   check sg g b' KType /\ check sg g r' (KRow EEffect))
         (ensures fun _ -> True)

(** * Clauses *)

(** The premises of `TCL_Full` for the clause `full op [b̄] (x : σ, k : κ) -> e`. *)
noeq type full_clause_inv (sg: sig) (ln: lctx) (g: ctx) (ei: effect_info) (ts: list typ)
  (r b: typ) (op: opname) (nb: nat) (s kt: typ) (body: exp) = {
  fc_os: op_sig;
  fc_body: typing sg ln (push_var (push_var (push_tvars g fc_os.binders) s) kt) [] body
             (ren_ty (shift nb) b) (ren_ty (shift nb) r);
  fc_facts: squash (op_of ei op == Some fc_os /\ nb == L.length fc_os.binders /\
                    check sg (push_tvars g fc_os.binders) s KType /\
                    ty_eq s (eff_inst nb ts fc_os.arg) /\
                    check sg (push_tvars g fc_os.binders) kt KType /\
                    ty_eq kt (t_fun (eff_inst nb ts fc_os.res) (ren_ty (shift nb) r)
                               (ren_ty (shift nb) b)));
}

(** The `full` clause that `clause_of` finds for `op` has the premises of
    `TCL_Full`. *)
val full_clause_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (hc: clauses_typing sg ln g ei ts r b cs)
  (op: opname) (nb: nat) (s kt: typ) (body: exp)
  : Pure (full_clause_inv sg ln g ei ts r b op nb s kt body)
         (requires clause_of op cs == Some (CFull op nb s kt body))
         (ensures fun _ -> True)

(** The premises of `TCL_Fast` for the clause `fast op [b̄] (x : σ) -> e`. *)
noeq type fast_clause_inv (sg: sig) (ln: lctx) (g: ctx) (ei: effect_info) (ts: list typ)
  (r: typ) (op: opname) (nb: nat) (s: typ) (body: exp) = {
  sc_os: op_sig;
  sc_body: typing sg ln (push_var (push_tvars g sc_os.binders) s) [] body
             (eff_inst nb ts sc_os.res) (ren_ty (shift nb) r);
  sc_facts: squash (op_of ei op == Some sc_os /\ nb == L.length sc_os.binders /\
                    check sg (push_tvars g sc_os.binders) s KType /\
                    ty_eq s (eff_inst nb ts sc_os.arg));
}

(** The `fast` clause that `clause_of` finds for `op` has the premises of
    `TCL_Fast`. *)
val fast_clause_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (hc: clauses_typing sg ln g ei ts r b cs)
  (op: opname) (nb: nat) (s: typ) (body: exp)
  : Pure (fast_clause_inv sg ln g ei ts r op nb s body)
         (requires clause_of op cs == Some (CFast op nb s body))
         (ensures fun _ -> True)
