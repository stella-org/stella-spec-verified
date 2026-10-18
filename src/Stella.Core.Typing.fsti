(**
 * The typing relation of the Core (spec 05; spec 06 §Run-time forms,
 * §Opaque values).
 *
 *     typing sg ln g d tl e t r            Γ; Δ ⊢ e : τ ! ρ
 *     dt_typing sg ln g d tl om dt t r     Γ; Δ; Ω ⊢ dt : τ ! ρ
 *     occ_typing sg g om o t               Ω ⊢ o : τ
 *
 * `sg` is `Σ`, `ln` is `Γ_N` (design §4.5), `g` is `Γ` (design §4.2), `d` is
 * `Δ` and `om` is `Ω` (`Stella.Core.Typing.Aux`). `r` is the ambient effect
 * row. Kinding, entailment and type equality are the total functions of
 * `Stella.Core.Kinding`, `Stella.Core.Entail` and `Stella.Core.Rows`; every
 * premise on them is a `squash`.
 *
 * ## Tail position
 *
 * `tl` says whether `e` stands in tail position, the positions
 * `Tl ::= [] | letjoin j (x̄ : τ̄) : τ = e' in Tl` of spec 06 §Evaluation
 * contexts, within the current function activation. `jump` requires it.
 *
 *   - A child that is no tail of its parent is typed with `tl = false` and
 *     the parent's `Δ`: both sides of an application, the bound side of
 *     `let`, the scrutinees of `case` and `match`, the condition of `guard`,
 *     the arguments of `jump`, every subterm of a record or variant
 *     operation, the argument of `perform`, the value of `writeCell`, the
 *     initial values of `region`, the operands of `openEff`, `openEffC`,
 *     `[σ]` and `[•]`.
 *   - The continuation of `letjoin`, the body of `let` and of `letrec`, and
 *     the leaves of a decision tree inherit `tl`. The definition of a join
 *     point is in tail position wherever its `letjoin` stands.
 *   - The bodies that discard `Δ` (design §4.3; spec 04 §Join points) are
 *     typed with `Δ = []` and `tl = true`: the bodies of `λ`, `Λ` and
 *     constraint `Λ`, the handled computation, the return clause and the
 *     operation clauses of `handle`, the body of `region` and of
 *     `region⟨ℓ⟩`, and the cells of `region⟨ℓ⟩`.
 *   - The initializers of `letrec`, and the operand of `fill`, which is an
 *     initializer running, also discard `Δ` but stand out of tail position
 *     (spec 05 §Basic rules): they are typed with `Δ = []` and
 *     `tl = false`.
 *
 * ## Leaves, conversion, and kinding premises
 *
 * Conversion (`T_Conv`) is the only rule that changes a type or a row
 * without changing the term. It converts both up to `ty_eq` and requires the
 * new ones to be well kinded. Every other rule is syntax-directed, matching
 * the types of its premises against the shapes it needs (`t_fun`,
 * `t_record`, …) exactly.
 *
 * A rule with no premise typing a term at the ambient row, a leaf, checks
 * that row: `Γ ⊢ ρ : Row Effect`. A rule that introduces a type into the
 * context or into the type it concludes checks that type, unless a premise
 * typing a subterm already carries it. The empty case of every list
 * judgement checks the types and rows it is indexed by, which no premise
 * would otherwise constrain. The kinding of every type a derivation
 * mentions is thus a premise or follows from a subderivation.
 *
 * ## Binders
 *
 * Term binders push onto `vars` (`push_var`, and `push_vars` for a
 * telescope, the last binder being index 0; design §3.1). Type binders push
 * onto `tvars` (`push_tvar`, `push_tvars`), shifting the context; nothing
 * else is shifted, `Δ` being empty under a type binder. A region body is
 * opened with an atom by cofinite quantification (design §1.3): the body
 * must be typed for every atom outside a finite list that holds at least
 * the regions in scope and the atoms of the body.
 *
 * ## Decision trees and run-time matching
 *
 * `case (ē) of dt` types `dt` under `Ω = { s_i ↦ τ_i }`. The run-time form
 * `match θ dt` types `dt` under an `Ω` written in the derivation, every
 * entry `o ↦ τ` of which is justified by the value `θ(o)` (`proj`) having
 * type `τ` (design §6).
 *)
module Stella.Core.Typing
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Typing.Aux
module L = FStar.List.Tot
module I = Stella.Core.Init
module V = Stella.Core.Value

(** * Occurrence typing (spec 05 §Occurrence typing) *)

(** `Ω ⊢ o : τ`. An occurrence is typed by an entry of `Ω`, which the
    scrutinees and the dispatches above it recorded, or as the element at a
    key of a record occurrence. The record's row `r` is written in the
    derivation; the element is read through `canon r`, as `nf(r)` in the
    spec, and its payload type `τ` is a type whose canonical form is the
    element's. *)
noeq type occ_typing (sg: sig) : ctx -> octx -> occ -> typ -> Type =
  | TO_Lookup :
      #g:ctx -> #om:octx -> #o:occ -> #t:typ ->
      squash (L.assoc o om == Some t) ->
      occ_typing sg g om o t
  | TO_Field :
      #g:ctx -> #om:octx -> #o:occ -> #k:key -> #t_o:typ -> #t:typ ->
      r:typ ->
      occ_typing sg g om o t_o ->
      squash (ty_eq t_o (t_record r) /\ check sg g r (KRow EType)) ->
      squash (L.mem (k, PTy (canon t)) (row_entries (canon r)) /\ check sg g t KType) ->
      occ_typing sg g om (ORecord o k) t

(** * Term typing *)

noeq type typing (sg: sig) (ln: lctx) : ctx -> jctx -> bool -> exp -> typ -> typ -> Type =

  (* -- Basic rules (spec 05 §Basic rules) -- *)

  (** `(x : τ) ∈ Γ` *)
  | T_Var :
      #g:ctx -> #d:jctx -> #tl:bool -> #i:nat -> #t:typ -> #r:typ ->
      squash (L.nth g.vars i == Some t) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln g d tl (EVar i) t r

  (** `M.x [[κ̄']] : σ[k̄ := κ̄']`, `M.x` a constructor, a foreign or a
      top-level value. *)
  | T_Global :
      #g:ctx -> #d:jctx -> #tl:bool -> #q:qname -> #ks:list kind -> #nk:nat -> #t:typ -> #r:typ ->
      squash (global_type sg q == Some (nk, t)) ->
      squash (L.length ks == nk /\ qkinds_wf g.nk ks) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln g d tl (EGlobal q ks) (kinst_ty ks t) r

  | T_Lit :
      #g:ctx -> #d:jctx -> #tl:bool -> #c:lit -> #r:typ ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln g d tl (ELit c) (lit_type c) r

  (** `λ (x : τ1) / ρ' . e : τ1 -{ρ'}-> τ2`: the body stands at the row the
      λ writes, under no join point. *)
  | T_Lam :
      #g:ctx -> #d:jctx -> #tl:bool -> #t1:typ -> #r':typ -> #body:exp -> #t2:typ -> #r:typ ->
      squash (check sg g t1 KType /\ check sg g r' (KRow EEffect)) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln (push_var g t1) [] true body t2 r' ->
      typing sg ln g d tl (ELam t1 r' body) (t_fun t1 r' t2) r

  (** The arrow's row is the ambient row. *)
  | T_App :
      #g:ctx -> #d:jctx -> #tl:bool -> #e1:exp -> #e2:exp -> #t1:typ -> #t2:typ -> #r:typ ->
      typing sg ln g d false e1 (t_fun t1 r t2) r ->
      typing sg ln g d false e2 t1 r ->
      typing sg ln g d tl (EApp e1 e2) t2 r

  (** `Λ (a : κ). v`, `v` a value form typed at `()`. *)
  | T_TyLam :
      #g:ctx -> #d:jctx -> #tl:bool -> #k:kind -> #body:exp -> #t:typ -> #r:typ ->
      squash (kind_wf g.nk k /\ qkind g.nk k) ->
      squash (value_form sg body) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln (push_tvar g k) [] true body t TRowEmpty ->
      typing sg ln g d tl (ETyLam k body) (TForall k t) r

  | T_TyApp :
      #g:ctx -> #d:jctx -> #tl:bool -> #e:exp -> #s:typ -> #k:kind -> #t:typ -> #r:typ ->
      typing sg ln g d false e (TForall k t) r ->
      squash (check sg g s k) ->
      typing sg ln g d tl (ETyApp e s) (subst1_ty s t) r

  (** `Λ (_ : C). v`. `C` is well formed and need not be satisfiable
      (design §2.2). *)
  | T_CLam :
      #g:ctx -> #d:jctx -> #tl:bool -> #c:constr -> #body:exp -> #t:typ -> #r:typ ->
      squash (constr_ok sg g c) ->
      squash (value_form sg body) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln (add_assump g c) [] true body t TRowEmpty ->
      typing sg ln g d tl (ECLam c body) (TConstr c t) r

  (** `e [•]` discharges `C` by entailment. *)
  | T_CApp :
      #g:ctx -> #d:jctx -> #tl:bool -> #e:exp -> #c:constr -> #t:typ -> #r:typ ->
      typing sg ln g d false e (TConstr c t) r ->
      squash (entails (hyps g) c) ->
      typing sg ln g d tl (ECApp e) t r

  | T_Let :
      #g:ctx -> #d:jctx -> #tl:bool -> #t1:typ -> #e1:exp -> #e2:exp -> #t2:typ -> #r:typ ->
      squash (check sg g t1 KType) ->
      typing sg ln g d false e1 t1 r ->
      typing sg ln (push_var g t1) d tl e2 t2 r ->
      typing sg ln g d tl (ELet t1 e1 e2) t2 r

  (** `letrec { x̄ : σ̄ = ē } in e`: the members are a telescope in every
      initializer and in the body, each initializer stands at `()` under no
      join point and out of tail position, and the group is
      initialization-safe (spec 10). *)
  | T_LetRec :
      #g:ctx -> #d:jctx -> #tl:bool -> #bs:list (typ & exp) -> #body:exp -> #t:typ -> #r:typ ->
      squash (I.init_safe_letrec sg bs) ->
      binds_typing sg ln (push_vars g (L.map fst bs)) bs ->
      typing sg ln (push_vars g (L.map fst bs)) d tl body t r ->
      typing sg ln g d tl (ELetRec bs body) t r

  | T_Conv :
      #g:ctx -> #d:jctx -> #tl:bool -> #e:exp -> #t1:typ -> #r1:typ -> #t2:typ -> #r2:typ ->
      typing sg ln g d tl e t1 r1 ->
      squash (ty_eq t1 t2 /\ ty_eq r1 r2) ->
      squash (check sg g t2 KType /\ check sg g r2 (KRow EEffect)) ->
      typing sg ln g d tl e t2 r2

  (* -- Join points and decision trees (spec 05 §Join points and decision trees) -- *)

  | T_Case :
      #g:ctx -> #d:jctx -> #tl:bool -> #es:list exp -> #dt:dtree -> #ts:list typ -> #t:typ -> #r:typ ->
      exps_typing sg ln g d false r es ts ->
      dt_typing sg ln g d tl (scrut_occs 0 ts) dt t r ->
      typing sg ln g d tl (ECase es dt) t r

  (** The definition is typed under its parameters with the join point in
      scope, in tail position; the continuation inherits `tl`. *)
  | T_LetJoin :
      #g:ctx -> #d:jctx -> #tl:bool -> #ts:list typ -> #t:typ -> #e1:exp -> #e2:exp -> #r:typ ->
      squash (tys_ok sg g ts /\ check sg g t KType) ->
      typing sg ln (push_vars g ts) ((ts, t, r) :: d) true e1 t r ->
      typing sg ln g ((ts, t, r) :: d) tl e2 t r ->
      typing sg ln g d tl (ELetJoin ts t e1 e2) t r

  (** `jump` stands in tail position, at the result type and the row of its
      join point. *)
  | T_Jump :
      #g:ctx -> #d:jctx -> #j:nat -> #es:list exp -> #ts:list typ -> #t:typ -> #r:typ ->
      squash (L.nth d j == Some (ts, t, r)) ->
      squash (check sg g t KType /\ check sg g r (KRow EEffect)) ->
      exps_typing sg ln g d false r es ts ->
      typing sg ln g d true (EJump j es) t r

  (* -- Records and variants (spec 05 §Records and variants) -- *)

  | T_RecEmpty :
      #g:ctx -> #d:jctx -> #tl:bool -> #r:typ ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln g d tl ERecEmpty (t_record TRowEmpty) r

  | T_Extend :
      #g:ctx -> #d:jctx -> #tl:bool -> #k:key -> #e1:exp -> #e2:exp -> #t:typ -> #r0:typ -> #r:typ ->
      typing sg ln g d false e1 t r ->
      typing sg ln g d false e2 (t_record r0) r ->
      squash (key_ok sg g k EType /\ entails (hyps g) (CLacks k r0)) ->
      typing sg ln g d tl (EExtend k e1 e2) (t_record (TRowExt (EntTy k t) r0)) r

  | T_Select :
      #g:ctx -> #d:jctx -> #tl:bool -> #k:key -> #e:exp -> #t:typ -> #r0:typ -> #r:typ ->
      typing sg ln g d false e (t_record (TRowExt (EntTy k t) r0)) r ->
      squash (key_ok sg g k EType) ->
      typing sg ln g d tl (ESelect k e) t r

  | T_Restrict :
      #g:ctx -> #d:jctx -> #tl:bool -> #k:key -> #e:exp -> #t:typ -> #r0:typ -> #r:typ ->
      typing sg ln g d false e (t_record (TRowExt (EntTy k t) r0)) r ->
      squash (key_ok sg g k EType) ->
      typing sg ln g d tl (ERestrict k e) (t_record r0) r

  (** The type at `k` may change. *)
  | T_Update :
      #g:ctx -> #d:jctx -> #tl:bool -> #k:key -> #e1:exp -> #e2:exp -> #t:typ -> #t':typ ->
      #r0:typ -> #r:typ ->
      typing sg ln g d false e1 (t_record (TRowExt (EntTy k t) r0)) r ->
      typing sg ln g d false e2 t' r ->
      squash (key_ok sg g k EType) ->
      typing sg ln g d tl (EUpdate k e1 e2) (t_record (TRowExt (EntTy k t') r0)) r

  | T_Merge :
      #g:ctx -> #d:jctx -> #tl:bool -> #e1:exp -> #e2:exp -> #r1:typ -> #r2:typ -> #r:typ ->
      typing sg ln g d false e1 (t_record r1) r ->
      typing sg ln g d false e2 (t_record r2) r ->
      squash (entails (hyps g) (CDisj r1 r2)) ->
      typing sg ln g d tl (EMerge e1 e2) (t_record (TRowUnion r1 r2)) r

  (** `inject k [r0] e` writes the rest `r0` of its variant. *)
  | T_Inject :
      #g:ctx -> #d:jctx -> #tl:bool -> #k:key -> #r0:typ -> #e:exp -> #t:typ -> #r:typ ->
      typing sg ln g d false e t r ->
      squash (key_ok sg g k EType /\ entails (hyps g) (CLacks k r0)) ->
      squash (check sg g r0 (KRow EType)) ->
      typing sg ln g d tl (EInject k r0 e) (t_variant (TRowExt (EntTy k t) r0)) r

  | T_Weaken :
      #g:ctx -> #d:jctx -> #tl:bool -> #k:key -> #t:typ -> #e:exp -> #r0:typ -> #r:typ ->
      typing sg ln g d false e (t_variant r0) r ->
      squash (key_ok sg g k EType /\ entails (hyps g) (CLacks k r0)) ->
      squash (check sg g t KType) ->
      typing sg ln g d tl (EWeaken k t e) (t_variant (TRowExt (EntTy k t) r0)) r

  | T_Absurd :
      #g:ctx -> #d:jctx -> #tl:bool -> #t:typ -> #e:exp -> #r:typ ->
      typing sg ln g d false e (t_variant TRowEmpty) r ->
      squash (check sg g t KType) ->
      typing sg ln g d tl (EAbsurd t e) t r

  (* -- Effects (spec 05 §Effects) -- *)

  (** `perform k.op [σ̄] e`. The ambient row has an element `k : E τ̄`, with
      `τ̄` written in the derivation and read through `canon r`; the
      operation is looked up in `E`, its binders instantiated at `σ̄` and
      `E`'s parameters at `τ̄`. *)
  | T_Perform :
      #g:ctx -> #d:jctx -> #tl:bool -> #k:key -> #op:opname -> #ss:list typ -> #e:exp -> #r:typ ->
      #q:qname -> #ei:effect_info -> #os:op_sig ->
      ts:list typ ->
      squash (L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r))) ->
      squash (sg.effects q == Some ei /\ op_of ei op == Some os) ->
      squash (check_tys sg g ts ei.eff_params /\ check_tys sg g ss os.binders) ->
      typing sg ln g d false e (op_inst ts ss os.arg) r ->
      typing sg ln g d tl (EPerform k op ss e) (op_inst ts ss os.res) r

  (** `handle e with h : β ! ρ`. `h` writes the element `E τ̄` (or
      `s : E τ̄`) it removes; the handled computation stands at the row with
      that element, the return clause and the operation clauses at `ρ`, all
      under no join point. The clauses cover `E`'s operations once each. *)
  | T_Handle :
      #g:ctx -> #d:jctx -> #tl:bool -> #e:exp -> #h:handler -> #b:typ -> #r:typ ->
      #lbl:option string -> #q:qname -> #ts:list typ -> #ei:effect_info ->
      squash (h.h_ent == EntEff lbl q ts /\ sg.effects q == Some ei) ->
      squash (check sg g (TRowExt h.h_ent r) (KRow EEffect) /\ check sg g h.h_ret_ty KType) ->
      squash (check sg g b KType /\ check sg g r (KRow EEffect)) ->
      squash (clauses_cover ei h.h_clauses) ->
      typing sg ln g [] true e h.h_ret_ty (TRowExt h.h_ent r) ->
      typing sg ln (push_var g h.h_ret_ty) [] true h.h_ret b r ->
      clauses_typing sg ln g ei ts r b h.h_clauses ->
      typing sg ln g d tl (EHandle e h) b r

  | T_OpenEff :
      #g:ctx -> #d:jctx -> #tl:bool -> #r':typ -> #e:exp -> #t1:typ -> #r1:typ -> #t2:typ -> #r:typ ->
      typing sg ln g d false e (t_fun t1 r1 t2) r ->
      squash (entails (hyps g) (CDisj r1 r') /\ check sg g r' (KRow EEffect)) ->
      typing sg ln g d tl (EOpenEff r' e) (t_fun t1 (TRowUnion r1 r') t2) r

  (* -- Regions (spec 05 §Regions) -- *)

  (** `region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e : β ! ρ`. The layout, kinded as a
      row (which makes its keys distinct), the initial values, `β` and `ρ`
      stand in the outer context. The body is opened with every atom `a`
      outside `l`, and typed with the region entered, under no join point, at
      `( region a | ρ )`. Since `β` and `ρ` are kinded where `a` is not in
      scope, `a` occurs in neither. *)
  | T_Region :
      #g:ctx -> #d:jctx -> #tl:bool -> #lay:layout -> #es:list exp -> #body:exp -> #b:typ -> #r:typ ->
      l:list atom ->
      squash (check sg g (layout_row lay) (KRow EType)) ->
      squash (check sg g b KType /\ check sg g r (KRow EEffect)) ->
      squash (forall (a: atom). L.mem a (rdom g) \/ L.mem a (frn_exp body) ==> L.mem a l) ->
      squash (forall (a: atom). ~(L.mem a l) ==>
                check sg (enter_region g a lay) (TRowExt (EntRegion (RFree a)) r) (KRow EEffect)) ->
      exps_typing sg ln g d false r es (L.map snd lay) ->
      (a: atom{~(L.mem a l)} ->
        typing sg ln (enter_region g a lay) [] true (open_region a body) b
          (TRowExt (EntRegion (RFree a)) r)) ->
      typing sg ln g d tl (ERegion lay es body) b r

  (** `readCell a.k`: the region `a` is in scope with a cell `k : σ`, and it
      is ambient. *)
  | T_ReadCell :
      #g:ctx -> #d:jctx -> #tl:bool -> #a:atom -> #k:key -> #lay:layout -> #t:typ -> #r:typ ->
      squash (L.assoc a g.regions == Some lay /\ L.assoc k lay == Some t) ->
      squash (L.mem (RegionKey (RFree a)) (known_keys r)) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln g d tl (EReadCell (RFree a) k) t r

  | T_WriteCell :
      #g:ctx -> #d:jctx -> #tl:bool -> #a:atom -> #k:key -> #e:exp -> #lay:layout -> #t:typ -> #r:typ ->
      squash (L.assoc a g.regions == Some lay /\ L.assoc k lay == Some t) ->
      squash (L.mem (RegionKey (RFree a)) (known_keys r)) ->
      typing sg ln g d false e t r ->
      typing sg ln g d tl (EWriteCell (RFree a) k e) t_unit r

  (* -- Run-time forms (spec 06 §Run-time forms, §Opaque values) -- *)

  (** `match θ dt`: each `θ[i]` is a typed value, and `dt` is typed under
      an `Ω` every entry of which `θ` justifies (`match_typing`). *)
  | T_Match :
      #g:ctx -> #d:jctx -> #tl:bool -> #th:list exp -> #dt:dtree -> #ts:list typ -> #t:typ -> #r:typ ->
      om:octx ->
      exps_typing sg ln g d false r th ts ->
      squash (L.for_all (V.is_value sg) th) ->
      match_typing sg ln g d r th om ->
      dt_typing sg ln g d tl om dt t r ->
      typing sg ln g d tl (EMatch th dt) t r

  (** `openEffC [ρ'] e` widens the ambient row of a computation. *)
  | T_OpenEffC :
      #g:ctx -> #d:jctx -> #tl:bool -> #r':typ -> #e:exp -> #t:typ -> #r0:typ ->
      typing sg ln g d false e t r0 ->
      squash (entails (hyps g) (CDisj r0 r') /\ check sg g r' (KRow EEffect)) ->
      typing sg ln g d tl (EOpenEffC r' e) t (TRowUnion r0 r')

  | T_Force :
      #g:ctx -> #d:jctx -> #tl:bool -> #nu:atom -> #t:typ -> #r:typ ->
      squash (L.nth ln nu == Some t /\ check sg g t KType) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln g d tl (EForce nu) t r

  | T_Fill :
      #g:ctx -> #d:jctx -> #tl:bool -> #nu:atom -> #e:exp -> #t:typ -> #r:typ ->
      squash (L.nth ln nu == Some t) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln g [] false e t TRowEmpty ->
      typing sg ln g d tl (EFill nu e) t r

  (** `region⟨a⟩ θ in e : β ! ρ`, the source rule with the region `a` of
      `Γ_R` in place of the binder and the cells `θ` in place of the
      initial values. `θ` holds one cell per key of the layout, in the
      layout's order. *)
  | T_RegionOpen :
      #g:ctx -> #d:jctx -> #tl:bool -> #a:atom -> #cells:list (key & exp) -> #body:exp ->
      #lay:layout -> #b:typ -> #r:typ ->
      squash (L.assoc a g.regions == Some lay) ->
      squash (check sg g b KType /\ check sg g r (KRow EEffect)) ->
      squash (~(L.mem a (frn_ty b @ frn_ty r))) ->
      cells_typing sg ln g cells lay ->
      typing sg ln (add_region_facts g a) [] true body b (TRowExt (EntRegion (RFree a)) r) ->
      typing sg ln g d tl (ERegionOpen a cells body) b r

  (** `opaque ω [τ]`, `τ` an application of a type constructor of class
      opaque. *)
  | T_Opaque :
      #g:ctx -> #d:jctx -> #tl:bool -> #w:nat -> #t:typ -> #r:typ ->
      squash (opaque_type sg t /\ check sg g t KType) ->
      squash (check sg g r (KRow EEffect)) ->
      typing sg ln g d tl (EOpaque w t) t r

(** `Γ; Δ ⊢ ē : τ̄ ! ρ`, pointwise, the lengths agreeing. *)
and exps_typing (sg: sig) (ln: lctx) : ctx -> jctx -> bool -> typ -> list exp -> list typ -> Type =
  | TE_Nil :
      #g:ctx -> #d:jctx -> #tl:bool -> #r:typ ->
      squash (check sg g r (KRow EEffect)) ->
      exps_typing sg ln g d tl r [] []
  | TE_Cons :
      #g:ctx -> #d:jctx -> #tl:bool -> #r:typ -> #e:exp -> #es:list exp -> #t:typ -> #ts:list typ ->
      typing sg ln g d tl e t r ->
      exps_typing sg ln g d tl r es ts ->
      exps_typing sg ln g d tl r (e :: es) (t :: ts)

(** The members of a `letrec`, under the context with every member bound:
    each annotation has kind `Type`, and each initializer has its member's
    type at `()`, under no join point and out of tail position. *)
and binds_typing (sg: sig) (ln: lctx) : ctx -> list (typ & exp) -> Type =
  | TB_Nil :
      #g:ctx ->
      binds_typing sg ln g []
  | TB_Cons :
      #g:ctx -> #t:typ -> #e:exp -> #bs:list (typ & exp) ->
      squash (check sg g t KType) ->
      typing sg ln g [] false e t TRowEmpty ->
      binds_typing sg ln g bs ->
      binds_typing sg ln g ((t, e) :: bs)

(** The cells of an open region against its layout: the same keys in the
    same order, each a value of its cell's type at `()`, under no join
    point. *)
and cells_typing (sg: sig) (ln: lctx) : ctx -> list (key & exp) -> layout -> Type =
  | TC_Nil :
      #g:ctx ->
      cells_typing sg ln g [] []
  | TC_Cons :
      #g:ctx -> #k:key -> #v:exp -> #t:typ -> #cs:list (key & exp) -> #lay:layout ->
      squash (V.is_value sg v) ->
      typing sg ln g [] true v t TRowEmpty ->
      cells_typing sg ln g cs lay ->
      cells_typing sg ln g ((k, v) :: cs) ((k, t) :: lay)

(** The scrutinee values `θ` of a `match` justify `Ω`: the value `θ(o)` at
    each occurrence `o ↦ τ` of `Ω` has type `τ`. *)
and match_typing (sg: sig) (ln: lctx) : ctx -> jctx -> typ -> list exp -> octx -> Type =
  | TM_Nil :
      #g:ctx -> #d:jctx -> #r:typ -> #th:list exp ->
      squash (check sg g r (KRow EEffect)) ->
      match_typing sg ln g d r th []
  | TM_Cons :
      #g:ctx -> #d:jctx -> #r:typ -> #th:list exp -> #o:occ -> #t:typ -> #om:octx -> #v:exp ->
      squash (proj sg th o == Some v) ->
      typing sg ln g d false v t r ->
      match_typing sg ln g d r th om ->
      match_typing sg ln g d r th ((o, t) :: om)

(** `Γ; Δ; Ω ⊢ dt : τ ! ρ` *)
and dt_typing (sg: sig) (ln: lctx) : ctx -> jctx -> bool -> octx -> dtree -> typ -> typ -> Type =
  | TD_Leaf :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #e:exp -> #t:typ -> #r:typ ->
      typing sg ln g d tl e t r ->
      dt_typing sg ln g d tl om (DLeaf e) t r

  | TD_Bind :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #dt:dtree -> #t_o:typ -> #t:typ -> #r:typ ->
      occ_typing sg g om o t_o ->
      dt_typing sg ln (push_var g t_o) d tl om dt t r ->
      dt_typing sg ln g d tl om (DBind o dt) t r

  (** `switchCtor` without a default. The occurrence has the type of a data
      type `T [[κ̄]] σ̄`, written in the derivation, whose constructors `cs`
      the branches name, each once, and exhaust. *)
  | TD_SwitchCtor :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #bs:list (qname & dtree) ->
      #t_o:typ -> #t:typ -> #r:typ ->
      tq:qname -> ks:list kind -> ss:list typ -> cs:list qname ->
      occ_typing sg g om o t_o ->
      squash (ty_eq t_o (tapps (TCon tq ks) ss) /\ check sg g (tapps (TCon tq ks) ss) KType) ->
      squash (has_class sg tq (TcData cs)) ->
      squash (L.noRepeats (L.map fst bs) /\ (forall (c: qname). L.mem c cs ==> L.mem c (L.map fst bs))) ->
      ctor_brs_typing sg ln g d tl om o ks ss cs bs t r ->
      dt_typing sg ln g d tl om (DSwitchCtor o bs None) t r

  (** `switchCtor` with a default, under the same `Ω`. *)
  | TD_SwitchCtorDef :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #bs:list (qname & dtree) ->
      #df:dtree -> #t_o:typ -> #t:typ -> #r:typ ->
      tq:qname -> ks:list kind -> ss:list typ -> cs:list qname ->
      occ_typing sg g om o t_o ->
      squash (ty_eq t_o (tapps (TCon tq ks) ss) /\ check sg g (tapps (TCon tq ks) ss) KType) ->
      squash (has_class sg tq (TcData cs)) ->
      squash (L.noRepeats (L.map fst bs)) ->
      ctor_brs_typing sg ln g d tl om o ks ss cs bs t r ->
      dt_typing sg ln g d tl om df t r ->
      dt_typing sg ln g d tl om (DSwitchCtor o bs (Some df)) t r

  (** `switchLit`: the occurrence has a literal type `lq`, the literals are
      distinct and of that type, and the default is mandatory. *)
  | TD_SwitchLit :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #bs:list (lit & dtree) -> #df:dtree ->
      #t_o:typ -> #t:typ -> #r:typ ->
      lq:qname ->
      occ_typing sg g om o t_o ->
      squash (ty_eq t_o (TCon lq []) /\ has_class sg lq (TcIntrinsic ClsLiteral)) ->
      squash (L.noRepeats (L.map fst bs)) ->
      lit_brs_typing sg ln g d tl om (TCon lq []) bs t r ->
      dt_typing sg ln g d tl om df t r ->
      dt_typing sg ln g d tl om (DSwitchLit o bs df) t r

  (** `switchKey` without a default. The occurrence has the type
      `Variant vr`, `vr` written in the derivation and read through
      `canon vr = ⟨F ; T⟩`. The keys are distinct elements of `F`, `T` is
      empty, and the keys exhaust `F`. *)
  | TD_SwitchKey :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #bs:list (key & dtree) ->
      #t_o:typ -> #t:typ -> #r:typ ->
      vr:typ ->
      occ_typing sg g om o t_o ->
      squash (ty_eq t_o (t_variant vr) /\ check sg g vr (KRow EType)) ->
      squash (L.noRepeats (L.map fst bs)) ->
      squash (row_tails (canon vr) == [] /\ keys_covered (row_entries (canon vr)) (L.map fst bs)) ->
      key_brs_typing sg ln g d tl om o (row_entries (canon vr)) bs t r ->
      dt_typing sg ln g d tl om (DSwitchKey o bs None) t r

  (** `switchKey` with a default, in which the occurrence takes the residual
      type `Variant vr'`, `canon vr' = ⟨F ∖ k̄ ; T⟩`, `vr'` written in the
      derivation. *)
  | TD_SwitchKeyDef :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #bs:list (key & dtree) -> #df:dtree ->
      #t_o:typ -> #t:typ -> #r:typ ->
      vr:typ -> vr':typ ->
      occ_typing sg g om o t_o ->
      squash (ty_eq t_o (t_variant vr) /\ check sg g vr (KRow EType)) ->
      squash (L.noRepeats (L.map fst bs)) ->
      squash (canon vr' ==
                mkrow (drop_keys (L.map fst bs) (row_entries (canon vr))) (row_tails (canon vr)) /\
              check sg g vr' (KRow EType)) ->
      key_brs_typing sg ln g d tl om o (row_entries (canon vr)) bs t r ->
      dt_typing sg ln g d tl ((o, t_variant vr') :: om) df t r ->
      dt_typing sg ln g d tl om (DSwitchKey o bs (Some df)) t r

  | TD_Guard :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #e:exp -> #dt1:dtree -> #dt2:dtree -> #t:typ -> #r:typ ->
      typing sg ln g d false e t_bool r ->
      dt_typing sg ln g d tl om dt1 t r ->
      dt_typing sg ln g d tl om dt2 t r ->
      dt_typing sg ln g d tl om (DGuard e dt1 dt2) t r

(** The branches of a `switchCtor` on `o : T [[κ̄]] σ̄`, `T`'s constructors
    being `cs`: each branch names one of them, and is typed with its fields
    `o ! Ctor . j ↦ τ_j[ā := σ̄]` added to `Ω`. *)
and ctor_brs_typing (sg: sig) (ln: lctx)
  : ctx -> jctx -> bool -> octx -> occ -> list kind -> list typ -> list qname ->
    list (qname & dtree) -> typ -> typ -> Type =
  | TCB_Nil :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #ks:list kind -> #ss:list typ ->
      #cs:list qname -> #t:typ -> #r:typ ->
      squash (check sg g t KType /\ check sg g r (KRow EEffect)) ->
      ctor_brs_typing sg ln g d tl om o ks ss cs [] t r
  | TCB_Cons :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #ks:list kind -> #ss:list typ ->
      #cs:list qname -> #c:qname -> #dt:dtree -> #bs:list (qname & dtree) -> #t:typ -> #r:typ ->
      #fs:list typ ->
      squash (L.mem c cs /\ ctor_fields sg c ks ss == Some fs) ->
      dt_typing sg ln g d tl (L.append (field_occs o c 0 fs) om) dt t r ->
      ctor_brs_typing sg ln g d tl om o ks ss cs bs t r ->
      ctor_brs_typing sg ln g d tl om o ks ss cs ((c, dt) :: bs) t r

(** The branches of a `switchLit` at the literal type `lt`. *)
and lit_brs_typing (sg: sig) (ln: lctx)
  : ctx -> jctx -> bool -> octx -> typ -> list (lit & dtree) -> typ -> typ -> Type =
  | TLB_Nil :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #lt:typ -> #t:typ -> #r:typ ->
      squash (check sg g t KType /\ check sg g r (KRow EEffect)) ->
      lit_brs_typing sg ln g d tl om lt [] t r
  | TLB_Cons :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #lt:typ -> #c:lit -> #dt:dtree ->
      #bs:list (lit & dtree) -> #t:typ -> #r:typ ->
      squash (ty_eq (lit_type c) lt) ->
      dt_typing sg ln g d tl om dt t r ->
      lit_brs_typing sg ln g d tl om lt bs t r ->
      lit_brs_typing sg ln g d tl om lt ((c, dt) :: bs) t r

(** The branches of a `switchKey` on `o`, the variant's entries being `F`:
    each branch names a key of `F`, and is typed with `o ? k ↦ τ` added to
    `Ω`, `τ` a type of kind `Type` whose canonical form is `F(k)`. *)
and key_brs_typing (sg: sig) (ln: lctx)
  : ctx -> jctx -> bool -> octx -> occ -> list centry -> list (key & dtree) -> typ -> typ -> Type =
  | TKB_Nil :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #fs:list centry -> #t:typ -> #r:typ ->
      squash (check sg g t KType /\ check sg g r (KRow EEffect)) ->
      key_brs_typing sg ln g d tl om o fs [] t r
  | TKB_Cons :
      #g:ctx -> #d:jctx -> #tl:bool -> #om:octx -> #o:occ -> #fs:list centry -> #k:key ->
      #dt:dtree -> #bs:list (key & dtree) -> #t:typ -> #r:typ ->
      pt:typ ->
      squash (L.mem (k, PTy (canon pt)) fs /\ check sg g pt KType) ->
      dt_typing sg ln g d tl ((OVariant o k, pt) :: om) dt t r ->
      key_brs_typing sg ln g d tl om o fs bs t r ->
      key_brs_typing sg ln g d tl om o fs ((k, dt) :: bs) t r

(** The operation clauses of a handler of `E τ̄` (`ei` being `E`) at the
    outer row `ρ` and the answer type `β` (spec 05 §Effects; spec 03 §full
    and fast clauses). A clause binds the operation's binders `b̄`, then
    `x`, then for `full` the continuation `k`; its annotations and its body
    stand under the `m = |b̄|` type binders, so `ρ` and `β` are shifted by
    `m` there. The written annotations are kinded and equal, up to
    `ty_eq`, to `σ[ā := τ̄]` and `τ'[ā := τ̄] -{ρ}-> β`.

      - A `full` clause's body has the answer type `β`.
      - A `fast` clause's body has the resume type `τ'[ā := τ̄]`. *)
and clauses_typing (sg: sig) (ln: lctx)
  : ctx -> effect_info -> list typ -> typ -> typ -> list clause -> Type =
  | TCL_Nil :
      #g:ctx -> #ei:effect_info -> #ts:list typ -> #r:typ -> #b:typ ->
      squash (check sg g b KType /\ check sg g r (KRow EEffect)) ->
      clauses_typing sg ln g ei ts r b []
  | TCL_Full :
      #g:ctx -> #ei:effect_info -> #ts:list typ -> #r:typ -> #b:typ ->
      #op:opname -> #nb:nat -> #s:typ -> #kt:typ -> #body:exp -> #cs:list clause -> #os:op_sig ->
      squash (op_of ei op == Some os /\ nb == L.length os.binders) ->
      squash (check sg (push_tvars g os.binders) s KType /\ ty_eq s (eff_inst nb ts os.arg)) ->
      squash (check sg (push_tvars g os.binders) kt KType /\
              ty_eq kt (t_fun (eff_inst nb ts os.res) (ren_ty (shift nb) r) (ren_ty (shift nb) b))) ->
      typing sg ln (push_var (push_var (push_tvars g os.binders) s) kt) [] true body
        (ren_ty (shift nb) b) (ren_ty (shift nb) r) ->
      clauses_typing sg ln g ei ts r b cs ->
      clauses_typing sg ln g ei ts r b (CFull op nb s kt body :: cs)
  | TCL_Fast :
      #g:ctx -> #ei:effect_info -> #ts:list typ -> #r:typ -> #b:typ ->
      #op:opname -> #nb:nat -> #s:typ -> #body:exp -> #cs:list clause -> #os:op_sig ->
      squash (op_of ei op == Some os /\ nb == L.length os.binders) ->
      squash (check sg (push_tvars g os.binders) s KType /\ ty_eq s (eff_inst nb ts os.arg)) ->
      typing sg ln (push_var (push_tvars g os.binders) s) [] true body
        (eff_inst nb ts os.res) (ren_ty (shift nb) r) ->
      clauses_typing sg ln g ei ts r b cs ->
      clauses_typing sg ln g ei ts r b (CFast op nb s body :: cs)
