(**
 * Evaluation contexts (spec 06 §Evaluation contexts).
 *
 * An evaluation context `Ev` is a list of frames, innermost first: `[]` is
 * the hole, and `f :: fs` is `fs` around `f` around the hole, so
 * `plug (f :: fs) e = plug fs (plug1 f e)`. Each frame is one production of
 * the spec's grammar
 *
 *     Ev ::= [] | e Ev | Ev v | Ev [τ] | Ev [•]
 *          | openEff [ρ] Ev | openEffC [ρ] Ev
 *          | extend k Ev e | extend k v Ev | update k Ev e | update k v Ev
 *          | merge Ev e | merge v Ev | select k Ev | restrict k Ev
 *          | inject k [ρ] Ev | weaken k [τ] Ev | absurd [τ] Ev
 *          | let x : τ = Ev in e | case (v̄, Ev, ē) of dt
 *          | match θ (guard Ev dt1 dt2)
 *          | letjoin j (x̄ : τ̄) : τ = e1 in Ev | jump j (v̄, Ev, ē)
 *          | perform k.op [τ̄] Ev | handle Ev with h
 *          | region [ℓ] ( k̄ : σ̄ ) @ ( v̄, Ev, ē ) in e | region⟨ℓ⟩ θ in Ev
 *          | writeCell ℓ.k Ev | fill ν Ev
 *
 * with the AST's own representation of each form (`Stella.Core.Syntax`).
 * A frame stores the parts of its production other than the hole. The
 * positions the production writes as values (`v`, `v̄`, and the values
 * `θ` of `match` and of an open region) hold arbitrary terms in `frame`,
 * and `frame_ok` says that they are values.
 *
 * Application evaluates the argument before the function (D35): `e Ev`
 * puts the hole in the argument with any function, and `Ev v` in the
 * function once the argument is a value. The lists of `case`, `jump` and
 * `region` are evaluated left to right, the values `v̄` standing before the
 * hole.
 *
 * No frame stands under a binder of the term: the hole of `let` is its
 * bound side, that of `region` an initial value, and that of `letjoin` its
 * continuation, under the join binder only. So the hole of an evaluation
 * context of a closed term is closed in its term variables.
 *
 * Three restrictions select sub-grammars:
 *
 *   - `tl_frames fs`: every frame is a `letjoin` continuation, the tail
 *     contexts `Tl ::= [] | letjoin j' (x̄ : τ̄) : τ = e' in Tl` of spec 06
 *     §Evaluation contexts, through which a `jump` reaches its join point;
 *   - `ev_k k fs`: no `handle` frame has a handler of key `k` (`Ev_k`);
 *   - `ev_l a fs`: no open region frame is named `a` (`Ev_ℓ`).
 *)
module Stella.Core.Semantics.Ctx
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Rows
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Frames *)

type frame =
  | FAppArg     : fn:exp -> frame                                  (** e Ev *)
  | FAppFun     : arg:exp -> frame                                 (** Ev v *)
  | FTyApp      : typ -> frame                                     (** Ev [τ] *)
  | FCApp       : frame                                            (** Ev [•] *)
  | FOpenEff    : typ -> frame                                     (** openEff [ρ] Ev *)
  | FOpenEffC   : typ -> frame                                     (** openEffC [ρ] Ev *)
  | FExtendL    : key -> rest:exp -> frame                         (** extend k Ev e *)
  | FExtendR    : key -> hd:exp -> frame                           (** extend k v Ev *)
  | FUpdateL    : key -> nv:exp -> frame                           (** update k Ev e *)
  | FUpdateR    : key -> rcd:exp -> frame                          (** update k v Ev *)
  | FMergeL     : rhs:exp -> frame                                 (** merge Ev e *)
  | FMergeR     : lhs:exp -> frame                                 (** merge v Ev *)
  | FSelect     : key -> frame                                     (** select k Ev *)
  | FRestrict   : key -> frame                                     (** restrict k Ev *)
  | FInject     : key -> typ -> frame                              (** inject k [ρ] Ev *)
  | FWeaken     : key -> typ -> frame                              (** weaken k [τ] Ev *)
  | FAbsurd     : typ -> frame                                     (** absurd [τ] Ev *)
  | FLet        : typ -> body:exp -> frame                         (** let x : τ = Ev in e *)
  | FCase       : vs:list exp -> es:list exp -> dtree -> frame     (** case (v̄, Ev, ē) of dt *)
  | FGuard      : th:list exp -> dtree -> dtree -> frame           (** match θ (guard Ev dt1 dt2) *)
  | FLetJoin    : list typ -> typ -> def:exp -> frame              (** letjoin j (x̄ : τ̄) : τ = e1 in Ev *)
  | FJump       : nat -> vs:list exp -> es:list exp -> frame       (** jump j (v̄, Ev, ē) *)
  | FPerform    : key -> opname -> list typ -> frame               (** perform k.op [τ̄] Ev *)
  | FHandle     : handler -> frame                                 (** handle Ev with h *)
  | FRegion     : list (key & typ) -> vs:list exp -> es:list exp -> body:exp -> frame
                                                       (** region [ℓ] ( k̄ : σ̄ ) @ ( v̄, Ev, ē ) in e *)
  | FRegionOpen : atom -> cells:list (key & exp) -> frame          (** region⟨ℓ⟩ θ in Ev *)
  | FWriteCell  : region_ref -> key -> frame                       (** writeCell ℓ.k Ev *)
  | FFill       : atom -> frame                                    (** fill ν Ev *)

(** Every cell of an open region holds a value. *)
let rec cells_values (sg: sig) (th: list (key & exp)) : Tot bool (decreases th) =
  match th with
  | [] -> true
  | (_, v) :: th -> V.is_value sg v && cells_values sg th

(** The positions that the production of `f` writes as values hold
    values. *)
let frame_ok (sg: sig) (f: frame) : bool =
  match f with
  | FAppFun v | FExtendR _ v | FUpdateR _ v | FMergeR v -> V.is_value sg v
  | FCase vs _ _ | FJump _ vs _ | FRegion _ vs _ _ -> L.for_all (V.is_value sg) vs
  | FGuard th _ _ -> L.for_all (V.is_value sg) th
  | FRegionOpen _ th -> cells_values sg th
  | _ -> true

let frames_ok (sg: sig) (fs: list frame) : bool = L.for_all (frame_ok sg) fs

(** * Plugging *)

(** `f[e]`, the frame `f` with `e` in its hole. *)
let plug1 (f: frame) (e: exp) : exp =
  match f with
  | FAppArg e1 -> EApp e1 e
  | FAppFun v -> EApp e v
  | FTyApp t -> ETyApp e t
  | FCApp -> ECApp e
  | FOpenEff r -> EOpenEff r e
  | FOpenEffC r -> EOpenEffC r e
  | FExtendL k e2 -> EExtend k e e2
  | FExtendR k v1 -> EExtend k v1 e
  | FUpdateL k e2 -> EUpdate k e e2
  | FUpdateR k v1 -> EUpdate k v1 e
  | FMergeL e2 -> EMerge e e2
  | FMergeR v1 -> EMerge v1 e
  | FSelect k -> ESelect k e
  | FRestrict k -> ERestrict k e
  | FInject k r -> EInject k r e
  | FWeaken k t -> EWeaken k t e
  | FAbsurd t -> EAbsurd t e
  | FLet t e2 -> ELet t e e2
  | FCase vs es dt -> ECase (L.append vs (e :: es)) dt
  | FGuard th dt1 dt2 -> EMatch th (DGuard e dt1 dt2)
  | FLetJoin ts t e1 -> ELetJoin ts t e1 e
  | FJump j vs es -> EJump j (L.append vs (e :: es))
  | FPerform k op ts -> EPerform k op ts e
  | FHandle h -> EHandle e h
  | FRegion lay vs es body -> ERegion lay (L.append vs (e :: es)) body
  | FRegionOpen a th -> ERegionOpen a th e
  | FWriteCell rr k -> EWriteCell rr k e
  | FFill nu -> EFill nu e

(** `Ev[e]` for `Ev` given innermost frame first. *)
let rec plug (fs: list frame) (e: exp) : Tot exp (decreases fs) =
  match fs with
  | [] -> e
  | f :: fs -> plug fs (plug1 f e)

(** Plugging into a context extended outside. *)
val plug_append (fs1 fs2: list frame) (e: exp)
  : Lemma (plug (L.append fs1 fs2) e == plug fs2 (plug fs1 e))

(** In particular, extended by one frame, plugging into the outermost
    frame. *)
val plug_snoc (fs: list frame) (f: frame) (e: exp)
  : Lemma (plug (L.append fs [f]) e == plug1 f (plug fs e))

(** * Values *)

(** A frame around a non-value is a non-value; equivalently, the hole of
    a frame a value is plugged from holds a value. The frames whose
    plugged term can be a value are those of a chain (`e Ev`, `Ev v`,
    `Ev [τ]`, `Ev [•]`), of `extend`, `inject`, `weaken` and `openEff`.
    The hole of `e Ev` is a value argument of the chain, and that of the
    other four forms a part the value grammar asks to be a value. The
    hole of `Ev v`, `Ev [τ]` and `Ev [•]` is a prefix of the
    chain: a constructor's chain is a value at every length, and a
    prefix of an unsaturated foreign's chain is unsaturated, since a
    saturated remainder consumes no further argument. *)
val plug1_not_value (sg: sig) (f: frame) (e: exp)
  : Lemma (requires not (V.is_value sg e)) (ensures not (V.is_value sg (plug1 f e)))

(** * Sub-grammars *)

let is_letjoin_frame (f: frame) : bool = FLetJoin? f

(** `Tl`: only `letjoin` continuation frames. *)
let tl_frames (fs: list frame) : bool = L.for_all is_letjoin_frame fs

(** The key of the element a handler removes. *)
let handler_key (h: handler) : key = ent_key h.h_ent

(** `f` is no `handle` frame for the key `k`. *)
let not_handle_of (k: key) (f: frame) : bool =
  match f with
  | FHandle h -> handler_key h <> k
  | _ -> true

(** `Ev_k`: no `handle` frame on the path to the hole has the key `k`. *)
let ev_k (k: key) (fs: list frame) : bool = L.for_all (not_handle_of k) fs

(** `f` is no open region frame named `a`. *)
let not_region_of (a: atom) (f: frame) : bool =
  match f with
  | FRegionOpen a' _ -> a' <> a
  | _ -> true

(** `Ev_ℓ`: no open region frame on the path to the hole is named `a`. *)
let ev_l (a: atom) (fs: list frame) : bool = L.for_all (not_region_of a) fs
