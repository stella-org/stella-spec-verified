module Stella.Core.Typing.Cut
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Kinding.Subst
open Stella.Core.Subst.Lemmas.Tm
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Weaken
module L = FStar.List.Tot

(* `ctx_weaker (add_assumps g cs) g` is all that is proved here; the
   typing judgement is then the identity term renaming, via
   `typing_weaken_ext` for terms and `dt_typing_ren_tm` for trees. *)

let ctx_weaker_cut g cs =
  let g0 = add_assumps g cs in
  introduce forall (h: constr). L.mem h (hyps g0) ==> entails (hyps g) h
  with introduce _ ==> _
  with (mem_hyps_add_assumps g cs h;
        if L.mem h (hyps g) then entails_hyp (hyps g) h);
  rdom_add_assumps g cs

let typing_cut #sg #ln #g #c #d #e #t #r h =
  add_assump_assumps g c;
  ctx_weaker_cut g [c];
  typing_weaken_ext h g

let typing_cut_all #sg #ln #g #cs #d #e #t #r h =
  ctx_weaker_cut g cs;
  typing_weaken_ext h g

let ren_tm_dt_id (dt: dtree) : Lemma (ren_tm_dt id_ren dt == dt) =
  rinst_tm_dt id_ren evar dt;
  sub_id_tm_dt evar dt

let dt_typing_cut_all' (#sg: sig) (#ln: lctx) (#g: ctx) (#cs: list constr) (#d: jctx)
  (#om: octx) (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln (add_assumps g cs) d om dt t r)
  : Pure (dt_typing sg ln g d om dt t r)
         (requires forall (c: constr). L.mem c cs ==> entails (hyps g) c)
         (ensures fun _ -> True) =
  ctx_weaker_cut g cs;
  tm_ren_ok_id (add_assumps g cs) g;
  ren_tm_dt_id dt;
  dt_typing_ren_tm h id_ren g

let dt_typing_cut #sg #ln #g #c #d #om #dt #t #r h =
  add_assump_assumps g c;
  dt_typing_cut_all' #sg #ln #g #[c] h

let dt_typing_cut_all #sg #ln #g #cs #d #om #dt #t #r h = dt_typing_cut_all' h
