module Stella.Core.Safety.Hidden
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Closed
open Stella.Core.Typing.Plug
open Stella.Core.Typing.Occ
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
module L = FStar.List.Tot
module V = Stella.Core.Value

let sok_intro sg = reveal_opaque (`%sok) (sok sg)

let sok_elim sg = reveal_opaque (`%sok) (sok sg)

let env_ok_intro sg gi ln rs = reveal_opaque (`%env_ok) (env_ok sg gi ln rs)

let env_ok_elim sg gi ln rs =
  reveal_opaque (`%env_ok) (env_ok sg gi ln rs);
  rctx_ok_wf_ctx sg rs;
  closed_ctx_consistent rs

let env_ok_sok sg gi ln rs =
  env_ok_elim sg gi ln rs;
  sok_intro sg

let retm #sg #ln #g #d #e #t #r h e2 = h

let plug1_typing_h #sg #ln #g #d #f #e #t #r h =
  sok_elim sg;
  plug1_typing #sg #ln #g #d #f #e #t #r h

let tl_typing_h #sg #ln #g #d #fs #e #t #r h =
  sok_elim sg;
  tl_typing #sg #ln #g #d #fs #e #t #r h

let foreign_redex_typed_h #sg #ln #g #d #e #t #r h s th =
  sok_elim sg;
  foreign_redex_typed h s th

let occ_sound_h #sg #ln #g #r #th #om #o #t_o hm ho =
  sok_elim sg;
  occ_sound hm ho
