(* A condition of `sig_ok` quantifies over every name. For `good_sig`,
   each recorded name has a closed entry whose condition holds by
   normalization, and every other name has no entry. A `bad_*` signature
   fails the condition at one name, which normalization shows. *)
module Stella.Core.Sig.Examples
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
module L = FStar.List.Tot

(* * `good_sig` *)

let good_tycons_wf () : Lemma (tycons_wf good_sig) =
  assert_norm (tycon_ok { tc_nk = 0;
                          tc_kind = KArrow KType (KArrow (KRow EEffect) (KArrow KType KType));
                          tc_class = TcIntrinsic ClsFunction });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KArrow (KRow EType) KType;
                          tc_class = TcIntrinsic ClsRecord });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KArrow (KRow EType) KType;
                          tc_class = TcIntrinsic ClsVariant });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KType; tc_class = TcIntrinsic ClsLiteral });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KArrow KType KType; tc_class = TcIntrinsic ClsOpaque });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KType; tc_class = TcData [prim_unit_ctor] });
  assert_norm (tycon_ok list_info);
  assert_norm (tycon_ok proxy_info);
  assert_norm (tycon_ok task_info)

let good_effects_wf () : Lemma (effects_wf good_sig) = assert_norm (effect_ok good_sig console_info)

let good_ctors_wf () : Lemma (ctors_wf good_sig) =
  assert_norm (scheme_ok good_sig unit_info.ct_nk unit_info.ct_ty);
  assert_norm (scheme_ok good_sig nil_info.ct_nk nil_info.ct_ty);
  assert_norm (scheme_ok good_sig cons_info.ct_nk cons_info.ct_ty);
  assert_norm (scheme_ok good_sig mkproxy_info.ct_nk mkproxy_info.ct_ty);
  assert_norm (scheme_ok good_sig mktask_info.ct_nk mktask_info.ct_ty)

let good_foreigns_wf () : Lemma (foreigns_wf good_sig) =
  assert_norm (scheme_ok good_sig length_info.fr_nk length_info.fr_ty)

let good_globals_disjoint () : Lemma (globals_disjoint good_sig) =
  assert_norm (good_foreigns prim_unit_ctor == None);
  assert_norm (good_foreigns (base "Nil") == None);
  assert_norm (good_foreigns (base "Cons") == None);
  assert_norm (good_foreigns (base "MkProxy") == None);
  assert_norm (good_foreigns (base "MkTask") == None)

let good_sig_wf () : Lemma (sig_wf good_sig) =
  good_tycons_wf ();
  good_effects_wf ();
  good_ctors_wf ();
  good_foreigns_wf ();
  good_globals_disjoint ()

let good_prim_wf () : Lemma (prim_wf good_sig) =
  assert_norm (prim_tycon good_sig prim_function
                 (KArrow KType (KArrow (KRow EEffect) (KArrow KType KType))) (TcIntrinsic ClsFunction));
  assert_norm (prim_tycon good_sig prim_record (KArrow (KRow EType) KType) (TcIntrinsic ClsRecord));
  assert_norm (prim_tycon good_sig prim_variant (KArrow (KRow EType) KType) (TcIntrinsic ClsVariant));
  assert_norm (prim_tycon good_sig prim_int KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon good_sig prim_number KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon good_sig prim_string KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon good_sig prim_char KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon good_sig prim_boolean KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon good_sig prim_io (KArrow KType KType) (TcIntrinsic ClsOpaque));
  assert_norm (prim_tycon good_sig prim_unit KType (TcData [prim_unit_ctor]));
  assert_norm (good_sig.ctors prim_unit_ctor == Some unit_info)

let good_ctors_ok () : Lemma (ctors_ok good_sig) =
  assert_norm (ctor_ok good_sig prim_unit_ctor unit_info);
  assert_norm (ctor_ok good_sig (base "Nil") nil_info);
  assert_norm (ctor_ok good_sig (base "Cons") cons_info);
  assert_norm (ctor_ok good_sig (base "MkProxy") mkproxy_info);
  assert_norm (ctor_ok good_sig (base "MkTask") mktask_info)

let good_datas_ok () : Lemma (datas_ok good_sig) =
  assert_norm (data_ok good_sig prim_unit [prim_unit_ctor]);
  assert_norm (data_ok good_sig (base "List") [base "Nil"; base "Cons"]);
  assert_norm (data_ok good_sig (base "Proxy") [base "MkProxy"]);
  assert_norm (data_ok good_sig (base "Task") [base "MkTask"])

let good_foreigns_pure () : Lemma (foreigns_pure good_sig) =
  assert_norm (arrows_pure length_info.fr_ty)

let good_globals_ok () : Lemma (globals_ok good_sig) =
  good_ctors_ok ();
  good_datas_ok ();
  good_foreigns_pure ()

let good_sig_ok () =
  good_sig_wf ();
  good_prim_wf ();
  good_globals_ok ()

(* * Rejected signatures *)

let reject_ctor (sg: sig) (c: qname) (ci: ctor_info)
  : Lemma (requires sg.ctors c == Some ci /\ not (ctor_ok sg c ci)) (ensures ~(sig_ok sg)) =
  introduce sig_ok sg ==> False
  with assert (match sg.ctors c with Some ci -> ctor_ok sg c ci | None -> True)

let reject_data (sg: sig) (q: qname) (ti: tycon_info) (cs: list qname)
  : Lemma (requires sg.tycons q == Some ti /\ ti.tc_class == TcData cs /\ not (data_ok sg q cs))
          (ensures ~(sig_ok sg)) =
  introduce sig_ok sg ==> False
  with assert (match sg.tycons q with
                  | Some ti -> (match ti.tc_class with TcData cs -> data_ok sg q cs | TcIntrinsic _ -> True)
                  | None -> True)

let reject_foreign (sg: sig) (q: qname) (fi: foreign_info)
  : Lemma (requires sg.foreigns q == Some fi /\ not (arrows_pure fi.fr_ty)) (ensures ~(sig_ok sg)) =
  introduce sig_ok sg ==> False
  with assert (match sg.foreigns q with Some fi -> arrows_pure fi.fr_ty | None -> True)

let bad_result_rejected () =
  assert_norm (bad_result.ctors (base "C") == Some c_info);
  assert_norm (not (ctor_ok bad_result (base "C") c_info));
  reject_ctor bad_result (base "C") c_info

let bad_absent_rejected () =
  let cs = [base "Nil"; base "Cons"; base "Snoc"] in
  assert_norm (bad_absent.tycons (base "List") == Some list_snoc_info);
  assert_norm (list_snoc_info.tc_class == TcData [base "Nil"; base "Cons"; base "Snoc"]);
  assert_norm (not (data_ok bad_absent (base "List") [base "Nil"; base "Cons"; base "Snoc"]));
  reject_data bad_absent (base "List") list_snoc_info cs

let bad_unlisted_rejected () =
  assert_norm (bad_unlisted.ctors (base "Extra") == Some extra_info);
  assert_norm (not (ctor_ok bad_unlisted (base "Extra") extra_info));
  reject_ctor bad_unlisted (base "Extra") extra_info

let bad_arity_rejected () =
  assert_norm (bad_arity.ctors (base "Cons") == Some cons_arity_info);
  assert_norm (not (ctor_ok bad_arity (base "Cons") cons_arity_info));
  reject_ctor bad_arity (base "Cons") cons_arity_info

let bad_tag_rejected () =
  assert_norm (bad_tag.tycons (base "List") == Some list_info);
  assert_norm (list_info.tc_class == TcData [base "Nil"; base "Cons"]);
  assert_norm (not (data_ok bad_tag (base "List") [base "Nil"; base "Cons"]));
  reject_data bad_tag (base "List") list_info [base "Nil"; base "Cons"]

let bad_ctor_effect_rejected () =
  assert_norm (bad_ctor_effect.ctors (base "Cons") == Some cons_effect_info);
  assert_norm (not (ctor_ok bad_ctor_effect (base "Cons") cons_effect_info));
  reject_ctor bad_ctor_effect (base "Cons") cons_effect_info

let bad_foreign_effect_rejected () =
  assert_norm (bad_foreign_effect.foreigns (base "print") == Some print_info);
  assert_norm (not (arrows_pure print_info.fr_ty));
  reject_foreign bad_foreign_effect (base "print") print_info

let bad_foreign_arg_rejected () =
  assert_norm (bad_foreign_arg.foreigns (base "apply") == Some apply_info);
  assert_norm (not (arrows_pure apply_info.fr_ty));
  reject_foreign bad_foreign_arg (base "apply") apply_info
