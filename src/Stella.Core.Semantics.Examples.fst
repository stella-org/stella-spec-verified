(* Each step is built from its rule, whose conclusion is stated with the
   operations of the rule (substitution, plugging, `foreign_config`); the
   closed facts it needs, and the equation between that conclusion and the
   term written in the interface, hold by normalization.

   `sig_ok ex_sig` is checked one table at a time, each closed fact by
   normalization. Conformance is shown before any region or location
   (`genv_ok_closed`). The polymorphic foreigns share one shape,
   `forall (a : Type). A -> B` with `B` saturated, so a saturated chain of
   one is `[τ] v` and its cursor instance is `B` under `τ` (`sat_poly`);
   the outcome of each adapter is then typed at that instance, a literal
   by the literal rule, `opaque ω [IO τ]` by the opaque rule with the
   kinding of `IO τ` read off the call (`typed_kinded`), `Nil [τ]` as a
   chain with the kinding of `τ` read off that of `List τ`, and the
   argument of `ident` from the domains of the call's chain
   (`ident_arg_typed`). Lemmas reading `sig_ok` are stated over an
   arbitrary signature, so that `sig_ok ex_sig` is never unfolded beside a
   goal on `ex_sig`.

   A non-conforming environment is refuted at the empty contexts: its
   condition (3) is instantiated at a typed call built by hand, whose
   cursor and instance are computed by normalization. *)
module Stella.Core.Semantics.Examples
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Kinst
open Stella.Core.Typing.Chain
open Stella.Core.Typing.Ctor
open Stella.Core.Sig.Examples
open Stella.Core.Erase
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module I32 = FStar.Int32
module V = Stella.Core.Value
module R = Stella.Core.Typing.Regularity

(* * sig_ok *)

let ex_tycons_wf () : Lemma (tycons_wf ex_sig) =
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

let ex_effects_wf () : Lemma (effects_wf ex_sig) = assert_norm (effect_ok ex_sig console_info)

let ex_ctors_wf () : Lemma (ctors_wf ex_sig) =
  assert_norm (scheme_ok ex_sig unit_info.ct_nk unit_info.ct_ty);
  assert_norm (scheme_ok ex_sig nil_info.ct_nk nil_info.ct_ty);
  assert_norm (scheme_ok ex_sig cons_info.ct_nk cons_info.ct_ty);
  assert_norm (scheme_ok ex_sig mkproxy_info.ct_nk mkproxy_info.ct_ty);
  assert_norm (scheme_ok ex_sig mktask_info.ct_nk mktask_info.ct_ty)

let ex_foreigns_wf () : Lemma (foreigns_wf ex_sig) =
  assert_norm (scheme_ok ex_sig length_info.fr_nk length_info.fr_ty);
  assert_norm (scheme_ok ex_sig boom_info.fr_nk boom_info.fr_ty);
  assert_norm (scheme_ok ex_sig pure_info.fr_nk pure_info.fr_ty);
  assert_norm (scheme_ok ex_sig mknil_info.fr_nk mknil_info.fr_ty);
  assert_norm (scheme_ok ex_sig ident_info.fr_nk ident_info.fr_ty);
  assert_norm (scheme_ok ex_sig leak_info.fr_nk leak_info.fr_ty)

let ex_values_wf () : Lemma (values_wf ex_sig) =
  assert_norm (scheme_ok ex_sig one_info.vl_nk one_info.vl_ty);
  assert_norm (scheme_ok ex_sig missing_info.vl_nk missing_info.vl_ty)

let ex_globals_disjoint () : Lemma (globals_disjoint ex_sig) =
  assert_norm (ex_sig.foreigns prim_unit_ctor == None);
  assert_norm (ex_sig.foreigns (base "Nil") == None);
  assert_norm (ex_sig.foreigns (base "Cons") == None);
  assert_norm (ex_sig.foreigns (base "MkProxy") == None);
  assert_norm (ex_sig.foreigns (base "MkTask") == None);
  assert_norm (ex_sig.values prim_unit_ctor == None);
  assert_norm (ex_sig.values (base "Nil") == None);
  assert_norm (ex_sig.values (base "Cons") == None);
  assert_norm (ex_sig.values (base "MkProxy") == None);
  assert_norm (ex_sig.values (base "MkTask") == None);
  assert_norm (ex_sig.values (base "length") == None);
  assert_norm (ex_sig.values (base "boom") == None);
  assert_norm (ex_sig.values (base "pure") == None);
  assert_norm (ex_sig.values (base "mkNil") == None);
  assert_norm (ex_sig.values (base "ident") == None);
  assert_norm (ex_sig.values (base "leak") == None)

let ex_prim_wf () : Lemma (prim_wf ex_sig) =
  assert_norm (prim_tycon ex_sig prim_function
                 (KArrow KType (KArrow (KRow EEffect) (KArrow KType KType))) (TcIntrinsic ClsFunction));
  assert_norm (prim_tycon ex_sig prim_record (KArrow (KRow EType) KType) (TcIntrinsic ClsRecord));
  assert_norm (prim_tycon ex_sig prim_variant (KArrow (KRow EType) KType) (TcIntrinsic ClsVariant));
  assert_norm (prim_tycon ex_sig prim_int KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_number KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_string KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_char KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_boolean KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_io (KArrow KType KType) (TcIntrinsic ClsOpaque));
  assert_norm (prim_tycon ex_sig prim_unit KType (TcData [prim_unit_ctor]));
  assert_norm (ex_sig.ctors prim_unit_ctor == Some unit_info)

let ex_globals_ok () : Lemma (globals_ok ex_sig) =
  assert_norm (ctor_ok ex_sig prim_unit_ctor unit_info);
  assert_norm (ctor_ok ex_sig (base "Nil") nil_info);
  assert_norm (ctor_ok ex_sig (base "Cons") cons_info);
  assert_norm (ctor_ok ex_sig (base "MkProxy") mkproxy_info);
  assert_norm (ctor_ok ex_sig (base "MkTask") mktask_info);
  assert_norm (data_ok ex_sig prim_unit [prim_unit_ctor]);
  assert_norm (data_ok ex_sig (base "List") [base "Nil"; base "Cons"]);
  assert_norm (data_ok ex_sig (base "Proxy") [base "MkProxy"]);
  assert_norm (data_ok ex_sig (base "Task") [base "MkTask"]);
  assert_norm (arrows_pure length_info.fr_ty);
  assert_norm (arrows_pure boom_info.fr_ty);
  assert_norm (arrows_pure pure_info.fr_ty);
  assert_norm (arrows_pure mknil_info.fr_ty);
  assert_norm (arrows_pure ident_info.fr_ty);
  assert_norm (arrows_pure leak_info.fr_ty)

let ex_sig_ok () =
  ex_tycons_wf (); ex_effects_wf (); ex_ctors_wf (); ex_foreigns_wf (); ex_values_wf ();
  ex_globals_disjoint (); ex_prim_wf (); ex_globals_ok ()

(* * Facts read off a signature *)

(* A foreign `forall (a : Type). A -> B` with `B` saturated: its saturated
   chains are `[τ] v`, and their cursor is `⟨ B ; τ .: id ⟩`. *)
let poly_ty (a b: typ) : typ = TForall KType (t_fun a TRowEmpty b)

#push-options "--fuel 4 --ifuel 2"
let sat_poly (sg: sig) (q: qname) (a b: typ) (ks: list kind) (args: list spine_arg)
  : Lemma (requires global_scheme sg q == Some (GForeign, 0, poly_ty a b) /\
                    kinst_ty [] (poly_ty a b) == poly_ty a b /\
                    is_function_tycon sg prim_function /\ saturated sg b /\
                    spine_saturated sg q ks args)
          (ensures (match args with
                    | [STy s; SVal _] -> ks == [] /\ spine_cursor sg q ks args == Some (b, scons s tvar)
                    | _ -> False)) =
  as_function_fun_ty sg prim_function a TRowEmpty b;
  match args with
  | [] -> ()
  | [_] -> ()
  | [_; _] -> ()
  | x :: y :: z :: _ ->
    (match x, y with
     | STy s, SVal _ ->
       assert (cursor sg (poly_ty a b) tvar [x; y] == Some (b, scons s tvar));
       assert (cursor_step sg b (scons s tvar) z == None)
     | _ -> ())

(* The domains of a chain `[τ] v` of such a foreign. *)
let poly_domains (sg: sig) (q: qname) (a b: typ) (e: exp) (s: typ) (v: exp)
  : Lemma (requires global_scheme sg q == Some (GForeign, 0, poly_ty a b) /\
                    kinst_ty [] (poly_ty a b) == poly_ty a b /\
                    is_function_tycon sg prim_function /\
                    decompose_global_app e == Some (q, [], [STy s; SVal v]))
          (ensures chain_domains sg e == [sub_ty (scons s tvar) a] /\ chain_value_args e == [v]) =
  as_function_fun_ty sg prim_function a TRowEmpty b
#pop-options

(* The type of a typed term is kinded. *)
let typed_kinded (sg: sig) (ln: lctx) (rs: list (atom & layout)) (e: exp) (t: typ)
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ typed sg ln (closed_ctx rs) e t)
          (ensures check sg (closed_ctx rs) t KType) =
  rctx_ok_wf_ctx sg rs;
  eliminate exists (h: typing sg ln (closed_ctx rs) [] e t TRowEmpty). True
  with R.typing_regular h

(* The value argument of a typed chain `[τ] v` has the domain it meets. *)
let arg_typed (sg: sig) (ln: lctx) (g: ctx) (e: exp) (v: exp) (t t1: typ)
  : Lemma (requires sig_ok sg /\ Some? (decompose_global_app e) /\ Some? (chain_cursor sg e) /\
                    chain_domains sg e == [t1] /\ chain_value_args e == [v] /\
                    typed sg ln g e t)
          (ensures typed sg ln g v t1) =
  eliminate exists (h: typing sg ln g [] e t TRowEmpty). True
  with (
    let hc = chain_normal h in
    let hd = chain_typing_domains hc in
    let hv = exps_typing_nth hd 0 v t1 in
    introduce exists (h': typing sg ln g [] v t1 TRowEmpty). True with hv and ()
  )

let ex_typed_kinded (ln: lctx) (rs: list (atom & layout)) (e: exp) (t: typ)
  : Lemma (requires rctx_ok ex_sig rs /\ typed ex_sig ln (closed_ctx rs) e t)
          (ensures check ex_sig (closed_ctx rs) t KType) =
  ex_sig_ok (); typed_kinded ex_sig ln rs e t

let ex_arg_typed (ln: lctx) (g: ctx) (e: exp) (v: exp) (t t1: typ)
  : Lemma (requires Some? (decompose_global_app e) /\ Some? (chain_cursor ex_sig e) /\
                    chain_domains ex_sig e == [t1] /\ chain_value_args e == [v] /\
                    typed ex_sig ln g e t)
          (ensures typed ex_sig ln g v t1) =
  ex_sig_ok (); arg_typed ex_sig ln g e v t t1

(* * Building derivations *)

let chain_head (ln: lctx) (g: ctx) (q: qname)
  : Pure (chain_typing ex_sig ln g [] TRowEmpty (EGlobal q []))
         (requires (match global_scheme ex_sig q with Some (_, nk, _) -> nk == 0 | None -> False))
         (ensures fun _ -> True) =
  match global_scheme ex_sig q with
  | Some (c, nk, t) -> TS_Head #ex_sig #ln #g #[] #TRowEmpty #q #[] #c #nk #t () () ()

let chain_ty (#ln: lctx) (#g: ctx) (#e: exp) (s: typ) (h: chain_typing ex_sig ln g [] TRowEmpty e)
  : Pure (chain_typing ex_sig ln g [] TRowEmpty (ETyApp e s))
         (requires (match chain_cursor ex_sig e with
                    | Some (TForall k _, _) -> check ex_sig g s k
                    | _ -> False))
         (ensures fun _ -> True) =
  match chain_cursor ex_sig e with
  | Some (TForall k t, th) -> TS_Ty #ex_sig #ln #g #[] #TRowEmpty #e #s #k #t #th h () ()

let chain_val (#ln: lctx) (#g: ctx) (#e: exp) (#v: exp) (t1: typ)
  (h: chain_typing ex_sig ln g [] TRowEmpty e) (hv: typing ex_sig ln g [] v t1 TRowEmpty)
  : Pure (chain_typing ex_sig ln g [] TRowEmpty (EApp e v))
         (requires (match chain_cursor ex_sig e with
                    | Some (t, th) ->
                      (match as_function ex_sig t with
                       | Some (a, _, _) -> sub_ty th a == t1
                       | None -> False)
                    | None -> False))
         (ensures fun _ -> True) =
  match chain_cursor ex_sig e with
  | Some (t, th) ->
    (match as_function ex_sig t with
     | Some (a, ra, b) -> TS_Val #ex_sig #ln #g #[] #TRowEmpty #e #v #t #th #a #ra #b h () hv)

let chain_typed (#ln: lctx) (#g: ctx) (#e: exp) (t: typ) (h: chain_typing ex_sig ln g [] TRowEmpty e)
  : Pure (typing ex_sig ln g [] e t TRowEmpty)
         (requires (match chain_cursor ex_sig e with
                    | Some (s, th) -> sub_ty th s == t
                    | None -> False))
         (ensures fun _ -> True) =
  match chain_cursor ex_sig e with
  | Some (s, th) -> T_Chain #ex_sig #ln #g #[] #e #s #th #TRowEmpty h ()

let typed_intro (ln: lctx) (g: ctx) (e: exp) (t: typ) (h: typing ex_sig ln g [] e t TRowEmpty)
  : Lemma (typed ex_sig ln g e t) =
  introduce exists (h': typing ex_sig ln g [] e t TRowEmpty). True with h and ()

let list_ty_kinded (g: ctx) (s: typ)
  : Lemma (requires check ex_sig g (list_ty s) KType) (ensures check ex_sig g s KType) =
  assert_norm (synth_kind ex_sig g (TCon (base "List") []) == Some (KArrow KType KType))

(* `Nil [τ] : List τ` *)
let nil_typed (ln: lctx) (g: ctx) (s: typ)
  : Lemma (requires check ex_sig g s KType)
          (ensures V.is_value ex_sig (nil_at s) /\ typed ex_sig ln g (nil_at s) (list_ty s)) =
  assert_norm (match global_scheme ex_sig (base "Nil") with
               | Some (_, nk, _) -> nk == 0
               | None -> False);
  let h0 = chain_head ln g (base "Nil") in
  assert_norm (match chain_cursor ex_sig (EGlobal (base "Nil") []) with
               | Some (TForall k _, _) -> k == KType
               | _ -> False);
  let h1 = chain_ty s h0 in
  assert_norm (match chain_cursor ex_sig (nil_at s) with
               | Some (s', th) -> sub_ty th s' == list_ty s
               | None -> False);
  typed_intro ln g (nil_at s) (list_ty s) (chain_typed (list_ty s) h1);
  assert_norm (V.is_value ex_sig (nil_at s))

(* `opaque ω [IO τ] : IO τ` *)
let opaque_io_typed (ln: lctx) (g: ctx) (w: nat) (s: typ)
  : Lemma (requires check ex_sig g (io_ty s) KType)
          (ensures typed ex_sig ln g (EOpaque w (io_ty s)) (io_ty s)) =
  assert_norm (opaque_type ex_sig (io_ty s));
  typed_intro ln g (EOpaque w (io_ty s)) (io_ty s)
    (T_Opaque #ex_sig #ln #g #[] #w #(io_ty s) #TRowEmpty () ())

let lit_typed (ln: lctx) (g: ctx) (c: lit)
  : Lemma (V.is_value ex_sig (ELit c) /\ typed ex_sig ln g (ELit c) (lit_type c)) =
  typed_intro ln g (ELit c) (lit_type c) (T_Lit #ex_sig #ln #g #[] #c #TRowEmpty ())

(* * Conformance *)

let length_q : qname = base "length"
let boom_q : qname = base "boom"
let pure_q : qname = base "pure"
let mknil_q : qname = base "mkNil"
let ident_q : qname = base "ident"
let leak_q : qname = base "leak"
let one_q : qname = base "one"

let poly_facts (q: qname) (fi: foreign_info) (a b: typ)
  : Lemma (requires ex_sig.foreigns q == Some fi /\ fi.fr_nk == 0 /\ fi.fr_ty == poly_ty a b /\
                    ex_sig.ctors q == None /\ ex_sig.values q == None /\
                    kinst_ty [] (poly_ty a b) == poly_ty a b)
          (ensures global_scheme ex_sig q == Some (GForeign, 0, poly_ty a b) /\
                   is_function_tycon ex_sig prim_function) =
  assert_norm (is_function_tycon ex_sig prim_function)

(* The shape of a typed saturated call of a polymorphic foreign `q`. *)
let poly_call (q: qname) (fi: foreign_info) (a b: typ) (e: exp) (t: typ) (th: tsub)
  (ks: list kind) (args: list spine_arg)
  : Lemma (requires ex_sig.foreigns q == Some fi /\ fi.fr_nk == 0 /\ fi.fr_ty == poly_ty a b /\
                    ex_sig.ctors q == None /\ ex_sig.values q == None /\
                    kinst_ty [] (poly_ty a b) == poly_ty a b /\ saturated ex_sig b /\
                    chain_cursor ex_sig e == Some (t, th) /\
                    decompose_global_app e == Some (q, ks, args) /\ V.foreign_redex ex_sig e)
          (ensures (match args with
                    | [STy s; SVal v] ->
                      ks == [] /\ t == b /\ th == scons s tvar /\
                      chain_instance e == { inst_kinds = []; inst_types = [s] } /\
                      value_args args == [v] /\ V.is_value ex_sig v /\
                      chain_domains ex_sig e == [sub_ty (scons s tvar) a] /\
                      chain_value_args e == [v]
                    | _ -> False)) =
  poly_facts q fi a b;
  sat_poly ex_sig q a b ks args;
  match args with
  | [STy s; SVal v] ->
    V.chain_values_view ex_sig e;
    poly_domains ex_sig q a b e s v
  | _ -> ()

let length_call_ok (ln': lctx) (rs': list (atom & layout)) (e: exp)
  (t: typ) (th: tsub) (ks: list kind) (args: list spine_arg)
  : Lemma (requires chain_cursor ex_sig e == Some (t, th) /\
                    decompose_global_app e == Some (length_q, ks, args) /\
                    V.foreign_redex ex_sig e /\ length_pre (L.map erase (value_args args)))
          (ensures entry_call_ok ex_sig ex_genv ln' rs' length_q length_entry (chain_instance e)
                     (value_args args) (sub_ty th t)) =
  assert_norm (kinst_ty [] length_info.fr_ty == length_info.fr_ty);
  assert_norm (saturated ex_sig t_int);
  poly_call length_q length_info (list_ty (TVar 0)) t_int e t th ks args;
  match args with
  | [STy s; SVal l] ->
    assert_norm (sub_ty th t_int == t_int);
    (match ulist_len (erase l) with
     | Some n ->
       lit_typed ln' (closed_ctx rs') (len_lit n);
       assert_norm (lit_type (len_lit n) == t_int);
       assert_norm (covers_relative ex_sig ex_genv [l] (ELit (len_lit n)))
     | None -> ())

let boom_call_ok (ln': lctx) (rs': list (atom & layout)) (e: exp) (t: typ) (xi: chain_inst)
  (vs: list exp)
  : Lemma (entry_call_ok ex_sig ex_genv ln' rs' boom_q boom_entry xi vs t) =
  assert_norm (observ_none ex_sig boom_q == false)

let pure_call_ok (ln': lctx) (rs': list (atom & layout)) (e: exp)
  (t: typ) (th: tsub) (ks: list kind) (args: list spine_arg)
  : Lemma (requires chain_cursor ex_sig e == Some (t, th) /\
                    decompose_global_app e == Some (pure_q, ks, args) /\
                    V.foreign_redex ex_sig e /\ rctx_ok ex_sig rs' /\
                    typed ex_sig ln' (closed_ctx rs') e (sub_ty th t))
          (ensures entry_call_ok ex_sig ex_genv ln' rs' pure_q pure_entry (chain_instance e)
                     (value_args args) (sub_ty th t)) =
  assert_norm (kinst_ty [] pure_info.fr_ty == pure_info.fr_ty);
  assert_norm (saturated ex_sig (io_ty (TVar 0)));
  poly_call pure_q pure_info (TVar 0) (io_ty (TVar 0)) e t th ks args;
  match args with
  | [STy s; SVal v] ->
    assert_norm (sub_ty (scons s tvar) (io_ty (TVar 0)) == io_ty s);
    ex_typed_kinded ln' rs' e (io_ty s);
    opaque_io_typed ln' (closed_ctx rs') pure_payload s;
    assert_norm (V.is_value ex_sig (EOpaque pure_payload (io_ty s)));
    assert_norm (covers_relative ex_sig ex_genv [v] (EOpaque pure_payload (io_ty s)))

let mknil_call_ok (ln': lctx) (rs': list (atom & layout)) (e: exp)
  (t: typ) (th: tsub) (ks: list kind) (args: list spine_arg)
  : Lemma (requires chain_cursor ex_sig e == Some (t, th) /\
                    decompose_global_app e == Some (mknil_q, ks, args) /\
                    V.foreign_redex ex_sig e /\ rctx_ok ex_sig rs' /\
                    typed ex_sig ln' (closed_ctx rs') e (sub_ty th t))
          (ensures entry_call_ok ex_sig ex_genv ln' rs' mknil_q mknil_entry (chain_instance e)
                     (value_args args) (sub_ty th t)) =
  assert_norm (kinst_ty [] mknil_info.fr_ty == mknil_info.fr_ty);
  assert_norm (saturated ex_sig (list_ty (TVar 0)));
  poly_call mknil_q mknil_info t_unit (list_ty (TVar 0)) e t th ks args;
  match args with
  | [STy s; SVal v] ->
    assert_norm (sub_ty (scons s tvar) (list_ty (TVar 0)) == list_ty s);
    ex_typed_kinded ln' rs' e (list_ty s);
    list_ty_kinded (closed_ctx rs') s;
    nil_typed ln' (closed_ctx rs') s;
    assert_norm (covers_relative ex_sig ex_genv [v] (nil_at s))

let ident_call_ok (ln': lctx) (rs': list (atom & layout)) (e: exp)
  (t: typ) (th: tsub) (ks: list kind) (args: list spine_arg)
  : Lemma (requires chain_cursor ex_sig e == Some (t, th) /\
                    decompose_global_app e == Some (ident_q, ks, args) /\
                    V.foreign_redex ex_sig e /\
                    typed ex_sig ln' (closed_ctx rs') e (sub_ty th t))
          (ensures entry_call_ok ex_sig ex_genv ln' rs' ident_q ident_entry (chain_instance e)
                     (value_args args) (sub_ty th t)) =
  assert_norm (kinst_ty [] ident_info.fr_ty == ident_info.fr_ty);
  assert_norm (saturated ex_sig (TVar 0));
  poly_call ident_q ident_info (TVar 0) (TVar 0) e t th ks args;
  match args with
  | [STy s; SVal v] ->
    assert_norm (sub_ty (scons s tvar) (TVar 0) == s);
    ex_arg_typed ln' (closed_ctx rs') e v s s;
    covers_relative_self ex_sig ex_genv [v] v

#push-options "--fuel 1 --ifuel 1"
let call_ok (ln': lctx) (rs': list (atom & layout)) (e: exp)
  : Lemma (requires rt_ext ex_sig [] [] ln' rs')
          (ensures foreign_call_ok ex_sig ex_genv ln' rs' e) =
  match chain_cursor ex_sig e, decompose_global_app e with
  | Some (t, th), Some (q, ks, args) ->
    let ty = sub_ty th t in
    let vs = value_args args in
    let pre (fe: foreign_entry) : prop =
      V.foreign_redex ex_sig e /\ typed ex_sig ln' (closed_ctx rs') e ty /\
      fe.fe_pre (L.map erase vs) in
    if q = length_q then begin
      assert_norm (ex_genv.gforeign length_q == Some length_entry);
      introduce pre length_entry ==>
                entry_call_ok ex_sig ex_genv ln' rs' q length_entry (chain_instance e) vs ty
      with length_call_ok ln' rs' e t th ks args
    end
    else if q = boom_q then begin
      assert_norm (ex_genv.gforeign boom_q == Some boom_entry);
      boom_call_ok ln' rs' e ty (chain_instance e) vs
    end
    else if q = pure_q then begin
      assert_norm (ex_genv.gforeign pure_q == Some pure_entry);
      introduce pre pure_entry ==>
                entry_call_ok ex_sig ex_genv ln' rs' q pure_entry (chain_instance e) vs ty
      with pure_call_ok ln' rs' e t th ks args
    end
    else if q = mknil_q then begin
      assert_norm (ex_genv.gforeign mknil_q == Some mknil_entry);
      introduce pre mknil_entry ==>
                entry_call_ok ex_sig ex_genv ln' rs' q mknil_entry (chain_instance e) vs ty
      with mknil_call_ok ln' rs' e t th ks args
    end
    else if q = ident_q then begin
      assert_norm (ex_genv.gforeign ident_q == Some ident_entry);
      introduce pre ident_entry ==>
                entry_call_ok ex_sig ex_genv ln' rs' q ident_entry (chain_instance e) vs ty
      with ident_call_ok ln' rs' e t th ks args
    end
    else assert (ex_genv.gforeign q == None)
  | _ -> ()
#pop-options

let gval_one_typed () : Lemma (gval_typed ex_sig [] [] ex_genv one_q) =
  assert_norm (ex_sig.values one_q == Some one_info);
  assert_norm (ex_genv.gvals one_q == Some (lit_int 1l));
  lit_typed [] (decl_rctx 0 []) (LInt 1l)

let ex_genv_ok ln rs =
  introduce forall (rs': list (atom & layout)) (ln': lctx) (e: exp).
    rt_ext ex_sig [] [] ln' rs' ==> foreign_call_ok ex_sig ex_genv ln' rs' e
  with introduce _ ==> _ with call_ok ln' rs' e;
  introduce forall (q: qname). gval_typed ex_sig [] [] ex_genv q
  with (if q = one_q then gval_one_typed () else ());
  assert_norm (covers ex_sig ex_genv (lit_int 1l));
  assert (gvals_covered ex_sig ex_genv);
  genv_ok_closed ex_sig ex_genv ln rs

let premises_inhabited () =
  ex_sig_ok ();
  assert_norm (rctx_ok ex_sig rs1);
  assert_norm (lctx_ok ex_sig rs1 ln1);
  ex_genv_ok ln1 rs1

let retype (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#c: config)
  (e2: exp) (c2: config) (h: step ex_sig ex_genv ra st e ra' st' c)
  : Pure (step ex_sig ex_genv ra st e2 ra' st' c2) (requires e == e2 /\ c == c2)
         (ensures fun _ -> True) =
  h

(* * β *)

let beta_step =
  assert_norm (V.is_value ex_sig (lit_int 1l));
  let h = S_Pure #ex_sig #ex_genv #[] #[]
            (PH_Beta #ex_sig #ex_genv #t_int #TRowEmpty #(EVar 0) #(lit_int 1l) ()) in
  assert_norm (subst1_tm (lit_int 1l) (EVar 0) == lit_int 1l);
  retype beta_redex (CTerm (lit_int 1l)) h

let arg_first_step =
  assert_norm (V.is_value ex_sig (lit_int 2l));
  let h = S_Pure #ex_sig #ex_genv #[] #[]
            (PH_Beta #ex_sig #ex_genv #t_int #TRowEmpty #(EVar 0) #(lit_int 2l) ()) in
  let h' = S_Ctx (FAppArg id_int) () h in
  assert_norm (subst1_tm (lit_int 2l) (EVar 0) == lit_int 2l);
  retype arg_first (CTerm (EApp id_int (lit_int 2l))) h'

(* * Join points *)

let join0_step =
  assert_norm (L.for_all (V.is_value ex_sig) [lit_int 1l]);
  let h = PH_Join #ex_sig #ex_genv #[t_int] #t_int #(EVar 0) #[] #0 #[lit_int 1l] () () in
  assert_norm (ELetJoin [t_int] t_int (EVar 0) (plug [] (EJump 0 [lit_int 1l])) == join0);
  assert_norm (plug [] (sub_tm (list_esub (L.rev [lit_int 1l])) (ren_jp (shift 0) (EVar 0))) ==
               lit_int 1l);
  retype join0 (CTerm (ELetJoin [t_int] t_int (EVar 0) (lit_int 1l))) (S_Pure #_ #_ #[] #[] h)

let join1_step =
  let fs = [FLetJoin [] t_int (lit_int 0l)] in
  assert_norm (tl_frames fs);
  assert_norm (L.for_all (V.is_value ex_sig) [lit_int 5l]);
  let h = PH_Join #ex_sig #ex_genv #[t_int] #t_int #self_jump #fs #1 #[lit_int 5l] () () in
  assert_norm (ELetJoin [t_int] t_int self_jump (plug fs (EJump 1 [lit_int 5l])) == join1);
  assert_norm (ELetJoin [t_int] t_int self_jump
                 (plug fs (sub_tm (list_esub (L.rev [lit_int 5l])) (ren_jp (shift 1) self_jump))) ==
               join1);
  retype join1 (CTerm join1) (S_Pure #_ #_ #[] #[] h)

(* * Top-level values *)

let unfold_step =
  assert_norm (value_scheme ex_sig one_q == Some one_info);
  assert_norm (ex_genv.gvals one_q == Some (lit_int 1l));
  assert_norm (kinst_exp [] (lit_int 1l) == lit_int 1l);
  let h = PH_Unfold #ex_sig #ex_genv #one_q #[] #one_info #(lit_int 1l) () () in
  retype one_ref (CTerm (lit_int 1l)) (S_Pure #_ #_ #[] #[] h)

(* * Foreign calls *)

let length_call_redex () = assert_norm (V.foreign_redex ex_sig length_call)

let length_step =
  let args = [STy t_int; SVal int_list1] in
  let o = FOVal (ELit (LInt (I32.int_to_t 1))) in
  length_call_redex ();
  assert_norm (decompose_global_app length_call == Some (length_q, [], args));
  assert_norm (ex_genv.gforeign length_q == Some length_entry);
  assert_norm (length_entry.fe_pre (L.map erase (value_args args)));
  assert_norm (length_entry.fe_adapt (chain_instance length_call) (value_args args) == Some o);
  let h =
    PH_Foreign #ex_sig #ex_genv #length_call #length_q #[] #args #length_entry #o () () () ()
  in
  retype length_call (CTerm (ELit (LInt (I32.int_to_t 1)))) (S_Pure #_ #_ #[] #[] h)

let boom_step =
  let args = [SVal (lit_int 0l)] in
  let o = FOFault boom_fault in
  assert_norm (V.foreign_redex ex_sig boom_call);
  assert_norm (decompose_global_app boom_call == Some (boom_q, [], args));
  assert_norm (ex_genv.gforeign boom_q == Some boom_entry);
  assert_norm (boom_entry.fe_pre (L.map erase (value_args args)));
  assert_norm (boom_entry.fe_adapt (chain_instance boom_call) (value_args args) == Some o);
  let h = PH_Foreign #ex_sig #ex_genv #boom_call #boom_q #[] #args #boom_entry #o () () () () in
  retype boom_call (CFault (FAbi boom_fault)) (S_Pure #_ #_ #[] #[] h)

let boom_let_step =
  let h = S_CtxFault (FLet t_int (EVar 0)) () boom_step in
  retype boom_let (CFault (FAbi boom_fault)) h

(* * One foreign at two instances *)

let pure_step_at (t: typ) (v: exp)
  : Pure (step ex_sig ex_genv [] [] (pure_call t v) [] [] (CTerm (pure_result t)))
         (requires V.is_value ex_sig v) (ensures fun _ -> True) =
  let e = pure_call t v in
  let args = [STy t; SVal v] in
  let o = FOVal (pure_result t) in
  assert_norm (global_scheme ex_sig pure_q == Some (GForeign, 0, pure_info.fr_ty));
  assert_norm (spine_saturated ex_sig pure_q [] args);
  assert_norm (V.chain_values ex_sig e == V.is_value ex_sig v);
  assert_norm (decompose_global_app e == Some (pure_q, [], args));
  assert (V.foreign_redex ex_sig e);
  assert_norm (ex_genv.gforeign pure_q == Some pure_entry);
  assert_norm (pure_entry.fe_pre (L.map erase (value_args args)));
  assert_norm (pure_entry.fe_adapt (chain_instance e) (value_args args) == Some o);
  let h = PH_Foreign #ex_sig #ex_genv #e #pure_q #[] #args #pure_entry #o () () () () in
  retype e (CTerm (pure_result t)) (S_Pure #_ #_ #[] #[] h)

let pure_int_step =
  assert_norm (V.is_value ex_sig (nil_at t_int));
  pure_step_at (list_ty t_int) (nil_at t_int)

let pure_string_step =
  assert_norm (V.is_value ex_sig (nil_at t_string));
  pure_step_at (list_ty t_string) (nil_at t_string)

let pure_erasure () =
  assert_norm (erase (nil_at t_int) == erase (nil_at t_string));
  assert_norm (~(pure_result (list_ty t_int) == pure_result (list_ty t_string)));
  assert_norm (erase (pure_result (list_ty t_int)) == erase (pure_result (list_ty t_string)));
  assert_norm (pure_erased [erase (nil_at t_int)] ==
               Some (erase_outcome (FOVal (pure_result (list_ty t_int)))))

(* * A constructor value built from the instance *)

let mknil_step =
  let e = mknil_call t_int in
  let args = [STy t_int; SVal unit_val] in
  let o = FOVal (nil_at t_int) in
  assert_norm (V.foreign_redex ex_sig e);
  assert_norm (decompose_global_app e == Some (mknil_q, [], args));
  assert_norm (ex_genv.gforeign mknil_q == Some mknil_entry);
  assert_norm (mknil_entry.fe_pre (L.map erase (value_args args)));
  assert_norm (mknil_entry.fe_adapt (chain_instance e) (value_args args) == Some o);
  let h = PH_Foreign #ex_sig #ex_genv #e #mknil_q #[] #args #mknil_entry #o () () () () in
  retype e (CTerm (nil_at t_int)) (S_Pure #_ #_ #[] #[] h)

let mknil_erasure () =
  assert_norm (mknil_erased (L.map erase [unit_val]) == Some (erase_outcome (FOVal (nil_at t_int))))

(* * Coverage relative to the arguments *)

let ident_step =
  let args = [STy (t_fun t_unit TRowEmpty t_unit); SVal thunk] in
  let o = FOVal thunk in
  assert_norm (V.foreign_redex ex_sig ident_call);
  assert_norm (decompose_global_app ident_call == Some (ident_q, [], args));
  assert_norm (ex_genv.gforeign ident_q == Some ident_entry);
  assert_norm (ident_entry.fe_pre (L.map erase (value_args args)));
  assert_norm (ident_entry.fe_adapt (chain_instance ident_call) (value_args args) == Some o);
  let h = PH_Foreign #ex_sig #ex_genv #ident_call #ident_q #[] #args #ident_entry #o () () () () in
  retype ident_call (CTerm thunk) (S_Pure #_ #_ #[] #[] h)

let ident_relative () =
  assert_norm (covers ex_sig ex_genv thunk == false);
  assert_norm (covers_relative ex_sig ex_genv [thunk] thunk)

(* * Preconditions

   A term is taken apart one frame at a time (`pre_ok_intro`): the frames
   a `let` or an application is plugged from are read off its node, and
   every hole other than the call is a value (`value_pre_ok`). *)

let plug1_let_inv (f: frame) (x: exp) (t: typ) (b body: exp)
  : Lemma (requires plug1 f x == ELet t b body) (ensures f == FLet t body /\ x == b) =
  match f with
  | FLet _ _ -> ()
  | _ -> ()

let plug1_app_inv (f: frame) (x: exp) (a b: exp)
  : Lemma (requires plug1 f x == EApp a b)
          (ensures (f == FAppArg a /\ x == b) \/ (f == FAppFun b /\ x == a)) =
  match f with
  | FAppArg _ | FAppFun _ -> ()
  | _ -> ()

let length_head : exp = ETyApp (EGlobal (base "length") []) t_int

(* The holes of the chain `length [Int] l` other than itself are `l` and
   `length [Int]`, which are values when `l` is. *)
let length_frames_pre_ok (l: exp)
  : Lemma (requires V.is_value ex_sig l /\ V.is_value ex_sig length_head)
          (ensures forall (f: frame) (x: exp).
                     (frame_ok ex_sig f /\ plug1 f x == EApp length_head l) ==> pre_ok ex_sig ex_genv x) =
  introduce forall (f: frame) (x: exp).
      (frame_ok ex_sig f /\ plug1 f x == EApp length_head l) ==> pre_ok ex_sig ex_genv x
  with introduce _ ==> _
  with (
    plug1_app_inv f x length_head l;
    value_pre_ok ex_sig ex_genv x
  )

let length_call_pre_ok () : Lemma (pre_ok ex_sig ex_genv length_call) =
  assert_norm (V.is_value ex_sig length_head);
  assert_norm (V.is_value ex_sig int_list1);
  length_call_redex ();
  assert_norm (foreign_pre_ok ex_genv length_call);
  length_frames_pre_ok int_list1;
  pre_ok_intro ex_sig ex_genv length_call

let length_let_pre_ok () =
  length_call_pre_ok ();
  assert_norm (not (V.foreign_redex ex_sig length_let));
  introduce forall (f: frame) (x: exp).
      (frame_ok ex_sig f /\ plug1 f x == length_let) ==> pre_ok ex_sig ex_genv x
  with introduce _ ==> _
  with plug1_let_inv f x t_int length_call (EVar 0);
  pre_ok_intro ex_sig ex_genv length_let

let length_lit_not_pre_ok () =
  assert_norm (V.foreign_redex ex_sig length_lit);
  assert_norm (~(foreign_pre_ok ex_genv length_lit));
  assert (plug [] length_lit == length_lit)

let length_lit_no_step #ra #st #ra' #st' #c h =
  assert_norm (V.is_value ex_sig length_head);
  assert_norm (V.is_value ex_sig (lit_int 0l));
  assert_norm (decompose_global_app length_lit ==
               Some (length_q, [], [STy t_int; SVal (lit_int 0l)]));
  assert_norm (ex_genv.gforeign length_q == Some length_entry);
  assert_norm (~(length_entry.fe_pre (L.map erase [lit_int 0l])));
  match h with
  | S_Pure ph -> ()
  | S_Eff eh -> eff_step_shape eh
  | S_Region rh -> region_step_shape rh
  | S_Ctx #_ #_ #_ #_ #x #_ #_ #_ f _ h' ->
    plug1_app_inv f x length_head (lit_int 0l); value_no_step h'
  | S_CtxFault #_ #_ #_ #_ #x #_ #_ #_ f _ h' ->
    plug1_app_inv f x length_head (lit_int 0l); value_no_step h'

(* * A `switchKey` default *)

let switch_key_default_step =
  let bs = [(SymbolKey "x", DLeaf (lit_int 0l))] in
  assert_norm (proj ex_sig [inj_y] (OScrut 0) == Some inj_y);
  assert_norm (branch (carrier_key inj_y) bs == None);
  let h =
    PH_SwitchKeyDef #ex_sig #ex_genv #[inj_y] #(OScrut 0) #bs #(DLeaf (lit_int 1l)) #inj_y ()
  in
  retype (EMatch [inj_y] key_tree) (CTerm (EMatch [inj_y] (DLeaf (lit_int 1l))))
    (S_Pure #_ #_ #[] #[] h)

(* * Environments that do not conform

   Condition (3) of a conforming environment, read at the empty contexts
   at one typed call inside the precondition. *)

let rt_ext_empty () : Lemma (rt_ext ex_sig [] [] [] []) =
  assert_norm (rctx_ok ex_sig [] /\ lctx_ok ex_sig [] [])

let call_ok_elim (gi: genv) (e: exp) (t: typ) (th: tsub) (q: qname) (ks: list kind)
  (args: list spine_arg) (fe: foreign_entry)
  : Lemma (requires genv_ok ex_sig [] [] gi /\
                    chain_cursor ex_sig e == Some (t, th) /\
                    decompose_global_app e == Some (q, ks, args) /\ gi.gforeign q == Some fe /\
                    V.foreign_redex ex_sig e /\ typed ex_sig [] (closed_ctx []) e (sub_ty th t) /\
                    fe.fe_pre (L.map erase (value_args args)))
          (ensures entry_call_ok ex_sig gi [] [] q fe (chain_instance e) (value_args args)
                     (sub_ty th t)) =
  rt_ext_empty ();
  assert (foreign_call_ok ex_sig gi [] [] e)

let g_empty : ctx = closed_ctx []

(* `Prim.Unit : Unit` *)
let unit_typing (ln: lctx) (g: ctx) : typing ex_sig ln g [] unit_val t_unit TRowEmpty =
  assert_norm (match global_scheme ex_sig prim_unit_ctor with
               | Some (_, nk, _) -> nk == 0
               | None -> False);
  let h = chain_head ln g prim_unit_ctor in
  assert_norm (match chain_cursor ex_sig unit_val with
               | Some (s, th) -> sub_ty th s == t_unit
               | None -> False);
  chain_typed t_unit h

(* `mkNil [τ] Prim.Unit : List τ` *)
let mknil_call_typed (t: typ)
  : Lemma (requires check ex_sig g_empty t KType)
          (ensures typed ex_sig [] g_empty (mknil_call t) (list_ty t)) =
  assert_norm (match global_scheme ex_sig mknil_q with
               | Some (_, nk, _) -> nk == 0
               | None -> False);
  let h0 = chain_head [] g_empty mknil_q in
  assert_norm (match chain_cursor ex_sig (EGlobal mknil_q []) with
               | Some (TForall k _, _) -> k == KType
               | _ -> False);
  let h1 = chain_ty t h0 in
  assert_norm (match chain_cursor ex_sig (ETyApp (EGlobal mknil_q []) t) with
               | Some (s, th) ->
                 (match as_function ex_sig s with
                  | Some (a, _, _) -> sub_ty th a == t_unit
                  | None -> False)
               | None -> False);
  let h2 = chain_val t_unit h1 (unit_typing [] g_empty) in
  assert_norm (match chain_cursor ex_sig (mknil_call t) with
               | Some (s, th) -> sub_ty th s == list_ty t
               | None -> False);
  typed_intro [] g_empty (mknil_call t) (list_ty t) (chain_typed (list_ty t) h2)

let bad_nil_entry (er: list uexp -> option uoutcome) : foreign_entry =
  { fe_adapt = bad_nil_adapt; fe_erased = er; fe_pre = (fun _ -> True) }

(* The call at `τ` under a conforming `bad_nil_genv er`. *)
let bad_nil_call (er: list uexp -> option uoutcome) (t: typ)
  : Lemma (requires genv_ok ex_sig [] [] (bad_nil_genv er) /\ check ex_sig g_empty t KType)
          (ensures (match bad_nil_adapt { inst_kinds = []; inst_types = [t] } [unit_val],
                          er [UGlobal prim_unit_ctor] with
                    | Some o, Some u -> erase_outcome o == u
                    | _ -> False)) =
  let e = mknil_call t in
  let args = [STy t; SVal unit_val] in
  assert_norm (V.foreign_redex ex_sig e);
  assert_norm (decompose_global_app e == Some (mknil_q, [], args));
  assert_norm (match chain_cursor ex_sig e with
               | Some (s, th) -> sub_ty th s == list_ty t
               | None -> False);
  assert_norm ((bad_nil_genv er).gforeign mknil_q == Some (bad_nil_entry er));
  assert_norm (chain_instance e == { inst_kinds = []; inst_types = [t] });
  assert_norm (value_args args == [unit_val]);
  assert_norm (L.map erase [unit_val] == [UGlobal prim_unit_ctor]);
  mknil_call_typed t;
  match chain_cursor ex_sig e with
  | Some (s, th) -> call_ok_elim (bad_nil_genv er) e s th mknil_q [] args (bad_nil_entry er)

let bad_nil_not_ok er =
  introduce genv_ok ex_sig [] [] (bad_nil_genv er) ==> False
  with (
    assert_norm (check ex_sig g_empty t_int KType);
    assert_norm (check ex_sig g_empty t_string KType);
    bad_nil_call er t_int;
    bad_nil_call er t_string;
    assert_norm (bad_nil_adapt { inst_kinds = []; inst_types = [t_int] } [unit_val] ==
                 Some (FOVal (nil_at t_int)));
    assert_norm (bad_nil_adapt { inst_kinds = []; inst_types = [t_string] } [unit_val] ==
                 Some (FOFault nil_fault));
    assert_norm (erase_outcome (FOVal (nil_at t_int)) == UOVal (UGlobal (base "Nil")))
  )

(* `MkTask (λ (u : Unit) / (Console). missing) : Task` *)
let leaked_typing () : typing ex_sig [] g_empty [] leaked task_ty TRowEmpty =
  let g1 = push_var g_empty t_unit in
  assert_norm (global_type ex_sig (base "missing") == Some (0, t_unit));
  assert_norm (check ex_sig g1 console_row (KRow EEffect));
  let hb : typing ex_sig [] g1 [] (EGlobal (base "missing") []) (kinst_ty [] t_unit) console_row =
    T_Global #ex_sig #[] #g1 #[] #(base "missing") #[] #0 #t_unit #console_row () () () in
  assert_norm (kinst_ty [] t_unit == t_unit);
  let hb : typing ex_sig [] g1 [] (EGlobal (base "missing") []) t_unit console_row = hb in
  assert_norm (check ex_sig g_empty t_unit KType /\ check ex_sig g_empty console_row (KRow EEffect));
  let hl = T_Lam #ex_sig #[] #g_empty #[] #t_unit #console_row #(EGlobal (base "missing") [])
             #t_unit #TRowEmpty () () hb in
  assert_norm (match global_scheme ex_sig (base "MkTask") with
               | Some (_, nk, _) -> nk == 0
               | None -> False);
  let h0 = chain_head [] g_empty (base "MkTask") in
  assert_norm (match chain_cursor ex_sig (EGlobal (base "MkTask") []) with
               | Some (s, th) ->
                 (match as_function ex_sig s with
                  | Some (a, _, _) -> sub_ty th a == t_fun t_unit console_row t_unit
                  | None -> False)
               | None -> False);
  let h1 = chain_val (t_fun t_unit console_row t_unit) h0 hl in
  assert_norm (match chain_cursor ex_sig leaked with
               | Some (s, th) -> sub_ty th s == task_ty
               | None -> False);
  chain_typed task_ty h1

let leaked_typed () =
  assert_norm (V.is_value ex_sig leaked);
  typed_intro [] g_empty leaked task_ty (leaked_typing ())

(* `leak Prim.Unit : Task` *)
let leak_call : exp = EApp (EGlobal leak_q []) unit_val

let leak_call_typed () : Lemma (typed ex_sig [] g_empty leak_call task_ty) =
  assert_norm (match global_scheme ex_sig leak_q with
               | Some (_, nk, _) -> nk == 0
               | None -> False);
  let h0 = chain_head [] g_empty leak_q in
  assert_norm (match chain_cursor ex_sig (EGlobal leak_q []) with
               | Some (s, th) ->
                 (match as_function ex_sig s with
                  | Some (a, _, _) -> sub_ty th a == t_unit
                  | None -> False)
               | None -> False);
  let h1 = chain_val t_unit h0 (unit_typing [] g_empty) in
  assert_norm (match chain_cursor ex_sig leak_call with
               | Some (s, th) -> sub_ty th s == task_ty
               | None -> False);
  typed_intro [] g_empty leak_call task_ty (chain_typed task_ty h1)

let leak_not_ok () =
  introduce genv_ok ex_sig [] [] leak_genv ==> False
  with (
    let args = [SVal unit_val] in
    assert_norm (V.foreign_redex ex_sig leak_call);
    assert_norm (decompose_global_app leak_call == Some (leak_q, [], args));
    assert_norm (match chain_cursor ex_sig leak_call with
                 | Some (s, th) -> sub_ty th s == task_ty
                 | None -> False);
    assert_norm (leak_genv.gforeign leak_q == Some leak_entry);
    leak_call_typed ();
    (match chain_cursor ex_sig leak_call with
     | Some (s, th) -> call_ok_elim leak_genv leak_call s th leak_q [] args leak_entry);
    assert_norm (leak_entry.fe_adapt (chain_instance leak_call) (value_args args) ==
                 Some (FOVal leaked));
    assert_norm (leak_entry.fe_erased (L.map erase (value_args args)) ==
                 Some (UOVal (erase leaked)));
    assert_norm (value_args args == [unit_val]);
    assert_norm (covers_relative ex_sig leak_genv [unit_val] leaked == false)
  )

(* * Conformance of the empty environment *)

let empty_genv_ok sg ln rs =
  introduce forall (q: qname). gval_typed sg ln rs empty_genv q
  with ();
  introduce forall (rs': list (atom & layout)) (ln': lctx) (e: exp).
      rt_ext sg ln rs ln' rs' ==> foreign_call_ok sg empty_genv ln' rs' e
  with ()
