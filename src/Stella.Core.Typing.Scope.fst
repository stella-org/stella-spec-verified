(* Proof structure.

   One mutual induction over every judgement. A type a rule kinds is in
   scope by `check_tvs_below` and `check_lc`; a key it reads from a kinded
   row by `Stella.Core.Kinding.Keys.row_entry_key`, and from the ambient row,
   which the induction carries in scope, by `row_entry_key_scope`. A key of
   a record or variant operation is structural (`key_ok_struct`), and so is
   a layout key (`layouts_struct`).

   The induction carries `layouts_struct g.regions` alone, which `wf_ctx`
   implies (`wf_ctx_layouts_struct`) and every context a rule extends to
   keeps without any kinding hypothesis; the stated theorems take `wf_ctx`.

   Under a binder, the subderivation's context differs from `g` in one
   component only, whose size the scope bound follows; the region domain
   changes only on entering a region. A region body is read at one fresh
   atom, `fresh_atom (rdom g @ frn_exp body)`.

   Join-point scoping alone is a second, smaller mutual induction with no
   hypothesis at all: it reads the premise of `jump` and the `Δ` of each
   premise, never a kinding or a layout. The consequences on join indices
   (`typing_jps_below`, `typing_value_ren_jp`) follow from it. *)
module Stella.Core.Typing.Scope
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
open Stella.Core.Kinding.Keys
open Stella.Core.Scope
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Wf
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* Lists. *)

let rec nth_lt (#a: Type) (l: list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures i < L.length l) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else nth_lt l' (i - 1)

let rec nth_mem (#a: eqtype) (l: list a) (i: nat) (x: a)
  : Lemma (requires L.nth l i == Some x) (ensures L.mem x l) (decreases l) =
  match l with
  | y :: l' -> if i = 0 then () else nth_mem l' (i - 1) x

let assoc_fst (#a: eqtype) (#b: Type) (x: a) (l: list (a & b)) (y: b)
  : Lemma (requires L.assoc x l == Some y) (ensures L.mem x (L.map fst l)) =
  LP.assoc_mem x l

(* Types in scope. *)

let check_scoped (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg g t k)
          (ensures tvs_below (L.length g.tvars) t /\ lc_ty t /\ in_rdom (frn_ty t) g) =
  check_tvs_below sg g t k;
  check_lc sg g t k

let constr_ok_scoped (sg: sig) (g: ctx) (c: constr)
  : Lemma (requires constr_ok sg g c)
          (ensures tvs_below_constr (L.length g.tvars) c /\ lc_constr_at 0 c /\
                   in_rdom (frn_constr c) g) =
  constr_ok_lc sg g c;
  match c with
  | CLacks _ r ->
    if check sg g r (KRow EType) then check_tvs_below sg g r (KRow EType)
    else check_tvs_below sg g r (KRow EEffect)
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_tvs_below sg g r1 (KRow EType); check_tvs_below sg g r2 (KRow EType)
    end else begin
      check_tvs_below sg g r1 (KRow EEffect); check_tvs_below sg g r2 (KRow EEffect)
    end

let rec check_tys_scoped (sg: sig) (g: ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ts ks)
          (ensures tvs_below_tys (L.length g.tvars) ts /\ lc_tys_at 0 ts /\ in_rdom (frn_tys ts) g)
          (decreases ts) =
  match ts, ks with
  | [], [] -> ()
  | t :: ts', k :: ks' -> check_scoped sg g t k; check_tys_scoped sg g ts' ks'

let rec tys_ok_scoped (sg: sig) (g: ctx) (ts: list typ)
  : Lemma (requires tys_ok sg g ts)
          (ensures tvs_below_tys (L.length g.tvars) ts /\ lc_tys_at 0 ts /\ in_rdom (frn_tys ts) g)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> check_scoped sg g t KType; tys_ok_scoped sg g ts'

(* A structural key. *)
let key_ok_scoped (sg: sig) (g: ctx) (k: key)
  : Lemma (requires key_ok sg g k EType) (ensures lc_key 0 k /\ frn_key k == []) =
  key_ok_struct sg g k;
  rmap_key_struct id k

(* A key read off the canonical entries of a row in scope. *)
let row_key_scoped (g: ctx) (r: typ) (k: key) (p: cpayload)
  : Lemma (requires row_scoped g r /\ L.mem (k, p) (row_entries (canon r)))
          (ensures lc_key 0 k /\ in_rdom (frn_key k) g) =
  introduce forall (b: atom). L.mem b (frn_key k) ==> L.mem b (rdom g)
  with row_entry_key_scope r 0 k p b;
  row_entry_key_scope r 0 k p 0

(* Layouts. *)

let rec layout_row_scoped (n: nat) (l: layout) (b: atom)
  : Lemma (ensures tvs_below n (layout_row l) == tvs_below_layout n l /\
                   lc_ty (layout_row l) == lc_layout_at 0 l /\
                   (L.mem b (frn_layout l) <==> L.mem b (frn_ty (layout_row l))))
          (decreases l) =
  match l with
  | [] -> ()
  | (_, _) :: l' -> layout_row_scoped n l' b

let layout_scoped (sg: sig) (g: ctx) (l: layout)
  : Lemma (requires check sg g (layout_row l) (KRow EType))
          (ensures tvs_below_layout (L.length g.tvars) l /\ lc_layout_at 0 l /\
                   in_rdom (frn_layout l) g) =
  check_scoped sg g (layout_row l) (KRow EType);
  layout_row_scoped (L.length g.tvars) l 0;
  introduce forall (b: atom). L.mem b (frn_layout l) ==> L.mem b (rdom g)
  with layout_row_scoped (L.length g.tvars) l b

let rec layout_row_struct sg g l =
  match l with
  | [] -> ()
  | (k, t) :: l' ->
    check_ext_ty sg g k t (layout_row l');
    layout_row_struct sg g l'

let rec layouts_struct_assoc (rs: list (atom & layout)) (a: atom) (l: layout)
  : Lemma (requires layouts_struct rs /\ L.assoc a rs == Some l) (ensures keys_struct (L.map fst l))
          (decreases rs) =
  match rs with
  | (a', _) :: rs' -> if a = a' then () else layouts_struct_assoc rs' a l

let rec regions_ok_layouts_struct (sg: sig) (g: ctx) (rs: list (atom & layout))
  : Lemma (requires regions_ok sg g rs) (ensures layouts_struct rs) (decreases rs) =
  match rs with
  | [] -> ()
  | (_, l) :: rs' -> layout_ok_keys_struct sg g l; regions_ok_layouts_struct sg g rs'

let wf_ctx_layouts_struct sg g = regions_ok_layouts_struct sg g g.regions

(* A key of a layout with structural keys. *)
let layout_key_scoped (l: layout) (k: key) (t: typ)
  : Lemma (requires keys_struct (L.map fst l) /\ L.assoc k l == Some t)
          (ensures lc_key 0 k /\ frn_key k == []) =
  assoc_fst k l t;
  keys_struct_mem (L.map fst l) k;
  rmap_key_struct id k

let rec ren_layout_keys (xi: ren) (l: layout)
  : Lemma (ensures L.map fst (ren_layout xi l) == L.map fst l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l' -> ren_layout_keys xi l'

let rec layouts_struct_ren (xi: ren) (rs: list (atom & layout))
  : Lemma (ensures layouts_struct (L.map (ren_region xi) rs) == layouts_struct rs) (decreases rs) =
  match rs with
  | [] -> ()
  | (_, l) :: rs' -> ren_layout_keys xi l; layouts_struct_ren xi rs'

let layouts_struct_push_tvar (g: ctx) (k: kind)
  : Lemma (layouts_struct (push_tvar g k).regions == layouts_struct g.regions) =
  layouts_struct_ren (shift 1) g.regions

let rec layouts_struct_push_tvars (g: ctx) (ks: list kind)
  : Lemma (ensures layouts_struct (push_tvars g ks).regions == layouts_struct g.regions)
          (decreases ks) =
  match ks with
  | [] -> ()
  | k :: ks' -> layouts_struct_push_tvar g k; layouts_struct_push_tvars (push_tvar g k) ks'

let rec push_vars_regions (g: ctx) (ts: list typ)
  : Lemma (ensures (push_vars g ts).regions == g.regions) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> push_vars_regions (push_var g t) ts'

let layouts_struct_enter_region (sg: sig) (g: ctx) (a: atom) (l: layout)
  : Lemma (requires layouts_struct g.regions /\ check sg g (layout_row l) (KRow EType))
          (ensures layouts_struct (enter_region g a l).regions) =
  layout_row_struct sg g l

(* The contexts of the rules. *)

let rec push_vars_shape (g: ctx) (ts: list typ)
  : Lemma (ensures (let g' = push_vars g ts in
                    g'.tvars == g.tvars /\ g'.regions == g.regions /\
                    L.length g'.vars == L.length g.vars + L.length ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> push_vars_shape (push_var g t) ts'

let push_tvar_shape (g: ctx) (k: kind)
  : Lemma (let g' = push_tvar g k in
           L.length g'.tvars == L.length g.tvars + 1 /\ L.length g'.vars == L.length g.vars /\
           rdom g' == rdom g /\ layouts_struct g'.regions == layouts_struct g.regions) =
  rdom_push_tvar g k;
  layouts_struct_push_tvar g k

let rec push_tvars_shape (g: ctx) (ks: list kind)
  : Lemma (ensures (let g' = push_tvars g ks in
                    L.length g'.tvars == L.length g.tvars + L.length ks /\
                    L.length g'.vars == L.length g.vars /\ rdom g' == rdom g /\
                    layouts_struct g'.regions == layouts_struct g.regions))
          (decreases ks) =
  match ks with
  | [] -> ()
  | k :: ks' -> push_tvar_shape g k; push_tvars_shape (push_tvar g k) ks'

(* Occurrence contexts. *)

let rec octx_scoped_rdom (g g': ctx) (om: octx)
  : Lemma (requires rdom g == rdom g') (ensures octx_scoped g om <==> octx_scoped g' om)
          (decreases om) =
  match om with
  | [] -> ()
  | _ :: om' -> octx_scoped_rdom g g' om'

let rec octx_scoped_append (g: ctx) (om1 om2: octx)
  : Lemma (requires octx_scoped g om1 /\ octx_scoped g om2)
          (ensures octx_scoped g (L.append om1 om2)) (decreases om1) =
  match om1 with
  | [] -> ()
  | _ :: om1' -> octx_scoped_append g om1' om2

let rec octx_scoped_assoc (g: ctx) (om: octx) (o: occ) (t: typ)
  : Lemma (requires octx_scoped g om /\ L.assoc o om == Some t) (ensures occ_scoped g o)
          (decreases om) =
  match om with
  | (o', _) :: om' -> if o = o' then () else octx_scoped_assoc g om' o t

let rec octx_scoped_scrut (g: ctx) (i: nat) (ts: list typ)
  : Lemma (ensures octx_scoped g (scrut_occs i ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts' -> octx_scoped_scrut g (i + 1) ts'

let rec octx_scoped_fields (g: ctx) (o: occ) (c: qname) (j: nat) (fs: list typ)
  : Lemma (requires occ_scoped g o) (ensures octx_scoped g (field_occs o c j fs)) (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs' -> octx_scoped_fields g o c (j + 1) fs'

(* The keys of a `switchKey`, an entry each of the kinded variant row. *)
let rec split_keys_scoped (sg: sig) (g: ctx) (vr: typ) (kts0: list (key & typ)) (r': typ)
  (kts: list (key & typ))
  : Lemma (requires key_split vr kts0 r' /\ check sg g vr (KRow EType) /\
                    (forall (kt: key & typ). L.mem kt kts ==> L.mem kt kts0))
          (ensures keys_scoped g (L.map fst kts)) (decreases kts) =
  match kts with
  | [] -> ()
  | (k, t) :: kts' ->
    key_split_branch vr kts0 r' k t;
    row_entry_key sg g vr EType k (PTy (canon t));
    split_keys_scoped sg g vr kts0 r' kts'

(* Projections out of the values of a `match`. *)

let rec value_args_append (a1 a2: list spine_arg)
  : Lemma (ensures value_args (L.append a1 a2) == L.append (value_args a1) (value_args a2))
          (decreases a1) =
  match a1 with
  | [] -> ()
  | SVal _ :: a1' | STy _ :: a1' | SConstr :: a1' -> value_args_append a1' a2

let rec chain_arg_scoped (e v: exp) (b: atom)
  : Lemma (requires Some? (decompose_global_app e) /\
                    L.mem v (value_args (Mktuple3?._3 (Some?.v (decompose_global_app e)))))
          (ensures (lc_exp e ==> lc_exp v) /\ (L.mem b (frn_exp v) ==> L.mem b (frn_exp e)))
          (decreases e) =
  match e with
  | EApp f w ->
    let Some (_, _, args) = decompose_global_app f in
    value_args_append args [SVal w];
    LP.append_mem (value_args args) [w] v;
    if L.mem v (value_args args) then chain_arg_scoped f v b
  | ETyApp f t ->
    let Some (_, _, args) = decompose_global_app f in
    value_args_append args [STy t];
    LP.append_l_nil (value_args args);
    chain_arg_scoped f v b
  | ECApp f ->
    let Some (_, _, args) = decompose_global_app f in
    value_args_append args [SConstr];
    LP.append_l_nil (value_args args);
    chain_arg_scoped f v b
  | _ -> ()

let rec record_field_scoped (k: key) (v0 v: exp) (b: atom)
  : Lemma (requires record_field k v0 == Some v)
          (ensures (lc_exp v0 ==> lc_key 0 k /\ lc_exp v) /\
                   (L.mem b (frn_key k) \/ L.mem b (frn_exp v) ==> L.mem b (frn_exp v0)))
          (decreases v0) =
  match v0 with
  | EExtend k' _ v2 -> if k' = k then () else record_field_scoped k v2 v b

let rec variant_payload_scoped (k: key) (v0 v: exp) (b: atom)
  : Lemma (requires variant_payload k v0 == Some v)
          (ensures (lc_exp v0 ==> lc_key 0 k /\ lc_exp v) /\
                   (L.mem b (frn_key k) \/ L.mem b (frn_exp v) ==> L.mem b (frn_exp v0)))
          (decreases v0) =
  match v0 with
  | EInject _ _ _ -> ()
  | EWeaken _ _ v1 -> variant_payload_scoped k v1 v b

let rec nth_exp_scoped (th: list exp) (i: nat) (v: exp) (b: atom)
  : Lemma (requires L.nth th i == Some v)
          (ensures (lc_exps_at 0 th ==> lc_exp v) /\ (L.mem b (frn_exp v) ==> L.mem b (frn_exps th)))
          (decreases th) =
  match th with
  | _ :: th' -> if i = 0 then () else nth_exp_scoped th' (i - 1) v b

let rec proj_scoped (sg: sig) (g: ctx) (th: list exp) (o: occ) (v: exp)
  : Lemma (requires proj sg th o == Some v /\ lc_exps_at 0 th /\ in_rdom (frn_exps th) g)
          (ensures occ_scoped g o /\ lc_exp v /\ in_rdom (frn_exp v) g) (decreases o) =
  match o with
  | OScrut i ->
    nth_exp_scoped th i v 0;
    introduce forall (b: atom). L.mem b (frn_exp v) ==> L.mem b (rdom g)
    with nth_exp_scoped th i v b
  | OCtor o' q j ->
    let Some v0 = proj sg th o' in
    proj_scoped sg g th o' v0;
    let Some (_, _, args) = decompose_global_app v0 in
    nth_mem (value_args args) j v;
    chain_arg_scoped v0 v 0;
    introduce forall (b: atom). L.mem b (frn_exp v) ==> L.mem b (rdom g)
    with chain_arg_scoped v0 v b
  | ORecord o' k ->
    let Some v0 = proj sg th o' in
    proj_scoped sg g th o' v0;
    record_field_scoped k v0 v 0;
    introduce forall (b: atom). L.mem b (frn_key k) \/ L.mem b (frn_exp v) ==> L.mem b (rdom g)
    with record_field_scoped k v0 v b
  | OVariant o' k ->
    let Some v0 = proj sg th o' in
    proj_scoped sg g th o' v0;
    variant_payload_scoped k v0 v 0;
    introduce forall (b: atom). L.mem b (frn_key k) \/ L.mem b (frn_exp v) ==> L.mem b (rdom g)
    with variant_payload_scoped k v0 v b

let occ_typing_scoped #sg #g #om #o #t h =
  let rec aux (#o: occ) (#t: typ) (h: occ_typing sg g om o t)
    : Lemma (requires octx_scoped g om) (ensures occ_scoped g o) (decreases h) =
    match h with
    | TO_Lookup _ -> octx_scoped_assoc g om o t
    | TO_Field #_ #_ #_ #o' #k #_ #t' r h' _ _ ->
      aux h';
      row_entry_key sg g r EType k (PTy (canon t'))
  in
  aux h

(* A region body, read at one fresh atom. *)
let region_body_scoped (g: ctx) (lay: layout) (a: atom) (body: exp)
  : Lemma (requires ~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body)) /\
                    exp_scoped (enter_region g a lay) 0 (open_region a body))
          (ensures tvs_below_exp (L.length g.tvars) body /\ vars_below_exp (L.length g.vars) body /\
                   V.jp_scoped 0 body /\ lc_exp_at 1 body /\ in_rdom (frn_exp body) g) =
  rdom_enter_region g a lay;
  rmap_scope (open_rr a) 0 (L.length g.tvars) (L.length g.vars) 0 body;
  lc_open_inv a 0 body;
  introduce forall (b: atom). L.mem b (frn_exp body) ==> L.mem b (rdom g)
  with introduce _ ==> _
  with frn_open_incl a 0 body b

let fresh_for (g: ctx) (body: exp)
  : a:atom{~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body))} =
  let a = fresh_atom (L.append (rdom g) (frn_exp body)) in
  LP.append_mem (rdom g) (frn_exp body) a;
  a

(* The decision trees, from their parts. *)

let odt_scoped (g: ctx) (nj: nat) (df: option dtree) : prop =
  match df with
  | None -> True
  | Some dt -> dt_scoped g nj dt

let scoped_switch_ctor (g: ctx) (nj: nat) (o: occ) (bs: list (qname & dtree)) (df: option dtree)
  : Lemma (requires occ_scoped g o /\ brs_scoped g nj bs /\ odt_scoped g nj df)
          (ensures dt_scoped g nj (DSwitchCtor o bs df)) =
  match df with
  | None -> ()
  | Some _ -> ()

let scoped_switch_lit (g: ctx) (nj: nat) (o: occ) (bs: list (lit & dtree)) (df: dtree)
  : Lemma (requires occ_scoped g o /\ brs_scoped g nj bs /\ dt_scoped g nj df)
          (ensures dt_scoped g nj (DSwitchLit o bs df)) = ()

let scoped_switch_key (g: ctx) (nj: nat) (o: occ) (bs: list (key & dtree)) (df: option dtree)
  : Lemma (requires occ_scoped g o /\ kbrs_scoped g nj bs /\ odt_scoped g nj df)
          (ensures dt_scoped g nj (DSwitchKey o bs df)) =
  match df with
  | None -> ()
  | Some _ -> ()

(* A non-tail subterm is typed under no join point, and its scope under
   none is a scope under any number. *)

let rec jp_scoped_mono_exps (n m: nat) (es: list exp)
  : Lemma (requires n <= m /\ V.jp_scoped_exps n es) (ensures V.jp_scoped_exps m es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' -> V.jp_scoped_mono n m e; jp_scoped_mono_exps n m es'

let scoped_mono (g: ctx) (nj: nat) (e: exp)
  : Lemma (requires exp_scoped g 0 e) (ensures exp_scoped g nj e) =
  V.jp_scoped_mono 0 nj e

let scoped_mono_exps (g: ctx) (nj: nat) (es: list exp)
  : Lemma (requires exps_scoped g 0 es) (ensures exps_scoped g nj es) =
  jp_scoped_mono_exps 0 nj es

(* The mutual induction. *)

let rec typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r)
  : Lemma (requires layouts_struct g.regions)
          (ensures exp_scoped g (L.length d) e /\ row_scoped g r)
          (decreases h) =
  match h with
  | T_Var #_ #_ #_ #_ #i _ _ -> nth_lt g.vars i; check_scoped sg g r (KRow EEffect)
  | T_Global _ _ _ -> check_scoped sg g r (KRow EEffect)
  | T_Lit _ -> check_scoped sg g r (KRow EEffect)
  | T_Lam #_ #_ #_ #_ #t1 #r' _ _ hb ->
    check_scoped sg g t1 KType;
    check_scoped sg g r' (KRow EEffect);
    check_scoped sg g r (KRow EEffect);
    typing_scoped' hb
  | T_App #_ #_ #_ #_ #e1 #e2 h1 h2 ->
    typing_scoped' h1; typing_scoped' h2;
    scoped_mono g (L.length d) e1; scoped_mono g (L.length d) e2
  | T_Chain hc _ -> chain_typing_scoped' hc; scoped_mono g (L.length d) e
  | T_TyLam #_ #_ #_ #_ #k _ _ _ hb ->
    check_scoped sg g r (KRow EEffect);
    push_tvar_shape g k;
    typing_scoped' hb
  | T_TyApp #_ #_ #_ #_ #e1 #s #k h1 _ ->
    typing_scoped' h1; check_scoped sg g s k; scoped_mono g (L.length d) e1
  | T_CLam #_ #_ #_ #_ #c _ _ _ hb ->
    constr_ok_scoped sg g c;
    check_scoped sg g r (KRow EEffect);
    rdom_add_assump g c;
    typing_scoped' hb
  | T_CApp #_ #_ #_ #_ #e1 h1 _ -> typing_scoped' h1; scoped_mono g (L.length d) e1
  | T_Let #_ #_ #_ #_ #t1 #e1 _ h1 h2 ->
    check_scoped sg g t1 KType; typing_scoped' h1; typing_scoped' h2;
    scoped_mono g (L.length d) e1
  | T_LetRec #_ #_ #_ #_ #bs _ hbs hb ->
    push_vars_shape g (L.map fst bs);
    binds_typing_scoped' hbs;
    typing_scoped' hb
  | T_Conv h1 _ _ -> typing_scoped' h1; check_scoped sg g r (KRow EEffect)
  | T_Case #_ #_ #_ #_ #es #_ #ts hes hdt ->
    exps_typing_scoped' hes;
    scoped_mono_exps g (L.length d) es;
    octx_scoped_scrut g 0 ts;
    dt_typing_scoped' hdt
  | T_LetJoin #_ #_ #_ #_ #ts #t1 _ h1 h2 ->
    tys_ok_scoped sg g ts;
    check_scoped sg g t1 KType;
    push_vars_shape g ts;
    typing_scoped' h1;
    typing_scoped' h2
  | T_Jump #_ #_ #_ #_ #j #es _ _ hes ->
    nth_lt d j; exps_typing_scoped' hes; scoped_mono_exps g (L.length d) es
  | T_RecEmpty _ -> check_scoped sg g r (KRow EEffect)
  | T_Extend #_ #_ #_ #_ #k #e1 #e2 h1 h2 _ ->
    typing_scoped' h1; typing_scoped' h2; key_ok_scoped sg g k;
    scoped_mono g (L.length d) e1; scoped_mono g (L.length d) e2
  | T_Select #_ #_ #_ #_ #k #e1 h1 _ ->
    typing_scoped' h1; key_ok_scoped sg g k; scoped_mono g (L.length d) e1
  | T_Restrict #_ #_ #_ #_ #k #e1 h1 _ ->
    typing_scoped' h1; key_ok_scoped sg g k; scoped_mono g (L.length d) e1
  | T_Update #_ #_ #_ #_ #k #e1 #e2 h1 h2 _ ->
    typing_scoped' h1; typing_scoped' h2; key_ok_scoped sg g k;
    scoped_mono g (L.length d) e1; scoped_mono g (L.length d) e2
  | T_Merge #_ #_ #_ #_ #e1 #e2 h1 h2 _ ->
    typing_scoped' h1; typing_scoped' h2;
    scoped_mono g (L.length d) e1; scoped_mono g (L.length d) e2
  | T_Inject #_ #_ #_ #_ #k #r0 #e1 h1 _ _ ->
    typing_scoped' h1; key_ok_scoped sg g k; check_scoped sg g r0 (KRow EType);
    scoped_mono g (L.length d) e1
  | T_Weaken #_ #_ #_ #_ #k #t1 #e1 h1 _ _ ->
    typing_scoped' h1; key_ok_scoped sg g k; check_scoped sg g t1 KType;
    scoped_mono g (L.length d) e1
  | T_VariantValue _ _ h1 _ _ _ -> typing_scoped' h1; scoped_mono g (L.length d) e
  | T_Absurd #_ #_ #_ #_ #_ #e1 h1 _ ->
    typing_scoped' h1; check_scoped sg g t KType; scoped_mono g (L.length d) e1
  | T_Perform #_ #_ #_ #_ #k #_ #ss #e1 #_ #q #ei #os ts _ _ _ h1 ->
    typing_scoped' h1;
    scoped_mono g (L.length d) e1;
    row_key_scoped g r k (PEff q (canon_tys ts));
    check_tys_scoped sg g ss os.binders
  | T_Handle #_ #_ #_ #_ #e1 #hd #b #_ #_ #_ #_ #_ _ _ _ _ h1 h2 hcl ->
    check_scoped sg g (TRowExt hd.h_ent r) (KRow EEffect);
    check_scoped sg g hd.h_ret_ty KType;
    check_scoped sg g r (KRow EEffect);
    typing_scoped' h1;
    typing_scoped' h2;
    clauses_typing_scoped' hcl
  | T_OpenEff #_ #_ #_ #_ #r' #e1 h1 _ ->
    typing_scoped' h1; check_scoped sg g r' (KRow EEffect); scoped_mono g (L.length d) e1
  | T_Region #_ #_ #_ #_ #lay #es #body _ _ hes hbody ->
    layout_scoped sg g lay;
    check_scoped sg g r (KRow EEffect);
    exps_typing_scoped' hes;
    scoped_mono_exps g (L.length d) es;
    let a = fresh_for g body in
    layouts_struct_enter_region sg g a lay;
    typing_scoped' (hbody a);
    region_body_scoped g lay a body
  | T_ReadCell #_ #_ #_ #_ #a #k #lay #t1 _ _ _ ->
    assoc_fst a g.regions lay;
    layouts_struct_assoc g.regions a lay;
    layout_key_scoped lay k t1;
    check_scoped sg g r (KRow EEffect)
  | T_WriteCell #_ #_ #_ #_ #a #k #e1 #lay #t1 _ _ h1 ->
    assoc_fst a g.regions lay;
    layouts_struct_assoc g.regions a lay;
    layout_key_scoped lay k t1;
    typing_scoped' h1;
    scoped_mono g (L.length d) e1
  | T_Match #_ #_ #_ #_ #th om hes _ hm hdt ->
    exps_typing_scoped' hes;
    scoped_mono_exps g (L.length d) th;
    match_typing_scoped' hm;
    dt_typing_scoped' hdt
  | T_OpenEffC #_ #_ #_ #_ #r' #e1 h1 _ ->
    typing_scoped' h1; check_scoped sg g r' (KRow EEffect); scoped_mono g (L.length d) e1
  | T_Force _ _ -> check_scoped sg g r (KRow EEffect)
  | T_Fill _ _ h1 -> typing_scoped' h1; check_scoped sg g r (KRow EEffect)
  | T_RegionOpen #_ #_ #_ #_ #a #_ #_ #lay _ _ _ hc hb ->
    assoc_fst a g.regions lay;
    layouts_struct_assoc g.regions a lay;
    check_closed_lc sg g.regions r (KRow EEffect);
    cells_typing_scoped' hc;
    typing_scoped' hb
  | T_Opaque _ _ -> check_scoped sg g t KType; check_scoped sg g r (KRow EEffect)

and exps_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts)
  : Lemma (requires layouts_struct g.regions)
          (ensures exps_scoped g (L.length d) es /\ row_scoped g r)
          (decreases h) =
  match h with
  | TE_Nil _ -> check_scoped sg g r (KRow EEffect)
  | TE_Cons h1 h2 -> typing_scoped' h1; exps_typing_scoped' h2

and chain_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e)
  : Lemma (requires layouts_struct g.regions)
          (ensures exp_scoped g (L.length d) e /\ row_scoped g r)
          (decreases h) =
  match h with
  | TS_Head _ _ _ -> check_scoped sg g r (KRow EEffect)
  | TS_Ty #_ #_ #_ #_ #_ #_ #s #k h0 _ _ -> chain_typing_scoped' h0; check_scoped sg g s k
  | TS_Constr h0 _ _ -> chain_typing_scoped' h0
  | TS_Val h0 _ hv -> chain_typing_scoped' h0; typing_scoped' hv

and binds_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs)
  : Lemma (requires layouts_struct g.regions) (ensures binds_scoped g bs) (decreases h) =
  match h with
  | TB_Nil -> ()
  | TB_Cons #_ #_ #_ #t1 _ h1 h2 ->
    check_scoped sg g t1 KType; typing_scoped' h1; binds_typing_scoped' h2

and cells_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#th: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g th lay)
  : Lemma (requires layouts_struct g.regions /\ keys_struct (L.map fst lay))
          (ensures cells_scoped g th) (decreases h) =
  match h with
  | TC_Nil -> ()
  | TC_Cons #_ #_ #_ #k _ h1 h2 ->
    rmap_key_struct id k;
    typing_scoped' h1;
    cells_typing_scoped' h2

and match_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om)
  : Lemma (requires layouts_struct g.regions /\ lc_exps_at 0 th /\ in_rdom (frn_exps th) g)
          (ensures octx_scoped g om /\ row_scoped g r) (decreases h) =
  match h with
  | TM_Nil _ -> check_scoped sg g r (KRow EEffect)
  | TM_Cons #_ #_ #_ #_ #_ #_ #o #_ #_ #v _ _ h2 ->
    proj_scoped sg g th o v;
    match_typing_scoped' h2

and dt_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r)
  : Lemma (requires layouts_struct g.regions /\ octx_scoped g om)
          (ensures dt_scoped g (L.length d) dt /\ row_scoped g r) (decreases h) =
  match h with
  | TD_Leaf h1 -> typing_scoped' h1
  | TD_Bind #_ #_ #_ #_ #_ #_ #_ #t_o ho hdt ->
    occ_typing_scoped ho;
    octx_scoped_rdom g (push_var g t_o) om;
    dt_typing_scoped' hdt
  | TD_SwitchCtor #_ #_ #_ #_ #_ #o #bs _ _ _ _ ho _ _ _ hbr ->
    occ_typing_scoped ho; ctor_brs_typing_scoped' hbr;
    scoped_switch_ctor g (L.length d) o bs None
  | TD_SwitchCtorDef #_ #_ #_ #_ #_ #o #bs #df _ _ _ _ ho _ _ _ hbr hdf ->
    occ_typing_scoped ho; ctor_brs_typing_scoped' hbr; dt_typing_scoped' hdf;
    scoped_switch_ctor g (L.length d) o bs (Some df)
  | TD_SwitchLit #_ #_ #_ #_ #_ #o #bs #df _ ho _ _ hbr hdf ->
    occ_typing_scoped ho; lit_brs_typing_scoped' hbr; dt_typing_scoped' hdf;
    scoped_switch_lit g (L.length d) o bs df
  | TD_SwitchKey #_ #_ #_ #_ #_ #o #bs vr kts ho _ _ _ hbr ->
    occ_typing_scoped ho;
    split_keys_scoped sg g vr kts TRowEmpty kts;
    key_brs_typing_scoped' hbr;
    scoped_switch_key g (L.length d) o bs None
  | TD_SwitchKeyDef #_ #_ #_ #_ #_ #o #bs #df vr vr' kts ho _ _ _ hbr hdf ->
    occ_typing_scoped ho;
    split_keys_scoped sg g vr kts vr' kts;
    key_brs_typing_scoped' hbr;
    dt_typing_scoped' hdf;
    scoped_switch_key g (L.length d) o bs (Some df)
  | TD_Guard #_ #_ #_ #_ #_ #e1 h1 h2 h3 ->
    typing_scoped' h1; dt_typing_scoped' h2; dt_typing_scoped' h3;
    scoped_mono g (L.length d) e1

and ctor_brs_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ) (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r)
  : Lemma (requires layouts_struct g.regions /\ octx_scoped g om /\ occ_scoped g o)
          (ensures brs_scoped g (L.length d) bs /\ row_scoped g r) (decreases h) =
  match h with
  | TCB_Nil _ -> check_scoped sg g r (KRow EEffect)
  | TCB_Cons #_ #_ #_ #_ #_ #_ #_ #_ #_ #c #_ #_ #_ #_ #fs _ hdt h2 ->
    octx_scoped_fields g o c 0 fs;
    octx_scoped_append g (field_occs o c 0 fs) om;
    dt_typing_scoped' hdt;
    ctor_brs_typing_scoped' h2

and lit_brs_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ) (h: lit_brs_typing sg ln g d om lt bs t r)
  : Lemma (requires layouts_struct g.regions /\ octx_scoped g om)
          (ensures brs_scoped g (L.length d) bs /\ row_scoped g r) (decreases h) =
  match h with
  | TLB_Nil _ -> check_scoped sg g r (KRow EEffect)
  | TLB_Cons _ hdt h2 -> dt_typing_scoped' hdt; lit_brs_typing_scoped' h2

and key_brs_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r)
  : Lemma (requires layouts_struct g.regions /\ octx_scoped g om /\ occ_scoped g o /\
                    keys_scoped g (L.map fst kts))
          (ensures kbrs_scoped g (L.length d) bs /\ row_scoped g r) (decreases h) =
  match h with
  | TKB_Nil _ -> check_scoped sg g r (KRow EEffect)
  | TKB_Cons _ hdt h2 -> dt_typing_scoped' hdt; key_brs_typing_scoped' h2

and clauses_typing_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs)
  : Lemma (requires layouts_struct g.regions) (ensures cls_scoped g cs) (decreases h) =
  match h with
  | TCL_Nil _ -> ()
  | TCL_Full #_ #_ #_ #_ #_ #_ #_ #_ #_ #s #kt #_ #_ #os _ _ _ hb h2 ->
    let g1 = push_tvars g os.binders in
    push_tvars_shape g os.binders;
    check_scoped sg g1 s KType;
    check_scoped sg g1 kt KType;
    typing_scoped' hb;
    clauses_typing_scoped' h2
  | TCL_Fast #_ #_ #_ #_ #_ #_ #_ #_ #_ #s #_ #_ #os _ _ hb h2 ->
    let g1 = push_tvars g os.binders in
    push_tvars_shape g os.binders;
    check_scoped sg g1 s KType;
    typing_scoped' hb;
    clauses_typing_scoped' h2

let typing_scoped #sg #ln #g #d #e #t #r h =
  wf_ctx_layouts_struct sg g;
  typing_scoped' h

let exps_typing_scoped #sg #ln #g #d #r #es #ts h =
  wf_ctx_layouts_struct sg g;
  exps_typing_scoped' h

let chain_typing_scoped #sg #ln #g #d #r #e h =
  wf_ctx_layouts_struct sg g;
  chain_typing_scoped' h

let binds_typing_scoped #sg #ln #g #bs h =
  wf_ctx_layouts_struct sg g;
  binds_typing_scoped' h

let cells_typing_scoped #sg #ln #g #th #lay h =
  wf_ctx_layouts_struct sg g;
  cells_typing_scoped' h

let match_typing_scoped #sg #ln #g #d #r #th #om h =
  wf_ctx_layouts_struct sg g;
  match_typing_scoped' h

let dt_typing_scoped #sg #ln #g #d #om #dt #t #r h =
  wf_ctx_layouts_struct sg g;
  dt_typing_scoped' h

let ctor_brs_typing_scoped #sg #ln #g #d #om #o #ks #ss #cs #bs #t #r h =
  wf_ctx_layouts_struct sg g;
  ctor_brs_typing_scoped' h

let lit_brs_typing_scoped #sg #ln #g #d #om #lt #bs #t #r h =
  wf_ctx_layouts_struct sg g;
  lit_brs_typing_scoped' h

let key_brs_typing_scoped #sg #ln #g #d #om #o #kts #bs #t #r h =
  wf_ctx_layouts_struct sg g;
  key_brs_typing_scoped' h

let clauses_typing_scoped #sg #ln #g #ei #ts #r #b #cs h =
  wf_ctx_layouts_struct sg g;
  clauses_typing_scoped' h

(* Join-point scoping alone. It reads nothing of the context: the bound
   of a `jump` is `|Δ|` by its premise, and every other rule either keeps
   `Δ` or types its subterm under `Δ = []`, whose scope under no join point
   is a scope under any number. A region body is read at any atom, since
   opening a region moves no join index. *)

let any_fresh (g: ctx) (body: exp) : a:atom{~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body))} =
  fresh_for g body

let rec typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r)
  : Lemma (ensures V.jp_scoped (L.length d) e) (decreases h) =
  let n = L.length d in
  match h with
  | T_Var _ _ | T_Global _ _ _ | T_Lit _ -> ()
  | T_Lam _ _ hb -> typing_jp_scoped' hb
  | T_App #_ #_ #_ #_ #e1 #e2 h1 h2 ->
    typing_jp_scoped' h1; typing_jp_scoped' h2;
    V.jp_scoped_mono 0 n e1; V.jp_scoped_mono 0 n e2
  | T_Chain hc _ -> chain_typing_jp_scoped' hc; V.jp_scoped_mono 0 n e
  | T_TyLam _ _ _ hb -> typing_jp_scoped' hb
  | T_TyApp #_ #_ #_ #_ #e1 h1 _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_CLam _ _ _ hb -> typing_jp_scoped' hb
  | T_CApp #_ #_ #_ #_ #e1 h1 _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Let #_ #_ #_ #_ #_ #e1 _ h1 h2 ->
    typing_jp_scoped' h1; typing_jp_scoped' h2; V.jp_scoped_mono 0 n e1
  | T_LetRec _ hbs hb -> binds_typing_jp_scoped' hbs; typing_jp_scoped' hb
  | T_Conv h1 _ _ -> typing_jp_scoped' h1
  | T_Case #_ #_ #_ #_ #es hes hdt ->
    exps_typing_jp_scoped' hes; jp_scoped_mono_exps 0 n es; dt_typing_jp_scoped' hdt
  | T_LetJoin _ h1 h2 -> typing_jp_scoped' h1; typing_jp_scoped' h2
  | T_Jump #_ #_ #_ #_ #j #es _ _ hes ->
    nth_lt d j; exps_typing_jp_scoped' hes; jp_scoped_mono_exps 0 n es
  | T_RecEmpty _ -> ()
  | T_Extend #_ #_ #_ #_ #_ #e1 #e2 h1 h2 _ ->
    typing_jp_scoped' h1; typing_jp_scoped' h2;
    V.jp_scoped_mono 0 n e1; V.jp_scoped_mono 0 n e2
  | T_Select #_ #_ #_ #_ #_ #e1 h1 _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Restrict #_ #_ #_ #_ #_ #e1 h1 _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Update #_ #_ #_ #_ #_ #e1 #e2 h1 h2 _ ->
    typing_jp_scoped' h1; typing_jp_scoped' h2;
    V.jp_scoped_mono 0 n e1; V.jp_scoped_mono 0 n e2
  | T_Merge #_ #_ #_ #_ #e1 #e2 h1 h2 _ ->
    typing_jp_scoped' h1; typing_jp_scoped' h2;
    V.jp_scoped_mono 0 n e1; V.jp_scoped_mono 0 n e2
  | T_Inject #_ #_ #_ #_ #_ #_ #e1 h1 _ _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Weaken #_ #_ #_ #_ #_ #_ #e1 h1 _ _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_VariantValue _ _ h1 _ _ _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e
  | T_Absurd #_ #_ #_ #_ #_ #e1 h1 _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Perform #_ #_ #_ #_ #_ #_ #_ #e1 _ _ _ _ h1 -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Handle _ _ _ _ h1 h2 hcl ->
    typing_jp_scoped' h1; typing_jp_scoped' h2; clauses_typing_jp_scoped' hcl
  | T_OpenEff #_ #_ #_ #_ #_ #e1 h1 _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Region #_ #_ #_ #_ #_ #es #body _ _ hes hbody ->
    exps_typing_jp_scoped' hes; jp_scoped_mono_exps 0 n es;
    let a = any_fresh g body in
    typing_jp_scoped' (hbody a);
    rmap_scope (open_rr a) 0 0 0 0 body
  | T_ReadCell _ _ _ -> ()
  | T_WriteCell #_ #_ #_ #_ #_ #_ #e1 _ _ h1 -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Match #_ #_ #_ #_ #th _ hes _ _ hdt ->
    exps_typing_jp_scoped' hes; jp_scoped_mono_exps 0 n th; dt_typing_jp_scoped' hdt
  | T_OpenEffC #_ #_ #_ #_ #_ #e1 h1 _ -> typing_jp_scoped' h1; V.jp_scoped_mono 0 n e1
  | T_Force _ _ -> ()
  | T_Fill _ _ h1 -> typing_jp_scoped' h1
  | T_RegionOpen _ _ _ hc hb -> cells_typing_jp_scoped' hc; typing_jp_scoped' hb
  | T_Opaque _ _ -> ()

and exps_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts)
  : Lemma (ensures V.jp_scoped_exps (L.length d) es) (decreases h) =
  match h with
  | TE_Nil _ -> ()
  | TE_Cons h1 h2 -> typing_jp_scoped' h1; exps_typing_jp_scoped' h2

and chain_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e)
  : Lemma (ensures V.jp_scoped (L.length d) e) (decreases h) =
  match h with
  | TS_Head _ _ _ -> ()
  | TS_Ty h0 _ _ -> chain_typing_jp_scoped' h0
  | TS_Constr h0 _ _ -> chain_typing_jp_scoped' h0
  | TS_Val h0 _ hv -> chain_typing_jp_scoped' h0; typing_jp_scoped' hv

and binds_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs)
  : Lemma (ensures V.jp_scoped_binds 0 bs) (decreases h) =
  match h with
  | TB_Nil -> ()
  | TB_Cons _ h1 h2 -> typing_jp_scoped' h1; binds_typing_jp_scoped' h2

and cells_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#th: list (key & exp))
  (#lay: layout) (h: cells_typing sg ln g th lay)
  : Lemma (ensures V.jp_scoped_cells 0 th) (decreases h) =
  match h with
  | TC_Nil -> ()
  | TC_Cons _ h1 h2 -> typing_jp_scoped' h1; cells_typing_jp_scoped' h2

and dt_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r)
  : Lemma (ensures V.jp_scoped_dt (L.length d) dt) (decreases h) =
  match h with
  | TD_Leaf h1 -> typing_jp_scoped' h1
  | TD_Bind _ hdt -> dt_typing_jp_scoped' hdt
  | TD_SwitchCtor _ _ _ _ _ _ _ _ hbr -> ctor_brs_typing_jp_scoped' hbr
  | TD_SwitchCtorDef _ _ _ _ _ _ _ _ hbr hdf ->
    ctor_brs_typing_jp_scoped' hbr; dt_typing_jp_scoped' hdf
  | TD_SwitchLit _ _ _ _ hbr hdf -> lit_brs_typing_jp_scoped' hbr; dt_typing_jp_scoped' hdf
  | TD_SwitchKey _ _ _ _ _ _ hbr -> key_brs_typing_jp_scoped' hbr
  | TD_SwitchKeyDef _ _ _ _ _ _ _ hbr hdf ->
    key_brs_typing_jp_scoped' hbr; dt_typing_jp_scoped' hdf
  | TD_Guard #_ #_ #_ #_ #_ #e1 h1 h2 h3 ->
    typing_jp_scoped' h1; dt_typing_jp_scoped' h2; dt_typing_jp_scoped' h3;
    V.jp_scoped_mono 0 (L.length d) e1

and ctor_brs_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ) (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r)
  : Lemma (ensures V.jp_scoped_brs (L.length d) bs) (decreases h) =
  match h with
  | TCB_Nil _ -> ()
  | TCB_Cons _ hdt h2 -> dt_typing_jp_scoped' hdt; ctor_brs_typing_jp_scoped' h2

and lit_brs_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ) (h: lit_brs_typing sg ln g d om lt bs t r)
  : Lemma (ensures V.jp_scoped_brs (L.length d) bs) (decreases h) =
  match h with
  | TLB_Nil _ -> ()
  | TLB_Cons _ hdt h2 -> dt_typing_jp_scoped' hdt; lit_brs_typing_jp_scoped' h2

and key_brs_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r)
  : Lemma (ensures V.jp_scoped_brs (L.length d) bs) (decreases h) =
  match h with
  | TKB_Nil _ -> ()
  | TKB_Cons _ hdt h2 -> dt_typing_jp_scoped' hdt; key_brs_typing_jp_scoped' h2

and clauses_typing_jp_scoped' (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs)
  : Lemma (ensures V.jp_scoped_cls 0 cs) (decreases h) =
  match h with
  | TCL_Nil _ -> ()
  | TCL_Full _ _ _ hb h2 -> typing_jp_scoped' hb; clauses_typing_jp_scoped' h2
  | TCL_Fast _ _ hb h2 -> typing_jp_scoped' hb; clauses_typing_jp_scoped' h2

let typing_jp_scoped #sg #ln #g #d #e #t #r h = typing_jp_scoped' h

let exps_typing_jp_scoped #sg #ln #g #d #r #es #ts h = exps_typing_jp_scoped' h

let dt_typing_jp_scoped #sg #ln #g #d #om #dt #t #r h = dt_typing_jp_scoped' h

let typing_jps_below #sg #ln #g #d #e #t #r h =
  typing_jp_scoped' h;
  jp_scoped_jps_below (L.length d) (L.length d) e

let typing_value_ren_jp #sg #ln #g #d #v #t #r h xi =
  typing_jp_scoped' h;
  V.value_jp_scoped sg (L.length d) v;
  V.value_ren_jp sg 0 xi v
