(**
 * Canonical forms of types, and type equality (design §2, §2.1).
 *
 * `canon τ` is the canonical form of `τ`, and type equality is
 *
 *     ty_eq τ1 τ2  =  (canon τ1 = canon τ2)
 *
 * on the eqtype `ctyp`. A row is normalized to a set of entries, each a
 * pair of a key and the canonical form of its payload, together with a set
 * of tails; both sets are sorted, duplicate-free lists (`Stella.Core.OrdSet`),
 * so set equality is list equality. Every other type former keeps its
 * structure, with its children canonicalized.
 *
 * ## Totality and kind-agnosticism
 *
 * `canon` is total and never consults kinds, so that it behaves uniformly
 * under every substitution, ill-kinded ones included:
 *
 *   - a row is built by `mkrow`, which collapses a row with no entries and
 *     a single tail to that tail, so `canon a = CVar a = canon (a ⊎ ())`;
 *   - a row operation reads a canonical form through `view_row`, under which
 *     a form that is not a row is a row with no entries and itself as its
 *     only tail. So `()` is `CRow [] []`, and a type that is not a row,
 *     standing where a row is expected, is an opaque tail.
 *
 * In a well-kinded type every tail is a type variable, and the entry set
 * is the graph of a finite map; there the canonical form is the `nf` of
 * spec 02 §Sharp normal form. Entries with one key and different payloads
 * remain distinct: excluding them is the job of kinding (spec 02
 * §Sharpness).
 *
 * ## Operations on canonical forms
 *
 * Renaming (`cren`), substitution (`csub`), maps over region references
 * (`cmap`) and kind instantiation (`ckinst`) act on canonical forms and
 * re-normalize every row they rebuild, since they may merge entries or
 * tails. `Stella.Core.Rows.Lemmas` proves that `canon` commutes with each
 * of them.
 *)
module Stella.Core.Rows
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.OrdSet
module L = FStar.List.Tot

(** * Canonical forms *)

(** The canonical forms. A `CRow` carries its entries and tails as sorted,
    duplicate-free lists; `canon` never produces a `CRow` with no entries
    and exactly one tail, nor a tail that is itself a `CRow`. *)
type ctyp =
  | CVar    : nat -> ctyp
  | CCon    : qname -> list kind -> ctyp
  | CApp    : ctyp -> ctyp -> ctyp
  | CForall : kind -> ctyp -> ctyp                     (** binds `CVar 0` *)
  | CConstr : cconstr -> ctyp -> ctyp
  | CRow    : entries: list (key & cpayload) -> tails: list ctyp -> ctyp

(** The canonical payload of a row element (spec 01 §Row elements). *)
and cpayload =
  | PTy     : ctyp -> cpayload                  (** of `k : τ` *)
  | PEff    : qname -> list ctyp -> cpayload    (** of `E τ̄` and `s : E τ̄` *)
  | PRegion : region_ref -> cpayload            (** of `region ℓ` *)

(** Constraints, compared structurally: `CCDisj` is not symmetric (spec 02
    §What entailment does not derive). *)
and cconstr =
  | CCLacks : key -> ctyp -> cconstr
  | CCDisj  : ctyp -> ctyp -> cconstr

(** A canonical row entry: a key and a payload. *)
type centry = key & cpayload

(** A row read as its entries and its tails. *)
type rview = list centry & list ctyp

(** * The total order

    Every value is encoded as a prefix-free token list; the encoding of a
    composite value is a constructor tag followed by the encodings of its
    fields. A list is encoded element by element, each element preceded by
    the tag `1` and the whole list closed by `0`. A string is encoded as
    the list of its character codes. Each `enc_*` takes the tokens to follow
    as an accumulator, so that prefix-freeness reads as injectivity of
    `enc_* x r` in the pair `(x, r)`. *)

let rec enc_chars (l: list FStar.Char.char) (r: tokens) : Tot tokens (decreases l) =
  match l with
  | [] -> 0 :: r
  | c :: l -> 1 :: FStar.Char.int_of_char c :: enc_chars l r

let enc_string (s: string) (r: tokens) : tokens = enc_chars (FStar.String.list_of_string s) r

let rec enc_strings (l: list string) (r: tokens) : Tot tokens (decreases l) =
  match l with
  | [] -> 0 :: r
  | s :: l -> 1 :: enc_string s (enc_strings l r)

let enc_qname (q: qname) (r: tokens) : tokens = enc_strings q.qmod (enc_string q.qid r)

let rec enc_kind (k: kind) (r: tokens) : Tot tokens (decreases k) =
  match k with
  | KVar i -> 0 :: i :: r
  | KType -> 1 :: r
  | KEffect -> 2 :: r
  | KRow EType -> 3 :: r
  | KRow EEffect -> 4 :: r
  | KArrow a b -> 5 :: enc_kind a (enc_kind b r)

let rec enc_kinds (l: list kind) (r: tokens) : Tot tokens (decreases l) =
  match l with
  | [] -> 0 :: r
  | k :: l -> 1 :: enc_kind k (enc_kinds l r)

let enc_rr (x: region_ref) (r: tokens) : tokens =
  match x with
  | RBound i -> 0 :: i :: r
  | RFree a -> 1 :: a :: r

let enc_key (k: key) (r: tokens) : tokens =
  match k with
  | SymbolKey s -> 0 :: enc_string s r
  | TagKey s -> 1 :: enc_string s r
  | PositionKey n -> 2 :: n :: r
  | EffectKey q -> 3 :: enc_qname q r
  | RegionKey x -> 4 :: enc_rr x r

let rec enc_ctyp (c: ctyp) (r: tokens) : Tot tokens (decreases c) =
  match c with
  | CVar i -> 0 :: i :: r
  | CCon q ks -> 1 :: enc_qname q (enc_kinds ks r)
  | CApp a b -> 2 :: enc_ctyp a (enc_ctyp b r)
  | CForall k a -> 3 :: enc_kind k (enc_ctyp a r)
  | CConstr cc a -> 4 :: enc_cconstr cc (enc_ctyp a r)
  | CRow es ts -> 5 :: enc_centries es (enc_ctyps ts r)

and enc_pay (p: cpayload) (r: tokens) : Tot tokens (decreases p) =
  match p with
  | PTy c -> 0 :: enc_ctyp c r
  | PEff q cs -> 1 :: enc_qname q (enc_ctyps cs r)
  | PRegion x -> 2 :: enc_rr x r

and enc_centry (e: key & cpayload) (r: tokens) : Tot tokens (decreases e) =
  match e with
  | (k, p) -> enc_key k (enc_pay p r)

and enc_centries (es: list (key & cpayload)) (r: tokens) : Tot tokens (decreases es) =
  match es with
  | [] -> 0 :: r
  | e :: es -> 1 :: enc_centry e (enc_centries es r)

and enc_ctyps (cs: list ctyp) (r: tokens) : Tot tokens (decreases cs) =
  match cs with
  | [] -> 0 :: r
  | c :: cs -> 1 :: enc_ctyp c (enc_ctyps cs r)

and enc_cconstr (cc: cconstr) (r: tokens) : Tot tokens (decreases cc) =
  match cc with
  | CCLacks k c -> 0 :: enc_key k (enc_ctyp c r)
  | CCDisj a b -> 1 :: enc_ctyp a (enc_ctyp b r)

let enc_ctyp0 (c: ctyp) : tokens = enc_ctyp c []

let enc_centry0 (e: centry) : tokens = enc_centry e []

val enc_ctyp0_injective (_: unit) : Lemma (injective enc_ctyp0)

val enc_centry0_injective (_: unit) : Lemma (injective enc_centry0)

let ord_ctyp : ord ctyp = enc_ctyp0_injective (); enc_ctyp0

let ord_centry : ord centry = enc_centry0_injective (); enc_centry0

(** * Rows *)

(** The row with entries `es` and tails `ts`. A row with no entries and a
    single tail `t` is `t` itself, unless `t` is a `CRow`; that case never
    arises in a canonical form, and excluding it makes
    `view_row (mkrow es ts) = (es, ts)` hold unconditionally. *)
let mkrow (es: list centry) (ts: list ctyp) : ctyp =
  match es, ts with
  | [], [t] -> if CRow? t then CRow es ts else t
  | _ -> CRow es ts

(** A canonical form read as a row: a form that is not a `CRow` is its own
    only tail. *)
let view_row (c: ctyp) : rview =
  match c with
  | CRow es ts -> (es, ts)
  | _ -> ([], [c])

let row_entries (c: ctyp) : list centry = fst (view_row c)

let row_tails (c: ctyp) : list ctyp = snd (view_row c)

(** The row with the entry set and the tail set of the given lists. *)
let nrow (es: list centry) (ts: list ctyp) : ctyp =
  mkrow (norm ord_centry es) (norm ord_ctyp ts)

(** `c` is its own row rebuilt from its view. Every canonical form is,
    and so is every result of `cren`, `csub` (from such substitutes) and
    `cmap` (`Stella.Core.Rows.Lemmas`). *)
let row_canonical (c: ctyp) : bool = nrow (row_entries c) (row_tails c) = c

(** The concatenations of the entry and tail lists of a list of views. *)
let rec flat_es (vs: list rview) : Tot (list centry) (decreases vs) =
  match vs with
  | [] -> []
  | v :: vs -> L.append (fst v) (flat_es vs)

let rec flat_ts (vs: list rview) : Tot (list ctyp) (decreases vs) =
  match vs with
  | [] -> []
  | v :: vs -> L.append (snd v) (flat_ts vs)

(** The row with entries `es` and the entries and tails of the views `vs`.
    This is how every operation rebuilds a row: the views are those of the
    images of the tails. *)
let build (es: list centry) (vs: list rview) : ctyp =
  nrow (L.append es (flat_es vs)) (flat_ts vs)

(** The un-normalized view of an operation applied to a row view: `fe` maps
    each entry and `fv` gives the view of the image of each tail. *)
let rop (fe: centry -> centry) (fv: ctyp -> rview) (v: rview) : rview =
  (L.append (L.map fe (fst v)) (flat_es (L.map fv (snd v))), flat_ts (L.map fv (snd v)))

(** * Canonicalization *)

(** The key of an effect element: its label if it has one, its effect
    otherwise (spec 01 §Row elements). *)
let eff_key (lbl: option string) (q: qname) : key =
  match lbl with
  | None -> EffectKey q
  | Some s -> SymbolKey s

(** `key(ent)` (spec 01 §Row elements). *)
let ent_key (en: entry) : key =
  match en with
  | EntTy k _ -> k
  | EntEff lbl q _ -> eff_key lbl q
  | EntRegion r -> RegionKey r

let rec canon (t: typ) : Tot ctyp (decreases t) =
  match t with
  | TVar i -> CVar i
  | TCon q ks -> CCon q ks
  | TApp a b -> CApp (canon a) (canon b)
  | TForall k a -> CForall k (canon a)
  | TConstr cn a -> CConstr (canon_constr cn) (canon a)
  | TRowEmpty -> CRow [] []
  | TRowExt en r ->
    let v = view_row (canon r) in
    nrow (canon_ent en :: fst v) (snd v)
  | TRowUnion a b ->
    let v1 = view_row (canon a) in
    let v2 = view_row (canon b) in
    nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2))

(** The key and the canonical payload of a row element. *)
and canon_ent (en: entry) : Tot centry (decreases en) =
  match en with
  | EntTy k t -> (k, PTy (canon t))
  | EntEff lbl q ts -> (eff_key lbl q, PEff q (canon_tys ts))
  | EntRegion r -> (RegionKey r, PRegion r)

and canon_constr (cn: constr) : Tot cconstr (decreases cn) =
  match cn with
  | CLacks k t -> CCLacks k (canon t)
  | CDisj t1 t2 -> CCDisj (canon t1) (canon t2)

and canon_tys (ts: list typ) : Tot (list ctyp) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> canon t :: canon_tys ts

(** * Type equality (design §2) *)

let ty_eq (t1 t2: typ) : bool = canon t1 = canon t2

let ent_eq (e1 e2: entry) : bool = canon_ent e1 = canon_ent e2

let constr_eq (c1 c2: constr) : bool = canon_constr c1 = canon_constr c2

(** * Known keys *)

let rec keys_of (es: list centry) : Tot (list key) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> fst e :: keys_of es

(** The keys of the entries of a canonical form read as a row. A key with
    several payloads occurs once per payload. *)
let ckeys (c: ctyp) : list key = keys_of (row_entries c)

(** `knownKeys(ρ)` (design §2.1). *)
let known_keys (t: typ) : list key = ckeys (canon t)

(** * Renaming *)

let rec cren (xi: ren) (c: ctyp) : Tot ctyp (decreases c) =
  match c with
  | CVar i -> CVar (xi i)
  | CCon _ _ -> c
  | CApp a b -> CApp (cren xi a) (cren xi b)
  | CForall k a -> CForall k (cren (up_ren xi) a)
  | CConstr cc a -> CConstr (cren_constr xi cc) (cren xi a)
  | CRow es ts -> build (cren_ents xi es) (cren_views xi ts)

and cren_pay (xi: ren) (p: cpayload) : Tot cpayload (decreases p) =
  match p with
  | PTy c -> PTy (cren xi c)
  | PEff q cs -> PEff q (cren_list xi cs)
  | PRegion _ -> p

and cren_ent (xi: ren) (e: centry) : Tot centry (decreases e) =
  match e with
  | (k, p) -> (k, cren_pay xi p)

and cren_ents (xi: ren) (es: list centry) : Tot (list centry) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> cren_ent xi e :: cren_ents xi es

(** The views of the images of a list of tails. *)
and cren_views (xi: ren) (ts: list ctyp) : Tot (list rview) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> view_row (cren xi t) :: cren_views xi ts

and cren_list (xi: ren) (cs: list ctyp) : Tot (list ctyp) (decreases cs) =
  match cs with
  | [] -> []
  | c :: cs -> cren xi c :: cren_list xi cs

and cren_constr (xi: ren) (cc: cconstr) : Tot cconstr (decreases cc) =
  match cc with
  | CCLacks k c -> CCLacks k (cren xi c)
  | CCDisj a b -> CCDisj (cren xi a) (cren xi b)

(** The view of the image of a tail, as a function. *)
let cren_vf (xi: ren) (t: ctyp) : rview = view_row (cren xi t)

(** * Substitution *)

(** A substitution of canonical forms for type variables. *)
type csubst = nat -> ctyp

(** `s` lifted across `n` type binders, as `upn_tsub`. *)
let cupn (n: nat) (s: csubst) (i: nat) : ctyp =
  if i < n then CVar i else cren (shift n) (s (i - n))

unfold let cup (s: csubst) : csubst = cupn 1 s

(** A variable, in a tail position or elsewhere, is replaced by its
    substitute; in a tail position the substitute is read through
    `view_row`, so its entries and tails join the row. *)
let rec csub (s: csubst) (c: ctyp) : Tot ctyp (decreases c) =
  match c with
  | CVar i -> s i
  | CCon _ _ -> c
  | CApp a b -> CApp (csub s a) (csub s b)
  | CForall k a -> CForall k (csub (cup s) a)
  | CConstr cc a -> CConstr (csub_constr s cc) (csub s a)
  | CRow es ts -> build (csub_ents s es) (csub_views s ts)

and csub_pay (s: csubst) (p: cpayload) : Tot cpayload (decreases p) =
  match p with
  | PTy c -> PTy (csub s c)
  | PEff q cs -> PEff q (csub_list s cs)
  | PRegion _ -> p

and csub_ent (s: csubst) (e: centry) : Tot centry (decreases e) =
  match e with
  | (k, p) -> (k, csub_pay s p)

and csub_ents (s: csubst) (es: list centry) : Tot (list centry) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> csub_ent s e :: csub_ents s es

and csub_views (s: csubst) (ts: list ctyp) : Tot (list rview) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> view_row (csub s t) :: csub_views s ts

and csub_list (s: csubst) (cs: list ctyp) : Tot (list ctyp) (decreases cs) =
  match cs with
  | [] -> []
  | c :: cs -> csub s c :: csub_list s cs

and csub_constr (s: csubst) (cc: cconstr) : Tot cconstr (decreases cc) =
  match cc with
  | CCLacks k c -> CCLacks k (csub s c)
  | CCDisj a b -> CCDisj (csub s a) (csub s b)

let csub_vf (s: csubst) (t: ctyp) : rview = view_row (csub s t)

(** * Maps over region references *)

(** `cmap f` applies `f` to every region reference, in keys and in region
    payloads, as `rmap_ty` does on types. *)
let rec cmap (f: region_ref -> region_ref) (c: ctyp) : Tot ctyp (decreases c) =
  match c with
  | CVar _ | CCon _ _ -> c
  | CApp a b -> CApp (cmap f a) (cmap f b)
  | CForall k a -> CForall k (cmap f a)
  | CConstr cc a -> CConstr (cmap_constr f cc) (cmap f a)
  | CRow es ts -> build (cmap_ents f es) (cmap_views f ts)

and cmap_pay (f: region_ref -> region_ref) (p: cpayload) : Tot cpayload (decreases p) =
  match p with
  | PTy c -> PTy (cmap f c)
  | PEff q cs -> PEff q (cmap_list f cs)
  | PRegion r -> PRegion (f r)

and cmap_ent (f: region_ref -> region_ref) (e: centry) : Tot centry (decreases e) =
  match e with
  | (k, p) -> (rmap_key f k, cmap_pay f p)

and cmap_ents (f: region_ref -> region_ref) (es: list centry) : Tot (list centry) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> cmap_ent f e :: cmap_ents f es

and cmap_views (f: region_ref -> region_ref) (ts: list ctyp) : Tot (list rview) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> view_row (cmap f t) :: cmap_views f ts

and cmap_list (f: region_ref -> region_ref) (cs: list ctyp) : Tot (list ctyp) (decreases cs) =
  match cs with
  | [] -> []
  | c :: cs -> cmap f c :: cmap_list f cs

and cmap_constr (f: region_ref -> region_ref) (cc: cconstr) : Tot cconstr (decreases cc) =
  match cc with
  | CCLacks k c -> CCLacks (rmap_key f k) (cmap f c)
  | CCDisj a b -> CCDisj (cmap f a) (cmap f b)

let cmap_vf (f: region_ref -> region_ref) (t: ctyp) : rview = view_row (cmap f t)

(** * Kind instantiation

    `ckinst ks` instantiates the kinds of constructors and quantifiers, as
    `kinst_ty` does on types. Keys and region payloads hold no kinds. *)
let rec ckinst (ks: list kind) (c: ctyp) : Tot ctyp (decreases c) =
  match c with
  | CVar _ -> c
  | CCon q kl -> CCon q (kinst_kinds ks kl)
  | CApp a b -> CApp (ckinst ks a) (ckinst ks b)
  | CForall k a -> CForall (kinst_kind ks k) (ckinst ks a)
  | CConstr cc a -> CConstr (ckinst_constr ks cc) (ckinst ks a)
  | CRow es ts -> build (ckinst_ents ks es) (ckinst_views ks ts)

and ckinst_pay (ks: list kind) (p: cpayload) : Tot cpayload (decreases p) =
  match p with
  | PTy c -> PTy (ckinst ks c)
  | PEff q cs -> PEff q (ckinst_list ks cs)
  | PRegion _ -> p

and ckinst_ent (ks: list kind) (e: centry) : Tot centry (decreases e) =
  match e with
  | (k, p) -> (k, ckinst_pay ks p)

and ckinst_ents (ks: list kind) (es: list centry) : Tot (list centry) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> ckinst_ent ks e :: ckinst_ents ks es

and ckinst_views (ks: list kind) (ts: list ctyp) : Tot (list rview) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> view_row (ckinst ks t) :: ckinst_views ks ts

and ckinst_list (ks: list kind) (cs: list ctyp) : Tot (list ctyp) (decreases cs) =
  match cs with
  | [] -> []
  | c :: cs -> ckinst ks c :: ckinst_list ks cs

and ckinst_constr (ks: list kind) (cc: cconstr) : Tot cconstr (decreases cc) =
  match cc with
  | CCLacks k c -> CCLacks k (ckinst ks c)
  | CCDisj a b -> CCDisj (ckinst ks a) (ckinst ks b)

let ckinst_vf (ks: list kind) (t: ctyp) : rview = view_row (ckinst ks t)

(** * Local closure of canonical forms

    `clc_at n c` holds when every region reference of `c` is `lc_rr n`, as
    `lc_ty_at` on types. *)

let rec clc_at (n: nat) (c: ctyp) : Tot bool (decreases c) =
  match c with
  | CVar _ | CCon _ _ -> true
  | CApp a b -> clc_at n a && clc_at n b
  | CForall _ a -> clc_at n a
  | CConstr cc a -> clc_constr_at n cc && clc_at n a
  | CRow es ts -> clc_ents_at n es && clc_list_at n ts

and clc_pay_at (n: nat) (p: cpayload) : Tot bool (decreases p) =
  match p with
  | PTy c -> clc_at n c
  | PEff _ cs -> clc_list_at n cs
  | PRegion r -> lc_rr n r

and clc_ent_at (n: nat) (e: centry) : Tot bool (decreases e) =
  match e with
  | (k, p) -> lc_key n k && clc_pay_at n p

and clc_ents_at (n: nat) (es: list centry) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: es -> clc_ent_at n e && clc_ents_at n es

and clc_list_at (n: nat) (cs: list ctyp) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: cs -> clc_at n c && clc_list_at n cs

and clc_constr_at (n: nat) (cc: cconstr) : Tot bool (decreases cc) =
  match cc with
  | CCLacks k c -> lc_key n k && clc_at n c
  | CCDisj a b -> clc_at n a && clc_at n b
