import Flapjack.CakeParser.ParseTree
import Flapjack.CakeParser.Grammar
import Flapjack.AstHOL.Syntax

/-! CakeML parse-tree conversion. The type converter uses a structurally
bounded worker; its public wrapper derives the bound from the input tree.
It remains untagged until its bound and full correspondence are proved. -/
namespace Flapjack.CakeParser.PtreeConversion
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL

private def children (n : Nonterminal) : ParseTree → Option (List ParseTree)
  | .node (.inl actual) _ xs => if actual == n then some xs else none
  | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "tokcheck_def"]
def tokcheck (pt : ParseTree) (tok : Token) : Bool := pt.token == some tok

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "Long_Short_def"]
def longShort : Path → MlString → Ident MlString MlString
  | .end, s => .short s
  | .mod x xs, s => .long x (longShort xs s)

private def tyvar (pt : ParseTree) : Option MlString :=
  match pt.token with
  | some (.tyvarT s) => some s
  | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_UQTyop_def"]
def ptreeUQTyop (pt : ParseTree) : Option MlString := do
  let [leaf] ← children .nUQTyOp pt | none
  match leaf.token with
  | some (.symbolT s) | some (.alphaT s) => some s
  | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_TyvarN_def"]
def ptreeTyvarN (pt : ParseTree) : Option MlString := do
  let [leaf] ← children .nTyvarN pt | none
  tyvar leaf

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_Tyop_def"]
def ptreeTyop (pt : ParseTree) : Option (Ident MlString MlString) := do
  let [child] ← children .nTyOp pt | none
  match child.token with
  | some (.longidT path s) => some (longShort path s)
  | _ => (ptreeUQTyop child).map Ident.short

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_V_def"]
def ptreeV (pt : ParseTree) : Option MlString := do
  let [leaf] ← children .nV pt | none
  match leaf.token with
  | some (.alphaT s) | some (.symbolT s) => some s
  | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_FQV_def"]
def ptreeFQV (pt : ParseTree) : Option (Ident MlString MlString) := do
  let [child] ← children .nFQV pt | none
  match ptreeV child with
  | some s => some (.short s)
  | none => match child.token with
    | some (.longidT path s) => some (longShort path s)
    | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "tuplify_def"]
def tuplify : List AstT → Option AstT
  | [] => none
  | [t] => some t
  | ts => some (.attup ts)

mutual
private def typeWorker : Nat → Nonterminal → ParseTree → Option AstT
  | 0, _, _ => none
  | fuel + 1, n, pt => do
    let xs ← children n pt
    match n, xs with
    | .nType, [p] => ptypeWorker fuel p >>= tuplify
    | .nType, [p, arrow, rest] => do
      if !tokcheck arrow .arrowT then none else
      let lhs ← ptypeWorker fuel p >>= tuplify
      let rhs ← typeWorker fuel .nType rest
      some (.atfun lhs rhs)
    | .nDType, [base] => typeWorker fuel .nTbase base
    | .nDType, [first, op] => do
      let arg ← typeWorker fuel .nDType first
      let name ← ptreeTyop op
      some (.atapp [arg] name)
    | .nTbase, [base] =>
      match tyvar base with
      | some v => some (.atvar v)
      | none => (ptreeTyop base).map (AstT.atapp [])
    | .nTbase, [lp, t, rp] =>
      if tokcheck lp .lparT && tokcheck rp .rparT then typeWorker fuel .nType t else none
    | .nTbase, [lp, ts, rp, op] => do
      if !(tokcheck lp .lparT && tokcheck rp .rparT) then none else
      let args ← typeList2Worker fuel ts
      let name ← ptreeTyop op
      some (.atapp args name)
    | _, _ => none

private def typeList2Worker : Nat → ParseTree → Option (List AstT)
  | 0, _ => none
  | fuel + 1, pt => do
    let [first, comma, rest] ← children .nTypeList2 pt | none
    if !tokcheck comma .commaT then none else
    let t ← typeWorker fuel .nType first
    let ts ← typeList1Worker fuel rest
    some (t :: ts)

private def typeList1Worker : Nat → ParseTree → Option (List AstT)
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nTypeList1 pt
    match xs with
    | [first] => do
      let t ← typeWorker fuel .nType first
      some [t]
    | [first, comma, rest] => do
      if !tokcheck comma .commaT then none else
      let t ← typeWorker fuel .nType first
      let ts ← typeList1Worker fuel rest
      some (t :: ts)
    | _ => none

private def ptypeWorker : Nat → ParseTree → Option (List AstT)
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nPType pt
    match xs with
    | [first] => do
      let t ← typeWorker fuel .nDType first
      some [t]
    | [first, star, rest] => do
      if !tokcheck star .starT then none else
      let t ← typeWorker fuel .nDType first
      let ts ← ptypeWorker fuel rest
      some (t :: ts)
    | _ => none
end

mutual
private def treeSize : ParseTree → Nat
  | .leaf _ _ => 1
  | .node _ _ xs => 1 + forestSize xs
termination_by t => sizeOf t

private def forestSize : List ParseTree → Nat
  | [] => 0
  | x :: xs => treeSize x + forestSize xs
termination_by xs => sizeOf xs
end

/-- Convert a type parse tree using a bound based on its size. This is
Flapjack infrastructure until the bound is proved sufficient for every tree. -/
def ptreeType (n : Nonterminal) (pt : ParseTree) : Option AstT :=
  typeWorker (treeSize pt + 1) n pt


private def tyvarList : Nat → ParseTree → Option (List MlString)
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nTyVarList pt
    match xs with
    | [x] => (ptreeTyvarN x).map (fun v => [v])
    | [front, comma, last] => do
      if !tokcheck comma .commaT then none else
      let vs ← tyvarList fuel front
      let v ← ptreeTyvarN last
      some (vs ++ [v])
    | _ => none

/-- Convert a type constructor name and its type parameters. The list worker
uses a tree-size bound; its correspondence with HOL remains to be proved. -/
def ptreeTypeName (pt : ParseTree) : Option (List MlString × MlString) := do
  let xs ← children .nTypeName pt
  match xs with
  | [name] => do
    let n ← ptreeUQTyop name
    some ([], n)
  | [param, name] => do
    let v ← tyvar param
    let n ← ptreeUQTyop name
    some ([v], n)
  | [lp, params, rp, name] => do
    if !(tokcheck lp .lparT && tokcheck rp .rparT) then none else
    let vs ← tyvarList (treeSize params + 1) params
    let n ← ptreeUQTyop name
    some (vs, n)
  | _ => none

/-- Convert a type-abbreviation declaration, preserving its source span.
This uses the bounded type converter and is not yet a reviewed HOL port. -/
def ptreeTypeAbbrevDec (pt : ParseTree) : Option Dec := do
  let .node _ loc _ := pt | none
  let [keyword, name, equals, typ] ← children .nTypeAbbrevDec pt | none
  if !(tokcheck keyword .typeT && tokcheck equals .equalsT) then none else
  let (vars, n) ← ptreeTypeName name
  let t ← ptreeType .nType typ
  some (.dtabbrev loc vars n t)


@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_UQConstructorName_def"]
def ptreeUQConstructorName (pt : ParseTree) : Option MlString := do
  let [leaf] ← children .nUQConstructorName pt | none
  match leaf.token with
  | some (.alphaT s) => some s
  | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_ConstructorName_def"]
def ptreeConstructorName (pt : ParseTree) : Option (Ident MlString MlString) := do
  let [child] ← children .nConstructorName pt | none
  match ptreeUQConstructorName child with
  | some s => some (.short s)
  | none => match child.token with
    | some (.longidT path s) => some (longShort path s)
    | _ => none

private def uppercase (s : MlString) : Bool :=
  match s.explode with
  | c :: _ => 65 ≤ c.toNat && c.toNat ≤ 90
  | [] => false

private def constructorName (s : MlString) : Bool :=
  s == ofString "::" || uppercase s

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_OpID_def"]
def ptreeOpID (pt : ParseTree) : Option Exp := do
  let [leaf] ← children .nOpID pt | none
  match leaf.token with
  | some (.alphaT s) =>
    some (if constructorName s then .con (some (.short s)) [] else .var (.short s))
  | some (.symbolT s) =>
    some (if s == ofString "::" then .con (some (.short s)) [] else .var (.short s))
  | some (.longidT path s) =>
    let name := longShort path s
    some (if constructorName s then .con (some name) [] else .var name)
  | some .starT => some (.var (.short (ofString "*")))
  | some .equalsT => some (.var (.short (ofString "=")))
  | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "EtoPat_def"]
def etoPat : Exp → Option Pat
  | .con c [] => some (.pcon c [])
  | .var (.short n) => some (.pvar n)
  | .var (.long m rest) => some (.pcon (some (.long m rest)) [])
  | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "Papply_def"]
def papply (pat arg : Pat) : Pat :=
  match pat with
  | .pcon c args => .pcon c (args ++ [arg])
  | _ => pat

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "maybe_handleRef_def"]
def maybeHandleRef : Pat → Pat
  | .pcon (some (.short s)) [p] => if s == ofString "Ref" then .pref p else .pcon (some (.short s)) [p]
  | p => p

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_Eliteral_def"]
def ptreeEliteral (pt : ParseTree) : Option Exp := do
  let [leaf] ← children .nEliteral pt | none
  match leaf.token with
  | some (.intT i) => some (.lit (.intLit i))
  | some (.charT c) => some (.lit (.char c))
  | some (.stringT s) => some (.lit (.strLit s))
  | some (.wordT n) => some (.lit (.word64 (BitVec.ofNat 64 n)))
  | some (.ffiT s) => some (.app (.ffi s) [])
  | _ => none

private def emptyListPat : Pat := .pcon (some (.short (ofString "[]"))) []
private def consPat (x xs : Pat) : Pat := .pcon (some (.short (ofString "::"))) [x, xs]

mutual
private def patternWorker : Nat → Nonterminal → ParseTree → Option Pat
  | 0, _, _ => none
  | fuel + 1, n, pt => do
    let xs ← children n pt
    match n, xs with
    | .nPbase, [x] =>
      match patternWorker fuel .nPtuple x with
      | some p => some p
      | none => match ptreeConstructorName x with
        | some name => some (.pcon (some name) [])
        | none => match ptreeV x with
          | some name => some (.pvar name)
          | none => match x.token with
            | some (.intT i) => some (.plit (.intLit i))
            | some (.stringT s) => some (.plit (.strLit s))
            | some (.charT c) => some (.plit (.char c))
            | some .underbarT => some .pany
            | _ => none
    | .nPbase, [l, r] =>
      if tokcheck l .lbrackT && tokcheck r .rbrackT then some emptyListPat
      else if tokcheck l .opT then ptreeOpID r >>= etoPat
      else none
    | .nPbase, [l, ps, r] => do
      if !(tokcheck l .lbrackT && tokcheck r .rbrackT) then none else
      let pats ← patternListWorker fuel ps
      some (pats.foldr consPat emptyListPat)
    | .nPConApp, [c] => (ptreeConstructorName c).map (fun name => .pcon (some name) [])
    | .nPConApp, [c, p] => do
      let cp ← patternWorker fuel .nPConApp c
      let arg ← patternWorker fuel .nPbase p
      some (papply cp arg)
    | .nPapp, [p] => patternWorker fuel .nPbase p
    | .nPapp, [c, p] => do
      let cp ← patternWorker fuel .nPConApp c
      let arg ← patternWorker fuel .nPbase p
      some (maybeHandleRef (papply cp arg))
    | .nPcons, [p] => patternWorker fuel .nPapp p
    | .nPcons, [p, tok, rest] => do
      if !tokcheck tok (.symbolT (ofString "::")) then none else
      let p ← patternWorker fuel .nPapp p
      let rest ← patternWorker fuel .nPcons rest
      some (consPat p rest)
    | .nPas, [p] => patternWorker fuel .nPcons p
    | .nPas, [v, tok, p] => do
      if !tokcheck tok .asT then none else
      let pat ← patternWorker fuel .nPcons p
      let name ← ptreeV v
      some (.pas pat name)
    | .nPattern, [p] => patternWorker fuel .nPas p
    | .nPattern, [p, tok, typ] => do
      if !tokcheck tok .colonT then none else
      let pat ← patternWorker fuel .nPas p
      let typ ← ptreeType .nType typ
      some (.ptannot pat typ)
    | .nPtuple, [l, r] =>
      if tokcheck l .lparT && tokcheck r .rparT then some (.pcon none []) else none
    | .nPtuple, [l, ps, r] => do
      if !(tokcheck l .lparT && tokcheck r .rparT) then none else
      let pats ← patternListWorker fuel ps
      match pats with
      | [] => none
      | [p] => some p
      | ps => some (.pcon none ps)
    | _, _ => none

private def patternListWorker : Nat → ParseTree → Option (List Pat)
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nPatternList pt
    match xs with
    | [p] => (patternWorker fuel .nPattern p).map (fun p => [p])
    | [p, comma, rest] => do
      if !tokcheck comma .commaT then none else
      let p ← patternWorker fuel .nPattern p
      let rest ← patternListWorker fuel rest
      some (p :: rest)
    | _ => none
end

/-- Convert a pattern using a tree-size bound. This infrastructure is not yet
proved equivalent to the original unbounded HOL conversion. -/
def ptreePattern (n : Nonterminal) (pt : ParseTree) : Option Pat :=
  patternWorker (treeSize pt + 1) n pt


private def symOp (p : List HolChar → Bool) (xs : List ParseTree) : Option (Ident MlString MlString) := do
  let [leaf] := xs | none
  let some (.symbolT s) := leaf.token | none
  if p s.explode then some (.short s) else none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "ptree_Op_def"]
def ptreeOp (pt : ParseTree) : Option (Ident MlString MlString) := do
  let .node (.inl n) _ xs := pt | none
  match n with
  | .nMultOps => match xs with
    | [leaf] =>
      if tokcheck leaf .starT then some (.short (ofString "*"))
      else match leaf.token with
        | some (.alphaT s) => if s == ofString "mod" || s == ofString "div" then some (.short s) else none
        | _ => symOp Grammar.validMultSym xs
    | _ => none
  | .nAddOps => symOp Grammar.validAddSym xs
  | .nListOps => symOp Grammar.validListSym xs
  | .nRelOps => match symOp Grammar.validRelSym xs with
    | some x => some x
    | none => match xs with
      | [leaf] => if tokcheck leaf .equalsT then some (.short (ofString "=")) else none
      | _ => none
  | .nCompOps => match xs with
    | [leaf] => match leaf.token with
      | some (.symbolT s) => if s == ofString ":=" then some (.short s) else none
      | some (.alphaT s) => if s == ofString "o" then some (.short s) else none
      | _ => none
    | _ => none
  | _ => none

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "mk_binop_def"]
def mkBinop (op : Ident MlString MlString) (a b : Exp) : Exp :=
  if op == .short (ofString "::") then .con (some (.short (ofString "::"))) [a, b]
  else .app .opapp [.app .opapp [.var op, a], b]

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "bind_loc_def"]
def bindLoc (e : Exp) (loc : Flapjack.Misc.Location.Locs) : Exp :=
  match e with
  | .lannot _ _ => e
  | _ => .lannot e loc

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "strip_loc_expr_def"]
def stripLocExpr : Exp → Exp × Option Flapjack.Misc.Location.Locs
  | .lannot e loc => ((stripLocExpr e).1, some loc)
  | e => (e, none)

private def mergeLocs (a b : Flapjack.Misc.Location.Locs) : Flapjack.Misc.Location.Locs :=
  match a, b with | .locs start _, .locs _ stop => .locs start stop

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "mkAst_App_def"]
def mkAstApp (a b : Exp) : Exp :=
  let (bare, l1) := stripLocExpr a
  match bare with
  | .con name args =>
    if name == some (.short (ofString "Ref")) && args.isEmpty then .app .opref [b]
    else
      let (b', l2) := stripLocExpr b
      let result := Exp.con name (args ++ [b'])
      match l1, l2 with
      | some l, some r => .lannot result (mergeLocs l r)
      | _, _ => result
  | .app (.ffi name) args => .app (.ffi name) (args ++ [b])
  | _ => .app .opapp [a, b]

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "dePat_def"]
def dePat (p : Pat) (body : Exp) : MlString × Exp :=
  match p with
  | .pvar n => (n, body)
  | _ => (ofString "", .mat (.var (.short (ofString ""))) [(p, body)])

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "mkFun_def"]
def mkFun (p : Pat) (body : Exp) : Exp :=
  let (v, e) := dePat p body
  .fn v e

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "letFromPat_def"]
def letFromPat (p : Pat) (rhs body : Exp) : Exp :=
  match p with
  | .pany => .let_ none rhs body
  | .pvar v => .let_ (some v) rhs body
  | _ => .mat rhs [(p, body)]

private def seqEncode : List Exp → Option Exp
  | [] => none
  | [x] => some x
  | x :: xs => (seqEncode xs).map (Exp.let_ none x)

private abbrev FunDecl := MlString × MlString × Exp
private abbrev LetDecl := Sum (Pat × Exp) (List FunDecl)

mutual
private def exprWorker : Nat → Nonterminal → ParseTree → Option Exp
  | 0, _, _ => none
  | fuel + 1, n, pt => do
    let .node _ loc _ := pt | none
    let xs ← children n pt
    let e ← match n, xs with
      | .nEbase, [l, p, r] =>
        if tokcheck l .lparT then do
          if !tokcheck r .rparT then none else
          seqWorker fuel p >>= seqEncode
        else do
          if !(tokcheck l .lbrackT && tokcheck r .rbrackT) then none else
          let es ← exprListWorker fuel p
          some (es.foldr (fun x acc => .con (some (.short (ofString "::"))) [x, acc])
            (.con (some (.short (ofString "[]"))) []))
      | .nEbase, [x] => match ptreeEliteral x with
        | some e => some e
        | none => match ptreeFQV x with
          | some v => some (.var v)
          | none => match ptreeConstructorName x with
            | some c => some (.con (some c) [])
            | none => exprWorker fuel .nEtuple x
      | .nEbase, [l, r] =>
        if tokcheck l .lparT && tokcheck r .rparT then some (.con none [])
        else if tokcheck l .lbrackT && tokcheck r .rbrackT then some (.con (some (.short (ofString "[]"))) [])
        else if tokcheck l .opT then ptreeOpID r else none
      | .nEbase, [lt, ds, it, body, et] => do
        if !(tokcheck lt .letT && tokcheck it .inT && tokcheck et .endT) then none else
        let decls ← letDecsWorker fuel ds
        let body ← seqWorker fuel body >>= seqEncode
        some (decls.foldr (fun d acc => match d with
          | .inl (p, e) => letFromPat p e acc
          | .inr fs => .letrec fs acc) body)
      | .nEapp, [x] => exprWorker fuel .nEbase x
      | .nEapp, [x, y] => do
        let a ← exprWorker fuel .nEapp x
        let b ← exprWorker fuel .nEbase y
        some (mkAstApp a b)
      | .nEtuple, [l, es, r] => do
        if !(tokcheck l .lparT && tokcheck r .rparT) then none else
        let es ← exprListWorker fuel es
        some (.con none es)
      | .nEmult, [x] => exprWorker fuel .nEapp x
      | .nEadd, [x] => exprWorker fuel .nEmult x
      | .nElistop, [x] => exprWorker fuel .nEadd x
      | .nErel, [x] => exprWorker fuel .nElistop x
      | .nEcomp, [x] => exprWorker fuel .nErel x
      | .nEbefore, [x] => exprWorker fuel .nEcomp x
      | .nEtyped, [x] => exprWorker fuel .nEbefore x
      | .nElogicAND, [x] => exprWorker fuel .nEtyped x
      | .nElogicOR, [x] => exprWorker fuel .nElogicAND x
      | .nEhandle, [x] => exprWorker fuel .nElogicOR x
      | .nE, [x] => exprWorker fuel .nEhandle x
      | .nEmult, [a, op, b] => binaryWorker fuel .nEmult .nEapp a op b
      | .nEadd, [a, op, b] => binaryWorker fuel .nEadd .nEmult a op b
      | .nElistop, [a, op, b] => binaryWorker fuel .nEadd .nElistop a op b
      | .nErel, [a, op, b] => binaryWorker fuel .nErel .nElistop a op b
      | .nEcomp, [a, op, b] => binaryWorker fuel .nEcomp .nErel a op b
      | .nEbefore, [a, op, b] => do
        if !tokcheck op (.alphaT (ofString "before")) then none else
        let a ← exprWorker fuel .nEbefore a
        let b ← exprWorker fuel .nEcomp b
        some (mkBinop (.short (ofString "before")) a b)
      | .nEtyped, [x, colon, t] => do
        if !tokcheck colon .colonT then none else
        let x ← exprWorker fuel .nEbefore x
        let t ← ptreeType .nType t
        some (.tannot x t)
      | .nElogicAND, [a, op, b] => do
        if !tokcheck op .andalsoT then none else
        let a ← exprWorker fuel .nElogicAND a
        let b ← exprWorker fuel .nEtyped b
        some (.log .andalso a b)
      | .nElogicOR, [a, op, b] => do
        if !tokcheck op .orelseT then none else
        let a ← exprWorker fuel .nElogicOR a
        let b ← exprWorker fuel .nElogicAND b
        some (.log .orelse a b)
      | .nEhandle, [x, tok, clauses] => do
        if !tokcheck tok .handleT then none else
        let x ← exprWorker fuel .nElogicOR x
        let clauses ← pesWorker fuel clauses
        some (.handle x clauses)
      | .nE, [tok, x] => do
        if !tokcheck tok .raiseT then none else
        (exprWorker fuel .nE x).map Exp.raise
      | .nE, [tok, x, separator, body] =>
        if tokcheck tok .fnT && tokcheck separator .darrowT then do
          let p ← ptreePattern .nPattern x
          let body ← exprWorker fuel .nE body
          some (mkFun p body)
        else if tokcheck tok .caseT && tokcheck separator .ofT then do
          let x ← exprWorker fuel .nE x
          let clauses ← pesWorker fuel body
          some (.mat x clauses)
        else none
      | .nE, [it, guard, tt, yes, et, no] => do
        if !(tokcheck it .ifT && tokcheck tt .thenT && tokcheck et .elseT) then none else
        let guard ← exprWorker fuel .nE guard
        let yes ← exprWorker fuel .nE yes
        let no ← exprWorker fuel .nE no
        some (.if_ guard yes no)
      | _, _ => none
    some (bindLoc e loc)

private def binaryWorker : Nat → Nonterminal → Nonterminal → ParseTree → ParseTree → ParseTree → Option Exp
  | 0, _, _, _, _, _ => none
  | fuel + 1, left, right, a, op, b => do
    let a ← exprWorker fuel left a
    let op ← ptreeOp op
    let b ← exprWorker fuel right b
    some (mkBinop op a b)

private def exprListWorker : Nat → ParseTree → Option (List Exp)
  | 0, _ => none
  | fuel + 1, pt => do
    let .node (.inl n) _ xs := pt | none
    match n, xs with
    | .nElist1, [x] => (exprWorker fuel .nE x).map (fun e => [e])
    | .nElist1, [x, comma, rest] | .nElist2, [x, comma, rest] => do
      if !tokcheck comma .commaT then none else
      let x ← exprWorker fuel .nE x
      let rest ← exprListWorker fuel rest
      some (x :: rest)
    | _, _ => none

private def seqWorker : Nat → ParseTree → Option (List Exp)
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nEseq pt
    match xs with
    | [x] => (exprWorker fuel .nE x).map (fun e => [e])
    | [x, semi, rest] => do
      if !tokcheck semi .semicolonT then none else
      let x ← exprWorker fuel .nE x
      let rest ← seqWorker fuel rest
      some (x :: rest)
    | _ => none

private def pbaseListWorker : Nat → ParseTree → Option (List Pat)
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nPbaseList1 pt
    match xs with
    | [x] => (ptreePattern .nPbase x).map (fun p => [p])
    | [x, rest] => do
      let x ← ptreePattern .nPbase x
      let rest ← pbaseListWorker fuel rest
      some (x :: rest)
    | _ => none

private def fdeclWorker : Nat → ParseTree → Option FunDecl
  | 0, _ => none
  | fuel + 1, pt => do
    let [name, pats, eq, body] ← children .nFDecl pt | none
    if !tokcheck eq .equalsT then none else
    let name ← ptreeV name
    let p :: ps ← pbaseListWorker fuel pats | none
    let body ← exprWorker fuel .nE body
    let (arg, body) := dePat p (ps.foldr mkFun body)
    some (name, arg, body)

private def andFdeclsWorker : Nat → ParseTree → Option (List FunDecl)
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nAndFDecls pt
    match xs with
    | [x] => (fdeclWorker fuel x).map (fun d => [d])
    | [ds, tok, d] => do
      if !tokcheck tok .andT then none else
      let ds ← andFdeclsWorker fuel ds
      let d ← fdeclWorker fuel d
      some (ds ++ [d])
    | _ => none

private def letDecsWorker : Nat → ParseTree → Option (List LetDecl)
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nLetDecs pt
    match xs with
    | [] => some []
    | [d, rest] => if tokcheck d .semicolonT then letDecsWorker fuel rest else do
      let d ← letDecWorker fuel d
      let rest ← letDecsWorker fuel rest
      some (d :: rest)
    | _ => none

private def letDecWorker : Nat → ParseTree → Option LetDecl
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nLetDec pt
    match xs with
    | [tok, fs] => do
      if !tokcheck tok .funT then none else
      (andFdeclsWorker fuel fs).map Sum.inr
    | [tok, pat, eq, body] => do
      if !(tokcheck tok .valT && tokcheck eq .equalsT) then none else
      let pat ← ptreePattern .nPattern pat
      let body ← exprWorker fuel .nE body
      some (.inl (pat, body))
    | _ => none

private def pesWorker : Nat → ParseTree → Option (List (Pat × Exp))
  | 0, _ => none
  | fuel + 1, pt => do
    let [p, arrow, rest] ← children .nPEs pt | none
    if !tokcheck arrow .darrowT then none else
    let p ← ptreePattern .nPattern p
    let (e, rest) ← peWorker fuel rest
    some ((p, e) :: rest)

private def peWorker : Nat → ParseTree → Option (Exp × List (Pat × Exp))
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nPE pt
    match xs with
    | [first, rest] =>
      if tokcheck first .raiseT then do
        let (e, rest) ← peWorker fuel rest
        some (.raise e, rest)
      else do
        let e ← exprWorker fuel .nElogicOR first
        let (isHandle, clauses) ← pesfxWorker fuel rest
        if isHandle then some (.handle e clauses, []) else some (e, clauses)
    | [tok, x, sep, rest] =>
      if tokcheck tok .fnT && tokcheck sep .darrowT then do
        let p ← ptreePattern .nPattern x
        let e ← exprWorker fuel .nE rest
        some (mkFun p e, [])
      else if tokcheck tok .caseT && tokcheck sep .ofT then do
        let e ← exprWorker fuel .nE x
        let ps ← pesWorker fuel rest
        some (.mat e ps, [])
      else none
    | [it, guard, tt, yes, et, no] => do
      if !(tokcheck it .ifT && tokcheck tt .thenT && tokcheck et .elseT) then none else
      let guard ← exprWorker fuel .nE guard
      let yes ← exprWorker fuel .nE yes
      let (no, rest) ← peWorker fuel no
      some (.if_ guard yes no, rest)
    | _ => none

private def pesfxWorker : Nat → ParseTree → Option (Bool × List (Pat × Exp))
  | 0, _ => none
  | fuel + 1, pt => do
    let xs ← children .nPEsfx pt
    match xs with
    | [] => some (false, [])
    | [tok, rest] =>
      if tokcheck tok .handleT then (pesWorker fuel rest).map (fun xs => (true, xs))
      else if tokcheck tok .barT then (pesWorker fuel rest).map (fun xs => (false, xs))
      else none
    | _ => none
end

/-- Convert an expression with a tree-size based recursion bound. This is
Flapjack infrastructure until the bound and correspondence with HOL are proved. -/
def ptreeExpr (n : Nonterminal) (pt : ParseTree) : Option Exp :=
  exprWorker (2 * treeSize pt + 1) n pt

end Flapjack.CakeParser.PtreeConversion
