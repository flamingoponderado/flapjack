import Flapjack.CakeParser.ParseTree
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

end Flapjack.CakeParser.PtreeConversion
