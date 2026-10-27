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

end Flapjack.CakeParser.PtreeConversion
