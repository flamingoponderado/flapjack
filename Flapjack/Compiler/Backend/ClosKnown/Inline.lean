module

public import Flapjack.Compiler.Backend.ClosKnown.Config
public import Flapjack.Compiler.Backend.ClosKnown.Inline.Free
public import Flapjack.Compiler.Backend.ClosCall
public import Flapjack.Compiler.Backend.ClosLang.Budget

@[expose] public section

/-! Source-shaped size and closure checks for the inlining decision. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

mutual
/-- The original list-valued closure-presence predicate. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "contains_closures_def"]
def containsClosuresHOL : List Exp → Bool
  | [] => false
  | e :: es => containsClosuresExpHOL e || containsClosuresHOL es
termination_by es => sizeOf es

/-- Single-expression helper for the source list traversal. -/
def containsClosuresExpHOL : Exp → Bool
  | .var .. => false
  | .fn .. | .letrec .. => true
  | .ifThenElse _ x y z => containsClosuresExpHOL x || containsClosuresExpHOL y || containsClosuresExpHOL z
  | .let _ xs body => containsClosuresHOL xs || containsClosuresExpHOL body
  | .raise _ body | .tick _ body => containsClosuresExpHOL body
  | .handle _ x y => containsClosuresExpHOL x || containsClosuresExpHOL y
  | .op _ _ xs | .call _ _ _ xs => containsClosuresHOL xs
  | .app _ _ fn xs => containsClosuresExpHOL fn || containsClosuresHOL xs
termination_by e => sizeOf e
end

mutual
/-- The original size of an expression list; ticks contribute no node. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_aux_def"]
def getSizeAuxHOL : List Exp → Nat
  | [] => 0
  | e :: es => getSizeExpHOL e + getSizeAuxHOL es
termination_by es => sizeOf es

/-- Single-expression helper for the source size traversal. -/
def getSizeExpHOL : Exp → Nat
  | .var .. => 1
  | .tick _ e => getSizeExpHOL e
  | .ifThenElse _ x y z => 1 + getSizeExpHOL x + getSizeExpHOL y + getSizeExpHOL z
  | .let _ xs body => 1 + getSizeAuxHOL xs + getSizeExpHOL body
  | .raise _ e | .fn _ _ _ _ e => 1 + getSizeExpHOL e
  | .handle _ x y => 1 + getSizeExpHOL x + getSizeExpHOL y
  | .op _ _ xs | .call _ _ _ xs => 1 + getSizeAuxHOL xs
  | .letrec _ _ _ fs body => 1 + getSizeFunsHOL fs + getSizeExpHOL body
  | .app _ _ e xs => 1 + getSizeExpHOL e + getSizeAuxHOL xs
termination_by e => sizeOf e

/-- Helper for the source traversal of recursive-function bodies. -/
def getSizeFunsHOL : List (Nat × Exp) → Nat
  | [] => 0
  | (_, e) :: es => getSizeExpHOL e + getSizeFunsHOL es
termination_by es => sizeOf es
end

/-- The original size of one closure expression. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_def"]
def getSizeHOL (e : Exp) : Nat := getSizeAuxHOL [e]

mutual
/-- The source's budgeted list traversal, stopping as soon as the budget
reaches zero. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_sc_aux_def"]
def getSizeScAuxHOL (n : Nat) : List Exp → Nat
  | [] => n
  | [e] => getSizeScExpHOL n e
  | e :: next :: es =>
    if n = 0 then n else
      let remaining := getSizeScExpHOL n e
      if remaining = 0 then remaining else getSizeScAuxHOL remaining (next :: es)
termination_by es => sizeOf es

/-- Single-expression helper for the source's budgeted traversal. -/
def getSizeScExpHOL (n : Nat) : Exp → Nat
  | .var .. => n - 1
  | .tick _ e => getSizeScExpHOL n e
  | .ifThenElse _ x y z =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScExpHOL n x
      if n = 0 then 0 else
        let n := getSizeScExpHOL n y
        if n = 0 then 0 else getSizeScExpHOL n z
  | .let _ xs body =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScAuxHOL n xs
      if n = 0 then 0 else getSizeScExpHOL n body
  | .raise _ e | .fn _ _ _ _ e =>
    let n := n - 1
    if n = 0 then 0 else getSizeScExpHOL n e
  | .handle _ x y =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScExpHOL n x
      if n = 0 then 0 else getSizeScExpHOL n y
  | .op _ _ xs | .call _ _ _ xs =>
    let n := n - 1
    if n = 0 then 0 else getSizeScAuxHOL n xs
  | .letrec _ _ _ fs body =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScFunsHOL n fs
      if n = 0 then 0 else getSizeScExpHOL n body
  | .app _ _ e xs =>
    let n := n - 1
    if n = 0 then 0 else
      let n := getSizeScExpHOL n e
      if n = 0 then 0 else getSizeScAuxHOL n xs
termination_by e => sizeOf e

/-- Budgeted traversal of the bodies in a recursive function group. -/
def getSizeScFunsHOL (n : Nat) : List (Nat × Exp) → Nat
  | [] => n
  | (_, e) :: es =>
    let remaining := getSizeScExpHOL n e
    if remaining = 0 then 0 else getSizeScFunsHOL remaining es
termination_by es => sizeOf es
end

/-- Return the source expression size when it fits within the limit. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_sc_def"]
def getSizeScHOL (limit : Nat) (e : Exp) : Option Nat :=
  let remaining := getSizeScAuxHOL (limit + 1) [e]
  if remaining = 0 then none else some (limit + 1 - remaining)

/-- Construct the source closure approximation using its short-circuit size
check. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "clos_approx_def"]
def closApproxHOL (maxSize loc arity : Nat) (body : Exp) : ValApprox :=
  match getSizeScHOL maxSize body with
  | none => .closNoInline loc arity
  | some size => .clos loc arity body size

/-- The original inlining decision, including closure and closedness checks. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "decide_inline_def"]
def decideInlineHOL {L : Type} (c : Config) (approx : ValApprox) (loc : Option L)
    (arity : Nat) : InliningDecision :=
  match approx with
  | .closNoInline target n =>
      if loc.isNone = true ∧ arity = n then .annotate target else .nothing
  | .clos target n body size =>
      if loc.isNone = true ∧ arity = n then
        if size < c.inlineFactor * (1 + arity) ∧ containsClosuresHOL [body] = false ∧
          closedHOL (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body) = true then
          .letInline body
        else .annotate target
      else .nothing
  | _ => .nothing

/-- The checked optimizer uses the total source inlining decision. -/
def decideInlineFuel (_fuel : Nat) (c : Config) (approx : ValApprox) (loc : Option Nat)
    (arity : Nat) : Option InliningDecision := some (decideInlineHOL c approx loc arity)

end Flapjack.Compiler.Backend.ClosKnown
