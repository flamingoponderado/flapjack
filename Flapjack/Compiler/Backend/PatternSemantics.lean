import Flapjack.Compiler.Backend.PatternCommon
import Flapjack.AstHOL.LitOp

/-! Input and output syntax of the CakeML pattern-match compiler. -/
namespace Flapjack.Compiler.Backend.PatternSemantics
open PatternCommon

/-- Pattern compiler input syntax. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "pat"]
inductive Pat where
  | any
  | cons : Option (Nat × Option (List (Nat × Nat))) → List Pat → Pat
  | or : Pat → Pat → Pat
  | lit : AstHOL.Lit → Pat
  | ref : Pat → Pat

/-- A test on the value at a position. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "dTest"]
inductive DTest where
  | tagLenEq : Nat → Nat → DTest
  | litEq : AstHOL.Lit → DTest
  deriving DecidableEq

/-- Boolean structure of a decision-tree test. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "dGuard"]
inductive DGuard where
  | posTest : Position → DTest → DGuard
  | not : DGuard → DGuard
  | conj : DGuard → DGuard → DGuard
  | disj : DGuard → DGuard → DGuard
  | true_
  deriving DecidableEq

/-- Decision tree emitted by the pattern compiler. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "dTree"]
inductive DTree where
  | leaf : Nat → DTree
  | fail | typeFail
  | if_ : DGuard → DTree → DTree → DTree

end Flapjack.Compiler.Backend.PatternSemantics
