import Flapjack.Pancake.Semantics.CrepProps

/-!
# `crepProps$every_exp` over the exact `CrepExpHOL` carrier

`crepEveryExpW` (`CrepProps.lean`) renders `crepPropsScript.sml`'s `every_exp_def`
over `CrepExp (BitVec width)`, while the reviewed exact `crep_to_loop` compiler
(`compile_exp_def`, `compile_def`) and `exps_of_def` use the exact `CrepExpHOL
width` carrier. `crepEveryExpHOL` is the same definition, clause for clause, over
`CrepExpHOL`, with HOL's `bool`-valued predicate and result rendered as `Prop`
(as for loopProps `every_prog`), so a HOL predicate such as
`λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2` is stated literally.
-/

namespace Flapjack

mutual
/-- Exact HOL `every_exp_def` (`crepPropsScript.sml`) over `CrepExpHOL width`:
the predicate holds at the expression and, recursively, at every
subexpression. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "every_exp_def"]
def crepEveryExpHOL {width : Nat} [NeZero width] (predicate : CrepExpHOL width → Prop) :
    CrepExpHOL width → Prop
  | .const value => predicate (.const value)
  | .var name => predicate (.var name)
  | .load address => predicate (.load address) ∧ crepEveryExpHOL predicate address
  | .load32 address => predicate (.load32 address) ∧ crepEveryExpHOL predicate address
  | .loadByte address => predicate (.loadByte address) ∧ crepEveryExpHOL predicate address
  | .loadGlob address => predicate (.loadGlob address)
  | .op operator arguments =>
      predicate (.op operator arguments) ∧ crepEveryExpListHOL predicate arguments
  | .crepOp operator arguments =>
      predicate (.crepOp operator arguments) ∧ crepEveryExpListHOL predicate arguments
  | .cmp operator left right =>
      predicate (.cmp operator left right) ∧ crepEveryExpHOL predicate left ∧
        crepEveryExpHOL predicate right
  | .shift operator left right =>
      predicate (.shift operator left right) ∧ crepEveryExpHOL predicate left ∧
        crepEveryExpHOL predicate right
  | .baseAddr => predicate .baseAddr
  | .topAddr => predicate .topAddr

/-- HOL's `EVERY (every_exp P)` over the argument lists of `Op`/`Crepop`, written
as a mutual list recursion for Lean's nested-inductive termination (Flapjack
infrastructure; `crepEveryExpListHOL_iff` is the membership form). -/
def crepEveryExpListHOL {width : Nat} [NeZero width] (predicate : CrepExpHOL width → Prop) :
    List (CrepExpHOL width) → Prop
  | [] => True
  | expression :: expressions =>
      crepEveryExpHOL predicate expression ∧ crepEveryExpListHOL predicate expressions
end

/-- `crepEveryExpListHOL` is HOL's `EVERY (every_exp P)` (Flapjack infrastructure). -/
theorem crepEveryExpListHOL_iff {width : Nat} [NeZero width]
    (predicate : CrepExpHOL width → Prop) (es : List (CrepExpHOL width)) :
    crepEveryExpListHOL predicate es ↔ ∀ e ∈ es, crepEveryExpHOL predicate e := by
  induction es with
  | nil => simp [crepEveryExpListHOL]
  | cons e es ih => simp [crepEveryExpListHOL, ih]

end Flapjack
