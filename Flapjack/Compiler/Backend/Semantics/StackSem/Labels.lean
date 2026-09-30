import Flapjack.Compiler.Backend.Semantics.StackSem.State
import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.StackLang.Prog

/-!
# StackSem label collection and location checking

Exact definitions from `stackSemScript.sml`: `get_labels_def` and
`loc_check_def`. These helpers are part of the HOL semantics, not Flapjack-only
infrastructure. As in the rest of this port, HOL sets are represented as
predicates (`Nat × Nat → Prop`); the code map uses the reviewed Spt carrier.
-/

namespace Flapjack.StackSem

open Flapjack.Compiler.Backend.StackLang

/-- HOL StackSem `get_labels_def` (`stackSemScript.sml:667-680`): collect
return and handler continuation labels as well as labels recursively nested
inside those continuations. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "get_labels_def"]
def getLabels {α : Type} : ProgM α → (Nat × Nat) → Prop
  | .seq first second => fun label => getLabels first label ∨ getLabels second label
  | .ite _ _ _ thenBranch elseBranch =>
      fun label => getLabels thenBranch label ∨ getLabels elseBranch label
  | .loop body => getLabels body
  | .call returnHandler _ handler =>
      match returnHandler with
      | none => fun _ => False
      | some (body, _link, first, second) =>
          let handlerLabels :=
            match handler with
            | none => fun _ => False
            | some (handlerBody, handlerFirst, handlerSecond) =>
                fun label => label = (handlerFirst, handlerSecond) ∨
                  getLabels handlerBody label
          fun label => label = (first, second) ∨ getLabels body label ∨
            handlerLabels label
  | _ => fun _ => False
termination_by program => sizeOf program
decreasing_by all_goals simp_wf <;> omega

/-- HOL StackSem `loc_check_def` (`stackSemScript.sml:682-686`). A label with
zero second component is also accepted when its first component is a code-map
key; otherwise it must be one of the labels found in a stored program. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "loc_check_def"]
def locCheck {α : Type}
    (code : Spt (ProgM α)) (labels : Nat × Nat) : Prop :=
  (labels.2 = 0 ∧ sptMem labels.1 code) ∨
    ∃ key program, sptLookup key code = some program ∧ getLabels program labels

end Flapjack.StackSem

namespace Flapjack.StackSemLabels

open Flapjack.Compiler.Backend.StackLang

/-- Forget the exact instruction payloads for label observation.  The HOL
    label equations inspect only `Seq`, `Ite`, `Loop`, and `Call` structure;
    every other constructor is a leaf for this observation.  This adapter lets
    width-indexed `HolProg` clients reuse the one source-reviewed generic
    `StackSem.getLabels` implementation instead of carrying a duplicate clause
    definition. -/
def labelsProgram {width : Nat} [NeZero width] : HolProg width → ProgM (BitVec width)
  | .seq first second => .seq (labelsProgram first) (labelsProgram second)
  | .ite _ _ _ thenBranch elseBranch =>
      .ite .equal 0 (.imm (0 : BitVec width))
        (labelsProgram thenBranch) (labelsProgram elseBranch)
  | .loop body => .loop (labelsProgram body)
  | .call none _ none => .call none (.inl 0) none
  | .call none _ (some (handlerBody, handlerFirst, handlerSecond)) =>
      .call none (.inl 0)
        (some (labelsProgram handlerBody, handlerFirst, handlerSecond))
  | .call (some (body, link, first, second)) _ none =>
      .call (some (labelsProgram body, link, first, second)) (.inl 0) none
  | .call (some (body, link, first, second)) _
      (some (handlerBody, handlerFirst, handlerSecond)) =>
      .call (some (labelsProgram body, link, first, second)) (.inl 0)
        (some (labelsProgram handlerBody, handlerFirst, handlerSecond))
  | _ => .skip
termination_by program => sizeOf program
decreasing_by all_goals simp_wf <;> omega

/-- Width-indexed compatibility name implemented through the canonical
    source-reviewed generic `StackSem.getLabels` definition. -/
abbrev getLabels {width : Nat} [NeZero width] : HolProg width → (Nat × Nat) → Prop :=
  fun program => Flapjack.StackSem.getLabels (labelsProgram program)

end Flapjack.StackSemLabels
