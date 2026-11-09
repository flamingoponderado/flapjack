module

public import Flapjack.Compiler.Backend.ClosToBvl.Constants
public import Flapjack.Compiler.Backend.ClosLang.CodeLabels
public import Flapjack.Misc.Option

@[expose] public section

/-! Code-label properties of closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang

/-- Compiling a primitive operator preserves exactly its label, when present. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "assign_get_code_label_compile_op"]
theorem assignGetCodeLabel_compileOp (op : Op) :
    assignGetCodeLabel (compileOp op) =
      match Flapjack.holOptionSome (fun n : Nat => op = .label n) with
      | some n => {n}
      | none => ∅ := by
  classical
  by_cases h : ∃ n : Nat, op = .label n
  · obtain ⟨n, rfl⟩ := h
    have selected : Flapjack.holOptionSome (fun k : Nat => Op.label n = .label k) = some n := by
      apply (Flapjack.holOptionSome_eq_some_iff _ ?_ _).2
      · rfl
      · intro a b ha hb
        simpa using ha.symm.trans hb
    rw [selected]
    rfl
  · have absent : Flapjack.holOptionSome (fun n : Nat => op = .label n) = none := by
      simp [Flapjack.holOptionSome, h]
    rw [absent]
    cases op <;> try rfl
    case label n => exact (h ⟨n, rfl⟩).elim
    case blockOp b =>
      cases b <;> try rfl
      case constant c =>
        cases c <;> try rfl
        case constCons t cs =>
          simp only [compileOp, compileConst]
          split <;> rfl
    case globOp g => cases g <;> rfl
    case memOp m => cases m <;> rfl

end Flapjack.Compiler.Backend.ClosToBvl
