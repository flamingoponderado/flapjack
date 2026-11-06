import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.BlockBoolean
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ValueEquality

/-! Constructor extension and the assembled block primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Constructor extension preserves related slices and checks the same bounds. -/
theorem primitiveSimulation_consExtend {C F : Type} (tag : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.consExtend tag)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases first with
    | block original fields nextFields fieldsRel =>
      cases rest with
      | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
      | cons lowerRel rest =>
        cases lowerRel with
        | number lower =>
          cases rest with
          | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
          | cons lenRel rest =>
            cases lenRel with
            | number len =>
              cases rest with
              | nil => exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
              | cons totalRel initialRel =>
                cases totalRel with
                | number total =>
                  rename_i initial nextInitial
                  have fieldsLength := fieldsRel.length_eq
                  have initialLength := initialRel.length_eq
                  have sliceRel := List.forall₂_take len.toNat (List.forall₂_drop lower.toNat fieldsRel)
                  have resultRel := ValueRel.block tag _ _ (List.rel_append initialRel sliceRel)
                  by_cases invalid : lower < 0 ∨ len < 0 ∨ Int.ofNat fields.length < lower + len ∨
                      total = 0 ∨ total ≠ Int.ofNat initial.length + len
                  · refine ⟨.err (.abort .typeError), ?_, ?_⟩
                    · simp only [doApp, applyBlock, ← fieldsLength, ← initialLength, if_pos invalid]
                    · simp only [doApp, applyBlock, if_pos invalid, AppResultRel, ResultRel]
                  · refine ⟨.val (.block tag (nextInitial ++ (nextFields.drop lower.toNat).take len.toNat), target), ?_, ?_⟩
                    · simp only [doApp, applyBlock, ← fieldsLength, ← initialLength, if_neg invalid]
                    · simp only [doApp, applyBlock, if_neg invalid, AppResultRel]
                      exact ⟨resultRel, stateRel⟩
                | _ =>
                  exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
            | _ =>
              cases rest <;> exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
        | _ =>
          cases rest <;> exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩
    | _ =>
      cases rest <;> exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩

/-- Every case of the current proof-side block dispatcher preserves the
candidate primitive relation. The dispatcher itself is not yet reviewed as a
HOL port; its build case currently returns a type error. -/
theorem primitiveSimulation_block {C F : Type} (op : ClosLang.BlockOp) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp op) := by
  cases op with
  | cons tag => exact primitiveSimulation_cons tag
  | elemAt index => exact primitiveSimulation_elemAt index
  | tagLenEq tag length => exact primitiveSimulation_tagLenEq tag length
  | lenEq length => exact primitiveSimulation_lenEq length
  | tagEq tag => exact primitiveSimulation_tagEq tag
  | lengthBlock => exact primitiveSimulation_lengthBlock
  | boolTest test => exact primitiveSimulation_boolTest test
  | boolNot => exact primitiveSimulation_boolNot
  | boundsCheckBlock => exact primitiveSimulation_boundsCheckBlock
  | consExtend tag => exact primitiveSimulation_consExtend tag
  | fromList tag => exact primitiveSimulation_fromList tag
  | listAppend => exact primitiveSimulation_listAppend
  | constant constant => exact primitiveSimulation_constant constant
  | equal => exact primitiveSimulation_equal
  | equalConst constant => exact primitiveSimulation_equalConst constant
  | build constants =>
    intro args nextArgs source target argsRel states
    exact ⟨.err (.abort .typeError), by simp [doApp, applyBlock], by simp [doApp, applyBlock, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
