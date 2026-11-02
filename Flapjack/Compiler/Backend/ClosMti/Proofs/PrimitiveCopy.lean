import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveByteVector
import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveAlloc

/-! Byte copying and XOR for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- XOR updates corresponding byte arrays and rejects the same invalid inputs. -/
theorem primitiveSimulation_memory_xorByte {C F : Type} :
    @PrimitiveSimulation C F (.memOp .xorByte) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | refPtr flag ptr =>
          cases second with
          | byteVector input =>
            have lookup := stateRel_lookupRefs states ptr
            cases l : source.refs.lookup ptr with
            | none => cases r : target.refs.lookup ptr <;> simp_all [OptionRel, doApp, applyMemory, excRel]
            | some leftRef =>
              cases r : target.refs.lookup ptr with
              | none => simp_all [OptionRel]
              | some rightRef =>
                have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
                cases refs with
                | valueArray fields nextFields rel => simp [doApp, applyMemory, l, r, excRel]
                | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
                | byteArray bytes =>
                  cases xorRun : SemanticPrimitivesHOL.xorBytes input bytes with
                  | none => simp [doApp, applyMemory, l, r, xorRun, excRel]
                  | some updatedBytes =>
                    have updated := stateRel_updateRefs states ptr (.byteArray updatedBytes)
                      (.byteArray updatedBytes) (.byteArray _)
                    have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
                    simp [doApp, applyMemory, l, r, xorRun, unitRel, updated]
          | number _ | word64 _ | block _ _ _ _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
          simp [doApp, applyMemory, excRel]
      | cons head tail => simp [doApp, applyMemory, excRel]

/-- Copying a byte slice into a new vector preserves vector and array inputs
and reports the same invalid bounds. -/
theorem primitiveSimulation_memory_copyByte_new {C F : Type} :
    @PrimitiveSimulation C F (.memOp (.copyByte true)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil => simp [doApp, applyMemory, excRel]
      | cons third tail =>
        cases tail with
        | nil =>
          cases first with
          | byteVector bytes =>
            cases second with
            | number offset =>
              cases third with
              | number length =>
                cases copyRun : SemanticPrimitivesHOL.copyArray (bytes, offset) length none with
                | none => simp [doApp, applyMemory, copyRun, excRel]
                | some copied =>
                  have valueRel : ValueRel source.maxApp (.byteVector copied) (.byteVector copied) := .byteVector _
                  simp [doApp, applyMemory, copyRun, valueRel, states]
              | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
                simp [doApp, applyMemory, excRel]
            | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
              simp [doApp, applyMemory, excRel]
          | refPtr flag ptr =>
            cases second with
            | number offset =>
              cases third with
              | number length =>
                have lookup := stateRel_lookupRefs states ptr
                cases l : source.refs.lookup ptr with
                | none => cases r : target.refs.lookup ptr <;> simp_all [OptionRel, doApp, applyMemory, excRel]
                | some leftRef =>
                  cases r : target.refs.lookup ptr with
                  | none => simp_all [OptionRel]
                  | some rightRef =>
                    have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
                    cases refs with
                    | valueArray fields nextFields rel => simp [doApp, applyMemory, l, r, excRel]
                    | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
                    | byteArray bytes =>
                      cases copyRun : SemanticPrimitivesHOL.copyArray (bytes, offset) length none with
                      | none => simp [doApp, applyMemory, l, r, copyRun, excRel]
                      | some copied =>
                        have valueRel : ValueRel source.maxApp (.byteVector copied) (.byteVector copied) := .byteVector _
                        simp [doApp, applyMemory, l, r, copyRun, valueRel, states]
              | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
                simp [doApp, applyMemory, excRel]
            | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
              simp [doApp, applyMemory, excRel]
          | number _ | word64 _ | block _ _ _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyMemory, excRel]
        | cons head tail => simp [doApp, applyMemory, excRel]

/-- Copy a byte vector into a related destination array. -/
theorem copyByte_write_vector {C F : Type} (source target : State C F)
    (input : List (BitVec 8)) (offset length dstOffset : Int) (flag : Bool) (dst : Nat)
    (states : StateRel source target) :
    match (generalizing := false) doApp (.memOp (.copyByte false))
        [.byteVector input, .number offset, .number length, .refPtr flag dst, .number dstOffset] target with
    | .err targetError => ∃ sourceError,
        doApp (.memOp (.copyByte false))
          [.byteVector input, .number offset, .number length, .refPtr flag dst, .number dstOffset] source = .err sourceError ∧
        excRel (ValueRel source.maxApp) sourceError targetError
    | .val (targetValue, targetNext) => ∃ sourceValue sourceNext,
        ValueRel source.maxApp sourceValue targetValue ∧ StateRel sourceNext targetNext ∧
        doApp (.memOp (.copyByte false))
          [.byteVector input, .number offset, .number length, .refPtr flag dst, .number dstOffset] source = .val (sourceValue, sourceNext) := by
  have lookup := stateRel_lookupRefs states dst
  cases l : source.refs.lookup dst with
  | none => cases r : target.refs.lookup dst <;> simp_all [OptionRel, doApp, applyMemory, excRel]
  | some leftRef =>
    cases r : target.refs.lookup dst with
    | none => simp_all [OptionRel]
    | some rightRef =>
      have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
      cases refs with
      | valueArray fields nextFields rel => simp [doApp, applyMemory, l, r, excRel]
      | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
      | byteArray bytes =>
        cases copyRun : SemanticPrimitivesHOL.copyArray (input, offset) length (some (bytes, dstOffset)) with
        | none => simp [doApp, applyMemory, l, r, copyRun, excRel]
        | some copied =>
          have updated := stateRel_updateRefs states dst (.byteArray copied) (.byteArray copied) (.byteArray _)
          have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
          simp [doApp, applyMemory, l, r, copyRun, unitRel, updated]

/-- Copy from a related source array, including overlapping source and
destination addresses. -/
theorem copyByte_write_ref {C F : Type} (source target : State C F)
    (srcFlag : Bool) (src : Nat) (offset length dstOffset : Int) (dstFlag : Bool) (dst : Nat)
    (states : StateRel source target) :
    match (generalizing := false) doApp (.memOp (.copyByte false))
        [.refPtr srcFlag src, .number offset, .number length, .refPtr dstFlag dst, .number dstOffset] target with
    | .err targetError => ∃ sourceError,
        doApp (.memOp (.copyByte false))
          [.refPtr srcFlag src, .number offset, .number length, .refPtr dstFlag dst, .number dstOffset] source = .err sourceError ∧
        excRel (ValueRel source.maxApp) sourceError targetError
    | .val (targetValue, targetNext) => ∃ sourceValue sourceNext,
        ValueRel source.maxApp sourceValue targetValue ∧ StateRel sourceNext targetNext ∧
        doApp (.memOp (.copyByte false))
          [.refPtr srcFlag src, .number offset, .number length, .refPtr dstFlag dst, .number dstOffset] source = .val (sourceValue, sourceNext) := by
  have lookup := stateRel_lookupRefs states src
  cases l : source.refs.lookup src with
  | none => cases r : target.refs.lookup src <;> simp_all [OptionRel, doApp, applyMemory, excRel]
  | some leftRef =>
    cases r : target.refs.lookup src with
    | none => simp_all [OptionRel]
    | some rightRef =>
      have refs : RefRel source.maxApp leftRef rightRef := by simpa [OptionRel, l, r] using lookup
      cases refs with
      | valueArray fields nextFields rel => simp [doApp, applyMemory, l, r, excRel]
      | thunk mode value next rel => simp [doApp, applyMemory, l, r, excRel]
      | byteArray bytes =>
        have vectorSim := copyByte_write_vector source target bytes offset length dstOffset dstFlag dst states
        simpa [doApp, applyMemory, l, r] using vectorSim

/-- In-place byte copying preserves related stores for both source forms. -/
theorem primitiveSimulation_memory_copyByte_write {C F : Type} :
    @PrimitiveSimulation C F (.memOp (.copyByte false)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | cons second tail =>
      cases tail with
      | nil => simp [doApp, applyMemory, excRel]
      | cons third tail =>
        cases tail with
        | nil => simp [doApp, applyMemory, excRel]
        | cons fourth tail =>
          cases tail with
          | nil => simp [doApp, applyMemory, excRel]
          | cons fifth tail =>
            cases tail with
            | nil =>
              cases second with
              | number offset =>
                cases third with
                | number length =>
                  cases fourth with
                  | refPtr flag dst =>
                    cases fifth with
                    | number dstOffset =>
                      cases first with
                      | byteVector input => exact copyByte_write_vector source target input offset length dstOffset flag dst states
                      | refPtr srcFlag src => exact copyByte_write_ref source target srcFlag src offset length dstOffset flag dst states
                      | number _ | word64 _ | block _ _ _ _ | closure | recclosure | partialRecclosure =>
                        simp [doApp, applyMemory, excRel]
                    | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
                      cases first <;> simp [doApp, applyMemory, excRel]
                  | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure | partialRecclosure =>
                    cases first <;> simp [doApp, applyMemory, excRel]
                | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
                  cases first <;> simp [doApp, applyMemory, excRel]
              | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
                cases first <;> simp [doApp, applyMemory, excRel]
            | cons head tail => simp [doApp, applyMemory, excRel]

/-- Every memory operation in the current proof-side dispatcher preserves
the relation. Source correspondence remains a separate review obligation. -/
theorem primitiveSimulation_memory {C F : Type} (op : ClosLang.MemOp) :
    @PrimitiveSimulation C F (.memOp op) := by
  cases op with
  | ref => exact primitiveSimulation_memory_ref
  | update => exact primitiveSimulation_memory_update
  | el => exact primitiveSimulation_memory_el
  | length => exact primitiveSimulation_memory_length
  | lengthByte => exact primitiveSimulation_memory_lengthByte
  | refByte flag =>
    cases flag with
    | false => exact primitiveSimulation_memory_refByte
    | true =>
      intro source target left right states values
      simp [doApp, applyMemory, excRel]
  | refArray => exact primitiveSimulation_memory_refArray
  | derefByte => exact primitiveSimulation_memory_derefByte
  | updateByte => exact primitiveSimulation_memory_updateByte
  | concatByteVec => exact primitiveSimulation_memory_concatByteVec
  | copyByte fresh =>
    cases fresh with
    | false => exact primitiveSimulation_memory_copyByte_write
    | true => exact primitiveSimulation_memory_copyByte_new
  | fromListByte => exact primitiveSimulation_memory_fromListByte
  | toListByte => exact primitiveSimulation_memory_toListByte
  | lengthByteVec => exact primitiveSimulation_memory_lengthByteVec
  | derefByteVec => exact primitiveSimulation_memory_derefByteVec
  | stringCmp fast comparison => exact primitiveSimulation_memory_stringCmp fast comparison
  | xorByte => exact primitiveSimulation_memory_xorByte
  | boundsCheckArray => exact primitiveSimulation_memory_boundsCheckArray
  | boundsCheckByte loose => exact primitiveSimulation_memory_boundsCheckByte loose
  | mutCons _ _ | updateCons | finaliseCons =>
    intro source target left right states values
    simp [doApp, applyMemory, excRel]
  | configGC => exact primitiveSimulation_memory_configGC

/-- Memory expressions satisfy the backward evaluator simulation. -/
theorem evaluateRel_memory {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.MemOp)
    (targetArgs sourceCode : List ClosLang.Exp)
    (argsIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode targetArgs) :
    @EvaluateRelAt C F sourceCode [.op trace (.memOp op) targetArgs] :=
  evaluateRel_ordinary trace (.memOp op) targetArgs sourceCode (by simp) (by simp)
    argsIH (primitiveSimulation_memory op)

end Flapjack.Compiler.Backend.ClosMti
