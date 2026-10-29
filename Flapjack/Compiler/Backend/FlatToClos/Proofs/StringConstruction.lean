import Flapjack.Compiler.Backend.FlatToClos.Proofs.VectorRead

/-! String construction in the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- A successful character-list decoding is also a value-list decoding with
character literals. This is an infrastructure lemma for the simulation. -/
theorem charList_valueList (source : FlatSem.Value) (chars : List HolChar)
    (decoded : FlatSem.valueToCharList source = some chars) :
    FlatSem.valueToList source = some (chars.map (.litv ∘ Lit.char)) := by
  cases source with
  | conv stamp fields =>
    cases stamp with
    | none => simp [FlatSem.valueToCharList] at decoded
    | some stamp =>
      obtain ⟨tag, typeId⟩ := stamp
      cases fields with
      | nil =>
        simp only [FlatSem.valueToCharList] at decoded
        split at decoded
        · rename_i tags
          simp at decoded
          subst chars
          simp [FlatSem.valueToList, tags]
        · simp at decoded
      | cons head rest =>
        cases rest with
        | nil => simp [FlatSem.valueToCharList] at decoded
        | cons tail rest =>
          cases rest with
          | cons extra rest => simp [FlatSem.valueToCharList] at decoded
          | nil =>
            cases head with
            | litv literal =>
              cases literal with
              | char byte =>
                simp only [FlatSem.valueToCharList] at decoded
                split at decoded
                · rename_i tags
                  cases tailDecoded : FlatSem.valueToCharList tail with
                  | none => simp [tailDecoded] at decoded
                  | some tailChars =>
                    simp [tailDecoded] at decoded
                    subst chars
                    have ih := charList_valueList tail tailChars tailDecoded
                    simp [FlatSem.valueToList, tags, ih]
                · simp at decoded
              | intLit | strLit | word8 | word64 | float64 => simp [FlatSem.valueToCharList] at decoded
            | conv | closure | recclosure | loc | vectorv => simp [FlatSem.valueToCharList] at decoded
  | litv | closure | recclosure | loc | vectorv => simp [FlatSem.valueToCharList] at decoded
termination_by sizeOf source

/-- Related character literals have exactly the closure number encoding of
their byte values. -/
theorem related_charList (chars : List HolChar) (target : List ClosSem.Value)
    (related : List.Forall₂ ValueRel (chars.map (.litv ∘ Lit.char)) target) :
    target = chars.map (fun byte => .number byte.toNat) := by
  induction chars generalizing target with
  | nil => cases related; rfl
  | cons first rest ih =>
    cases related with
    | cons head tail =>
      cases head
      simp [ih _ tail]

/-- Decoding related flat and closure lists yields the same character bytes. -/
theorem valueToCharList_related (source : FlatSem.Value) (target : ClosSem.Value)
    (chars : List HolChar) (related : ValueRel source target)
    (decoded : FlatSem.valueToCharList source = some chars) :
    ClosSem.valueToList target = some (chars.map (fun byte => .number byte.toNat)) := by
  have flatList := charList_valueList source chars decoded
  obtain ⟨targetValues, targetDecoded, valuesRelated⟩ :=
    valueToList_related source target _ related flatList
  rw [related_charList chars targetValues valuesRelated] at targetDecoded
  exact targetDecoded

/-- String construction rejects any argument count other than one. -/
theorem stringImplode_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (args : List FlatSem.Value) (wrong : args.length ≠ 1) :
    (FlatSem.applyResult state (.src .implode) args).2 = .err (.abort .typeError) := by
  cases args with
  | nil => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
  | cons first rest =>
    cases rest with
    | nil => simp at wrong
    | cons second rest => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]

/-- String construction preserves related character bytes after evaluating arbitrary
argument lists, provided the source application avoids a type error. -/
theorem evaluate_stringImplode {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .implode) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .implode) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argSim := argSim argsNotTypeError
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps_reverse] at argSim
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src .implode) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have length : sourceArgs.length = 1 := by
          by_contra wrong
          apply resultShape
          apply stringImplode_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            simp only [List.reverse_singleton] at resultShape
            rename_i sourceValue targetValue
            cases decoded : FlatSem.valueToCharList sourceValue with
            | none =>
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.doAppData, decoded] at resultShape
            | some items =>
              have targetDecoded := valueToCharList_related sourceValue targetValue items head decoded
              have targetApplied := ClosSem.applyMemory_fromCharList nextTarget targetValue items targetDecoded
              have resultRel : ValueRel (.litv (.strLit (.implode items))) (.byteVector items) := by
                simpa using (ValueRel.string (.implode items))
              simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                FlatSem.doAppData, decoded, ClosSem.doApp, targetApplied, states,
                EvalResultRel.value (.cons resultRel .nil)]

end Flapjack.Compiler.Backend.FlatToClos
