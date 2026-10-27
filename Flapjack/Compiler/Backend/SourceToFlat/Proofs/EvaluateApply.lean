import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MemoryOps
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.Equality

/-! Expression-level primitive application simulations. These use the
preliminary factored relations and are not yet reviewed HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- A successful source dereference has a location operand pointing to a
reference cell. This is infrastructure for the expression simulation. -/
theorem opDeref_success {F : Type} (state : SemanticPrimitivesHOL.State F)
    (operand : SemanticPrimitivesHOL.Value)
    (successful : doApp (state.refs, state.ffi) .opderef [operand] ≠ none) :
    ∃ flag address value, operand = .loc flag address ∧ storeLookup address state.refs = some (.refv value) := by
  cases operand <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc flag address =>
    cases lookup : storeLookup address state.refs with
    | none => simp [lookup] at successful
    | some cell =>
      cases cell with
      | refv value => exact ⟨flag, address, value, rfl, lookup⟩
      | w8array bytes => simp [lookup] at successful
      | varray values => simp [lookup] at successful
      | thunk mode value => simp [lookup] at successful

/-- Successful source assignment identifies a location and its updated store. -/
theorem opAssign_success {F : Type} (state : SemanticPrimitivesHOL.State F)
    (pointer value : SemanticPrimitivesHOL.Value)
    (successful : doApp (state.refs, state.ffi) .opassign [pointer, value] ≠ none) :
    ∃ flag address refs, pointer = .loc flag address ∧ storeAssign address (.refv value) state.refs = some refs := by
  cases pointer <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
  case loc flag address =>
    cases assigned : storeAssign address (.refv value) state.refs with
    | none => simp [assigned] at successful
    | some refs => exact ⟨flag, address, refs, rfl, assigned⟩

/-- Allocating a reference after evaluating its operand preserves the value
and state relations, including operand errors and the flat store offset. -/
theorem exprSim_opref {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (body : AstHOL.Exp)
    (bodySim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState body) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .opref [body]) := by
  unfold ExprSim at bodySim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [body] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at bodySim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap body] with
    | mk flatNext flatResult =>
      rw [flatRun] at bodySim
      obtain ⟨related, nextRel⟩ := bodySim
      cases sourceResult with
      | err error =>
        cases error with
        | raise value =>
          cases related with
          | raise valueRel =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState sourceNext sourceEnv body values sourceRun
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              rename_i flatValue
              obtain ⟨sourceApp, flatApp, locationRel, stateRel, _⟩ :=
                opref_related genv sourceNext flatNext nextRel value flatValue valueRel
              unfold ExprSim
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
              rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flatState
                [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, getOpClass, astOpToFlatOp]
              simp [doApp, doAppNumericCore, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
              exact ⟨.value (.cons locationRel .nil), stateRel⟩

/-- Dereferencing a source reference is simulated by the compiled flat field
access, provided the source expression does not end in a type error. -/
theorem exprSim_opderef {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (body : AstHOL.Exp)
    (bodySim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState body)
    (notTypeError : ∀ next, EvaluateHOL.evaluate sourceState sourceEnv [.app .opderef [body]] ≠
      (next, .err (.abort .typeError))) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .opderef [body]) := by
  unfold ExprSim at bodySim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [body] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at bodySim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap body] with
    | mk flatNext flatResult =>
      rw [flatRun] at bodySim
      obtain ⟨related, nextRel⟩ := bodySim
      cases sourceResult with
      | err error =>
        cases error with
        | raise value =>
          cases related with
          | raise valueRel =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        obtain ⟨operand, rfl⟩ := EvaluateProps.evaluateSingFull sourceState sourceNext sourceEnv body values sourceRun
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              rename_i flatOperand
              have successful : doApp (sourceNext.refs, sourceNext.ffi) .opderef [operand] ≠ none := by
                intro failed
                apply notTypeError sourceNext
                rw [EvaluateHOL.evaluate]
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
                rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
                simp [getOpClass, failed, EvaluateHOL.typeError]
              obtain ⟨flag, address, value, rfl, sourceLookup⟩ := opDeref_success sourceNext operand successful
              have flatLocation := (valueRel_location_iff genv flag address flatOperand).mp valueRel
              subst flatOperand
              obtain ⟨flatValue, flatLookup, resultRel⟩ :=
                stateRel_ref_lookup genv sourceNext flatNext nextRel address value sourceLookup
              unfold ExprSim
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
              rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flatState
                [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simp [getOpClass, doApp, doAppNumericCore, doAppBasic, sourceLookup, astOpToFlatOp,
                FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, flatLookup, EvaluateHOL.listResult]
              exact ⟨.value (.cons resultRel .nil), nextRel⟩

/-- Reference assignment simulates the reversed operand evaluation order and
the source store update, assuming the source does not end in a type error. -/
theorem exprSim_opassign {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (pointer value : AstHOL.Exp)
    (argsSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState [value, pointer])
    (notTypeError : ∀ next, EvaluateHOL.evaluate sourceState sourceEnv [.app .opassign [pointer, value]] ≠
      (next, .err (.abort .typeError))) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .opassign [pointer, value]) := by
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [value, pointer] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at argsSim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap value, compileExp trace compMap pointer] with
    | mk flatNext flatResult =>
      rw [flatRun] at argsSim
      obtain ⟨related, nextRel⟩ := argsSim
      cases sourceResult with
      | err error =>
        cases error with
        | raise errorValue =>
          cases related with
          | raise valueRel =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [value, pointer] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap value, compileExp trace compMap pointer]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [value, pointer] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap value, compileExp trace compMap pointer]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        have length := EvaluateProps.evaluateLengthFull sourceState sourceNext sourceEnv [value, pointer] values sourceRun
        have two : ∃ v p, values = [v, p] := by
          cases values with
          | nil => simp at length
          | cons v tail =>
            cases tail with
            | nil => simp at length
            | cons p rest =>
              cases rest with
              | nil => exact ⟨v, p, rfl⟩
              | cons q rest => simp at length
        obtain ⟨sourceValue, sourcePointer, rfl⟩ := two
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons valueRel tail =>
            cases tail with
            | cons pointerRel tail =>
              cases tail with
              | nil =>
                rename_i flatValue flatPointer
                have successful : doApp (sourceNext.refs, sourceNext.ffi) .opassign [sourcePointer, sourceValue] ≠ none := by
                  intro failed
                  apply notTypeError sourceNext
                  rw [EvaluateHOL.evaluate]
                  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                  rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [value, pointer] []).1, sourceRun]
                  simp [getOpClass, failed, EvaluateHOL.typeError]
                obtain ⟨flag, address, refs, rfl, assigned⟩ :=
                  opAssign_success sourceNext sourcePointer sourceValue successful
                have flatLocation := (valueRel_location_iff genv flag address flatPointer).mp pointerRel
                subst flatPointer
                obtain ⟨flatRefs, sourceApp, flatApp, unitRel, stateRel, _⟩ :=
                  opassign_related genv sourceNext flatNext nextRel flag address sourceValue flatValue valueRel refs assigned
                unfold ExprSim
                rw [EvaluateHOL.evaluate]
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [value, pointer] []).1, sourceRun]
                simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                rw [FlatSem.evaluate]
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                rw [(FlatSem.fixClock_evaluations flatEnv flatState
                  [compileExp trace compMap value, compileExp trace compMap pointer]
                  (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                simp [getOpClass, doApp, doAppNumericCore, sourceApp, astOpToFlatOp,
                  FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
                exact ⟨.value (.cons unitRel .nil), stateRel⟩


/-- Equality expressions preserve operand evaluation and their boolean result
for the preliminary source-to-flat relations. -/
theorem exprSim_equality {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (left right : AstHOL.Exp) (ok : genvCOk genv.c)
    (argsSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState [right, left])
    (notTypeError : ∀ next, EvaluateHOL.evaluate sourceState sourceEnv [.app .equality [left, right]] ≠
      (next, .err (.abort .typeError))) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .equality [left, right]) := by
  unfold ExprListSim at argsSim
  simp only [compileExps] at argsSim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [right, left] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at argsSim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap right, compileExp trace compMap left] with
    | mk flatNext flatResult =>
      rw [flatRun] at argsSim
      obtain ⟨related, nextRel⟩ := argsSim
      cases sourceResult with
      | err error =>
        cases error with
        | raise errorValue =>
          cases related with
          | raise rightRel =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.raise rightRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [right, left] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap right, compileExp trace compMap left]
              (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        have length := EvaluateProps.evaluateLengthFull sourceState sourceNext sourceEnv [right, left] values sourceRun
        have two : ∃ v p, values = [v, p] := by
          cases values with
          | nil => simp at length
          | cons v tail =>
            cases tail with
            | nil => simp at length
            | cons p rest =>
              cases rest with
              | nil => exact ⟨v, p, rfl⟩
              | cons q rest => simp at length
        obtain ⟨sourceRight, sourceLeft, rfl⟩ := two
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons rightRel tail =>
            cases tail with
            | cons leftRel tail =>
              cases tail with
              | nil =>
                rename_i flatRight flatLeft
                have sameEq := equality_preserved genv ok sourceLeft sourceRight flatLeft flatRight leftRel rightRel
                cases comparison : SemanticPrimitivesHOL.doEq sourceLeft sourceRight with
                | typeError =>
                  apply False.elim
                  apply notTypeError sourceNext
                  rw [EvaluateHOL.evaluate]
                  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                  rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [right, left] []).1, sourceRun]
                  simp [getOpClass, doApp, doAppNumericCore, doAppBasic, comparison, EvaluateHOL.typeError]
                | val b =>
                  unfold ExprSim
                  rw [EvaluateHOL.evaluate]
                  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                  rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [right, left] []).1, sourceRun]
                  simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
                  rw [FlatSem.evaluate]
                  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                  rw [(FlatSem.fixClock_evaluations flatEnv flatState
                    [compileExp trace compMap right, compileExp trace compMap left]
                    (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
                  simp [getOpClass, doApp, doAppNumericCore, doAppBasic, comparison, astOpToFlatOp,
                    FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, sameEq, EvaluateHOL.listResult]
                  exact ⟨.value (.cons (boolValue_related genv ok b) .nil), nextRel⟩

end Flapjack.Compiler.Backend.SourceToFlat
