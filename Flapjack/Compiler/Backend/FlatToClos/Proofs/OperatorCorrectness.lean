import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Equality
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Ffi
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Globals
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Element
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Assignment
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Thunk
import Flapjack.Compiler.Backend.FlatToClos.Proofs.CopyUpdate
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Array
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
import Flapjack.Compiler.Backend.FlatToClos.Op
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
import Flapjack.SemanticPrimitivesProps.ResultRelation
import Flapjack.EvaluateHOL
import Mathlib.Data.List.Forall2

namespace Flapjack.Compiler.Backend.FlatToClos

open Flapjack.SemanticPrimitivesHOL

namespace OperatorCorrectness
/-- The closure-state finite maps roundtrip through their broad carrier. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end OperatorCorrectness

/-- The original Eval operator case of value-level operator correctness.
The flat primitive dispatcher handles Eval in the evaluator rather than
`doApp`, so the original successful-application premise is impossible. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_eval"
  (fmap_as_finite_support := [refs, code])]
theorem opEval {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    op = .src .eval →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opEq premises
  subst op
  simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
    FlatSem.doAppData, FlatSem.doAppCopy] at premises

/-- The original identity-operator case of value-level operator correctness. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_id"
  (fmap_as_finite_support := [refs, code])]
theorem opId {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    op = .id →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opEq premises
  subst op
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  cases vs with
  | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
  | cons v vs =>
    cases vs with
    | cons w rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
    | nil =>
      simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
      rcases applied with ⟨rfl, rfl⟩
      cases xs with
      | nil => simp at length
      | cons x xs =>
        cases xs with
        | cons y ys => simp at length
        | nil =>
          refine ⟨.val ws, targetNext, ?_, states, ?_⟩
          · simpa [compileOp, arg1] using evaluated
          · simp [Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
            have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
            cases ws with
            | nil => simp at wsLen
            | cons w rest =>
              cases rest with
              | cons z zs => simp at wsLen
              | nil => simpa using related

/-- The original word-shift operator case of value-level correctness. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_shifts"
  (fmap_as_finite_support := [refs, code])]
theorem opShifts {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (∃ width shift amount, op = .src (.shift width shift amount)) →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro ⟨width, shift, amount, h⟩ premises
  subst op
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  cases vs with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric] at applied
  | cons v vs =>
    cases vs with
    | cons u rest => simp [FlatSem.doApp, FlatSem.doAppNumeric] at applied
    | nil =>
      cases v with
      | litv lit =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric] at applied
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons rel tail =>
              cases width <;> cases lit <;>
                simp [SemanticPrimitivesProps.doShift] at applied
              all_goals rcases applied with ⟨rfl, rfl⟩
              all_goals cases rel
              all_goals simp only [compileOp]
              all_goals rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
              all_goals simp [ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doWordApp,
                ClosSem.doWordAppIntegral, ClosSem.intToByte_toNat,
                Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
              all_goals refine ⟨states, ?_⟩
              all_goals first
                | exact .word8 _
                | exact .word64 _
      | conv _ _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric] at applied

/-- Equality and GC configuration satisfy the original value-level operator correctness goal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_eq_gc"
  (fmap_as_finite_support := [refs, code])]
theorem opEqGc {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (op = .src .configGC ∨ op = .src .equality) →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with opEq | opEq <;> subst op
  all_goals cases vs with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
  | cons v vs =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons u rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | nil => simp at wsLen
          | cons t rest =>
            cases rest with
            | cons z zs => simp at wsLen
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
              cases related with
              | cons relV tail =>
                cases tail with
                | cons relU tail =>
                  simp only [compileOp]
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                  first
                  | have gc : FlatSem.doApp source (.src .configGC) [v,u] = some (sourceNext,result) := applied
                    cases v <;> cases u <;> simp [FlatSem.doApp, FlatSem.doAppNumeric,
                      FlatSem.doAppMemory, FlatSem.doAppData] at gc
                    rename_i lit1 lit2
                    cases lit1 <;> cases lit2 <;> simp at gc
                    obtain ⟨rfl, rfl⟩ := gc
                    cases relV
                    cases relU
                    simp [ClosSem.doApp, ClosSem.applyMemory,
                      Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                    exact ⟨states, (vRel_unit _).mpr rfl⟩
                  | have eq : FlatSem.doApp source (.src .equality) [v,u] = some (sourceNext,result) := applied
                    simp only [FlatSem.doApp, FlatSem.doAppNumeric] at eq
                    cases h : FlatSem.doEq v u with
                    | typeError => simp [h] at eq
                    | val b =>
                      simp [h] at eq
                      obtain ⟨rfl, rfl⟩ := eq
                      have targetEq := doEq_simulation.1 v u t w b relV relU h
                      simp [ClosSem.doApp, ClosSem.applyBlock, targetEq,
                        Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                      exact ⟨states, (vRel_bool _ _).mpr rfl⟩

/-- Foreign calls satisfy the original value-level operator correctness goal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_ffi"
  (fmap_as_finite_support := [refs, code])]
theorem opFfi {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (∃ name, op = .src (.ffi name)) →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro ⟨name, opEq⟩ premises
  subst op
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  cases vs with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
  | cons v vs =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons u rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | nil => simp at wsLen
          | cons t rest =>
            cases rest with
            | cons z zs => simp at wsLen
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
              cases related with
              | cons relV tail =>
                cases tail with
                | cons relU tail =>
                  simp only [compileOp]
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                  cases relV <;> simp [FlatSem.doApp, FlatSem.doAppNumeric,
                    FlatSem.doAppMemory, FlatSem.doAppData] at applied
                  case string configuration =>
                    cases relU <;> simp at applied
                    case loc flag pointer =>
                      cases found : storeLookup pointer source.refs with
                      | none => simp [found] at applied
                      | some entry =>
                        cases entry <;> simp [found] at applied
                        case w8array bytes =>
                          have targetFound := lookup_byteArray states found
                          cases call : Flapjack.callFFIHOL source.ffi (.extCall name) configuration.explode bytes with
                          | ret ffi updated =>
                            obtain ⟨targetUpdated, sourceUpdate, targetUpdate, updatedStates⟩ :=
                              ffiReturn_related source targetNext pointer flag bytes updated configuration name ffi states found call
                            have foundList : source.refs[pointer]? = some (.w8array bytes) := by
                              simpa [storeLookup] using found
                            simp [call, storeAssign, storeValueSameType, foundList] at applied
                            obtain ⟨rfl, rfl⟩ := applied
                            simp [targetUpdate, Flapjack.EvaluateHOL.listResult,
                              SemanticPrimitivesProps.resultRel]
                            exact ⟨updatedStates, (vRel_unit _).mpr rfl⟩
                          | final event =>
                            have targetCall : Flapjack.callFFIHOL targetNext.ffi (.extCall name) configuration.explode bytes = .final event := by
                              rw [← states.2.1]
                              exact call
                            simp [call] at applied
                            obtain ⟨rfl, rfl⟩ := applied
                            simp [ClosSem.doApp, targetFound, targetCall, states,
                              Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]

/-- Global lookup, initialization and allocation satisfy the original operator goal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_globals"
  (fmap_as_finite_support := [refs, code])]
theorem opGlobals {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    ((∃ n, op = .globalVarLookup n) ∨ (∃ n, op = .globalVarInit n) ∨ (∃ n, op = .globalVarAlloc n)) →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩
  case inl =>
    cases vs with
    | cons v rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
    | nil =>
      have wsNil : ws = [] := by simpa using related.length_eq.symm
      have xsNil : xs = [] := by simpa using length
      subst ws
      subst xs
      simp [ClosSem.evaluate] at evaluated
      subst targetNext
      cases slot : source.globals[n]? with
      | none => simp [FlatSem.doApp, FlatSem.doAppFlat, slot] at applied
      | some v =>
        cases v with
        | none => simp [FlatSem.doApp, FlatSem.doAppFlat, slot] at applied
        | some value =>
          simp [FlatSem.doApp, FlatSem.doAppFlat, slot] at applied
          obtain ⟨rfl, rfl⟩ := applied
          obtain ⟨targetValue, targetFound, valueRel⟩ := globalLookup_related source target n value states slot
          simp [compileOp, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
            ClosSem.applyGlobal, targetFound, Flapjack.EvaluateHOL.listResult,
            SemanticPrimitivesProps.resultRel]
          exact ⟨states, valueRel⟩
  case inr.inr =>
    cases vs with
    | cons v rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
    | nil =>
      have wsNil : ws = [] := by simpa using related.length_eq.symm
      have xsNil : xs = [] := by simpa using length
      subst ws
      subst xs
      simp [ClosSem.evaluate] at evaluated
      subst targetNext
      simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
      obtain ⟨rfl, rfl⟩ := applied
      have updated := stateRel_allocGlobals source target n states
      simp [compileOp, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
        ClosSem.applyNumeric, ClosSem.doIntApp, ClosSem.applyGlobal,
        Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
      have nonneg : ¬ (Int.ofNat n < 0) := by exact Int.not_lt.mpr (Int.natCast_nonneg n)
      simp only [Int.ofNat_eq_natCast] at nonneg
      simp [nonneg]
      exact ⟨updated, (vRel_unit _).mpr rfl⟩
  case inr.inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
    | cons value rest =>
      cases rest with
      | cons v rest => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
      | nil =>
        cases slot : source.globals[n]? with
        | none => simp [FlatSem.doApp, FlatSem.doAppFlat, slot] at applied
        | some contents =>
          cases contents with
          | some v => simp [FlatSem.doApp, FlatSem.doAppFlat, slot] at applied
          | none =>
            simp [FlatSem.doApp, FlatSem.doAppFlat, slot] at applied
            obtain ⟨rfl, rfl⟩ := applied
            have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
            cases ws with
            | nil => simp at wsLen
            | cons w rest =>
              cases rest with
              | cons v rest => simp at wsLen
              | nil =>
                simp only [List.reverse_singleton] at related
                cases related with
                | cons valRel tail =>
                  obtain ⟨targetSlot, updated⟩ := stateRel_initGlobal source targetNext n value w states valRel slot
                  simp only [compileOp]
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                  simp [ClosSem.doApp, ClosSem.applyGlobal, targetSlot,
                    Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                  exact ⟨updated, (vRel_unit _).mpr rfl⟩

/-- Constructor tests and list append satisfy the original operator correctness goal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_blocks"
  (fmap_as_finite_support := [refs, code])]
theorem opBlocks {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    ((∃ tag n, op = .tagLenEq tag n) ∨ (∃ n, op = .lenEq n) ∨ op = .src .listAppend) →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with ⟨tag, n, rfl⟩ | ⟨n, rfl⟩ | rfl
  case inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases valRel <;> simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
              all_goals obtain ⟨rfl, rfl⟩ := applied
              all_goals rename_i rel
              all_goals have sameLength := rel.length_eq
              all_goals simp only [compileOp]
              all_goals rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
              all_goals simp [ClosSem.doApp, ClosSem.applyBlock, ← sameLength,
                Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
              all_goals exact ⟨states, (vRel_bool _ _).mpr rfl⟩
  case inr.inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases valRel <;> simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
              all_goals obtain ⟨rfl, rfl⟩ := applied
              all_goals rename_i rel
              all_goals have sameLength := rel.length_eq
              all_goals simp only [compileOp]
              all_goals rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
              all_goals simp [ClosSem.doApp, ClosSem.applyBlock, ← sameLength,
                Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
              all_goals exact ⟨states, (vRel_bool _ _).mpr rfl⟩
  case inr.inr =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v vs =>
      cases vs with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | cons u rest =>
        cases rest with
        | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
        | nil =>
          have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
          cases ws with
          | nil => simp at wsLen
          | cons w rest =>
            cases rest with
            | nil => simp at wsLen
            | cons t rest =>
              cases rest with
              | cons z zs => simp at wsLen
              | nil =>
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
                cases related with
                | cons relV tail =>
                  cases tail with
                  | cons relU tail =>
                    cases leftDecoded : FlatSem.valueToList v with
                    | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                        FlatSem.doAppData, leftDecoded] at applied
                    | some left =>
                      cases rightDecoded : FlatSem.valueToList u with
                      | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          FlatSem.doAppData, leftDecoded, rightDecoded] at applied
                      | some right =>
                        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          FlatSem.doAppData, leftDecoded, rightDecoded] at applied
                        obtain ⟨rfl, rfl⟩ := applied
                        obtain ⟨targetLeft, targetLeftDecoded, leftRel⟩ :=
                          valueToList_related v t left relV leftDecoded
                        obtain ⟨targetRight, targetRightDecoded, rightRel⟩ :=
                          valueToList_related u w right relU rightDecoded
                        have resultRel := listToValue_related (List.rel_append leftRel rightRel)
                        simp only [compileOp]
                        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                        simp [ClosSem.doApp, ClosSem.applyBlock, targetLeftDecoded, targetRightDecoded,
                          Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                        exact ⟨states, resultRel⟩

/-- Reference allocation, field reads and assignment satisfy the original operator goal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_refs"
  (fmap_as_finite_support := [refs, code])]
theorem opRefs {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (op = .src .opref ∨ (∃ n, op = .el n) ∨ op = .src .opassign) →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with rfl | ⟨n, rfl⟩ | rfl
  case inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc] at applied
              obtain ⟨rfl, rfl⟩ := applied
              have index := leastUnusedRef_eq_length source.refs targetNext.refs states.2.2.2.1
              have updated := stateRel_allocRef source targetNext v w states valRel
              simp only [compileOp]
              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
              simp [ClosSem.doApp, ClosSem.applyMemory, index,
                Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
              exact ⟨updated, ValueRel.loc true source.refs.length⟩
  case inr.inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppFlat] at applied
      | nil =>
        cases xs with
        | nil => simp at length
        | cons x rest =>
          cases rest with
          | cons z zs => simp at length
          | nil =>
            have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
            cases ws with
            | nil => simp at wsLen
            | cons w rest =>
              cases rest with
              | cons z zs => simp at wsLen
              | nil =>
                simp only [List.reverse_singleton] at related
                cases related with
                | cons valRel tail =>
                  cases run : FlatSem.doAppFlat source (.el n) [v] with
                  | none => simp [FlatSem.doAppFlat] at run
                  | some output =>
                    cases output with
                    | none => simp [FlatSem.doApp, run] at applied
                    | some pair =>
                      obtain ⟨after, res⟩ := pair
                      simp [FlatSem.doApp, run] at applied
                      obtain ⟨rfl, rfl⟩ := applied
                      cases res with
                      | err error =>
                        cases v <;> simp [FlatSem.doAppFlat] at run
                        case loc flag pointer => split at run <;> simp_all
                      | val value =>
                        have afterEq : after = source := by
                          cases v <;> simp [FlatSem.doAppFlat] at run
                          case conv stamp fields => cases h : fields[n]? <;> simp_all
                          case loc flag pointer => split at run <;> simp_all
                        subst after
                        obtain ⟨targetResult, targetRun, valueRel⟩ :=
                          element_related source targetNext n v w value states valRel run
                        simp only [compileOp, arg1]
                        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate,
                          evaluate_element_args, evaluated]
                        simp only [Int.ofNat_eq_natCast] at targetRun
                        simp [ClosSem.doApp, targetRun, Flapjack.EvaluateHOL.listResult,
                          SemanticPrimitivesProps.resultRel]
                        exact ⟨states, valueRel⟩
  case inr.inr =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    | cons v vs =>
      cases vs with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
      | cons u rest =>
        cases rest with
        | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
        | nil =>
          cases xs with
          | nil => simp at length
          | cons x rest =>
            cases rest with
            | nil => simp at length
            | cons y rest =>
              cases rest with
              | cons z zs => simp at length
              | nil =>
                have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
                cases ws with
                | nil => simp at wsLen
                | cons w rest =>
                  cases rest with
                  | nil => simp at wsLen
                  | cons t rest =>
                    cases rest with
                    | cons z zs => simp at wsLen
                    | nil =>
                      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
                      cases related with
                      | cons relV tail =>
                        cases tail with
                        | cons relU tail =>
                          cases relV <;> simp [FlatSem.doApp, FlatSem.doAppNumeric,
                            FlatSem.doAppMemory] at applied
                          case loc flag pointer =>
                            cases found : source.refs[pointer]? with
                            | none => simp [storeAssign, found] at applied
                            | some old =>
                              cases old with
                              | w8array | varray | thunk => simp [storeAssign, found, storeValueSameType] at applied
                              | refv old =>
                                obtain ⟨targetUpdated, sourceUpdate, targetUpdate, updatedStates⟩ :=
                                  assignRef_related source targetNext flag pointer old u w states relU found
                                simp [storeAssign, found, storeValueSameType] at applied
                                obtain ⟨rfl, rfl⟩ := applied
                                cases hx : ClosSem.evaluate [x] db target with
                                | mk xr mid =>
                                  cases xr with
                                  | err error =>
                                    rw [ClosProps.evaluate_cons_error _ _ _ _ _ _ hx] at evaluated
                                    simp at evaluated
                                  | val firsts =>
                                    obtain ⟨first, rfl⟩ := ClosSem.evaluate_singleton_value x db target mid firsts hx
                                    rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ hx] at evaluated
                                    cases hy : ClosSem.evaluate [y] db mid with
                                    | mk yr last =>
                                      cases yr with
                                      | err error => simp [hy] at evaluated
                                      | val seconds =>
                                        obtain ⟨second, rfl⟩ := ClosSem.evaluate_singleton_value y db mid last seconds hy
                                        simp [hy] at evaluated
                                        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := evaluated
                                        simp only [compileOp, arg2]
                                        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate,
                                          evaluate_assignment_args _ _ _ _ _ _ hx, hy]
                                        simp [ClosSem.doApp, targetUpdate,
                                          Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                                        exact ⟨updatedStates, (vRel_unit _).mpr rfl⟩

/-- Vector length, reads and construction satisfy the original operator goal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_vectors"
  (fmap_as_finite_support := [refs, code])]
theorem opVectors {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (op = .src .vlength ∨ op = .src .vsub ∨ op = .src .vsubUnsafe ∨ op = .src .vfromList) →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with rfl | rfl | rfl | rfl
  case inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases valRel <;> simp [FlatSem.doApp, FlatSem.doAppNumeric,
                FlatSem.doAppMemory, FlatSem.doAppData] at applied
              case vector rel =>
                obtain ⟨rfl, rfl⟩ := applied
                have sameLength := rel.length_eq
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                simp [ClosSem.doApp, ClosSem.applyBlock, ← sameLength,
                  Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                exact ⟨states, ValueRel.int _⟩
  case inr.inr.inr =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases decoded : FlatSem.valueToList v with
              | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, decoded] at applied
              | some items =>
                simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, decoded] at applied
                obtain ⟨rfl, rfl⟩ := applied
                obtain ⟨targetItems, targetDecoded, itemRel⟩ := valueToList_related v w items valRel decoded
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                simp [ClosSem.doApp, ClosSem.applyBlock, targetDecoded,
                  Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                exact ⟨states, ValueRel.vector itemRel⟩
  case inr.inr.inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v vs =>
      cases vs with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | cons u rest =>
        cases rest with
        | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
        | nil =>
          have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
          cases ws with
          | nil => simp at wsLen
          | cons w rest =>
            cases rest with
            | nil => simp at wsLen
            | cons t rest =>
              cases rest with
              | cons z zs => simp at wsLen
              | nil =>
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
                cases related with
                | cons relV tail =>
                  cases tail with
                  | cons relU tail =>
                    cases relV <;> cases relU <;>
                      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                        FlatSem.doAppData] at applied
                    case vector.int items targetItems itemRel index =>
                      by_cases negative : index < 0
                      · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at applied
                      · cases element : items[index.toNat]? with
                        | none => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, element] at applied
                        | some value =>
                          simp [FlatSem.readIndexed, negative, element] at applied
                          obtain ⟨rfl, rfl⟩ := applied
                          obtain ⟨targetValue, targetElement, valueRel⟩ :=
                            forall₂_lookup itemRel index.toNat value element
                          simp only [compileOp]
                          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                          simp [ClosSem.doApp, ClosSem.applyMemory, negative, targetElement,
                            Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                          exact ⟨states, valueRel⟩
  case inr.inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v vs =>
      cases vs with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | cons u rest =>
        cases rest with
        | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
        | nil =>
          have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
          cases ws with
          | nil => simp at wsLen
          | cons w rest =>
            cases rest with
            | nil => simp at wsLen
            | cons t rest =>
              cases rest with
              | cons z zs => simp at wsLen
              | nil =>
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
                cases related with
                | cons relV tail =>
                  cases tail with
                  | cons relU tail =>
                    cases relV <;> cases relU <;>
                      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                        FlatSem.doAppData] at applied
                    case vector.int items targetItems itemRel index =>
                      by_cases negative : index < 0
                      · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at applied
                        obtain ⟨rfl, rfl⟩ := applied
                        have body := evaluate_checkedVectorRead_outOfBounds targetNext trace db targetItems index (Or.inl negative)
                        simp only [compileOp]
                        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                        simp [body, Flapjack.EvaluateHOL.listResult,
                          SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
                        exact ⟨states, ValueRel.con .nil⟩
                      · cases element : items[index.toNat]? with
                        | none =>
                          have bound : targetItems.length ≤ index.toNat := by
                            have h := List.getElem?_eq_none_iff.mp element
                            have same := itemRel.length_eq
                            omega
                          simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, element] at applied
                          obtain ⟨rfl, rfl⟩ := applied
                          have body := evaluate_checkedVectorRead_outOfBounds targetNext trace db targetItems index (Or.inr bound)
                          simp only [compileOp]
                          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                          simp [body, Flapjack.EvaluateHOL.listResult,
                            SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
                          exact ⟨states, ValueRel.con .nil⟩
                        | some value =>
                          simp [FlatSem.readIndexed, negative, element] at applied
                          obtain ⟨rfl, rfl⟩ := applied
                          obtain ⟨targetValue, targetElement, valueRel⟩ :=
                            forall₂_lookup itemRel index.toNat value element
                          have body := evaluate_checkedVectorRead_inBounds targetNext trace db targetItems index targetValue negative targetElement
                          simp only [compileOp]
                          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                          simp [body, Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                          exact ⟨states, valueRel⟩

/-- String construction, observation and indexing satisfy the original operator goal. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_str"
  (fmap_as_finite_support := [refs, code])]
theorem opString {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (op = .src .explode ∨ op = .src .implode ∨ op = .src .strlen ∨ op = .src .strsub ∨ op = .src .strcat) →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with rfl | rfl | rfl | rfl | rfl
  case inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases valRel <;> simp [FlatSem.doApp, FlatSem.doAppNumeric,
                FlatSem.doAppMemory, FlatSem.doAppData] at applied
              case string str =>
                obtain ⟨rfl, rfl⟩ := applied
                have resultRel := listToValue_related (explodedChars_related str.explode)
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                simp [ClosSem.doApp, ClosSem.applyMemory,
                  Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                exact ⟨states, resultRel⟩
  case inr.inr.inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases valRel <;> simp [FlatSem.doApp, FlatSem.doAppNumeric,
                FlatSem.doAppMemory, FlatSem.doAppData] at applied
              case string str =>
                obtain ⟨rfl, rfl⟩ := applied
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                simp [ClosSem.doApp, ClosSem.applyMemory,
                  Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                exact ⟨states, ValueRel.int _⟩
  case inr.inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases decoded : FlatSem.valueToCharList v with
              | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, decoded] at applied
              | some items =>
                simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, decoded] at applied
                obtain ⟨rfl, rfl⟩ := applied
                have targetDecoded := valueToCharList_related v items w ⟨decoded, valRel⟩
                have targetApplied := ClosSem.applyMemory_fromCharList targetNext w items
                  (by simpa [List.map_map, Function.comp_def] using targetDecoded)
                have resultRel : ValueRel (.litv (.strLit (.implode items))) (.byteVector items) := by
                  simpa using (ValueRel.string (.implode items))
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                simp [ClosSem.doApp, targetApplied,
                  Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                exact ⟨states, resultRel⟩
  case inr.inr.inr.inr =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases decoded : FlatSem.valueToList v with
              | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                  FlatSem.doAppData, decoded] at applied
              | some items =>
                cases joined : FlatSem.valuesToString items with
                | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                    FlatSem.doAppData, decoded, joined] at applied
                | some str =>
                  simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                    FlatSem.doAppData, decoded, joined] at applied
                  obtain ⟨rfl, rfl⟩ := applied
                  obtain ⟨targetItems, targetDecoded, itemRel⟩ := valueToList_related v w items valRel decoded
                  obtain ⟨chunks, targetEq, bytesEq⟩ := valuesToString_related itemRel str joined
                  rw [targetEq] at targetDecoded
                  have targetApplied := ClosSem.applyMemory_concatByteVectors targetNext w chunks targetDecoded
                  have resultRel : ValueRel (.litv (.strLit str)) (.byteVector chunks.flatten) := by
                    simpa [bytesEq] using (ValueRel.string str)
                  simp only [compileOp]
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                  simp [ClosSem.doApp, targetApplied,
                    Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                  exact ⟨states, resultRel⟩
  case inr.inr.inr.inl =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v vs =>
      cases vs with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | cons u rest =>
        cases rest with
        | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
        | nil =>
          have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
          cases ws with
          | nil => simp at wsLen
          | cons w rest =>
            cases rest with
            | nil => simp at wsLen
            | cons t rest =>
              cases rest with
              | cons z zs => simp at wsLen
              | nil =>
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
                cases related with
                | cons relV tail =>
                  cases tail with
                  | cons relU tail =>
                    cases relV <;> cases relU <;>
                      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                        FlatSem.doAppData] at applied
                    case string.int str index =>
                      by_cases negative : index < 0
                      · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at applied
                        obtain ⟨rfl, rfl⟩ := applied
                        have body := evaluate_checkedStringRead_outOfBounds targetNext trace db str.explode index (Or.inl negative)
                        simp only [compileOp]
                        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                        simp [body, Flapjack.EvaluateHOL.listResult,
                          SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
                        exact ⟨states, ValueRel.con .nil⟩
                      · cases element : str.explode[index.toNat]? with
                        | none =>
                          have bound : str.explode.length ≤ index.toNat := List.getElem?_eq_none_iff.mp element
                          simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, element] at applied
                          obtain ⟨rfl, rfl⟩ := applied
                          have body := evaluate_checkedStringRead_outOfBounds targetNext trace db str.explode index (Or.inr bound)
                          simp only [compileOp]
                          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                          simp [body, Flapjack.EvaluateHOL.listResult,
                            SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
                          exact ⟨states, ValueRel.con .nil⟩
                        | some byte =>
                          simp [FlatSem.readIndexed, negative, element] at applied
                          obtain ⟨rfl, rfl⟩ := applied
                          have body := evaluate_checkedStringRead_inBounds targetNext trace db str.explode index byte negative element
                          simp only [compileOp]
                          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                          simp [body, Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                          exact ⟨states, ValueRel.char byte⟩


/-- The original thunk operator case of value-level correctness; forcing is excluded by the HOL premise. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_thunk"
  (fmap_as_finite_support := [refs, code])]
theorem opThunk {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (∀ thOp, op = .src (.thunkOp thOp) →
      FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult) := by
  intro thOp opEq premises
  subst op
  obtain ⟨applied, states, evaluated, related, length, _, notForce⟩ := premises
  cases thOp with
  | forceThunk => contradiction
  | allocThunk mode =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v rest =>
      cases rest with
      | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | nil =>
        have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
        cases ws with
        | nil => simp at wsLen
        | cons w rest =>
          cases rest with
          | cons z zs => simp at wsLen
          | nil =>
            simp only [List.reverse_singleton] at related
            cases related with
            | cons valRel tail =>
              cases safe : FlatSem.badThunkUpdate mode v source.refs with
              | true => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, safe] at applied
              | false =>
                have targetSafe := badThunkUpdate_related mode v w source.refs targetNext.refs valRel states.2.2.2.1
                rw [safe] at targetSafe
                have index := leastUnusedRef_eq_length source.refs targetNext.refs states.2.2.2.1
                have stores := storeRel_allocThunk source.refs targetNext.refs mode v w states.2.2.2.1 valRel
                have updated : StateRel { source with refs := source.refs ++ [.thunk mode v] }
                    { targetNext with refs := targetNext.refs.updateEq (source.refs.length, .thunk mode w) } := by
                  rcases states with ⟨maxApp, ffi, clock, _, globals, globalValues, install⟩
                  exact ⟨maxApp, ffi, clock, stores, globals, globalValues, install⟩
                simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, safe] at applied
                obtain ⟨rfl, rfl⟩ := applied
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                simp [ClosSem.doApp, ← targetSafe, index, storeAlloc,
                  Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                exact ⟨updated, ValueRel.loc false source.refs.length⟩
  | updateThunk mode =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
    | cons v vs =>
      cases vs with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
      | cons u rest =>
        cases rest with
        | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
        | nil =>
          have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
          cases ws with
          | nil => simp at wsLen
          | cons w rest =>
            cases rest with
            | nil => simp at wsLen
            | cons t rest =>
              cases rest with
              | cons z zs => simp at wsLen
              | nil =>
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
                cases related with
                | cons ptrRel tail =>
                  cases tail with
                  | cons valRel tail =>
                    cases ptrRel <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at applied
                    case loc flag pointer =>
                      cases flag with
                      | true => simp at applied
                      | false =>
                        cases safe : FlatSem.badThunkUpdate mode u source.refs with
                        | true => simp [safe] at applied
                        | false =>
                          cases found : source.refs[pointer]? with
                          | none => simp [safe, storeAssign, found] at applied
                          | some entry =>
                            cases entry with
                            | refv _ | w8array _ | varray _ =>
                              simp [safe, storeAssign, found, storeValueSameType] at applied
                            | thunk oldMode old =>
                              cases oldMode with
                              | evaluated => simp [safe, storeAssign, found, storeValueSameType] at applied
                              | notEvaluated =>
                                have slot := states.2.2.2.1 pointer
                                simp only [found] at slot
                                obtain ⟨oldTarget, targetFound, _⟩ := slot
                                have targetSafe := badThunkUpdate_related mode u w source.refs targetNext.refs valRel states.2.2.2.1
                                rw [safe] at targetSafe
                                have newStores := storeRel_setThunk source.refs targetNext.refs pointer _ mode u w states.2.2.2.1 found valRel
                                have updated : StateRel { source with refs := source.refs.set pointer (.thunk mode u) }
                                    { targetNext with refs := targetNext.refs.updateEq (pointer, .thunk mode w) } := by
                                  rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
                                  exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩
                                simp [safe, storeAssign, found, storeValueSameType] at applied
                                obtain ⟨rfl, rfl⟩ := applied
                                simp only [compileOp]
                                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                                simp [ClosSem.doApp, ← targetSafe, targetFound,
                                  Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                                exact ⟨updated, ValueRel.tuple .nil⟩

/-- The original byte-copy operator case, including overlapping arrays. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_byte_copy"
  (fmap_as_finite_support := [refs, code])]
theorem opByteCopy {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (op = .src .copyStrAw8 ∨ op = .src .copyAw8Str ∨ op = .src .copyAw8Aw8 ∨
      op = .src .copyStrStr ∨ op = .src .xorAw8StrUnsafe) →
      FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with rfl | rfl | rfl | rfl | rfl
  case inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨z, zs⟩⟩⟩⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at applied
    have wsLen : ws.length = 5 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨z, zs⟩⟩⟩⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons strRel tail =>
      cases tail with
      | cons offRel tail =>
        cases tail with
        | cons lenRel tail =>
          cases tail with
          | cons ptrRel tail =>
            cases tail with
            | cons dstRel tail =>
              cases strRel <;> try simp at applied
              case string value =>
                cases offRel <;> try simp at applied
                case int offset =>
                  cases lenRel <;> try simp at applied
                  case int size =>
                    cases ptrRel <;> try simp at applied
                    case loc flag pointer =>
                      cases dstRel <;> try simp at applied
                      case int dstOffset =>
                        cases found : storeLookup pointer source.refs with
                        | none => simp [found] at applied
                        | some entry =>
                          cases entry <;> simp [found] at applied
                          case w8array bytes =>
                            have body := copyStringToByteArray_body_related source targetNext trace db value bytes pointer flag offset size dstOffset states found
                            have bodyExact : StateRel sourceNext
                                (ClosSem.evaluate [copyByteAw8 trace] (.number dstOffset :: .refPtr flag pointer :: .number size :: .number offset :: .byteVector value.explode :: db) targetNext).2 ∧
                                EvalResultRel (Flapjack.EvaluateHOL.listResult result)
                                (ClosSem.evaluate [copyByteAw8 trace] (.number dstOffset :: .refPtr flag pointer :: .number size :: .number offset :: .byteVector value.explode :: db) targetNext).1 := by
                              cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
                            simp only [compileOp]
                            rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                            cases run : ClosSem.evaluate [copyByteAw8 trace] (.number dstOffset :: .refPtr flag pointer :: .number size :: .number offset :: .byteVector value.explode :: db) targetNext with
                            | mk out last =>
                              simp only [run] at bodyExact
                              obtain ⟨stateRel, resultRel⟩ := bodyExact
                              refine ⟨out, last, ?_, stateRel, ?_⟩
                              · simpa using run
                              · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨z, zs⟩⟩⟩⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at applied
    have wsLen : ws.length = 5 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨z, zs⟩⟩⟩⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons srcRel tail =>
      cases tail with
      | cons offRel tail =>
        cases tail with
        | cons lenRel tail =>
          cases tail with
          | cons ptrRel tail =>
            cases tail with
            | cons dstRel tail =>
              cases srcRel <;> try simp at applied
              case loc srcFlag srcPointer =>
                cases offRel <;> try simp at applied
                case int offset =>
                  cases lenRel <;> try simp at applied
                  case int size =>
                    cases ptrRel <;> try simp at applied
                    case loc flag pointer =>
                      cases dstRel <;> try simp at applied
                      case int dstOffset =>
                        cases found : storeLookup pointer source.refs with
                        | none => simp [found] at applied
                        | some entry =>
                          cases entry <;> simp [found] at applied
                          case w8array bytes =>
                            cases srcFound : storeLookup srcPointer source.refs with
                            | none => simp [srcFound] at applied
                            | some srcEntry =>
                              cases srcEntry <;> simp [srcFound] at applied
                              case w8array srcBytes =>
                                  have body := copyByteArrayToByteArray_body_related source targetNext trace db srcBytes bytes srcPointer pointer srcFlag flag offset size dstOffset states srcFound found
                                  have bodyExact : StateRel sourceNext
                                      (ClosSem.evaluate [copyByteAw8 trace] (.number dstOffset :: .refPtr flag pointer :: .number size :: .number offset :: .refPtr srcFlag srcPointer :: db) targetNext).2 ∧
                                      EvalResultRel (Flapjack.EvaluateHOL.listResult result)
                                      (ClosSem.evaluate [copyByteAw8 trace] (.number dstOffset :: .refPtr flag pointer :: .number size :: .number offset :: .refPtr srcFlag srcPointer :: db) targetNext).1 := by
                                    cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
                                  simp only [compileOp]
                                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                                  cases run : ClosSem.evaluate [copyByteAw8 trace] (.number dstOffset :: .refPtr flag pointer :: .number size :: .number offset :: .refPtr srcFlag srcPointer :: db) targetNext with
                                  | mk out last =>
                                    simp only [run] at bodyExact
                                    obtain ⟨stateRel, resultRel⟩ := bodyExact
                                    refine ⟨out, last, ?_, stateRel, ?_⟩
                                    · simpa using run
                                    · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨q, _ | ⟨z, zs⟩⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at applied
    have wsLen : ws.length = 3 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨r, _ | ⟨z, zs⟩⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons offRel tail =>
        cases tail with
        | cons lenRel tail =>
          cases ptrRel <;> try simp at applied
          case loc flag pointer =>
            cases offRel <;> try simp at applied
            case int offset =>
              cases lenRel <;> try simp at applied
              case int size =>
                cases found : storeLookup pointer source.refs with
                | none => simp [found] at applied
                | some entry =>
                  cases entry <;> simp [found] at applied
                  case w8array bytes =>
                      have body := copyByteArray_body_related source targetNext trace db pointer flag bytes offset size states found
                      have bodyExact : StateRel sourceNext
                          (ClosSem.evaluate [copyByteStr trace] (.number size :: .number offset :: .refPtr flag pointer :: db) targetNext).2 ∧
                          EvalResultRel (Flapjack.EvaluateHOL.listResult result)
                          (ClosSem.evaluate [copyByteStr trace] (.number size :: .number offset :: .refPtr flag pointer :: db) targetNext).1 := by
                        cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
                      clear body
                      simp only [compileOp]
                      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                      cases run : ClosSem.evaluate [copyByteStr trace] (.number size :: .number offset :: .refPtr flag pointer :: db) targetNext with
                      | mk out last =>
                        simp only [run] at bodyExact
                        obtain ⟨stateRel, resultRel⟩ := bodyExact
                        refine ⟨out, last, ?_, stateRel, ?_⟩
                        · simpa using run
                        · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inr.inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨q, _ | ⟨z, zs⟩⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at applied
    have wsLen : ws.length = 3 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨r, _ | ⟨z, zs⟩⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons strRel tail =>
      cases tail with
      | cons offRel tail =>
        cases tail with
        | cons lenRel tail =>
          cases strRel <;> try simp at applied
          case string value =>
            cases offRel <;> try simp at applied
            case int offset =>
              cases lenRel <;> try simp at applied
              case int size =>
                have body := copyString_body_related source targetNext trace db value offset size states
                have bodyExact : StateRel sourceNext
                    (ClosSem.evaluate [copyByteStr trace] (.number size :: .number offset :: .byteVector value.explode :: db) targetNext).2 ∧
                    EvalResultRel (Flapjack.EvaluateHOL.listResult result)
                    (ClosSem.evaluate [copyByteStr trace] (.number size :: .number offset :: .byteVector value.explode :: db) targetNext).1 := by
                  cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
                clear body
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                cases run : ClosSem.evaluate [copyByteStr trace] (.number size :: .number offset :: .byteVector value.explode :: db) targetNext with
                | mk out last =>
                  simp only [run] at bodyExact
                  obtain ⟨stateRel, resultRel⟩ := bodyExact
                  refine ⟨out, last, ?_, stateRel, ?_⟩
                  · simpa using run
                  · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inr.inr.inr =>
    cases vs with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at applied
    | cons v vs =>
      cases vs with
      | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at applied
      | cons u rest =>
        cases rest with
        | cons z zs => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at applied
        | nil =>
          have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
          cases ws with
          | nil => simp at wsLen
          | cons w rest =>
            cases rest with
            | nil => simp at wsLen
            | cons t rest =>
              cases rest with
              | cons z zs => simp at wsLen
              | nil =>
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
                cases related with
                | cons ptrRel tail =>
                  cases tail with
                  | cons valRel tail =>
                    cases ptrRel <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at applied
                    case loc flag pointer =>
                      cases valRel <;> try simp at applied
                      case string value =>
                        cases found : storeLookup pointer source.refs with
                        | none => simp [found] at applied
                        | some entry =>
                          cases entry <;> simp [found] at applied
                          case w8array bytes =>
                            cases xor : xorBytes value.explode bytes with
                            | none => simp [xor] at applied
                            | some updated =>
                              obtain ⟨targetUpdated, sourceUpdate, targetUpdate, updatedStates⟩ :=
                                xorByteArray_related source targetNext pointer flag bytes updated value states found xor
                              have foundList : source.refs[pointer]? = some (.w8array bytes) := by simpa [storeLookup] using found
                              simp [xor, storeAssign, foundList, storeValueSameType] at applied
                              obtain ⟨rfl, rfl⟩ := applied
                              simp only [compileOp]
                              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                              simp [ClosSem.doApp, targetUpdate, FlatSem.unitValue, ClosSem.unitValue,
                                Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                              exact ⟨updatedStates, ValueRel.tuple .nil⟩

/-- The original byte-array operator case, including checked and unchecked bounds. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_byte_arrays"
  (fmap_as_finite_support := [refs, code])]
theorem opByteArrays {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (op = .src .aw8length ∨ op = .src .aw8alloc ∨ op = .src .aw8subUnsafe ∨
      op = .src .aw8sub ∨ op = .src .aw8updateUnsafe ∨ op = .src .aw8update) →
      FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with rfl | rfl | rfl | rfl | rfl | rfl
  case inl =>
    rcases vs with _ | ⟨v, _ | ⟨z, zs⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨z, zs⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_singleton] at related
    cases related with
    | cons ptrRel tail =>
      cases ptrRel <;> try simp at applied
      case loc flag pointer =>
        cases found : storeLookup pointer source.refs with
        | none => simp [found] at applied
        | some entry =>
          cases entry <;> simp [found] at applied
          case w8array bytes =>
            obtain ⟨rfl, rfl⟩ := applied
            have targetFound := lookup_byteArray states found
            simp only [compileOp]
            rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
            simp [ClosSem.doApp, ClosSem.applyMemory, targetFound,
              Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
            exact ⟨states, ValueRel.int _⟩
  case inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨z, zs⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨z, zs⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons sizeRel tail =>
      cases tail with
      | cons byteRel tail =>
        cases sizeRel <;> try simp at applied
        case int size =>
          cases byteRel <;> try simp at applied
          case word8 byte =>
            have body := allocByteArray_body_related source targetNext trace db size byte states
            simp only [compileOp]
            rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
            have bodyExact : StateRel sourceNext (ClosSem.evaluate [.ifThenElse trace
                (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
                (.raise trace (.op trace (.blockOp (.cons 3)) []))
                (.op trace (.memOp (.refByte false)) [.var trace 0, .var trace 1])] (.number byte.toNat :: .number size :: db) targetNext).2 ∧
                EvalResultRel (Flapjack.EvaluateHOL.listResult result) (ClosSem.evaluate [.ifThenElse trace
                (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
                (.raise trace (.op trace (.blockOp (.cons 3)) []))
                (.op trace (.memOp (.refByte false)) [.var trace 0, .var trace 1])] (.number byte.toNat :: .number size :: db) targetNext).1 := by
              cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
            cases run : ClosSem.evaluate [.ifThenElse trace
                (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
                (.raise trace (.op trace (.blockOp (.cons 3)) []))
                (.op trace (.memOp (.refByte false)) [.var trace 0, .var trace 1])] (.number byte.toNat :: .number size :: db) targetNext with
            | mk out last =>
              simp only [run] at bodyExact
              obtain ⟨stateRel, resultRel⟩ := bodyExact
              refine ⟨out, last, ?_, stateRel, ?_⟩
              · simpa using run
              · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨z, zs⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨z, zs⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons idxRel tail =>
        cases ptrRel <;> try simp at applied
        case loc flag pointer =>
          cases idxRel <;> try simp at applied
          case int index =>
            cases found : storeLookup pointer source.refs with
            | none => simp [found] at applied
            | some entry =>
              cases entry <;> simp [found] at applied
              case w8array bytes =>
                by_cases negative : index < 0
                · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at applied
                · cases element : bytes[index.toNat]? with
                  | none => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, element] at applied
                  | some byte =>
                    obtain ⟨_, _, targetRead, valueRel⟩ :=
                      byteArrayRead_related source targetNext pointer flag bytes index byte states found negative element
                    simp [FlatSem.readIndexed, negative, element] at applied
                    obtain ⟨rfl, rfl⟩ := applied
                    simp only [compileOp]
                    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                    simp [ClosSem.doApp, targetRead, Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                    exact ⟨states, valueRel⟩
  case inr.inr.inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨z, zs⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨z, zs⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons idxRel tail =>
        cases ptrRel <;> try simp at applied
        case loc flag pointer =>
          cases idxRel <;> try simp at applied
          case int index =>
            cases found : storeLookup pointer source.refs with
            | none => simp [found] at applied
            | some entry =>
              cases entry <;> simp [found] at applied
              case w8array bytes =>
                have body := checkedByteRead_body_related source targetNext trace db pointer flag bytes index states found
                have bodyExact : StateRel sourceNext (ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
                  (.op trace (.memOp .derefByte) [.var trace 0, .var trace 1])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number index :: .refPtr flag pointer :: db) targetNext).2 ∧
                    EvalResultRel (Flapjack.EvaluateHOL.listResult result) (ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
                  (.op trace (.memOp .derefByte) [.var trace 0, .var trace 1])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number index :: .refPtr flag pointer :: db) targetNext).1 := by
                  cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                cases run : ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp (.boundsCheckByte false)) [.var trace 0, .var trace 1])
                  (.op trace (.memOp .derefByte) [.var trace 0, .var trace 1])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number index :: .refPtr flag pointer :: db) targetNext with
                | mk out last =>
                  simp only [run] at bodyExact
                  obtain ⟨stateRel, resultRel⟩ := bodyExact
                  refine ⟨out, last, ?_, stateRel, ?_⟩
                  · simpa using run
                  · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inr.inr.inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨q, _ | ⟨z, zs⟩⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 3 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨r, _ | ⟨z, zs⟩⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons idxRel tail =>
        cases tail with
        | cons byteRel tail =>
          cases ptrRel <;> try simp at applied
          case loc flag pointer =>
            cases idxRel <;> try simp at applied
            case int index =>
              cases byteRel <;> try simp at applied
              case word8 byte =>
                cases found : storeLookup pointer source.refs with
                | none => simp [found] at applied
                | some entry =>
                  cases entry <;> simp [found] at applied
                  case w8array bytes =>
                    have foundList : source.refs[pointer]? = some (.w8array bytes) := by simpa [storeLookup] using found
                    have nonnegative : ¬index < 0 := by
                      intro negative
                      simp [FlatSem.updateIndexed, FlatSem.boundsFailure, negative] at applied
                    have bound : index.toNat < bytes.length := by
                      by_contra bad
                      have outside : bytes.length ≤ index.toNat := by omega
                      simp [FlatSem.updateIndexed, FlatSem.boundsFailure, nonnegative, outside] at applied
                    obtain ⟨targetLast, _, flatUpdate, targetUpdate, updated⟩ :=
                      byteArrayUpdate_related source targetNext pointer flag bytes index byte states foundList nonnegative bound
                    simp [FlatSem.doApp, FlatSem.doAppNumeric, flatUpdate] at originalApplied
                    obtain ⟨rfl, rfl⟩ := originalApplied
                    simp only [compileOp]
                    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                    simp [ClosSem.doApp, targetUpdate, FlatSem.unitValue, ClosSem.unitValue,
                      Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                    exact ⟨updated, ValueRel.tuple .nil⟩
  case inr.inr.inr.inr.inr =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨q, _ | ⟨z, zs⟩⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 3 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨r, _ | ⟨z, zs⟩⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons idxRel tail =>
        cases tail with
        | cons byteRel tail =>
          cases ptrRel <;> try simp at applied
          case loc flag pointer =>
            cases idxRel <;> try simp at applied
            case int index =>
              cases byteRel <;> try simp at applied
              case word8 byte =>
                cases found : storeLookup pointer source.refs with
                | none => simp [found] at applied
                | some entry =>
                  cases entry <;> simp [found] at applied
                  case w8array bytes =>
                    have foundList : source.refs[pointer]? = some (.w8array bytes) := by simpa [storeLookup] using found
                    have body := checkedByteUpdate_body_related source targetNext trace db pointer flag bytes index byte states foundList
                    have bodyExact : StateRel sourceNext (ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp (.boundsCheckByte false)) [.var trace 1, .var trace 2])
                  (.op trace (.memOp .updateByte) [.var trace 0, .var trace 1, .var trace 2])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number byte.toNat :: .number index :: .refPtr flag pointer :: db) targetNext).2 ∧
                        EvalResultRel (Flapjack.EvaluateHOL.listResult result) (ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp (.boundsCheckByte false)) [.var trace 1, .var trace 2])
                  (.op trace (.memOp .updateByte) [.var trace 0, .var trace 1, .var trace 2])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number byte.toNat :: .number index :: .refPtr flag pointer :: db) targetNext).1 := by
                      cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
                    simp only [compileOp]
                    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                    cases run : ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp (.boundsCheckByte false)) [.var trace 1, .var trace 2])
                  (.op trace (.memOp .updateByte) [.var trace 0, .var trace 1, .var trace 2])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number byte.toNat :: .number index :: .refPtr flag pointer :: db) targetNext with
                    | mk out last =>
                      simp only [run] at bodyExact
                      obtain ⟨stateRel, resultRel⟩ := bodyExact
                      refine ⟨out, last, ?_, stateRel, ?_⟩
                      · simpa using run
                      · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]

/-- The original value-array operator case, including arbitrary fixed allocation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_arrays"
  (fmap_as_finite_support := [refs, code])]
theorem opArrays {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    (op = .src .aalloc ∨ op = .src .aallocFixed ∨ op = .src .asubUnsafe ∨
      op = .src .asub ∨ op = .src .alength ∨ op = .src .aupdateUnsafe ∨ op = .src .aupdate) →
      FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opCase premises
  obtain ⟨applied, states, evaluated, related, length, _, _⟩ := premises
  rcases opCase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inl =>
    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc] at applied
    obtain ⟨rfl, rfl⟩ := applied
    have index := leastUnusedRef_eq_length source.refs targetNext.refs states.2.2.2.1
    have updated := stateRel_allocArray source targetNext vs ws.reverse states related
    simp only [compileOp]
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
    simp [ClosSem.doApp, ClosSem.applyMemory, index, updated,
      Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
    exact ValueRel.loc true source.refs.length
  case inr.inr.inr.inr.inl =>
    rcases vs with _ | ⟨v, _ | ⟨z, zs⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 1 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨z, zs⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_singleton] at related
    cases related with
    | cons ptrRel tail =>
      cases ptrRel <;> try simp at applied
      case loc flag pointer =>
        cases found : storeLookup pointer source.refs with
        | none => simp [found] at applied
        | some entry =>
          cases entry <;> simp [found] at applied
          case varray items =>
            obtain ⟨rfl, rfl⟩ := applied
            obtain ⟨targetItems, targetFound, itemRel⟩ := lookup_array states found
            have sameLength := itemRel.length_eq
            simp only [compileOp]
            rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
            simp [ClosSem.doApp, ClosSem.applyMemory, targetFound, ← sameLength,
              Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
            exact ⟨states, ValueRel.int _⟩
  case inr.inr.inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨z, zs⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨z, zs⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons idxRel tail =>
        cases ptrRel <;> try simp at applied
        case loc flag pointer =>
          cases idxRel <;> try simp at applied
          case int index =>
            cases found : storeLookup pointer source.refs with
            | none => simp [found] at applied
            | some entry =>
              cases entry <;> simp [found] at applied
              case varray items =>
                have body := checkedArrayRead_body_related source targetNext trace db pointer flag items index states found
                have bodyExact : StateRel sourceNext (ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp .boundsCheckArray) [.var trace 0, .var trace 1])
                  (.op trace (.memOp .el) [.var trace 0, .var trace 1])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number index :: .refPtr flag pointer :: db) targetNext).2 ∧
                    EvalResultRel (Flapjack.EvaluateHOL.listResult result) (ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp .boundsCheckArray) [.var trace 0, .var trace 1])
                  (.op trace (.memOp .el) [.var trace 0, .var trace 1])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number index :: .refPtr flag pointer :: db) targetNext).1 := by
                  cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
                simp only [compileOp]
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                cases run : ClosSem.evaluate [.ifThenElse trace
                  (.op trace (.memOp .boundsCheckArray) [.var trace 0, .var trace 1])
                  (.op trace (.memOp .el) [.var trace 0, .var trace 1])
                  (.raise trace (.op trace (.blockOp (.cons 3)) []))] (.number index :: .refPtr flag pointer :: db) targetNext with
                | mk out last =>
                  simp only [run] at bodyExact
                  obtain ⟨stateRel, resultRel⟩ := bodyExact
                  refine ⟨out, last, ?_, stateRel, ?_⟩
                  · simpa using run
                  · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨z, zs⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨z, zs⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons idxRel tail =>
        cases ptrRel <;> try simp at applied
        case loc flag pointer =>
          cases idxRel <;> try simp at applied
          case int index =>
            cases found : storeLookup pointer source.refs with
            | none => simp [found] at applied
            | some entry =>
              cases entry <;> simp [found] at applied
              case varray items =>
                by_cases negative : index < 0
                · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at applied
                · cases element : items[index.toNat]? with
                  | none => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, element] at applied
                  | some value =>
                    obtain ⟨targetValue, _, _, targetRead, valueRel⟩ :=
                      arrayRead_related source targetNext pointer flag items index value states found negative element
                    simp [FlatSem.readIndexed, negative, element] at applied
                    obtain ⟨rfl, rfl⟩ := applied
                    simp only [compileOp]
                    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                    simp [ClosSem.doApp, targetRead, Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                    exact ⟨states, valueRel⟩
  case inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨z, zs⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 2 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨z, zs⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons sizeRel tail =>
      cases tail with
      | cons valRel tail =>
        cases sizeRel <;> try simp at applied
        case int size =>
          have body := allocArray_body_related source targetNext trace db size u w states valRel
          simp only [compileOp]
          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
          have bodyExact : StateRel sourceNext (ClosSem.evaluate [.ifThenElse trace
              (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
              (.raise trace (.op trace (.blockOp (.cons 3)) []))
              (.op trace (.memOp .refArray) [.var trace 0, .var trace 1])] (w :: .number size :: db) targetNext).2 ∧
              EvalResultRel (Flapjack.EvaluateHOL.listResult result) (ClosSem.evaluate [.ifThenElse trace
              (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
              (.raise trace (.op trace (.blockOp (.cons 3)) []))
              (.op trace (.memOp .refArray) [.var trace 0, .var trace 1])] (w :: .number size :: db) targetNext).1 := by
            cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
          cases run : ClosSem.evaluate [.ifThenElse trace
              (.op trace (.intOp .less) [.op trace (.intOp (.const 0)) [], .var trace 1])
              (.raise trace (.op trace (.blockOp (.cons 3)) []))
              (.op trace (.memOp .refArray) [.var trace 0, .var trace 1])] (w :: .number size :: db) targetNext with
          | mk out last =>
            simp only [run] at bodyExact
            obtain ⟨stateRel, resultRel⟩ := bodyExact
            refine ⟨out, last, ?_, stateRel, ?_⟩
            · simpa using run
            · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inr.inr.inr.inr.inr =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨q, _ | ⟨z, zs⟩⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 3 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨r, _ | ⟨z, zs⟩⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons idxRel tail =>
        cases tail with
        | cons valRel tail =>
          cases ptrRel <;> try simp at applied
          case loc flag pointer =>
            cases idxRel <;> try simp at applied
            case int index =>
              cases found : storeLookup pointer source.refs with
              | none => simp [found] at applied
              | some entry =>
                cases entry <;> simp [found] at applied
                case varray items =>
                  have foundList : source.refs[pointer]? = some (.varray items) := by simpa [storeLookup] using found
                  have body := checkedArrayUpdate_body_related source targetNext trace db pointer flag items index q w states foundList valRel
                  have bodyExact : StateRel sourceNext (ClosSem.evaluate [.ifThenElse trace
                (.op trace (.memOp .boundsCheckArray) [.var trace 1, .var trace 2])
                (.op trace (.memOp .update) [.var trace 0, .var trace 1, .var trace 2])
                (.raise trace (.op trace (.blockOp (.cons 3)) []))] (w :: .number index :: .refPtr flag pointer :: db) targetNext).2 ∧
                      EvalResultRel (Flapjack.EvaluateHOL.listResult result) (ClosSem.evaluate [.ifThenElse trace
                (.op trace (.memOp .boundsCheckArray) [.var trace 1, .var trace 2])
                (.op trace (.memOp .update) [.var trace 0, .var trace 1, .var trace 2])
                (.raise trace (.op trace (.blockOp (.cons 3)) []))] (w :: .number index :: .refPtr flag pointer :: db) targetNext).1 := by
                    cases result <;> simpa [FlatSem.applyResult, originalApplied, Flapjack.EvaluateHOL.listResult] using body
                  simp only [compileOp]
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                  cases run : ClosSem.evaluate [.ifThenElse trace
                (.op trace (.memOp .boundsCheckArray) [.var trace 1, .var trace 2])
                (.op trace (.memOp .update) [.var trace 0, .var trace 1, .var trace 2])
                (.raise trace (.op trace (.blockOp (.cons 3)) []))] (w :: .number index :: .refPtr flag pointer :: db) targetNext with
                  | mk out last =>
                    simp only [run] at bodyExact
                    obtain ⟨stateRel, resultRel⟩ := bodyExact
                    refine ⟨out, last, ?_, stateRel, ?_⟩
                    · simpa using run
                    · cases result <;> simp only [Flapjack.EvaluateHOL.listResult] at resultRel ⊢ <;> cases resultRel <;> simp_all [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel]
  case inr.inr.inr.inr.inr.inl =>
    have originalApplied := applied
    rcases vs with _ | ⟨v, _ | ⟨u, _ | ⟨q, _ | ⟨z, zs⟩⟩⟩⟩ <;>
      try simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at applied
    have wsLen : ws.length = 3 := by simpa using related.length_eq.symm
    rcases ws with _ | ⟨w, _ | ⟨t, _ | ⟨r, _ | ⟨z, zs⟩⟩⟩⟩ <;> try simp at wsLen
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at related
    cases related with
    | cons ptrRel tail =>
      cases tail with
      | cons idxRel tail =>
        cases tail with
        | cons valRel tail =>
          cases ptrRel <;> try simp at applied
          case loc flag pointer =>
            cases idxRel <;> try simp at applied
            case int index =>
              cases found : storeLookup pointer source.refs with
              | none => simp [found] at applied
              | some entry =>
                cases entry <;> simp [found] at applied
                case varray items =>
                  have foundList : source.refs[pointer]? = some (.varray items) := by simpa [storeLookup] using found
                  have nonnegative : ¬index < 0 := by
                    intro negative
                    simp [FlatSem.updateIndexed, FlatSem.boundsFailure, negative] at applied
                  have bound : index.toNat < items.length := by
                    by_contra bad
                    have outside : items.length ≤ index.toNat := by omega
                    simp [FlatSem.updateIndexed, FlatSem.boundsFailure, nonnegative, outside] at applied
                  obtain ⟨targetLast, _, flatUpdate, targetUpdate, updated⟩ :=
                    arrayUpdate_related source targetNext pointer flag items index q w states foundList nonnegative bound valRel
                  simp [FlatSem.doApp, FlatSem.doAppNumeric, flatUpdate] at originalApplied
                  obtain ⟨rfl, rfl⟩ := originalApplied
                  simp only [compileOp]
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, evaluated]
                  simp [ClosSem.doApp, targetUpdate, FlatSem.unitValue, ClosSem.unitValue,
                    Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel]
                  exact ⟨updated, ValueRel.tuple .nil⟩

end Flapjack.Compiler.Backend.FlatToClos
