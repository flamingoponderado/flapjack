import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Equality
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Ffi
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Globals
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

end Flapjack.Compiler.Backend.FlatToClos
