import Flapjack.Compiler.Backend.BviToData.Proofs.Install
import Flapjack.Compiler.Backend.BviToData.Proofs.Thunk

/-! Thunk forcing cases for the BVI-to-data simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Forcing an already evaluated thunk satisfies the expression simulation
in both tail positions. The unevaluated-thunk call case remains open, and
this case is untagged pending evaluator correspondence review. -/
theorem simulationFor_force_evaluated {C F : Type} (label index : Nat)
    (env : List BvlSem.Value) (source : BviSem.BviState C F)
    (thunk result : BvlSem.Value) (sourceVar : env[index]? = some thunk)
    (sourceThunk : BviSem.destThunk thunk source.refs = .isThunk .evaluated result)
    (target : DataSem.State C F) (n : Nat) (corr : List Nat) (tail : Bool) (live : List Nat)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ key, n ≤ key → sptLookup key target.locals = none)
    (related : stateRel source target) (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none) :
    BviSem.evaluate [.force label index] env source = (.val [result], source) ∧
    ∃ targetNext prog pres names next ls,
      compileSource n corr tail live [.force label index] = (prog, names, next) ∧
      DataSem.evaluate prog target = (pres, targetNext) ∧ stateRel source targetNext ∧
      correctOutcome (.val [result]) target targetNext n next corr live names env tail pres ls := by
  classical
  have sourceRun : BviSem.evaluate [.force label index] env source = (.val [result], source) := by
    simp [BviSem.evaluate, sourceVar, sourceThunk]
  obtain ⟨name, nameAt, valueAt⟩ :=
    DataProps.varCorr_lookup env corr (sptMap dataToBviValue target.locals) vars index thunk sourceVar
  simp only [DataSem.getVar, sptLookup_sptMap] at valueAt
  cases found : sptLookup name target.locals with
  | none => simp [found] at valueAt
  | some dataThunk =>
    simp only [found, Option.map_some, Option.some.injEq] at valueAt
    have refs : ∀ key, source.refs.lookup key = (sptLookup key target.refs).map dataToBviRef := by
      intro key
      rw [← sptLookup_sptMap]
      exact related.2.2.2.2.1 key
    have inspected := destThunk_projection dataThunk target.refs source.refs refs
    rw [valueAt, sourceThunk] at inspected
    cases inspect : DataSem.destThunk dataThunk target.refs with
    | badRef => simp [inspect, projectThunkResult] at inspected
    | notThunk => simp [inspect, projectThunkResult] at inspected
    | isThunk mode dataValue =>
      cases mode with
      | notEvaluated => simp [inspect, projectThunkResult] at inspected
      | evaluated =>
        simp [inspect, projectThunkResult] at inspected
        have projected : result = dataToBviValue dataValue := inspected
        have nameLt : name < n := by
          by_contra bound
          have absent := fresh name (by omega)
          rw [found] at absent
          contradiction
        have nextBound : max (n + 1) (name + 1) = n + 1 := Nat.max_eq_left (by omega)
        cases tail with
        | true =>
          refine ⟨sourceRun, DataSem.flushState false target, .force none label name, some (.val [dataValue]),
            [n], n + 1, none, ?_, ?_, ?_, ?_⟩
          · simp [compileSource, nameAt, nextBound]
          · simp [DataSem.evaluate, DataSem.getVar, found, inspect]
          · simpa [stateRel, DataSem.flushState] using related
          · simp [correctOutcome, dataToBviResult, isReturn, isResult, isException,
              DataSem.flushState, ← projected]
        | false =>
          let roots := live ++ corr
          let cut := sptMkWf (sptInter target.locals (namesOfList roots))
          let targetNext := DataSem.setVar n dataValue { target with locals := cut }
          have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
            simpa [roots, DataSem.getVars] using
              (roots_present target [] live corr env [] vars livePresent (by simp [DataSem.getVars]))
          have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
            cutEnv_namesOfList roots target.locals rootsPresent
          have execution : DataSem.evaluate (.force (some (n, namesOfList roots)) label name) target =
              (none, targetNext) := by
            simp [DataSem.evaluate, DataSem.getVar, found, inspect, cutEnv, targetNext]
          have finalRel : stateRel source targetNext := by
            simpa [targetNext, DataSem.setVar, stateRel] using related
          have locals : targetNext.locals = sptInsert n dataValue cut := by simp [targetNext, DataSem.setVar]
          have destRead : sptLookup n targetNext.locals = some dataValue := by
            simp [locals, sptLookup_sptInsert_same]
          have lookupOther : ∀ key, key ≠ n → sptLookup key targetNext.locals =
              if key ∈ roots then sptLookup key target.locals else none := by
            intro key different
            rw [locals, sptLookup_sptInsert_ne n key dataValue cut different]
            exact lookup_cut_namesOfList roots target.locals key
          have keeps : ∀ key ∈ roots, key ≠ n → sptLookup key targetNext.locals = sptLookup key target.locals := by
            intro key member different
            rw [lookupOther key different, if_pos member]
          have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
            apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
            intro key member
            have root : key ∈ roots := by simp [roots, member]
            have different : key ≠ n := by
              intro equal
              subst key
              exact rootsPresent n root (fresh n (Nat.le_refl n))
            exact keeps key root different
          refine ⟨sourceRun, targetNext, .force (some (n, namesOfList roots)) label name, none,
            [n], n + 1, none, ?_, execution, finalRel, ?_⟩
          · simp [compileSource, nameAt, nextBound, roots]
          · simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
            refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro key bound
              have different : key ≠ n := by omega
              rw [lookupOther key different]
              simp [fresh key (by omega)]
            · intro key v lookup
              by_cases equal : key = n
              · omega
              · have oldLookup : sptLookup key target.locals = some v := by
                  rw [lookupOther key equal] at lookup
                  split at lookup <;> simp_all
                by_contra bound
                have absent := fresh key (by omega)
                rw [oldLookup] at absent
                contradiction
            · intro key v lookup needed
              have different : key ≠ n := by
                intro equal
                subst key
                have absent := fresh n (Nat.le_refl n)
                rw [lookup] at absent
                contradiction
              have root : key ∈ roots := by
                by_cases member : key ∈ live
                · simp [roots, member]
                · simp [roots, needed member]
              rw [keeps key root different]
              exact lookup
            · rfl
            · rfl
            · intro available
              simpa [targetNext, DataSem.setVar, DataSem.jumpExc] using available
            · constructor
              · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
              · constructor

end Flapjack.Compiler.Backend.BviToData
