import Flapjack.Compiler.Backend.BviToData.Proofs.Simulation
import Flapjack.Compiler.Backend.BviToData.Proofs.Install

/-! Entry-call consequences of the BVI-to-data simulation. The evaluator and
state carriers remain pending correspondence review. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- An initial direct call never returns the BVI internal return marker. -/
theorem entryCall_notReturn {C F : Type} (start : Nat) (source next : BviSem.BviState C F)
    (res : BviSem.BviResult)
    (run : BviSem.evaluate [.call 0 (some start) [] none] [] source = (res, next)) : ¬ isReturn res := by
  intro ⟨values, eq⟩
  subst res
  simp only [BviSem.evaluate, BviSem.fixClock, Nat.min_self] at run
  cases code : BvlSem.findCode (some start) [] source.code with
  | none => simp [code] at run
  | some pair =>
    obtain ⟨args, body⟩ := pair
    by_cases zero : source.clock = 0
    · simp [code, zero] at run
    · generalize called : BviSem.evaluate [body] args (BviSem.decClock 1 source) = result
      obtain ⟨r, state⟩ := result
      cases r with
      | val xs => simp [code, zero, called] at run
      | err error =>
        cases error with
        | abort reason => simp [code, zero, called] at run
        | raise raised => cases raised <;> simp [code, zero, called] at run

/-- The compiled tail call simulates a BVI entry call. This is a Lean-side
consequence of the expression simulation, not yet a reviewed HOL port. -/
theorem compilePart_evaluate {C F : Type} (start : Nat) (source next : BviSem.BviState C F)
    (target : DataSem.State C F) (res : BviSem.BviResult)
    (run : BviSem.evaluate [.call 0 (some start) [] none] [] source = (res, next))
    (notType : res ≠ .err (.abort .typeError)) (related : stateRel source target)
    (empty : sptIsEmpty target.locals = true)
    (jump : ∀ x, res = .err (.raise x) → DataSem.jumpExc target ≠ none) :
    ∃ r final, DataSem.evaluate (.call none (some start) [] none) target = (some r, final) ∧
      stateRel next final ∧ dataToBviResult r = res := by
  have localsEmpty : target.locals = .ln := by
    cases h : target.locals <;> simp_all [sptIsEmpty]
  have fresh : ∀ k, 0 ≤ k → sptLookup k target.locals = none := by
    intro k _
    simp [localsEmpty]
  have jumpEx : isException res → DataSem.jumpExc target ≠ none := by
    intro ⟨v, eq⟩
    exact jump (.exn v) eq
  obtain ⟨final, prog, pres, names, nextVar, ls, compiled, targetRun, finalRel, outcome⟩ :=
    simulationFor_all [.call 0 (some start) [] none] [] source res next target 0 [] true []
      run notType (by simp [DataProps.varCorr]) (by simp) fresh related (by simp) jumpEx
  have shape : prog = .seq .skip (.call none (some start) [] none) := by
    simpa [compileSource, DataLang.mkTicks] using (congrArg Prod.fst compiled).symm
  rw [shape] at targetRun
  have direct : DataSem.evaluate (.call none (some start) [] none) target = (pres, final) := by
    simpa [DataSem.evaluate, DataSem.fixClock] using targetRun
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some r =>
    exact ⟨r, final, direct, finalRel, outcome.1 (entryCall_notReturn start source next res run)⟩

/-- Initial BVI and data states satisfy the simulation relation when the data
code and compiler oracle are obtained by compiling the BVI program lists. -/
theorem initialState_related {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (stamps : Bool) (limits : DataSem.Limits)
    (sizes : Spt Nat) (clock : Nat) :
    stateRel
      (BviSem.initialState ffi (sptFromAList program) oracle
        (fun cfg code => compiler cfg (compileProg code)) clock)
      (DataSem.initialState ffi (sptFromAList (compileProg program))
        (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
        compiler stamps limits sizes clock) := by
  simp [stateRel, BviSem.initialState, DataSem.initialState, codeRel_compileProg,
    HolFiniteMapExact.empty, sptMap]

/-- Whole-program initial calls produce related final states and the same
projected result when the BVI call does not fail with a type error or raise.
This is Lean-side infrastructure pending HOL evaluator and carrier review. -/
theorem compileProg_evaluate {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (stamps : Bool) (limits : DataSem.Limits)
    (sizes : Spt Nat) (clock start : Nat) (res : BviSem.BviResult) (last : BviSem.BviState C F)
    (run : BviSem.evaluate [.call 0 (some start) [] none] []
      (BviSem.initialState ffi (sptFromAList program) oracle
        (fun cfg code => compiler cfg (compileProg code)) clock) = (res, last))
    (notType : res ≠ .err (.abort .typeError))
    (notRaise : ∀ x, res ≠ .err (.raise x)) :
    ∃ r final,
      DataSem.evaluate (.call none (some start) [] none)
        (DataSem.initialState ffi (sptFromAList (compileProg program))
          (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
          compiler stamps limits sizes clock) = (some r, final) ∧
      stateRel last final ∧ dataToBviResult r = res := by
  apply compilePart_evaluate start _ _ _ res run notType
    (initialState_related ffi program oracle compiler stamps limits sizes clock)
  · simp [DataSem.initialState]
  · intro x raised
    exact False.elim (notRaise x raised)

end Flapjack.Compiler.Backend.BviToData
