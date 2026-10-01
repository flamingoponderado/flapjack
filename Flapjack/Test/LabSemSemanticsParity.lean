import Flapjack.Compiler.Backend.LabSem.Semantics

/-! Whole native behavior observations through the genuine clock evaluator.
These fixture lemmas have no HOL declaration counterparts. -/
namespace Flapjack.Test.LabSemSemanticsParity
open Flapjack Flapjack.Compiler.Backend.LabSem

private def failedStart (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :=
  { s with code := [], pc := 0 }

example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    semantics (failedStart s) = .fail := by
  unfold semantics
  rw [if_pos]
  exact ⟨1, by simp [failedStart, evaluate, asmFetch, asmFetchAux]⟩

private def haltStart (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat)
    (value : BitVec 64) :=
  { s with
    code := [{ sectionId := 1, lines := [.labAsm .halt 0 [] 7] }]
    pc := 0
    ptrReg := 0
    regs := fun _ => .word value }

private def haltOutcome (value : BitVec 64) : HolOutcome :=
  if value = 0 then .success else .resourceLimitHit

private theorem haltEval (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat)
    (value : BitVec 64) (clock : Nat) :
    evaluate { haltStart s value with clock := clock } =
      (if clock = 0 then .timeOut else .halt (haltOutcome value),
        { haltStart s value with clock := clock }) := by
  rw [evaluate]
  by_cases hclock : clock = 0
  · simp [hclock]
  · by_cases hvalue : value = 0#64
    all_goals simp [haltStart, asmFetch, asmFetchAux, isLabelHOL, haltOutcome, hclock, hvalue]

private theorem haltSemantics (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat)
    (value : BitVec 64) :
    semantics (haltStart s value) = .terminate (haltOutcome value) s.ffi.ioEvents := by
  unfold semantics
  have hn : ¬ ∃ k, (evaluate { haltStart s value with clock := k }).1 = .error := by
    simp only [haltEval]
    rintro ⟨k, h⟩
    split at h <;> cases h
  rw [if_neg hn]
  have hc : holOptionSome (fun result => ∃ k next outcome,
      evaluate { haltStart s value with clock := k } = (.halt outcome, next) ∧
      result = HolBehaviour.terminate outcome next.ffi.ioEvents) =
      some (.terminate (haltOutcome value) s.ffi.ioEvents) := by
    apply HolLList.holOptionSome_eq_some
    · exact ⟨1, { haltStart s value with clock := 1 }, haltOutcome value,
        by simpa using haltEval s value 1, rfl⟩
    · rintro result ⟨k, next, outcome, he, hr⟩
      rw [haltEval] at he
      split at he
      · cases he
      · cases he
        exact hr
  rw [hc]

-- lab_semantics_halt_success
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    semantics (haltStart s 0) = .terminate .success s.ffi.ioEvents :=
  haltSemantics s 0

-- lab_semantics_halt_resource
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    semantics (haltStart s 1) = .terminate .resourceLimitHit s.ffi.ioEvents := by
  simpa [haltOutcome] using haltSemantics s 1

private def loopStart (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :=
  { s with
    code := [{ sectionId := 1, lines := [.labAsm (.jump (.lab 1 0)) 0 [] 7] }]
    pc := 0 }

private theorem loopEval (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat)
    (clock : Nat) :
    evaluate { loopStart s with clock := clock } =
      (.timeOut, { loopStart s with clock := 0 }) := by
  induction clock with
  | zero => simp [evaluate]
  | succ clock ih =>
      rw [evaluate]
      simpa [loopStart, asmFetch, asmFetchAux, isLabelHOL, getPcValue, locToPc,
        updPc, decClock] using ih

-- lab_semantics_loop_diverge: all clocks, with the entire retained input trace.
example (s : Flapjack.Compiler.Backend.LabSem.State 64 Nat Nat) :
    semantics (loopStart s) = .diverge (HolLList.fromList s.ffi.ioEvents) := by
  unfold semantics
  have hn : ¬ ∃ k, (evaluate { loopStart s with clock := k }).1 = .error := by
    simp only [loopEval]
    rintro ⟨k, h⟩
    cases h
  rw [if_neg hn]
  have hc : holOptionSome (fun result => ∃ k next outcome,
      evaluate { loopStart s with clock := k } = (.halt outcome, next) ∧
      result = HolBehaviour.terminate outcome next.ffi.ioEvents) = none := by
    unfold holOptionSome
    simp [loopEval]
  rw [hc]
  simp only [loopEval]
  have hs : (fun trace => ∃ k : Nat,
      trace = HolLList.fromList ({ loopStart s with clock := 0 }).ffi.ioEvents) =
      (fun trace => trace = HolLList.fromList s.ffi.ioEvents) := by
    funext trace
    simp [loopStart]
  rw [hs]
  congr 1
  apply HolLList.unique_lprefix_lub (HolLList.buildLprefixLub_thm ?_) ?_
  · intro first second hfirst hsecond
    subst first
    subst second
    exact Or.inl (HolLList.lprefix_refl _)
  · constructor
    · intro trace htrace
      subst trace
      exact HolLList.lprefix_refl _
    · intro upper hupper
      exact hupper _ rfl

end Flapjack.Test.LabSemSemanticsParity
