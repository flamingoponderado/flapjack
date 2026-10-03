import Flapjack.Compiler.Backend.LabFilter.Proofs.FilterCorrect
import Flapjack.Compiler.Backend.LabProps.EvaluateAddClock
import Flapjack.Compiler.Backend.LabSem.Semantics

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabProps

/-- Flapjack infrastructure applying the full simulation at an arbitrary clock;
no separate HOL declaration names this projection. -/
private theorem simulateAtClock {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) (hr : stateRel s t) (clock : Nat) :
    ∃ extra, (evaluate {t with clock := clock + extra}).1 = (evaluate {s with clock := clock}).1 ∧
      (evaluate {t with clock := clock + extra}).2.ffi = (evaluate {s with clock := clock}).2.ffi := by
  have hrc : stateRel {s with clock := clock} {t with clock := clock} := by
    rcases hr with ⟨⟨compile, hs, hcomp⟩, hf⟩
    subst s
    exact ⟨⟨compile, rfl, hcomp⟩, hf⟩
  obtain ⟨extra, next, he, hf⟩ := filterCorrect {s with clock := clock} {t with clock := clock}
    (evaluate {s with clock := clock}).1 (evaluate {s with clock := clock}).2
    ⟨rfl, hrc, hrc.2⟩
  refine ⟨extra, ?_, ?_⟩
  · simpa only [Prod.fst] using congrArg Prod.fst he
  · simpa only [he] using hf.symm

/-- Flapjack infrastructure deriving same-clock observation agreement when the
unfiltered target has terminated or errored. The target run is not an assumed
simulation; its clock extension is proved by the original native clock law. -/
private theorem agreeAtClockOfTargetNotTimeout {width : Nat} [NeZero width] {C F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) (hr : stateRel s t) (clock : Nat)
    (hnt : (evaluate {t with clock := clock}).1 ≠ .timeOut) :
    (evaluate {s with clock := clock}).1 = (evaluate {t with clock := clock}).1 ∧
      (evaluate {s with clock := clock}).2.ffi = (evaluate {t with clock := clock}).2.ffi := by
  obtain ⟨extra, hres, hffi⟩ := simulateAtClock s t hr clock
  have he := evaluateAddClock {t with clock := clock}
    (evaluate {t with clock := clock}).1 (evaluate {t with clock := clock}).2 extra
    ⟨rfl, hnt⟩
  constructor
  · rw [he] at hres
    exact hres.symm
  · rw [he] at hffi
    exact hffi.symm

/-- Flapjack infrastructure: clock-indexed native event families form actual
lazy-list prefix chains, derived from the original clock monotonicity law. -/
private theorem clockTraceChain {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    HolLList.lprefixChain (fun trace => ∃ clock,
      trace = HolLList.fromList (evaluate {s with clock := clock}).2.ffi.ioEvents) := by
  intro left right hl hr
  obtain ⟨k1, rfl⟩ := hl
  obtain ⟨k2, rfl⟩ := hr
  rcases evaluatedClockTracesComparable s k1 k2 with h | h
  · exact Or.inl ((HolLList.lprefix_fromList _ _).mpr h)
  · exact Or.inr ((HolLList.lprefix_fromList _ _).mpr h)

/-- Full original local semantics lift, including fail, optional terminating
choice and the complete divergence trace LUB. All observation and cofinality
facts are derived from full evaluator simulation and native clock laws. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "state_rel_IMP_sem_EQ_sem"
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemEqSem {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F) :
    stateRel s t → semantics s = semantics t := by
  classical
  intro hr
  have herr : (∃ clock, (evaluate {s with clock := clock}).1 = .error) ↔
      ∃ clock, (evaluate {t with clock := clock}).1 = .error := by
    constructor
    · rintro ⟨clock, he⟩
      obtain ⟨extra, hres, _⟩ := simulateAtClock s t hr clock
      exact ⟨clock + extra, hres.trans he⟩
    · rintro ⟨clock, he⟩
      have hn : (evaluate {t with clock := clock}).1 ≠ .timeOut := by rw [he]; intro h; cases h
      exact ⟨clock, (agreeAtClockOfTargetNotTimeout s t hr clock hn).1.trans he⟩
  have hterm : (fun result => ∃ clock next outcome,
      evaluate {s with clock := clock} = (.halt outcome, next) ∧
      result = HolBehaviour.terminate outcome next.ffi.ioEvents) =
      (fun result => ∃ clock next outcome,
      evaluate {t with clock := clock} = (.halt outcome, next) ∧
      result = HolBehaviour.terminate outcome next.ffi.ioEvents) := by
    funext result
    apply propext
    constructor
    · rintro ⟨clock, next, outcome, he, rfl⟩
      obtain ⟨extra, hres, hffi⟩ := simulateAtClock s t hr clock
      rw [he] at hres hffi
      refine ⟨clock + extra, (evaluate {t with clock := clock + extra}).2, outcome, ?_, ?_⟩
      · exact Prod.ext hres rfl
      · rw [hffi]
    · rintro ⟨clock, next, outcome, he, rfl⟩
      have hn : (evaluate {t with clock := clock}).1 ≠ .timeOut := by rw [he]; intro h; cases h
      obtain ⟨hres, hffi⟩ := agreeAtClockOfTargetNotTimeout s t hr clock hn
      rw [he] at hres hffi
      refine ⟨clock, (evaluate {s with clock := clock}).2, outcome, ?_, ?_⟩
      · exact Prod.ext hres rfl
      · rw [hffi]
  have hlub : HolLList.buildLprefixLub (fun trace => ∃ clock,
      trace = HolLList.fromList (evaluate {s with clock := clock}).2.ffi.ioEvents) =
      HolLList.buildLprefixLub (fun trace => ∃ clock,
      trace = HolLList.fromList (evaluate {t with clock := clock}).2.ffi.ioEvents) := by
    apply HolLList.IMP_build_lprefix_lub_EQ (clockTraceChain s) (clockTraceChain t)
    · intro trace htrace
      obtain ⟨clock, rfl⟩ := htrace
      obtain ⟨extra, _, hffi⟩ := simulateAtClock s t hr clock
      refine ⟨HolLList.fromList (evaluate {t with clock := clock + extra}).2.ffi.ioEvents,
        ⟨clock + extra, rfl⟩, ?_⟩
      rw [hffi]
      exact HolLList.lprefix_refl _
    · intro trace htrace
      obtain ⟨clock, rfl⟩ := htrace
      obtain ⟨extra, _, hffi⟩ := simulateAtClock s t hr clock
      refine ⟨HolLList.fromList (evaluate {s with clock := clock}).2.ffi.ioEvents, ⟨clock, rfl⟩, ?_⟩
      apply (HolLList.lprefix_fromList _ _).mpr
      have hp := evaluateAddClockIoEventsMono {t with clock := clock} extra
      rw [hffi] at hp
      exact hp
  unfold semantics
  rw [propext herr, hterm, hlub]

end Flapjack.Compiler.Backend.LabFilter.Proofs
