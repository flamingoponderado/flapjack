import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Assembly
import Flapjack.Compiler.Backend.LabToTarget.Initialization.InitialStateContracts
import Flapjack.Compiler.Backend.LabToTarget.EvaluateIgnoreClocks
import Flapjack.Compiler.Backend.LabProps.EvaluateAddClockIoEventsMono
import Flapjack.Compiler.Backend.LabSem.Semantics
import Flapjack.Compiler.Backend.Semantics.TargetSem.MachineSem
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClockIoEventsMono

/-! Full source-to-machine observational assembly. Source clocks are unrestricted;
termination witnesses and the complete infinite trace LUB are derived from the
actual native compiler simulation, not supplied as theorem premises. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem

/-- Flapjack infrastructure for the image of an actual clock-indexed trace
family. It is not a separate original HOL declaration. -/
private theorem clockTraceChain {α : Type} (traces : Nat → List α)
    (h : ∀ i j, traces i <+: traces j ∨ traces j <+: traces i) :
    HolLList.lprefixChain (fun ll => ∃ k, ll = HolLList.fromList (traces k)) := by
  intro ll1 ll2 h1 h2
  obtain ⟨k1, rfl⟩ := h1
  obtain ⟨k2, rfl⟩ := h2
  rcases h k1 k2 with h | h
  · exact Or.inl ((HolLList.lprefix_fromList _ _).mpr h)
  · exact Or.inr ((HolLList.lprefix_fromList _ _).mpr h)

/-- Original whole machine behavior singleton theorem. The unrestricted
clock-indexed simulation is proved from the real compileCorrect theorem and
initial relation/oracle witnesses. Both finite termination and all-clock lazy
trace divergence are retained. Inherits the evaluator FP real rendering
assurance (SOUNDNESS item8); no stronger numerical parity claim is made. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem machineSemEqSem {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (p : BitVec width) (ms : S)
    (s : Flapjack.Compiler.Backend.LabSem.State width Config F) :
    encoderCorrect mc.target ∧ initOk (mc, p) s ms ∧ semantics s ≠ .fail →
      machineSemHOL mc s.ffi ms = fun behavior => behavior = semantics s := by
  rintro ⟨hencoder, hinit, hnonfail⟩
  have hnoerror : ¬ ∃ k, (evaluate {s with clock := k}).1 = .error := by
    intro h
    exact hnonfail (by simp only [semantics, if_pos h])
  obtain ⟨code2, labs, t1, hrel, htie⟩ := hinit
  have sim (k : Nat) : ∃ extra ms2,
      evaluateTargetHOL mc s.ffi (k + extra) ms =
        ((evaluate {s with clock := k}).1, ms2, (evaluate {s with clock := k}).2.ffi) := by
    generalize hev : evaluate {s with clock := k} = run
    rcases run with ⟨result, next⟩
    have hresult : result ≠ .error := by
      intro he
      apply hnoerror
      exact ⟨k, by rw [hev]; exact he⟩
    obtain ⟨extra, _, ms2, htarget⟩ := compileCorrect (T := Unit) p {s with clock := k}
      result mc next code2 labs t1 ms
      ⟨oracleTie_clock mc ms s k htie, hev, hresult, hencoder,
        stateRelClock (mc, code2, labs, p) s t1 ms k hrel⟩
    exact ⟨extra, ms2, htarget⟩
  let sourceEvents : Nat → List HolIoEvent := fun k =>
    (evaluate {s with clock := k}).2.ffi.ioEvents
  let targetEvents : Nat → List HolIoEvent := fun k =>
    (evaluateTargetHOL mc s.ffi k ms).2.2.ioEvents
  let sourceTraces : HolLList HolIoEvent → Prop := fun ll =>
    ∃ k, ll = HolLList.fromList (sourceEvents k)
  let targetTraces : HolLList HolIoEvent → Prop := fun ll =>
    ∃ k, ll = HolLList.fromList (targetEvents k)
  have hsChain : HolLList.lprefixChain sourceTraces :=
    clockTraceChain sourceEvents (LabProps.evaluatedClockTracesComparable s)
  have htChain : HolLList.lprefixChain targetTraces := by
    apply clockTraceChain targetEvents
    intro i j
    rcases Nat.le_total i j with h | h
    · exact Or.inl (evaluateTargetAddClockIoEventsMono mc s.ffi i ms j h)
    · exact Or.inr (evaluateTargetAddClockIoEventsMono mc s.ffi j ms i h)
  have hsTarget : HolLList.lprefixRel sourceTraces targetTraces := by
    rintro ll ⟨k, rfl⟩
    obtain ⟨extra, ms2, he⟩ := sim k
    refine ⟨HolLList.fromList (targetEvents (k + extra)), ⟨k + extra, rfl⟩, ?_⟩
    have hevents : targetEvents (k + extra) = sourceEvents k := by
      simp only [targetEvents, sourceEvents, he]
    rw [hevents]
    exact HolLList.lprefix_refl _
  have htSource : HolLList.lprefixRel targetTraces sourceTraces := by
    rintro ll ⟨k, rfl⟩
    obtain ⟨extra, ms2, he⟩ := sim k
    refine ⟨HolLList.fromList (sourceEvents k), ⟨k, rfl⟩, ?_⟩
    apply (HolLList.lprefix_fromList _ _).mpr
    have hp := evaluateTargetAddClockIoEventsMono mc s.ffi k ms (k + extra) (by omega)
    simpa only [he] using hp
  have hbuild : HolLList.buildLprefixLub targetTraces =
      HolLList.buildLprefixLub sourceTraces :=
    HolLList.IMP_build_lprefix_lub_EQ htChain hsChain htSource hsTarget
  have hlub : HolLList.lprefixLub targetTraces (HolLList.buildLprefixLub sourceTraces) := by
    rw [← hbuild]
    exact HolLList.buildLprefixLub_thm htChain
  cases hchoice : holOptionSome (fun result => ∃ clock next outcome,
      evaluate {s with clock := clock} = (.halt outcome, next) ∧
      result = HolBehaviour.terminate outcome next.ffi.ioEvents) with
  | some behavior =>
    obtain ⟨clock, next, outcome, hhalt, rfl⟩ := holOptionSome_some hchoice
    have hsem : semantics s = .terminate outcome next.ffi.ioEvents := by
      simp only [semantics, if_neg hnoerror, hchoice]
    obtain ⟨extra, ms2, htarget⟩ := sim clock
    rw [hhalt] at htarget
    funext behavior
    apply propext
    rw [hsem]
    cases behavior with
    | terminate otherOutcome events =>
      constructor
      · rintro ⟨k, ms', ffi', hr, hevents⟩
        have heq := evaluateTargetIgnoreClocks mc s.ffi (clock + extra) k ms
          (.halt outcome) (.halt otherOutcome) ms2 ms' next.ffi ffi'
          ⟨htarget, by simp, hr, by simp⟩
        have hout := congrArg Prod.fst heq
        have hffi := congrArg (fun run => run.2.2) heq
        injection hout with hout
        cases hout
        cases hffi
        rw [← hevents]
      · intro h
        cases h
        exact ⟨clock + extra, ms2, next.ffi, htarget, rfl⟩
    | diverge trace =>
      constructor
      · rintro ⟨h, _⟩
        obtain ⟨ms', ffi', hr⟩ := h (clock + extra)
        have heq := congrArg Prod.fst (htarget.symm.trans hr)
        cases heq
      · intro h; cases h
    | fail =>
      constructor
      · rintro ⟨k, hr⟩
        have hrun : evaluateTargetHOL mc s.ffi k ms =
            (.error, (evaluateTargetHOL mc s.ffi k ms).2.1,
              (evaluateTargetHOL mc s.ffi k ms).2.2) := Prod.ext hr rfl
        have heq := evaluateTargetIgnoreClocks mc s.ffi (clock + extra) k ms
          (.halt outcome) .error ms2 (evaluateTargetHOL mc s.ffi k ms).2.1
          next.ffi (evaluateTargetHOL mc s.ffi k ms).2.2
          ⟨htarget, by simp, hrun, by simp⟩
        have heq' := congrArg Prod.fst heq
        cases heq'
      · intro h; cases h
  | none =>
    have hsem : semantics s = .diverge (HolLList.buildLprefixLub sourceTraces) := by
      simp only [semantics, if_neg hnoerror, hchoice]
      rfl
    have hsourceTimeout (k : Nat) : (evaluate {s with clock := k}).1 = .timeOut := by
      cases he : (evaluate {s with clock := k}).1 with
      | timeOut => rfl
      | error => exact False.elim (hnoerror ⟨k, he⟩)
      | halt outcome =>
        have hev : evaluate {s with clock := k} =
            (.halt outcome, (evaluate {s with clock := k}).2) := by
          exact Prod.ext he rfl
        exact False.elim (holOptionSome_none hchoice
          (.terminate outcome (evaluate {s with clock := k}).2.ffi.ioEvents)
          ⟨k, _, outcome, hev, rfl⟩)
    have htargetTimeout (k : Nat) : (evaluateTargetHOL mc s.ffi k ms).1 = .timeOut := by
      by_contra hn
      obtain ⟨extra, ms2, he⟩ := sim k
      have stable := evaluateTargetAddClock mc s.ffi k ms extra
        (evaluateTargetHOL mc s.ffi k ms).1 (evaluateTargetHOL mc s.ffi k ms).2.1
        (evaluateTargetHOL mc s.ffi k ms).2.2 rfl hn
      have hfst := congrArg Prod.fst stable
      have hsim := congrArg Prod.fst he
      exact hn (hfst.symm.trans (hsim.trans (hsourceTimeout k)))
    have htargetAll : ∀ k, ∃ ms' ffi',
        evaluateTargetHOL mc s.ffi k ms = (.timeOut, ms', ffi') := by
      intro k
      exact ⟨(evaluateTargetHOL mc s.ffi k ms).2.1,
        (evaluateTargetHOL mc s.ffi k ms).2.2, Prod.ext (htargetTimeout k) rfl⟩
    have hfamily : (fun ll => ∃ k,
        HolLList.fromList (evaluateTargetHOL mc s.ffi k ms).2.2.ioEvents = ll) =
          targetTraces := by
      funext ll
      apply propext
      constructor
      · rintro ⟨k, he⟩; exact ⟨k, he.symm⟩
      · rintro ⟨k, he⟩; exact ⟨k, he.symm⟩
    funext behavior
    apply propext
    rw [hsem]
    cases behavior with
    | terminate outcome events =>
      constructor
      · rintro ⟨k, ms', ffi', hr, _⟩
        have he := htargetTimeout k
        rw [hr] at he
        cases he
      · intro h; cases h
    | fail =>
      constructor
      · rintro ⟨k, hr⟩
        have he := (htargetTimeout k).symm.trans hr
        cases he
      · intro h; cases h
    | diverge trace =>
      simp only [machineSemHOL, HolBehaviour.diverge.injEq]
      rw [hfamily]
      constructor
      · intro h; exact HolLList.unique_lprefix_lub h.2 hlub
      · intro h; cases h; exact ⟨htargetAll, hlub⟩

end Flapjack.Compiler.Backend.LabToTarget
