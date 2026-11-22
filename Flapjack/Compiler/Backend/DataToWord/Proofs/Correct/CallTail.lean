module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Induction
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FindCode
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JumpExc
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

@[expose] public section

/-! The tail-call (`ret = NONE`) branch of the `Call` case of the
data-to-word evaluator simulation (`data_to_wordProofScript.sml` lines
934-967). Flapjack-specific case infrastructure for `data_compile_correct`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The exception location does not depend on the recorded maximum stack size. -/
theorem mkLoc_jumpExc_stackMax {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (m : Option Nat) :
    mkLoc (width := width) (WordSemStateFiniteExact.jumpExc { t with stackMax := m }) =
      mkLoc (width := width) (WordSemStateFiniteExact.jumpExc t) := by
  unfold WordSemStateFiniteExact.jumpExc
  simp only
  split
  · split <;> simp [mkLoc]
  · rfl

/-- Entering a callee frame without a handler leaves the exception location
and its presence unchanged. -/
theorem jumpExc_callEnv_decClock {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (args : List (WordLocW width)) (ss : Option Nat) :
    mkLoc (width := width) (WordSemStateFiniteExact.jumpExc
        (WordSemStateFiniteExact.callEnv args ss (WordSemStateFiniteExact.decClock t))) =
      mkLoc (width := width) (WordSemStateFiniteExact.jumpExc t) ∧
    (WordSemStateFiniteExact.jumpExc
        (WordSemStateFiniteExact.callEnv args ss (WordSemStateFiniteExact.decClock t)) = none ↔
      WordSemStateFiniteExact.jumpExc t = none) := by
  rw [jumpExc_callEnv]
  constructor
  · rw [mkLoc_jumpExc_stackMax]
    exact jumpExc_decClock t
  · rw [(jumpExc_pushEnv_none_iff _ (.ln, .ln) _).2.2]
    exact (jumpExc_pushEnv_none_iff t (.ln, .ln) none).1

/-- The tail-call branch of `data_compile_correct`'s `Call` case, under the
evaluator induction hypothesis for the callee body. -/
theorem dataCompileCorrect_callTail {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × Flapjack.Compiler.Backend.DataLang.Prog))
    (ih : ∀ xs args1 prog ss,
      DataSem.getVars args source.locals = some xs ∧
      DataSem.findCode dest xs source.code source.stackFrameSizes = some (args1, prog, ss) ∧
      handler = none ∧ source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog
        (DataSem.callEnv args1 ss (DataSem.decClock source))) :
    dataCompileCorrectInduction (width := width) (.call none dest args handler) source := by
  intro conf n l l1 l2 res source1 target locs run notTypeError related depth
  have compiled : (compileControl (width := width) conf n l (.call none dest args handler)).1 =
      .call none dest (0 :: args.map adjustVar) none := by
    have h := compileControl_option (width := width) conf n l (.call none dest args handler)
    simp [compileControl?] at h
    rw [← h]
  have hclock : target.clock = source.clock := related.2.1
  have hffi : target.ffi = source.ffi := related.1
  have hsize : target.stackSize = source.stackFrameSizes :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have bound : optionLe target.stackMax source.stackMax :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hxs : DataSem.getVars args source.locals with
  | none =>
    exfalso
    apply notTypeError
    simpa [DataSem.evaluate, hxs] using (congrArg Prod.fst run).symm
  | some xs =>
  cases hfind : DataSem.findCode dest xs source.code source.stackFrameSizes with
  | none =>
    exfalso
    apply notTypeError
    simpa [DataSem.evaluate, hxs, hfind] using (congrArg Prod.fst run).symm
  | some found =>
  obtain ⟨args1, body, ss⟩ := found
  cases handler with
  | some h =>
    exfalso
    apply notTypeError
    simpa [DataSem.evaluate, hxs, hfind] using (congrArg Prod.fst run).symm
  | none =>
  obtain ⟨words, wordRead, _⟩ :=
    stateRel_zero_getVars conf l1 l2 source target locs args xs related hxs
  obtain ⟨args1', n1, n2, wordFind, calleeRel⟩ :=
    findCode_correct conf l1 l2 source target locs args xs words dest source.stackFrameSizes
      args1 body ss ⟨related, hxs, wordRead, hfind⟩
  rw [← hsize] at wordFind
  have notBad : wordSemBadDestArgs dest (0 :: args.map adjustVar) = false := by
    cases dest <;> rfl
  by_cases zero : source.clock = 0
  · have sourceEq : res = some (.err (.abort .timeoutError)) ∧
        source1 = DataSem.flushState true source := by
      simpa [DataSem.evaluate, hxs, hfind, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := sourceEq
    refine ⟨WordSemStateFiniteExact.flushState true target, some .timeOut, ?_, ?_, by simp, ?_⟩
    · simp [compiled, WordSemStateFiniteExact.evaluate, wordRead, notBad, wordSemAddRetLoc,
        wordFind, hclock, zero]
    · simpa [WordSemStateFiniteExact.flushState, DataSem.flushState] using bound
    · intro _
      simpa [WordSemStateFiniteExact.flushState, DataSem.flushState] using hffi
  · cases hcall : DataSem.evaluate body (DataSem.callEnv args1 ss (DataSem.decClock source)) with
    | mk r mid =>
    cases r with
    | none =>
      exfalso
      apply notTypeError
      simpa [DataSem.evaluate, hxs, hfind, zero, hcall] using (congrArg Prod.fst run).symm
    | some r =>
      have sourceEq : res = some r ∧ source1 = mid := by
        simpa [DataSem.evaluate, hxs, hfind, zero, hcall] using run.symm
      obtain ⟨rfl, rfl⟩ := sourceEq
      have depth' : (WordSemStateFiniteExact.callEnv args1' ss
          (WordSemStateFiniteExact.decClock target)).termdep > 1 := by
        simpa [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using depth
      obtain ⟨t1, res1, wordRun, stackBound, space, result⟩ :=
        ih xs args1 body ss ⟨hxs, hfind, rfl, zero⟩ conf n1 n2 l1 l2 (some r) source1
          _ locs hcall notTypeError calleeRel depth'
      have locFacts := jumpExc_callEnv_decClock target args1' ss
      have notBadRet : wordSemBadFunReturn res1 = false := by
        cases res1 with
        | none =>
          have h := result (by simp)
          rcases r with values | (value | (_ | _ | _))
          all_goals simp at h
        | some w =>
          cases w with
          | «break» _ =>
            have h := result (by simp)
            rcases r with values | (value | (_ | _ | _))
            all_goals simp at h
          | «continue» _ =>
            have h := result (by simp)
            rcases r with values | (value | (_ | _ | _))
            all_goals simp at h
          | _ => rfl
      refine ⟨t1, res1, ?_, stackBound, space, ?_⟩
      · simp [compiled, WordSemStateFiniteExact.evaluate, wordRead, notBad, wordSemAddRetLoc,
          wordFind, hclock, zero, wordRun, notBadRet]
      · intro hs
        have h := result hs
        rcases r with values | (value | e)
        · exact h
        · obtain ⟨hf, w, l5, l6, rest, hres, hjump⟩ := h
          refine ⟨hf, w, l5, l6, rest, ?_, ?_⟩
          · rw [hres, locFacts.1]
          · intro present
            exact hjump (fun empty => present (locFacts.2.mp empty))
        · cases e <;> exact h
end Flapjack.Compiler.Backend.DataToWord.Proofs
