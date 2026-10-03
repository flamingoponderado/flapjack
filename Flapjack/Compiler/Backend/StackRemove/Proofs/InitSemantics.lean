import Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeCorrect
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.Semantics.StackSem.Semantics
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeRelation

/-! Initializer semantics of `stack_removeProofScript.sml` (3856-4087):
`evaluate_init_code`, `init_semantics`, `make_init_opt_SOME_semantics` and
`make_init_semantics`; the latter uses the accepted `IMP_code_rel` port of
`InitCodeRelation`.
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitSemantics
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about any initializer run. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Complete original initializer run theorem: under `init_pre` and the
original oracle, code and halt-label premises, the native initializer returns
normally, `make_init_opt` yields a state in the original `state_rel` to the
post-state, and the FFI state is preserved. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_init_code"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateInitCode {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (pointer start : Nat) (s : StackSemStateFiniteExact width C F)
    (jump : Bool) (bounds : BitVec width × BitVec width)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : Spt (HolProg width))
    (hyp : InitMake.initPre generateGc maxHeap bitmaps dataSpace pointer start s ∧
      s.compileOracle = (fun index =>
        let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
        Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
      sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) ∧
      codeRelHOL jump bounds pointer code s.code) :
    match StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
    | (none, t) => ∃ r, InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump
        bounds pointer code s = some r ∧ stateRelHOL jump bounds pointer r t ∧ t.ffi = s.ffi
    | _ => False := by
  obtain ⟨⟨_, pre, maxOk⟩, oracleEq, oracleBound, errLab, codeRel⟩ := hyp
  have main := InitCodeCorrect.initCodeThm generateGc maxHeap pointer bitmaps dataSpace s jump
    bounds code oracle ⟨pre, codeRel, oracleEq, oracleBound, errLab, maxOk⟩
  unfold InitMake.makeInitOpt
  revert main
  cases StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
  | mk result t =>
    cases result with
    | some r => simp
    | none =>
      rintro ⟨_, rel, ffi, prop, _⟩
      exact ⟨_, by simp only []; rw [if_pos prop], rel, ffi⟩

/-- Prefixing a clock-zero timeout to the clock-indexed evaluations leaves
the observable semantics unchanged when results and FFI states shift by one.
Flapjack infrastructure for the clock argument of `init_semantics`. -/
theorem semanticsAux_shift {width : Nat} [NeZero width] {C F : Type}
    (E E' : Nat → Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (h0 : (E' 0).1 = some .timeOut) (hffi0 : (E' 0).2.ffi = (E 0).2.ffi)
    (hs : ∀ k, (E' (k + 1)).1 = (E k).1 ∧ (E' (k + 1)).2.ffi = (E k).2.ffi) :
    StackSemEvaluate.semanticsAux E' = StackSemEvaluate.semanticsAux E := by
  unfold StackSemEvaluate.semanticsAux
  have hfail : (∃ k, let res := (E' k).1
      res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
      (∀ w, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e)) ↔
    (∃ k, let res := (E k).1
      res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
      (∀ w, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e)) := by
    constructor
    · rintro ⟨k, hk⟩
      cases k with
      | zero => exact absurd h0 hk.1
      | succ k => exact ⟨k, by rw [← (hs k).1]; exact hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, by rw [(hs k).1]; exact hk⟩
  have hD : (fun l => ∃ k, l = HolLList.fromList (E' k).2.ffi.ioEvents) =
      (fun l => ∃ k, l = HolLList.fromList (E k).2.ffi.ioEvents) := by
    funext l
    apply propext
    constructor
    · rintro ⟨k, rfl⟩
      cases k with
      | zero => exact ⟨0, by rw [hffi0]⟩
      | succ k => exact ⟨k, by rw [(hs k).2]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k + 1, by rw [(hs k).2]⟩
  by_cases f : (∃ k, let res := (E k).1
      res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
      (∀ w, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e))
  · rw [if_pos (hfail.mpr f), if_pos f]
  · rw [if_neg (fun h => f (hfail.mp h)), if_neg f, hD]
    congr 2
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, o, he, hm, hr⟩
      cases k with
      | zero =>
        have : r = .timeOut := by
          have := congrArg Prod.fst he; rw [h0] at this; exact (Option.some.inj this).symm
        subst this; exact absurd hm id
      | succ k =>
        refine ⟨k, (E k).2, r, o, Prod.ext ?_ rfl, hm, ?_⟩
        · rw [← (hs k).1, he]
        · rw [hr, ← (hs k).2, he]
    · rintro ⟨k, t, r, o, he, hm, hr⟩
      refine ⟨k + 1, (E' (k + 1)).2, r, o, Prod.ext ?_ rfl, hm, ?_⟩
      · rw [(hs k).1, he]
      · rw [hr, (hs k).2, he]

/-- A direct tail call never returns a bad function result. -/
theorem callNotBad {width : Nat} [NeZero width] {C F : Type} (dest : Nat)
    (x : StackSemStateFiniteExact width C F) :
    StackSemControl.badFunReturn
      (StackSemEvaluate.evaluate (.call none (.inl dest) none, x)).1 = false := by
  rw [StackSemEvaluate.evaluate_call]
  simp only
  repeat' split
  all_goals simp_all [StackSemControl.badFunReturn]

/-- A direct tail call at clock zero keeps the FFI state. -/
theorem callZeroFfi {width : Nat} [NeZero width] {C F : Type} (dest : Nat)
    (x : StackSemStateFiniteExact width C F) (zero : x.clock = 0) :
    (StackSemEvaluate.evaluate (.call none (.inl dest) none, x)).2.ffi = x.ffi := by
  rw [StackSemEvaluate.evaluate_call]
  simp only
  split
  · rfl
  · simp [zero, StackSemStateOps.emptyEnv]

/-- Complete original initializer semantics theorem: under the original
premises the initializer returns normally, the semantics of the entry call
from label 0 equals that of `start` from the post-state, and `make_init_opt`
yields a state in the original `state_rel`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_semantics"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem initSemantics {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (pointer start : Nat) (s : StackSemStateFiniteExact width C F)
    (jump : Bool) (bounds : BitVec width × BitVec width)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : Spt (HolProg width))
    (hyp : sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) ∧
      codeRelHOL jump bounds pointer code s.code ∧
      InitMake.initPre generateGc maxHeap bitmaps dataSpace pointer start s ∧
      s.compileOracle = (fun index =>
        let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
        Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1)) :
    match StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
    | (none, t) => StackSemEvaluate.semantics 0 s = StackSemEvaluate.semantics start t ∧
        ∃ r, InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds
          pointer code s = some r ∧ stateRelHOL jump bounds pointer r t
    | _ => False := by
  obtain ⟨errLab, codeRel, pre, oracleEq, oracleBound⟩ := hyp
  have run := evaluateInitCode generateGc maxHeap bitmaps dataSpace pointer start s jump bounds
    oracle code ⟨pre, oracleEq, oracleBound, errLab, codeRel⟩
  have entry := pre.1
  revert run
  cases hrun : StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
  | mk result t =>
    cases result with
    | some r => simp
    | none =>
      rintro ⟨r, opt, rel, ffi⟩
      refine ⟨?_, r, opt, rel⟩
      rw [StackSemEvaluate.semantics_eq_aux, StackSemEvaluate.semantics_eq_aux]
      apply semanticsAux_shift
      · rw [StackSemEvaluate.evaluate_call]
        simp [StackSemControl.findCode, entry]
      · rw [callZeroFfi _ _ rfl, callZeroFfi _ _ rfl]
        exact ffi.symm
      · intro k
        have clockRun := InitClock.evaluateInitCodeClock generateGc maxHeap pointer s t none k hrun
        have body : StackSemEvaluate.evaluate (.seq (initCode generateGc maxHeap pointer)
            (.call none (.inl start) none), {s with clock := k}) =
            StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := k}) := by
          rw [StackSemEvaluate.evaluate_seq, clockRun]
          simp [StackSemControl.fixClock]
        have notBad := callNotBad start {t with clock := k}
        rw [StackSemEvaluate.evaluate_call]
        simp only [StackSemControl.findCode, entry, Nat.add_one_ne_zero, if_false,
          StackSemStateOps.decClock, Nat.add_sub_cancel]
        rw [show ({ ({s with clock := k + 1} : StackSemStateFiniteExact width C F) with
            clock := k } : StackSemStateFiniteExact width C F) = {s with clock := k} from rfl, body]
        simp only [StackSemControl.fixClock, notBad]
        exact ⟨rfl, rfl⟩

/-- Complete original optional-initialization semantics theorem: the initial
state yields an initialized state whose non-failing semantics from `start` is
the semantics of the whole program from label 0. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_opt_SOME_semantics"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem makeInitOptSomeSemantics {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (pointer start : Nat) (s2 : StackSemStateFiniteExact width C F)
    (jump : Bool) (bounds : BitVec width × BitVec width)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : Spt (HolProg width))
    (hyp : InitMake.initPre generateGc maxHeap bitmaps dataSpace pointer start s2 ∧
      s2.compileOracle = (fun index =>
        let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
        Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
      codeRelHOL jump bounds pointer code s2.code ∧
      sptLookup stackErrLab s2.code = some (haltInst (BitVec.ofNat width 2))) :
    ∃ s1, InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer
        code s2 = some s1 ∧
      (StackSemEvaluate.semantics start s1 ≠ HolBehaviour.fail →
        StackSemEvaluate.semantics 0 s2 = StackSemEvaluate.semantics start s1) := by
  obtain ⟨pre, oracleEq, oracleBound, codeRel, errLab⟩ := hyp
  have sem := initSemantics generateGc maxHeap bitmaps dataSpace pointer start s2 jump bounds
    oracle code ⟨errLab, codeRel, pre, oracleEq, oracleBound⟩
  revert sem
  cases StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s2) with
  | mk result t =>
    cases result with
    | some r => simp
    | none =>
      rintro ⟨semEq, r, opt, rel⟩
      refine ⟨r, opt, fun notFail => ?_⟩
      rw [semEq]
      exact CompileSemantics.compileSemantics jump bounds pointer start r t ⟨rel, notFail⟩

/-- Complete original top-level initialization semantics theorem: from the
compiler-side `discharge_these` and machine-side `propagate_these` bundles,
the optional initialization of the compiled program succeeds and the
semantics from label 0 equals the non-failing semantics of the initialized
state from `start`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_semantics"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem makeInitSemantics {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maxHeap pointer start : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : List (Nat × HolProg width)) (s2 : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (hyp : InitMake.dischargeThese jump bounds generateGc maxHeap pointer start oracle code s2 ∧
      InitMake.propagateThese s2 bitmaps dataSpace) :
    ∃ s1, InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer
        (sptFromAList code) s2 = some s1 ∧
      (StackSemEvaluate.semantics start s1 ≠ HolBehaviour.fail →
        StackSemEvaluate.semantics 0 s2 = StackSemEvaluate.semantics start s1) := by
  obtain ⟨⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩, good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := hyp
  apply makeInitOptSomeSemantics generateGc maxHeap bitmaps dataSpace pointer start s2 jump
    bounds oracle (sptFromAList code)
  refine ⟨⟨?_, ?_, maxOk⟩, oracleEq, oracleBound, InitCodeRelation.impCodeRel jump bounds
    generateGc maxHeap pointer start code s2.code ⟨every, codeEq⟩, ?_⟩
  · rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup]
  · have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
      rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
    rw [sub] at heap
    exact ⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
      m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩
  · rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup, stackErrLab]

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitSemantics
