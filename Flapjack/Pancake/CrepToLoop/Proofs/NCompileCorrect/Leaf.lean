import Flapjack.HolRef
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Leaf cases of `crep_to_loop`'s `ncompile_correct`

Exact source-shaped evaluator-induction cases for the four leaf constructors
resumed at `crep_to_loopProofScript.sml:1648-1678`. Each theorem retains the
HOL pre-evaluation, non-error, and five state/code/memory/global/local relation
hypotheses, and concludes the existential target run and all six postconditions.
The only specialization is the source constructor being proved. Source and
target evaluators, compiler, and relation carriers are the exact finite-support
HOL-shaped ports. In particular, the clock witness is produced in the target
evaluation, and no target result or post-relation is a premise.
-/

namespace Flapjack

namespace NCompileCorrectLeafFmapWitnesses

/-- Same-module roundtrip required by the relation qualifier for the exact
    finite-support Crep state fields used by these cases. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

/-- Same-module roundtrip required by the relation qualifier for the exact
    finite-support context fields used by these cases. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

/-- Same-module roundtrip required by the relation qualifier for the exact
    finite-support Loop state fields used by these cases. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : LoopSemStateBroad width σ) (h : state.FiniteSupport),
      (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width σ,
      LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end NCompileCorrectLeafFmapWitnesses

private abbrev NCompileResultMap {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) →
      Option (LoopSemStateFiniteExact.LoopResultExact width)
  | none => none
  | some (.break label) => some (.break label)
  | some (.continue label) => some (.continue label)
  | some (.return values) => some (.result (values.map wlabWlocExact))
  | some (.exception value) => some (.exception (.word value))
  | some .timeOut => some .timeOut
  | some (.finalFfi event) => some (.finalFfi event)
  | some .error => some .error

/-- Genuine `Skip` induction case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:1648-1653`). The
    statement is the theorem's full implication/existential specialized to
    `.skip`; `Skip` has no induction hypotheses. Both evaluators return their
    input states and `compileHOLExact` leaves the target `Skip` unchanged. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem ncompileCorrectSkipCase {width : Nat} [NeZero width] {σ : Type}
    (v1 : CrepSemHOLState width σ) (res : Option (CrepResultHOLExact width))
    (s1 : CrepSemHOLState width σ) (t : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (hEval : evalCrepSemHOLProgExact v1 (.skip : CrepProgHOL width) = (res, s1))
    (hNotError : res ≠ some .error)
    (hState : crepToLoopStateRelExact v1 t)
    (hMem : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt live v1.locals t.locals) :
    ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (t1 : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt live .skip)
          { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = NCompileResultMap res ∧
        (match res with
         | none => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.break _) => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.continue _) => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.return _) => True
         | some .error => False
         | _ => True) := by
  have hSource : (res, s1) = (none, v1) := by
    simpa only [evalCrepSemHOLProgExact_skip] using hEval.symm
  cases hSource
  rcases crepToLoopStateRelExact_clock_add_zero v1 t hState with ⟨ck, hStateClock⟩
  refine ⟨ck, none, { t with clock := ck + t.clock }, ?_, hStateClock,
    hMem, hGlobals, hCode, ?_, hLocals⟩
  · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact]
    omega
  · rfl

/-- Genuine `Break` induction case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:1655-1660`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem ncompileCorrectBreakCase {width : Nat} [NeZero width] {σ : Type}
    (label : Nat) (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact)
    (live : NumSet)
    (hEval : evalCrepSemHOLProgExact v1 (.break label : CrepProgHOL width) = (res, s1))
    (hNotError : res ≠ some .error)
    (hState : crepToLoopStateRelExact v1 t)
    (hMem : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt live v1.locals t.locals) :
    ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (t1 : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt live (.break label))
          { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = NCompileResultMap res ∧
        (match res with
         | none => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.break _) => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.continue _) => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.return _) => True
         | some .error => False
         | _ => True) := by
  have hSource : (res, s1) = (some (.break label), v1) := by
    simpa only [evalCrepSemHOLProgExact_break] using hEval.symm
  cases hSource
  rcases crepToLoopStateRelExact_clock_add_zero v1 t hState with ⟨ck, hStateClock⟩
  refine ⟨ck, some (.break label), { t with clock := ck + t.clock }, ?_, hStateClock,
    hMem, hGlobals, hCode, ?_, hLocals⟩
  · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact]
    omega
  · rfl

/-- Genuine `Continue` induction case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:1662-1667`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem ncompileCorrectContinueCase {width : Nat} [NeZero width] {σ : Type}
    (label : Nat) (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact)
    (live : NumSet)
    (hEval : evalCrepSemHOLProgExact v1 (.continue label : CrepProgHOL width) = (res, s1))
    (hNotError : res ≠ some .error)
    (hState : crepToLoopStateRelExact v1 t)
    (hMem : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt live v1.locals t.locals) :
    ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (t1 : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt live (.continue label))
          { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = NCompileResultMap res ∧
        (match res with
         | none => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.break _) => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.continue _) => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.return _) => True
         | some .error => False
         | _ => True) := by
  have hSource : (res, s1) = (some (.continue label), v1) := by
    simpa only [evalCrepSemHOLProgExact_continue] using hEval.symm
  cases hSource
  rcases crepToLoopStateRelExact_clock_add_zero v1 t hState with ⟨ck, hStateClock⟩
  refine ⟨ck, some (.continue label), { t with clock := ck + t.clock }, ?_, hStateClock,
    hMem, hGlobals, hCode, ?_, hLocals⟩
  · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact]
    omega
  · rfl

/-- Genuine `Tick` induction case of HOL `ncompile_correct`
    (`crep_to_loopProofScript.sml:110-154`, resumed at `:1669-1677`). The zero
    clock branch clears both local maps and produces `TimeOut`; the positive
    clock branch decrements both clocks and preserves `locals_rel`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem ncompileCorrectTickCase {width : Nat} [NeZero width] {σ : Type}
    (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact)
    (live : NumSet)
    (hEval : evalCrepSemHOLProgExact v1 (.tick : CrepProgHOL width) = (res, s1))
    (hNotError : res ≠ some .error)
    (hState : crepToLoopStateRelExact v1 t)
    (hMem : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt live v1.locals t.locals) :
    ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (t1 : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt live .tick)
          { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = NCompileResultMap res ∧
        (match res with
         | none => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.break _) => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.continue _) => crepToLoopLocalsRelExact ctxt live s1.locals t1.locals
         | some (.return _) => True
         | some .error => False
         | _ => True) := by
  have hClock : v1.clock = t.clock := hState.2.2.1
  by_cases hZero : v1.clock = 0
  · have hSource : (res, s1) =
        (some .timeOut, CrepSemHOLState.emptyLocals v1) := by
      simpa [evalCrepSemHOLProgExact_tick, hZero] using hEval.symm
    cases hSource
    have hTargetZero : t.clock = 0 := by omega
    refine ⟨0, some .timeOut, { t with locals := .ln }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact, hTargetZero]
    · simpa [crepToLoopStateRelExact, CrepSemHOLState.emptyLocals,
        LoopSemStateFiniteExact.evaluate, hTargetZero] using hState
    · simpa [CrepSemHOLState.emptyLocals] using hMem
    · simpa [CrepSemHOLState.emptyLocals] using hGlobals
    · simpa [CrepSemHOLState.emptyLocals] using hCode
    · rfl
    · simp
  · have hSource : (res, s1) = (none, decClockCrepSemHOL v1) := by
      simpa [evalCrepSemHOLProgExact_tick, hZero] using hEval.symm
    cases hSource
    have hTargetNonzero : t.clock ≠ 0 := by omega
    refine ⟨0, none, LoopSemStateFiniteExact.decClock t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact, hTargetNonzero]
    · simpa [crepToLoopStateRelExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock, hClock] using hState
    · simpa [crepToLoopMemRelHOLExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hMem
    · simpa [crepToLoopGlobalsRelHOLExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hGlobals
    · simpa [crepToLoopCodeRelExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hCode
    · rfl
    · exact hLocals

end Flapjack
