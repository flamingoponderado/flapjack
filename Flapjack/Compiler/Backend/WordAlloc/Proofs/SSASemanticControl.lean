import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcile
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopTable
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation
import Flapjack.Pancake.WordLang.OccurrencesExact

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof factoring of the shared conclusion across native SSA
simulation cases. It has no independent HOL declaration and introduces no
assumed target execution or post-state relation. -/
noncomputable def ssaSimulation {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Prop := by
  classical
  exact ∃ permutation : Nat → Nat → Nat,
    let sourceRun := WordSemStateFiniteExact.evaluate prog {source with permute := permutation}
    if sourceRun.1 = some .error then True else
      let compiled := ssaCcTrans prog ssa next tables
      let targetRun := WordSemStateFiniteExact.evaluate compiled.1 target
      sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        match sourceRun.1 with
        | none => ssaLocalsRel compiled.2.2 compiled.2.1 sourceRun.2.locals targetRun.2.locals
        | some (.break n) => match tables[n]? with
          | none => True
          | some (dest, _, exits) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup dest) (sptDomain exits) sourceRun.2.locals targetRun.2.locals
        | some (.continue n) => match tables[n]? with
          | none => True
          | some (dest, entries, _) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup dest) (sptDomain entries) sourceRun.2.locals targetRun.2.locals
        | some _ => sourceRun.2.locals = targetRun.2.locals

/-- Flapjack proof factoring of a compiler-generated exit after reconciliation;
its evaluation premise is an internal derived fact, never a public simulation
case premise. There is no independent HOL declaration. -/
private theorem exitAfterMoves {width : Nat} [NeZero width] {C F : Type}
    (moves exit : WordLangProgHOL (BitVec width)) (result : WordSemResult width)
    (before after : WordSemStateFiniteExact width C F)
    (exitEval : ∀ state : WordSemStateFiniteExact width C F, WordSemStateFiniteExact.evaluate exit state = (some result, state))
    (movesEval : WordSemStateFiniteExact.evaluate moves before = (none, after))
    (frame : Flapjack.WordAlloc.wordStateEqRel before after) :
    WordSemStateFiniteExact.evaluate
      (match moves with | .skip => exit | _ => .seq moves exit) before = (some result, after) := by
  by_cases skip : moves = .skip
  · subst moves
    have eq : before = after := by
      have step := congrArg Prod.snd movesEval
      simpa [WordSemStateFiniteExact.evaluate] using step
    simpa [eq] using exitEval before
  · have shape : (match moves with | .skip => exit | _ => .seq moves exit) = .seq moves exit := by
      cases moves <;> simp_all
    rw [shape]
    rcases frame with ⟨_, _, _, _, _, _, _, _, _, _, _, _, clock, _, _, _, depth, _, _, _, _⟩
    have fixed : WordSemStateFiniteExact.fixClock before ((none : Option (WordSemResult width)), after) = (none, after) := by
      simp only [WordSemStateFiniteExact.fixClock]
      rw [← clock, ← depth]
      simp
    simp only [WordSemStateFiniteExact.evaluate, movesEval, fixed]
    exact exitEval after

namespace SemanticControlWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticControlWitnesses

/-- Complete original resumed semantic Break case. All six original
premises are retained; the original existential source permutation, faithful
target result, complete frame and result-sensitive locals are proved. Both
absent/present loop-table and Skip/non-Skip reconciliation branches are covered.
No target execution, post-frame, additional lookup success or IH is assumed.
The full evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8); only
Break/Skip/Move/Seq run in this case.
Original word_allocProof:10098-10135 uses optional oEL for the loop table;
`tables[n]?` preserves past-end NONE. The inherited holEl/holHd observations
come through evaluateSSAReconcile's bounded filtered-key/value-list indexing
(original:6660-6704), with bounds and equal lengths derived internally.
The shared opaque out-of-range holHdNil/holArb convention remains unchanged;
no extra public index or oracle premise is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectBreak {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.break n : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.break n) source target ssa next tables := by
  refine ⟨target.permute, ?_⟩
  cases selected : tables[n]? with
  | none =>
      simpa [WordSemStateFiniteExact.evaluate, ssaCcTrans, selected,
        Flapjack.WordAlloc.wordStateEqRel] using h.1
  | some entry =>
      obtain ⟨dest, entries, exits⟩ := entry
      have member : (dest, entries, exits) ∈ tables := List.mem_of_getElem? selected
      have injection := (h.2.2.2.2.2 _ member).2
      obtain ⟨after, evaluation, frame, locals⟩ := evaluateSSAReconcile next ssa dest exits
        source.locals target ⟨h.2.1, injection⟩
      have execution : WordSemStateFiniteExact.evaluate
          (ssaCcTrans (.break n) ssa next tables).1 target = (some (.break n), after) := by
        simp only [ssaCcTrans, selected]
        exact exitAfterMoves _ (.break n) (.break n) target after
          (fun state => by simp [WordSemStateFiniteExact.evaluate]) evaluation frame
      have finalFrame : Flapjack.WordAlloc.wordStateEqRel
          {source with permute := target.permute} after := by
        simp_all [Flapjack.WordAlloc.wordStateEqRel]
      simpa [WordSemStateFiniteExact.evaluate, execution, selected] using
        (show some (.break n : WordSemResult width) = some (.break n) ∧
          Flapjack.WordAlloc.wordStateEqRel {source with permute := target.permute} after ∧
          Flapjack.WordAlloc.strongLocalsRel (optionLookup dest) (sptDomain exits)
            source.locals after.locals from ⟨rfl, finalFrame, locals⟩)

/-- Complete original resumed semantic Continue case. All six original
premises are retained; the original existential source permutation, faithful
target result, complete frame and result-sensitive locals are proved. Both
absent/present loop-table and Skip/non-Skip reconciliation branches are covered.
No target execution, post-frame, additional lookup success or IH is assumed.
The full evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8); only
Continue/Skip/Move/Seq run in this case.
Original word_allocProof:10098-10135 uses optional oEL for the loop table;
`tables[n]?` preserves past-end NONE. The inherited holEl/holHd observations
come through evaluateSSAReconcile's bounded filtered-key/value-list indexing
(original:6660-6704), with bounds and equal lengths derived internally.
The shared opaque out-of-range holHdNil/holArb convention remains unchanged;
no extra public index or oracle premise is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectContinue {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.continue n : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.continue n) source target ssa next tables := by
  refine ⟨target.permute, ?_⟩
  cases selected : tables[n]? with
  | none =>
      simpa [WordSemStateFiniteExact.evaluate, ssaCcTrans, selected,
        Flapjack.WordAlloc.wordStateEqRel] using h.1
  | some entry =>
      obtain ⟨dest, entries, exits⟩ := entry
      have member : (dest, entries, exits) ∈ tables := List.mem_of_getElem? selected
      have injection := (h.2.2.2.2.2 _ member).1
      obtain ⟨after, evaluation, frame, locals⟩ := evaluateSSAReconcile next ssa dest entries
        source.locals target ⟨h.2.1, injection⟩
      have execution : WordSemStateFiniteExact.evaluate
          (ssaCcTrans (.continue n) ssa next tables).1 target = (some (.continue n), after) := by
        simp only [ssaCcTrans, selected]
        exact exitAfterMoves _ (.continue n) (.continue n) target after
          (fun state => by simp [WordSemStateFiniteExact.evaluate]) evaluation frame
      have finalFrame : Flapjack.WordAlloc.wordStateEqRel
          {source with permute := target.permute} after := by
        simp_all [Flapjack.WordAlloc.wordStateEqRel]
      simpa [WordSemStateFiniteExact.evaluate, execution, selected] using
        (show some (.continue n : WordSemResult width) = some (.continue n) ∧
          Flapjack.WordAlloc.wordStateEqRel {source with permute := target.permute} after ∧
          Flapjack.WordAlloc.strongLocalsRel (optionLookup dest) (sptDomain entries)
            source.locals after.locals from ⟨rfl, finalFrame, locals⟩)

end Flapjack.Compiler.Backend.WordAlloc
