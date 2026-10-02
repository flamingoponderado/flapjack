import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectRight

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack proof factoring of the conditional immediate rename. The original
If compiler clause uses this literal match inline, so this private helper has
no independent HOL declaration. -/
private def renameConditionalImm {width : Nat} (ssa : Spt Nat) :
    WordRegImm (BitVec width) → WordRegImm (BitVec width)
  | .reg name => .reg (optionLookup ssa name)
  | .imm value => .imm value

/-- Flapjack corollary for the original If proof's two get_var_imm cases.
Success is an internal derived branch fact, never an extra premise of the
public pass case. This has no independent HOL declaration. -/
private theorem getVarImmTransport {width : Nat} [NeZero width]
    {C₁ F₁ C₂ F₂ : Type} (next : Nat) (ssa : Spt Nat)
    (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂)
    (immediate : WordRegImm (BitVec width)) (value : WordLocW width)
    (locals : ssaLocalsRel next ssa source.locals target.locals)
    (success : WordSemStateFiniteExact.getVarImm immediate source = some value) :
    WordSemStateFiniteExact.getVarImm (renameConditionalImm ssa immediate) target = some value := by
  cases immediate with
  | reg name =>
    exact ssaLocalsRelGetVar next ssa source target name value ⟨locals, success⟩
  | imm word =>
    simpa only [WordSemStateFiniteExact.getVarImm, renameConditionalImm] using success

/-- Flapjack proof factoring of the native Seq clause after the original
fix_clock_evaluate theorem discharges clock normalization. This has no
independent HOL declaration; the full semantic Seq case uses this equation
without assuming a target execution or successful first result. -/
private theorem evaluateSeqNative {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (state : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq first second) state =
      match WordSemStateFiniteExact.evaluate first state with
      | (none, after) => WordSemStateFiniteExact.evaluate second after
      | (some result, after) => (some result, after) := by
  simp only [WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.fix_clock_evaluate]
  cases WordSemStateFiniteExact.evaluate first state with
  | mk result after => cases result <;> rfl


/-- Flapjack-only factoring of a chosen If branch followed by native
reconciliation. It is an internal conclusion, not an added premise of the
public original case, and has no independent HOL declaration. -/
private noncomputable def reconciledBranch {width : Nat} [NeZero width] {C F : Type}
    (body output moves : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F)
    (finalMap : Spt Nat) (nextFinal : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Prop := by
  classical
  exact ∃ permutation : Nat → Nat → Nat,
    let sourceRun := WordSemStateFiniteExact.evaluate body {source with permute := permutation}
    if sourceRun.1 = some .error then True else
      let targetRun := WordSemStateFiniteExact.evaluate (.seq output moves) target
      sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        match sourceRun.1 with
        | none => ssaLocalsRel nextFinal finalMap sourceRun.2.locals targetRun.2.locals
        | some (.break n) => match tables[n]? with
          | none => True
          | some (dest, _, exits) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup dest) (sptDomain exits) sourceRun.2.locals targetRun.2.locals
        | some (.continue n) => match tables[n]? with
          | none => True
          | some (dest, entries, _) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup dest) (sptDomain entries) sourceRun.2.locals targetRun.2.locals
        | some _ => sourceRun.2.locals = targetRun.2.locals

/-- Flapjack proof composition for a chosen branch; both premises below are
internal facts derived from its legitimate IH and original fix-inconsistencies
wrapper. Neither is a premise of the public native If port. -/
private theorem simulateReconciledBranch {width : Nat} [NeZero width] {C F : Type}
    (body output moves : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F)
    (ssa mapOut finalMap : Spt Nat) (next nextOut nextFinal : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (compiled : ssaCcTrans body ssa next tables = (output, mapOut, nextOut))
    (moveSpec : ∀ (sourceAfter targetAfter : WordSemStateFiniteExact width C F),
      ssaLocalsRel nextOut mapOut sourceAfter.locals targetAfter.locals →
      let run := WordSemStateFiniteExact.evaluate moves targetAfter
      run.1 = none ∧ ssaLocalsRel nextFinal finalMap sourceAfter.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel targetAfter run.2)
    (sim : ssaSimulation body source target ssa next tables) :
    reconciledBranch body output moves source target finalMap nextFinal tables := by
  classical
  obtain ⟨permutation, simulation⟩ := sim
  refine ⟨permutation, ?_⟩
  cases sourceEval : WordSemStateFiniteExact.evaluate body {source with permute := permutation} with
  | mk result sourceAfter =>
    cases result with
    | some result =>
      by_cases error : result = .error
      · subst result
        simp only [↓reduceIte]
      · cases targetEval : WordSemStateFiniteExact.evaluate output target with
        | mk targetResult targetAfter =>
          dsimp only at simulation
          rw [sourceEval] at simulation
          have noError : (some result : Option (WordSemResult width)) ≠ some .error := by simpa using error
          simp only [if_neg noError, compiled, targetEval] at simulation
          have eq : targetResult = some result := simulation.1.symm
          subst targetResult
          dsimp only
          simp only [if_neg noError, evaluateSeqNative, targetEval]
          cases result <;> try (simpa only using simulation)
          all_goals
            rename_i n
            cases table : tables[n]? <;> simpa only [table] using simulation
    | none =>
      cases targetEval : WordSemStateFiniteExact.evaluate output target with
      | mk targetResult targetAfter =>
        dsimp only at simulation
        rw [sourceEval] at simulation
        simp only [reduceCtorEq, ↓reduceIte, compiled, targetEval] at simulation
        have eq : targetResult = none := simulation.1.symm
        subst targetResult
        have moved := moveSpec sourceAfter targetAfter simulation.2.2
        cases movesEval : WordSemStateFiniteExact.evaluate moves targetAfter with
        | mk movesResult movesAfter =>
          simp only [movesEval] at moved
          have eq : movesResult = none := moved.1
          subst movesResult
          dsimp only
          simp only [reduceCtorEq, ↓reduceIte, evaluateSeqNative, targetEval, movesEval]
          refine ⟨True.intro, ?_, moved.2.1⟩
          simp_all [Flapjack.WordAlloc.wordStateEqRel]

namespace SemanticIfWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticIfWitnesses

/-- Full original semantic If case with all six premises and the complete
Error-exempt source-permutation/result/frame/result-sensitive locals conclusion.
Only the legitimate two smaller-branch IHs supplement the original premises.
The second branch starts with the original SSA map at the first branch's fresh
bound. Native compiler invariants derive all growing allocation/map/occurrence
bounds; original fixInconsistenciesCorrectL/R derive reconciliation on NONE.
Early results preserve the original result-specific locals relation. No desired
target evaluation, success, or post-state relation is assumed. The total evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8). Canonical holEl/holHd are
inherited through the reviewed compiler invariant and reconciliation proofs;
original If9263-9331 adds no selector default or weakened out-of-range behavior.
Reconciliation selector bounds remain discharged by the original helper guards.
Final whole-program assembly must discharge both branch IHs. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectIf {width : Nat} [NeZero width] {C F : Type}
    (operator : Cmp) (left : Nat) (immediate : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (firstIH : ∀ (source target : WordSemStateFiniteExact width C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation first source target ssa next tables)
    (secondIH : ∀ (source target : WordSemStateFiniteExact width C F)
      (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) second = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation second source target ssa next tables)
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.ite operator left immediate first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.ite operator left immediate first second) source target ssa next tables := by
  classical
  have vars : decide (left < next) = true ∧ everyVarImmHOL (fun x => decide (x < next)) immediate = true ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      everyVarHOL (fun x => decide (x < next)) second = true := by
    simpa only [everyVarHOL, Bool.and_eq_true, and_assoc] using h.2.2.2.1
  rcases firstCompiled : ssaCcTrans first ssa next tables with ⟨firstOut, mapFirst, nextFirst⟩
  rcases secondCompiled : ssaCcTrans second ssa nextFirst tables with ⟨secondOut, mapSecond, nextSecond⟩
  rcases reconciled : fixInconsistencies (width := width) (mkPrio firstOut secondOut)
      mapFirst mapSecond nextSecond with ⟨movesFirst, movesSecond, nextFinal, finalMap⟩
  have compiled : ssaCcTrans (.ite operator left immediate first second) ssa next tables =
      (.ite operator (optionLookup ssa left) (renameConditionalImm ssa immediate)
        (.seq firstOut movesFirst) (.seq secondOut movesSecond), finalMap, nextFinal) := by
    simp only [ssaCcTrans, firstCompiled, secondCompiled, reconciled, renameConditionalImm]
    cases immediate <;> rfl
  have firstInvariant := ssaCcTransProps first ssa next tables firstOut mapFirst nextFirst
    firstCompiled ⟨h.2.2.2.2.1, h.2.2.1⟩
  have initialMapLater := ssaMapOKMore next ssa nextFirst ⟨h.2.2.2.2.1, firstInvariant.1⟩
  have secondInvariant := ssaCcTransProps second ssa nextFirst tables secondOut mapSecond nextSecond
    secondCompiled ⟨initialMapLater, firstInvariant.2.1⟩
  have readLeft (permutation : Nat → Nat → Nat) :
      WordSemStateFiniteExact.getVar left {source with permute := permutation} =
        WordSemStateFiniteExact.getVar left source := rfl
  have readRight (permutation : Nat → Nat → Nat) :
      WordSemStateFiniteExact.getVarImm immediate {source with permute := permutation} =
        WordSemStateFiniteExact.getVarImm immediate source := by
    cases immediate <;> rfl
  cases sourceLeft : WordSemStateFiniteExact.getVar left source with
  | none =>
    refine ⟨target.permute, ?_⟩
    simp [WordSemStateFiniteExact.evaluate, readLeft, readRight, sourceLeft]
  | some leftValue =>
    cases sourceRight : WordSemStateFiniteExact.getVarImm immediate source with
    | none =>
      refine ⟨target.permute, ?_⟩
      simp [WordSemStateFiniteExact.evaluate, readLeft, readRight, sourceLeft, sourceRight]
    | some rightValue =>
      have targetLeft := ssaLocalsRelGetVar next ssa source target left leftValue ⟨h.2.1, sourceLeft⟩
      have targetRight := getVarImmTransport next ssa source target immediate rightValue h.2.1 sourceRight
      cases comparison : wordSemWordCmp operator leftValue rightValue with
      | none =>
        refine ⟨target.permute, ?_⟩
        simp [WordSemStateFiniteExact.evaluate, readLeft, readRight, sourceLeft, sourceRight, comparison]
      | some condition =>
        cases condition with
        | false =>
          have secondVars : everyVarHOL (fun x => decide (x < nextFirst)) second = true := by
            apply Flapjack.everyVarMono _ second _
            refine ⟨?_, vars.2.2.2⟩
            intro x bound
            have : x < next := of_decide_eq_true bound
            exact decide_eq_true (Nat.lt_of_lt_of_le this firstInvariant.1)
          have sim := secondIH source target ssa nextFirst tables
            ⟨h.1, ssaLocalsRelMore next ssa source.locals target.locals nextFirst ⟨h.2.1, firstInvariant.1⟩,
              firstInvariant.2.1, secondVars, initialMapLater, h.2.2.2.2.2⟩
          have moveSpec : ∀ (sourceAfter targetAfter : WordSemStateFiniteExact width C F),
              ssaLocalsRel nextSecond mapSecond sourceAfter.locals targetAfter.locals →
              let run := WordSemStateFiniteExact.evaluate movesSecond targetAfter
              run.1 = none ∧ ssaLocalsRel nextFinal finalMap sourceAfter.locals run.2.locals ∧
                Flapjack.WordAlloc.wordStateEqRel targetAfter run.2 := by
            intro sourceAfter targetAfter locals
            have fixed := fixInconsistenciesCorrectR nextSecond mapFirst mapSecond
              (mkPrio firstOut secondOut) sourceAfter targetAfter
              ⟨secondInvariant.2.1, secondInvariant.2.2⟩
            rw [reconciled] at fixed
            exact fixed locals
          obtain ⟨permutation, branch⟩ := simulateReconciledBranch second secondOut movesSecond source target
            ssa mapSecond finalMap nextFirst nextSecond nextFinal tables secondCompiled moveSpec sim
          refine ⟨permutation, ?_⟩
          dsimp only at branch ⊢
          simp only [WordSemStateFiniteExact.evaluate, readLeft, readRight, sourceLeft, sourceRight, comparison, targetLeft,
            targetRight, compiled] at branch ⊢
          exact branch
        | true =>
          have sim := firstIH source target ssa next tables
            ⟨h.1, h.2.1, h.2.2.1, vars.2.2.1, h.2.2.2.2⟩
          have mapLater := ssaMapOKMore nextFirst mapFirst nextSecond
            ⟨firstInvariant.2.2, secondInvariant.1⟩
          have moveSpec : ∀ (sourceAfter targetAfter : WordSemStateFiniteExact width C F),
              ssaLocalsRel nextFirst mapFirst sourceAfter.locals targetAfter.locals →
              let run := WordSemStateFiniteExact.evaluate movesFirst targetAfter
              run.1 = none ∧ ssaLocalsRel nextFinal finalMap sourceAfter.locals run.2.locals ∧
                Flapjack.WordAlloc.wordStateEqRel targetAfter run.2 := by
            intro sourceAfter targetAfter locals
            have fixed := fixInconsistenciesCorrectL nextSecond mapFirst mapSecond
              (mkPrio firstOut secondOut) sourceAfter targetAfter ⟨secondInvariant.2.1, mapLater⟩
            rw [reconciled] at fixed
            exact fixed (ssaLocalsRelMore nextFirst mapFirst sourceAfter.locals targetAfter.locals nextSecond
              ⟨locals, secondInvariant.1⟩)
          obtain ⟨permutation, branch⟩ := simulateReconciledBranch first firstOut movesFirst source target
            ssa mapFirst finalMap next nextFirst nextFinal tables firstCompiled moveSpec sim
          refine ⟨permutation, ?_⟩
          dsimp only at branch ⊢
          simp only [WordSemStateFiniteExact.evaluate, readLeft, readRight, sourceLeft, sourceRight, comparison, targetLeft,
            targetRight, compiled] at branch ⊢
          exact branch

end Flapjack.Compiler.Backend.WordAlloc
