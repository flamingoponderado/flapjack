import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopIteration
import Flapjack.Pancake.WordConvs.ProgramMonotonicity

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticLoopWitnesses

/-- Canonical roundtrip of the imported native state finite maps. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticLoopWitnesses

/-- Full native SSA Loop case assembled from setup and inner clock induction.
Only the original smaller-body induction hypothesis supplements the six original
premises. All setup/body evaluations and post-state relations are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectLoop {width : Nat} [NeZero width] {C F : Type}
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact width C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → ssaSimulation body st ct map na lt)
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) (.loop names body exits) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.loop names body exits) source target ssa next tables := by
  classical
  obtain ⟨frame,locals,allocated,vars,valid,tableValid⟩ := premises
  have bounds : ((∀ key ∈ (sptToAList names).map Prod.fst, key < next) ∧
      everyVarHOL (fun key => decide (key < next)) body = true) ∧
      (∀ key ∈ (sptToAList exits).map Prod.fst, key < next) := by
    simpa only [everyVarHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] using vars
  rcases setup : loopSetup (width := width) names exits ssa next with ⟨setupProg,refreshed,nextRefreshed⟩
  obtain ⟨after,setupRun,afterFrame,afterLocals,increase,afterAllocated,afterValid,
    domain,entryInjection,exitInjection,images⟩ :=
    loopSetupCorrect source target ssa next names exits setupProg refreshed nextRefreshed
      ⟨frame,locals,valid,allocated,setup⟩
  have namesMapped : ∀ key, sptDomain names key → sptDomain refreshed key := by
    intro key member
    rw [domain,sptDomain_sptUnion]
    exact Or.inr (Or.inl member)
  have exitsMapped : ∀ key, sptDomain exits key → sptDomain refreshed key := by
    intro key member
    rw [domain,sptDomain_sptUnion]
    exact Or.inr (Or.inr member)
  have bodyVars : everyVarHOL (fun key => decide (key < nextRefreshed)) body = true :=
    Flapjack.everyVarMono _ body _ ⟨fun key bound => by
      simp only [decide_eq_true_eq] at bound ⊢
      exact Nat.lt_of_lt_of_le bound increase, bounds.1.2⟩
  rcases compiledBody : ssaCcTrans body (sptInter refreshed names) nextRefreshed
      ((refreshed,names,exits)::tables) with ⟨output,mapOut,nextOut⟩
  let finalBody : WordLangProgHOL (BitVec width) := match ssaReconcile mapOut refreshed names with
    | .skip => output | moves => .seq output moves
  let targetLoop : WordLangProgHOL (BitVec width) :=
    .loop (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names) finalBody
      (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) exits)
  have compiled : ssaCcTrans (.loop names body exits) ssa next tables =
      (.seq setupProg targetLoop,sptInter refreshed exits,nextOut) := by
    simp only [ssaCcTrans,setup,compiledBody]
    dsimp only [targetLoop,finalBody]
    cases ssaReconcile (width := width) mapOut refreshed names <;> rfl
  cases targetRun : WordSemStateFiniteExact.evaluate targetLoop after with
  | mk targetResult targetFinal =>
    have inner := ssaCcTransLoopHelper source after refreshed nextRefreshed names exits body output
      tables mapOut nextOut ⟨afterFrame,?_,?_,afterValid,afterAllocated,bodyVars,
        entryInjection,exitInjection,namesMapped,exitsMapped,?_,?_,tableValid,compiledBody,bodyIH⟩
    · obtain ⟨permutation,post⟩ := inner targetResult targetFinal targetRun
      refine ⟨permutation,?_⟩
      dsimp only [ssaSimulation]
      rw [compiled,evaluateSeqCollapse _ _ _ _ setupRun,targetRun]
      dsimp only at post ⊢
      generalize sourceRun : WordSemStateFiniteExact.evaluate (.loop names body exits)
        {source with permute := permutation} = run at post ⊢
      rcases run with ⟨result,state⟩
      dsimp only at post ⊢
      by_cases error : result = some .error
      · simp [error]
      · rw [if_neg error]
        exact post.resolve_left error
    · intro key value present
      have relation := afterLocals.2 key value present.2
      obtain ⟨register,read⟩ := (sptMem_iff_lookup key refreshed).mp relation.1
      simpa [optionLookup,read] using relation.2.1
    · intro key member
      exact images key (namesMapped key member)
    · intro key member
      exact Nat.lt_of_lt_of_le (bounds.1.1 key member) increase
    · intro key member
      exact Nat.lt_of_lt_of_le (bounds.2 key member) increase

end Flapjack.Compiler.Backend.WordAlloc
