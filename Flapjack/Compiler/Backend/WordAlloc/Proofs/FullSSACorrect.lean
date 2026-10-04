import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCorrect
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetupProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Properties
import Flapjack.Compiler.Backend.WordAlloc.FullSSA

namespace Flapjack.Compiler.Backend.WordAlloc
open Classical

namespace FullSSACorrectWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end FullSSACorrectWitnesses

/-- Full native SSA wrapper simulation, deriving the setup and body simulation
from the sole original initial locals-domain premise. Inherits evaluator
reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fullSsaCcTransCorrect {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
    (count : Nat) (domain : sptDomain state.locals = (fun key => key ∈ evenList count)) :
    ∃ permutation : Nat → Nat → Nat,
      let sourceRun := WordSemStateFiniteExact.evaluate prog {state with permute := permutation}
      if sourceRun.1 = some .error then True else
        let targetRun := WordSemStateFiniteExact.evaluate (fullSsaCcTrans count prog) state
        sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
          match sourceRun.1 with
          | none => True
          | some (.break _) => True
          | some (.continue _) => True
          | some _ => sourceRun.2.locals = targetRun.2.locals := by
  classical
  obtain ⟨allocated,bounded⟩ := limitVarProps prog (limitVar prog) rfl
  rcases produced : setupSSA (outputWidth := width) count (limitVar prog) prog with
    ⟨move,map,next⟩
  rcases run : WordSemStateFiniteExact.evaluate move state with ⟨result,target⟩
  have setup := setupSSAProps (limitVar prog) count state prog ⟨allocated,domain⟩
  rw [produced] at setup
  dsimp only at setup
  rw [run] at setup
  obtain ⟨rfl,frame,valid,related,nextAllocated,increase⟩ := setup
  have vars : everyVarHOL (fun key => decide (key < next)) prog = true := by
    apply Flapjack.everyVarMono _ prog _
    refine ⟨?_,bounded⟩
    intro key bound
    simp only [decide_eq_true_eq] at bound ⊢
    omega
  have body := ssaCcTransCorrect prog state target map next []
    ⟨frame,related,nextAllocated,vars,valid,by simp [ltOK]⟩
  obtain ⟨permutation,post⟩ := body
  refine ⟨permutation,?_⟩
  have executed : WordSemStateFiniteExact.evaluate (fullSsaCcTrans count prog) state =
      WordSemStateFiniteExact.evaluate (ssaCcTrans prog map next []).1 target := by
    simp only [fullSsaCcTrans, produced]
    rcases compiled : ssaCcTrans prog map next [] with ⟨output,mapOut,nextOut⟩
    exact evaluateSeqCollapse _ _ state target run
  rw [executed]
  dsimp only at post ⊢
  by_cases error : (WordSemStateFiniteExact.evaluate prog {state with permute := permutation}).1 = some .error
  · simp [error]
  · rw [if_neg error] at post ⊢
    refine ⟨post.1,post.2.1,?_⟩
    cases resultEq : (WordSemStateFiniteExact.evaluate prog {state with permute := permutation}).1 with
    | none => trivial
    | some result =>
      cases result <;> simp_all

end Flapjack.Compiler.Backend.WordAlloc
