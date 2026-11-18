module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.EvaluateMkLoc
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap
@[expose] public section

/-! Local-domain preservation after returning from pushed calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.WordSemStackEq WordSemStateFiniteExact

namespace evaluateDomainMap
/-- Canonical target-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end evaluateDomainMap

/-- A returning call restores exactly the two saved local domains. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "evaluate_IMP_domain_EQ"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_imp_domainEq {width : Nat} [NeZero width] {C F : Type}
    (c : WordLangProgHOL (BitVec width)) (args : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (opt : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (t t1 t2 : WordSemStateFiniteExact width C F) (ll : WordLocW width) (w : List (WordLocW width))
    (premises : evaluate c (WordSemStateFiniteExact.callEnv args ss (pushEnv envs opt (decClock t))) =
      (some (.result ll w), t1) ∧ popEnv t1 = some t2) :
    sptDomain t2.locals = fun k => sptDomain envs.1 k ∨ sptDomain envs.2 k := by
  obtain ⟨run, popped⟩ := premises
  have post := evaluateStackSwap c (WordSemStateFiniteExact.callEnv args ss (pushEnv envs opt (decClock t)))
  simp only [stackSwapPost, run] at post
  have keys : sKeyEq (pushEnv envs opt (decClock t)).stack t1.stack := by
    simpa only [WordSemStateFiniteExact.callEnv] using post.1
  obtain ⟨n, l, ls, optFrame, hstack, y, hy, hlocals, hdomain, hrest⟩ :=
    pushEnvPopEnvSKeyEq envs opt (decClock t) t1 keys
  rw [popped] at hy
  cases hy
  funext k
  have h := congrFun hdomain k
  rw [← h]
  exact propext or_comm
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
