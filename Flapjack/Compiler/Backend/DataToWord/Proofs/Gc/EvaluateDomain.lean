module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.EvaluateMkLoc
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.DomainFromAList
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
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
/-- An exception from a pushed handler restores exactly the saved domains. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "evaluate_IMP_domain_EQ_Exc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_imp_domainEq_exception {width : Nat} [NeZero width] {C F : Type}
    (c : WordLangProgHOL (BitVec width)) (args : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (x0 x1 l : Nat)
    (prog1 : WordLangProgHOL (BitVec width)) (t t1 : WordSemStateFiniteExact width C F)
    (xx w : WordLocW width)
    (run : evaluate c (WordSemStateFiniteExact.callEnv args ss (pushEnv envs (some (x0,prog1,x1,l)) (decClock t))) =
      (some (.exception xx w), t1)) :
    sptDomain t1.locals = fun k => sptDomain envs.1 k ∨ sptDomain envs.2 k := by
  have post := evaluateStackSwap c (WordSemStateFiniteExact.callEnv args ss (pushEnv envs (some (x0,prog1,x1,l)) (decClock t)))
  simp only [stackSwapPost, run] at post
  cases envList : wordSemEnvToList envs.2 t.permute with
  | mk entries perm =>
    simp only [WordSemStateFiniteExact.callEnv, pushEnv, decClock, envList] at post
    obtain ⟨_, e0, e, n, ls, m, lss, head, mEq, envEq, keys, handlerEq, transport⟩ := post
    have suffix : wordSemLastN (t.stack.length + 1)
        (.stackFrame t.localsSize (sptToAList envs.1) entries (some (t.handler, x1, l)) :: t.stack) =
        .stackFrame t.localsSize (sptToAList envs.1) entries (some (t.handler, x1, l)) :: t.stack := by
      apply lastNLengthCond
      simp
    rw [suffix] at head
    have frameEq := (List.cons.inj head).1
    have nonGcEq : sptToAList envs.1 = e0 :=
      congrArg (fun frame => match frame with | .stackFrame _ e0 _ _ => e0) frameEq
    have gcEq : entries = e :=
      congrArg (fun frame => match frame with | .stackFrame _ _ e _ => e) frameEq
    obtain ⟨keyEq, localEq⟩ := envEq
    rw [← gcEq] at keyEq
    rw [localEq, ← nonGcEq, sptDomain_sptUnion, sptDomainFromAListToAList]
    funext k
    apply propext
    have treeEq : sptDomain (sptFromAList entries) k ↔ sptDomain envs.2 k := by
      unfold sptDomain
      rw [sptLookup_sptFromAList, (wordSemEnvToListLookupEquiv envs.2 t.permute entries perm envList).1]
    have listsEq : sptDomain (sptFromAList lss) k ↔ sptDomain (sptFromAList entries) k := by
      rw [sptDomainFromAList, sptDomainFromAList, keyEq]
    exact (or_congr (listsEq.trans treeEq) Iff.rfl).trans or_comm

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
