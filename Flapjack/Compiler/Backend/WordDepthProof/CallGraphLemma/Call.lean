import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.CallRet

/-!
# `max_depth_call_graph_lemma`: `Call` case

The genuine `evaluate_ind` case for `Call`, from its four induction hypotheses
(returning continuation, exception handler, callee, tail callee), dispatched to
the tail-call and returning-call parts.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

namespace CallGraphLemmaCallWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallGraphLemmaCallWitnesses

open CallGraphLemmaCallWitnesses

/-- `max_depth_call_graph_lemma`, `Call` case. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_call_graph_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem maxDepthCallGraphLemma_Call {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (ih : (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x ys s1,
        WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
        evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) =
          (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length) ∧
        popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
        depthPost retHandler (WordSemStateFiniteExact.setVars n ys s1)) ∧
      (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x' y v n' v2
        h v4 l1' l2',
        WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
        evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) =
          (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (l1', l2') ∧ x' = .loc l1' l2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
        depthPost h (WordSemStateFiniteExact.setVar n' y s2)) ∧
      (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs,
        WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 →
        depthPost prog
          (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))) ∧
      (∀ xs v3 args1 v10 prog ss,
        WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = none ∧ handler = none ∧ s.clock ≠ 0 →
        depthPost prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)))) :
    depthPost (.call ret dest args handler) s := by
  obtain ⟨hreturn, hexception, hcallee, htail⟩ := ih
  cases ret with
  | none => exact depthPost_call_tail dest args handler s htail
  | some r =>
      obtain ⟨rn, names, retH, l1, l2⟩ := r
      cases handler with
      | none => exact depthPost_call_ret_none rn names retH l1 l2 dest args s hreturn hcallee
      | some h =>
          obtain ⟨hn, hprog, hl1, hl2⟩ := h
          exact depthPost_call_ret_some rn names retH l1 l2 dest args hn hprog hl1 hl2 s
            hreturn hexception hcallee

end Flapjack.Compiler.Backend.WordDepthProof
