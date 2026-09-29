import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

/-!
# HOL `wordSem` rebound `evaluate_ind`

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:1367-1368`
(bead `flapjack-h29l.9.2`): HOL rebinds `evaluate_ind` as
`REWRITE_RULE [fix_clock_evaluate] evaluate_ind`, the induction principle for
`evaluate` in which the `Seq`, `Loop` and returning-`Call` hypotheses mention
`evaluate` directly instead of through `fix_clock`.  The Lean statement
transcribes that theorem, with HOL's `P (p, s)` curried to `P p s`, HOL
`bool` guards as `= true`, and the `domain` set conditions as
`sptDomainEmpty`/`sptDomainEqUnion`.  It is proved by recursion on HOL's
termination measure, using `evaluate_clock` for the intermediate states.
Lean's generated `evaluate.induct` is not usable for this definition (it
fails the kernel check).
-/

namespace Flapjack

namespace WordSemEvaluateIndSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateIndSupport

namespace WordSemStateFiniteExact

section Ind

variable {width : Nat} [NeZero width] {C : Type} {F : Type}
  (P : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Prop)
  (hSkip : ∀ s, P .skip s)
  (hAlloc : ∀ n names s, P (.alloc n names) s)
  (hStoreConsts : ∀ t1 t2 addr offset words s, P (.storeConsts t1 t2 addr offset words) s)
  (hMove : ∀ pri moves s, P (.move pri moves) s)
  (hInst : ∀ i s, P (.inst i) s)
  (hAssign : ∀ v exp s, P (.assign v exp) s)
  (hGet : ∀ v name s, P (.get v name) s)
  (hSet : ∀ v exp s, P (.set v exp) s)
  (hOpCurrHeap : ∀ b dst src s, P (.opCurrHeap b dst src) s)
  (hStore : ∀ exp v s, P (.store exp v) s)
  (hTick : ∀ s, P .tick s)
  (hMustTerminate : ∀ p s,
    (s.termdep ≠ 0 →
      P p { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }) →
    P (.mustTerminate p) s)
  (hSeq : ∀ c1 c2 s,
    (∀ res s1, (res, s1) = evaluate c1 s ∧ res = none → P c2 s1) ∧ P c1 s → P (.seq c1 c2) s)
  (hReturn : ∀ n ms s, P (.return n ms) s)
  (hRaise : ∀ n s, P (.raise n) s)
  (hBreak : ∀ k s, P (.break k) s)
  (hContinue : ∀ k s, P (.continue k) s)
  (hIf : ∀ cmp r1 ri c1 c2 s,
    (∀ v3 v4 x y v, (getVar r1 s, getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ v = true → P c1 s) ∧
    (∀ v3 v4 x y v, (getVar r1 s, getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ ¬ v = true → P c2 s) →
    P (.ite cmp r1 ri c1 c2) s)
  (hLoop : ∀ names c exitNames s,
    (∀ v res s1, cutState (names, .ln) s = some v ∧ (res, s1) = evaluate c v ∧
        wordSemContLoop res = true ∧ s1.clock ≠ 0 →
      P (wordSemSTOP (.loop names c exitNames)) (decClock s1)) ∧
    (∀ v, cutState (names, .ln) s = some v → P c v) →
    P (.loop names c exitNames) s)
  (hLocValue : ∀ r l1 s, P (.locValue r l1) s)
  (hInstall : ∀ ptr len dptr dlen names s, P (.install ptr len dptr dlen names) s)
  (hCodeBufferWrite : ∀ r1 r2 s, P (.codeBufferWrite r1 r2) s)
  (hDataBufferWrite : ∀ r1 r2 s, P (.dataBufferWrite r1 r2) s)
  (hFfi : ∀ ffiIndex ptr1 len1 ptr2 len2 names s, P (.ffi ffiIndex ptr1 len1 ptr2 len2 names) s)
  (hShareInst : ∀ op v exp s, P (.shareInst op v exp) s)
  (hCall : ∀ ret dest args handler s,
    (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x ys s1,
        getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
        evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length) ∧
        popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
      P retHandler (setVars n ys s1)) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x' y v n' v2 h
        v4 l1' l2',
        getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
        evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (l1', l2') ∧ x' = .loc l1' l2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
      P h (setVar n' y s2)) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs,
        getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 →
      P prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) ∧
    (∀ xs v3 args1 v10 prog ss,
        getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = none ∧ handler = none ∧ s.clock ≠ 0 →
      P prog (callEnv args1 ss (decClock s))) →
    P (.call ret dest args handler) s)

include hSkip hAlloc hStoreConsts hMove hInst hAssign hGet hSet hOpCurrHeap hStore hTick
  hMustTerminate hSeq hReturn hRaise hBreak hContinue hIf hLoop hLocValue hInstall
  hCodeBufferWrite hDataBufferWrite hFfi hShareInst hCall in
/-- The rebound induction principle, by recursion on HOL's measure. -/
theorem evaluate_ind_aux (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) : P p s := by
  cases p with
  | skip => exact hSkip s
  | alloc n names => exact hAlloc n names s
  | storeConsts t1 t2 addr offset words => exact hStoreConsts t1 t2 addr offset words s
  | move pri moves => exact hMove pri moves s
  | inst i => exact hInst i s
  | assign v exp => exact hAssign v exp s
  | get v name => exact hGet v name s
  | set v exp => exact hSet v exp s
  | opCurrHeap b dst src => exact hOpCurrHeap b dst src s
  | store exp v => exact hStore exp v s
  | tick => exact hTick s
  | mustTerminate p =>
      exact hMustTerminate p s (fun hne => evaluate_ind_aux p _)
  | seq c1 c2 =>
      exact hSeq c1 c2 s ⟨fun res s1 hh =>
        have hc := evaluate_clock c1 s res s1 hh.1.symm
        evaluate_ind_aux c2 s1, evaluate_ind_aux c1 s⟩
  | «return» n ms => exact hReturn n ms s
  | raise n => exact hRaise n s
  | «break» k => exact hBreak k s
  | «continue» k => exact hContinue k s
  | ite cmp r1 ri c1 c2 =>
      exact hIf cmp r1 ri c1 c2 s ⟨fun _ _ _ _ _ _ => evaluate_ind_aux c1 s,
        fun _ _ _ _ _ _ => evaluate_ind_aux c2 s⟩
  | loop names c exitNames =>
      exact hLoop names c exitNames s
        ⟨fun v res s1 hh =>
            have hc := cutState_clock_termdep _ _ _ hh.1
            have he := evaluate_clock c v res s1 hh.2.1.symm
            have hz := hh.2.2.2
            evaluate_ind_aux (wordSemSTOP (.loop names c exitNames)) (decClock s1),
          fun v hv =>
            have hc := cutState_clock_termdep _ _ _ hv
            evaluate_ind_aux c v⟩
  | locValue r l1 => exact hLocValue r l1 s
  | install ptr len dptr dlen names => exact hInstall ptr len dptr dlen names s
  | codeBufferWrite r1 r2 => exact hCodeBufferWrite r1 r2 s
  | dataBufferWrite r1 r2 => exact hDataBufferWrite r1 r2 s
  | ffi ffiIndex ptr1 len1 ptr2 len2 names => exact hFfi ffiIndex ptr1 len1 ptr2 len2 names s
  | shareInst op v exp => exact hShareInst op v exp s
  | call ret dest args handler =>
      exact hCall ret dest args handler s
        ⟨fun _ _ args1 _ prog ss _ n _ _ _ retHandler _ _ _ envs v5 s2 _ _ ys s1 hh =>
            match hh with
            | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hclk, hev, _, _, _, hpop, _⟩ =>
              have hc := evaluate_clock prog _ v5 s2 hev
              have hpc := popEnv_clock _ _ hpop
              have hpt := popEnv_termdep _ _ hpop
              evaluate_ind_aux retHandler (setVars n ys s1),
          fun _ _ args1 _ prog ss _ _ _ _ _ _ _ _ _ envs v5 s2 _ _ y _ n' _ h _ _ _ hh =>
            match hh with
            | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hclk, hev, _⟩ =>
              have hc := evaluate_clock prog _ v5 s2 hev
              evaluate_ind_aux h (setVar n' y s2),
          fun _ _ args1 _ prog ss _ _ _ _ _ _ _ _ _ envs hh =>
            match hh with
            | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hclk⟩ =>
              evaluate_ind_aux prog (callEnv args1 ss (pushEnv envs handler (decClock s))),
          fun _ _ args1 _ prog ss hh =>
            match hh with
            | ⟨_, _, _, _, _, _, _, hclk⟩ =>
              evaluate_ind_aux prog (callEnv args1 ss (decClock s))⟩
termination_by (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try simp only [callEnv, decClock, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      wordSemSTOP, true_and] at *
    omega

end Ind

/-- Exact HOL rebound `evaluate_ind` (`wordSemScript.sml:1367-1368`,
    `REWRITE_RULE [fix_clock_evaluate] evaluate_ind`): the 26 clause
    hypotheses of HOL's statement, in HOL order, imply `P` for every program
    and state. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "evaluate_ind" 1367
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_ind {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (P : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Prop),
      ((∀ s, P .skip s) ∧
      (∀ n names s, P (.alloc n names) s) ∧
      (∀ t1 t2 addr offset words s, P (.storeConsts t1 t2 addr offset words) s) ∧
      (∀ pri moves s, P (.move pri moves) s) ∧
      (∀ i s, P (.inst i) s) ∧
      (∀ v exp s, P (.assign v exp) s) ∧
      (∀ v name s, P (.get v name) s) ∧
      (∀ v exp s, P (.set v exp) s) ∧
      (∀ b dst src s, P (.opCurrHeap b dst src) s) ∧
      (∀ exp v s, P (.store exp v) s) ∧
      (∀ s, P .tick s) ∧
      (∀ p s,
        (s.termdep ≠ 0 →
        P p { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }) →
        P (.mustTerminate p) s) ∧
      (∀ c1 c2 s,
        (∀ res s1, (res, s1) = evaluate c1 s ∧ res = none → P c2 s1) ∧ P c1 s → P (.seq c1 c2) s) ∧
      (∀ n ms s, P (.return n ms) s) ∧
      (∀ n s, P (.raise n) s) ∧
      (∀ k s, P (.break k) s) ∧
      (∀ k s, P (.continue k) s) ∧
      (∀ cmp r1 ri c1 c2 s,
        (∀ v3 v4 x y v, (getVar r1 s, getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ v = true → P c1 s) ∧
        (∀ v3 v4 x y v, (getVar r1 s, getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ ¬ v = true → P c2 s) →
        P (.ite cmp r1 ri c1 c2) s) ∧
      (∀ names c exitNames s,
        (∀ v res s1, cutState (names, .ln) s = some v ∧ (res, s1) = evaluate c v ∧
        wordSemContLoop res = true ∧ s1.clock ≠ 0 →
        P (wordSemSTOP (.loop names c exitNames)) (decClock s1)) ∧
        (∀ v, cutState (names, .ln) s = some v → P c v) →
        P (.loop names c exitNames) s) ∧
      (∀ r l1 s, P (.locValue r l1) s) ∧
      (∀ ptr len dptr dlen names s, P (.install ptr len dptr dlen names) s) ∧
      (∀ r1 r2 s, P (.codeBufferWrite r1 r2) s) ∧
      (∀ r1 r2 s, P (.dataBufferWrite r1 r2) s) ∧
      (∀ ffiIndex ptr1 len1 ptr2 len2 names s, P (.ffi ffiIndex ptr1 len1 ptr2 len2 names) s) ∧
      (∀ op v exp s, P (.shareInst op v exp) s) ∧
      (∀ ret dest args handler s,
        (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x ys s1,
        getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
        evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length) ∧
        popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
        P retHandler (setVars n ys s1)) ∧
        (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x' y v n' v2
        h v4 l1' l2',
        getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
        evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (l1', l2') ∧ x' = .loc l1' l2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
        P h (setVar n' y s2)) ∧
        (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs,
        getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 →
        P prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) ∧
        (∀ xs v3 args1 v10 prog ss,
        getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = none ∧ handler = none ∧ s.clock ≠ 0 →
        P prog (callEnv args1 ss (decClock s))) →
        P (.call ret dest args handler) s)) →
      ∀ v v1, P v v1 := by
  intro P ⟨hSkip, hAlloc, hStoreConsts, hMove, hInst, hAssign, hGet, hSet, hOpCurrHeap, hStore,
      hTick, hMustTerminate, hSeq, hReturn, hRaise, hBreak, hContinue, hIf, hLoop, hLocValue,
      hInstall, hCodeBufferWrite, hDataBufferWrite, hFfi, hShareInst, hCall⟩ v v1
  exact evaluate_ind_aux P hSkip hAlloc hStoreConsts hMove hInst hAssign hGet hSet hOpCurrHeap
      hStore hTick hMustTerminate hSeq hReturn hRaise hBreak hContinue hIf hLoop hLocValue
      hInstall hCodeBufferWrite hDataBufferWrite hFfi hShareInst hCall v v1

end WordSemStateFiniteExact

end Flapjack
