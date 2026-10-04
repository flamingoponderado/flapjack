import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

/-!
# HOL `wordSem` rebound `evaluate_ind` and `evaluate_def`

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:1367-1370`
(bead `flapjack-h29l.9.2`).  HOL rebinds `evaluate_def` as
`REWRITE_RULE [fix_clock_evaluate] evaluate_def`: the defining equations with
`fix_clock` removed (`evaluate_def_rebound`, proved clause by clause from the
equation lemmas of `evaluate` and `fix_clock_evaluate`).  It likewise rebinds
`evaluate_ind` as `REWRITE_RULE [fix_clock_evaluate] evaluate_ind`, the induction principle for
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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

open Classical in
/-- Rendering of HOL rebound `evaluate_def` (`wordSemScript.sml:1369-1370`,
    `REWRITE_RULE [fix_clock_evaluate] evaluate_def`): the `evaluate`
    equations with `fix_clock` removed from the `Seq`, `Loop` and returning
    `Call` clauses.  There is one conjunct per clause, in HOL order, with
    HOL's binder order.

    Exact port with an inherited assumption (PR #1179 review, bead
    `flapjack-qfld`): the `Inst` conjunct calls the tagged `inst`, which carries
    `(reals_as_rational_cuts)` for its `FPSqrt` rendering; this declaration
    does not use a real rendering itself and records the inherited
    `docs/SOUNDNESS.md` item 8 assumption in the theorem map.  Every other
    conjunct follows HOL clause by clause. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_def_rebound {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (s : WordSemStateFiniteExact width C F), evaluate (.skip) s =
      (
          (none, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) names n, evaluate (.alloc n names) s =
      (
          match getVar n s with
          | some (.word w) => alloc w names s
          | _ => (some .error, s))) ∧
    (∀ words t2 t1 (s : WordSemStateFiniteExact width C F) offset addr, evaluate (.storeConsts t1 t2 addr offset words) s =
      (
          match getVar addr s, getVar offset s with
          | some (.word a), some (.word off) =>
              if ¬ wordSemConstAddresses a words s.mdomain = true then (some .error, s)
              else
                let s := { s with memory := wordSemConstWrites a off words s.memory }
                let s := setVar offset (.word off) (unsetVar t1 (unsetVar t2 s))
                (none, setVar addr (.word (a + wordSemBytesInWord * BitVec.ofNat width words.length)) s)
          | _, _ => (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) pri moves, evaluate (.move pri moves) s =
      (
          if (moves.map Prod.fst).Nodup then
            match getVars (moves.map Prod.snd) s with
            | none => (some .error, s)
            | some vs => (none, setVars (moves.map Prod.fst) vs s)
          else (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) i, evaluate (.inst i) s =
      (
          match inst i s with
          | some s1 => (none, s1)
          | none => (some .error, s))) ∧
    (∀ v (s : WordSemStateFiniteExact width C F) exp, evaluate (.assign v exp) s =
      (
          match wordExp s exp with
          | none => (some .error, s)
          | some w => (none, setVar v w s))) ∧
    (∀ v (s : WordSemStateFiniteExact width C F) name, evaluate (.get v name) s =
      (
          match getStore name s with
          | none => (some .error, s)
          | some x => (none, setVar v x s))) ∧
    (∀ v (s : WordSemStateFiniteExact width C F) exp, evaluate (.set v exp) s =
      (
          if v = .handler ∨ v = .bitmapBase then (some .error, s)
          else
            match wordExp s exp with
            | none => (some .error, s)
            | some w => (none, setStore v w s))) ∧
    (∀ src (s : WordSemStateFiniteExact width C F) dst b, evaluate (.opCurrHeap b dst src) s =
      (
          match wordExp s (.op b [.var src, .lookup .currHeap]) with
          | none => (some .error, s)
          | some w => (none, setVar dst w s))) ∧
    (∀ v (s : WordSemStateFiniteExact width C F) exp, evaluate (.store exp v) s =
      (
          match wordExp s exp, getVar v s with
          | some (.word a), some w =>
              match memStore a w s with
              | some s1 => (none, s1)
              | none => (some .error, s)
          | _, _ => (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F), evaluate (.tick) s =
      (
          if s.clock = 0 then (some .timeOut, flushState true s) else (none, decClock s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) p, evaluate (.mustTerminate p) s =
      (
          if s.termdep = 0 then (some .error, s)
          else
            match evaluate p { s with clock := wordSemMustTerminateLimit width,
                                      termdep := s.termdep - 1 } with
            | (res, s1) =>
                match res with
                | some .timeOut => (some .error, s)
                | _ => (res, { s1 with clock := s.clock, termdep := s.termdep }))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) c2 c1, evaluate (.seq c1 c2) s =
      (
          match evaluate c1 s with
          | (res, s1) =>
              match res with
              | none => evaluate c2 s1
              | _ => (res, s1))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) n ms, evaluate (WordLangProgHOL.return n ms) s =
      (
          match getVar n s, getVars ms s with
          | some (.loc l1 l2), some ys => (some (.result (.loc l1 l2) ys), flushState false s)
          | _, _ => (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) n, evaluate (.raise n) s =
      (
          match getVar n s with
          | none => (some .error, s)
          | some w =>
              match jumpExc s with
              | none => (some .error, s)
              | some (s, l1, l2) => (some (.exception (.loc l1 l2) w), s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) k, evaluate (WordLangProgHOL.break k) s =
      (
          (some (.break k), s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) k, evaluate (WordLangProgHOL.continue k) s =
      (
          (some (.continue k), s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) ri r1 cmp c2 c1, evaluate (.ite cmp r1 ri c1 c2) s =
      (
          match getVar r1 s, getVarImm ri s with
          | some x, some y =>
              match wordSemWordCmp cmp x y with
              | some true => evaluate c1 s
              | some false => evaluate c2 s
              | none => (some .error, s)
          | _, _ => (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) names exitNames c, evaluate (.loop names c exitNames) s =
      (
          match cutState (names, .ln) s with
          | none => (some .error, s)
          | some s' =>
              match evaluate c s' with
              | (res, s1) =>
                  if wordSemContLoop res then
                    (if s1.clock = 0 then (some .timeOut, flushState true s1)
                     else evaluate (wordSemSTOP (.loop names c exitNames)) (decClock s1))
                  else
                    match res with
                    | some (.break 0) =>
                        match cutState (exitNames, .ln) s1 with
                        | none => (some .error, s1)
                        | some s2 => (none, s2)
                    | _ => (wordSemExitLoop res, s1))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) r l1, evaluate (.locValue r l1) s =
      (
          if sptMem l1 s.code then (none, setVar r (.loc l1 0) s) else (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) ptr names len dptr dlen, evaluate (.install ptr len dptr dlen names) s =
      (
          match wordSemCutEnv names s.locals with
          | none => (some .error, s)
          | some env =>
              match getVar ptr s, getVar len s, getVar dptr s, getVar dlen s with
              | some (.word w1), some (.word w2), some (.word w3), some (.word w4) =>
                  let (cfg, progs) := s.compileOracle 0
                  match wordSemBufferFlush s.codeBuffer w1 w2, wordSemBufferFlush s.dataBuffer w3 w4 with
                  | some (bytes, cb), some (data, db) =>
                      let newOracle := holShiftSeq 1 s.compileOracle
                      match s.compile cfg progs, progs with
                      | some (bytes', data', cfg'), (k, _) :: _ =>
                          if bytes = bytes' ∧ data = data' ∧ (newOracle 0).1 = cfg' then
                            (none, { s with
                              codeBuffer := cb
                              dataBuffer := db
                              code := sptUnion s.code (sptFromAList progs)
                              locals := sptInsert ptr (.loc k 0) env
                              fpRegs := HolFiniteMapExact.empty
                              compileOracle := newOracle
                              stackMax := none
                              stackSize := .ln })
                          else (some .error, s)
                      | _, _ => (some .error, s)
                  | _, _ => (some .error, s)
              | _, _, _, _ => (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) r2 r1, evaluate (.codeBufferWrite r1 r2) s =
      (
          match getVar r1 s, getVar r2 s with
          | some (.word w1), some (.word w2) =>
              match wordSemBufferWrite s.codeBuffer w1 (w2.setWidth 8) with
              | some newCb => (none, { s with codeBuffer := newCb })
              | none => (some .error, s)
          | _, _ => (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) r2 r1, evaluate (.dataBufferWrite r1 r2) s =
      (
          match getVar r1 s, getVar r2 s with
          | some (.word w1), some (.word w2) =>
              match wordSemBufferWrite s.dataBuffer w1 w2 with
              | some newDb => (none, { s with dataBuffer := newDb })
              | none => (some .error, s)
          | _, _ => (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) ptr2 ptr1 names len2 len1 ffiIndex, evaluate (.ffi ffiIndex ptr1 len1 ptr2 len2 names) s =
      (
          match getVar len1 s, getVar ptr1 s, getVar len2 s, getVar ptr2 s with
          | some (.word w), some (.word w2), some (.word w3), some (.word w4) =>
              match wordSemCutEnv names s.locals with
              | none => (some .error, s)
              | some env =>
                  match readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact s.memory s.mdomain s.be),
                      readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
                  | some bytes, some bytes2 =>
                      match callFFIHOL s.ffi (.extCall ffiIndex) bytes bytes2 with
                      | .final outcome => (some (.finalFfi outcome), flushState true s)
                      | .ret newFfi newBytes =>
                          let newM := writeBytearrayExact w4 newBytes s.memory s.mdomain s.be
                          (none, { s with memory := newM, locals := env,
                                          fpRegs := HolFiniteMapExact.empty, ffi := newFfi })
                  | _, _ => (some .error, s)
          | _, _, _, _ => (some .error, s))) ∧
    (∀ v (s : WordSemStateFiniteExact width C F) op exp, evaluate (.shareInst op v exp) s =
      (
          match wordExp s exp with
          | some (.word ad) => shareInst op v ad s
          | _ => (some .error, s))) ∧
    (∀ (s : WordSemStateFiniteExact width C F) ret handler dest args, evaluate (.call ret dest args handler) s =
      (
          match getVars args s with
          | none => (some .error, s)
          | some xs =>
              if wordSemBadDestArgs dest args then (some .error, s)
              else
                match wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
                | none => (some .error, s)
                | some (args1, prog, ss) =>
                    match ret with
                    | none =>
                        match handler with
                        | none =>
                            if s.clock = 0 then (some .timeOut, flushState true s)
                            else
                              match evaluate prog (callEnv args1 ss (decClock s)) with
                              | (res, s) =>
                                  if wordSemBadFunReturn res then (some .error, s) else (res, s)
                        | some _ => (some .error, s)
                    | some (n, names, retHandler, l1, l2) =>
                        if sptDomainEmpty names.1 ∨ ¬ n.Nodup then (some .error, s)
                        else
                          match wordSemCutEnvs names s.locals with
                          | none => (some .error, s)
                          | some envs =>
                              if s.clock = 0 then
                                (some .timeOut, flushState true
                                  { s with stack := [],
                                           stackMax := (callEnv args1 ss (pushEnv envs handler s)).stackMax })
                              else
                                match evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
                                | (some (.result x ys), s2) =>
                                    if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
                                    else
                                      match popEnv s2 with
                                      | none => (some .error, s2)
                                      | some s1 =>
                                          if sptDomainEqUnion s1.locals envs.1 envs.2 then
                                            evaluate retHandler (setVars n ys s1)
                                          else (some .error, s1)
                                | (some (.exception x y), s2) =>
                                    match handler with
                                    | none => (some (.exception x y), s2)
                                    | some (n, hprog, l1, l2) =>
                                        if x ≠ .loc l1 l2 then (some .error, s2)
                                        else if sptDomainEqUnion s2.locals envs.1 envs.2 then
                                          evaluate hprog (setVar n y s2)
                                        else (some .error, s2)
                                | (none, s) => (some .error, s)
                                | (some (.break _), s) => (some .error, s)
                                | (some (.continue _), s) => (some .error, s)
                                | res => res)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros
  all_goals first
    | (rw [evaluate]; done)
    | (rw [evaluate]; rfl)
    | (rw [evaluate, fix_clock_evaluate]; rfl)
    | (rw [evaluate]; simp only [fix_clock_evaluate, dite_eq_ite]
       split <;> (rename_i heq; simp only [heq]) <;> rfl)
    | (rw [evaluate]; simp only [dite_eq_ite]
       repeat' (first
         | (rw [fix_clock_evaluate])
         | (split <;> (try (rename_i heq; simp only [heq]))))
       all_goals (first | contradiction | simp_all))

end WordSemStateFiniteExact

end Flapjack
