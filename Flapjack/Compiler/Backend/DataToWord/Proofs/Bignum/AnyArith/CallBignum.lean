module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Setup

@[expose] public section

/-! `AnyArith_thm`: the call of the generated bignum code (Flapjack-only helper
following the HOL proof's `push_env`/`pop_env` steps). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.WordSemStateFiniteExact.BignumClauses

/-- The callee's initial state for the bignum call of `AnyArith_code`. -/
def bignumCallState {width : Nat} [NeZero width] {C F : Type} (t9 : WordSemStateFiniteExact width C F)
    (ret : WordLocW width) : WordSemStateFiniteExact width C F :=
  WordSemStateFiniteExact.callEnv [.loc anyArithLocation 3] (sptLookup bignumLocation t9.stackSize)
    (WordSemStateFiniteExact.pushEnv (.ls ret, .ln) none (WordSemStateFiniteExact.decClock t9))

/-- The caller's state after the bignum call returns. -/
def afterCallState {width : Nat} [NeZero width] {C F : Type} (t9 F2 : WordSemStateFiniteExact width C F)
    (ret : WordLocW width) : WordSemStateFiniteExact width C F :=
  { F2 with locals := sptInsert 1 (.loc anyArithLocation 3) (.ls ret), stack := t9.stack,
            localsSize := t9.localsSize,
            clock := if t9.clock - 1 < F2.clock then t9.clock - 1 else F2.clock,
            termdep := t9.termdep }

theorem envToList_ln {width : Nat} [NeZero width] (p : Nat → Nat → Nat) :
    wordSemEnvToList (.ln : Spt (WordLocW width)) p = ([], fun n => p (n + 1)) := by
  have e1 : sptToAList (.ln : Spt (WordLocW width)) = [] := by simp [sptToAList, sptFoldi]
  have e2 : Basis.Pure.MlList.sort wordSemKeyValCompare
      ([] : List (Nat × WordLocW width)) = [] := by
    simp [Basis.Pure.MlList.sort, Basis.Pure.MlList.mergesortTail,
      Basis.Pure.MlList.mergesortNTail]
  simp [wordSemEnvToList, e1, e2, wordSemListRearrange]

/-- The bignum call returns to the caller with the saved local restored. -/
theorem call_bignum {width : Nat} [NeZero width] {C F : Type}
    {t9 F2 : WordSemStateFiniteExact width C F} {ret : WordLocW width}
    {P : WordLangProgHOL (BitVec width)}
    (hloc : t9.locals = sptInsert 0 ret .ln)
    (hcode : sptLookup bignumLocation t9.code = some (1, P)) (c0 : t9.clock ≠ 0)
    (hrun : WordSemStateFiniteExact.evaluate P (bignumCallState t9 ret) =
      (some (.result (.loc anyArithLocation 3) [.loc anyArithLocation 3]), F2))
    (hstack : F2.stack = (bignumCallState t9 ret).stack)
    (rest : WordLangProgHOL (BitVec width)) :
    WordSemStateFiniteExact.evaluate
        (.seq (.call (some ([1], (.ls (), .ln), .skip, anyArithLocation, 3)) (some bignumLocation)
          [] none) rest) t9 =
      WordSemStateFiniteExact.evaluate rest (afterCallState t9 F2 ret) := by
  have l0 : sptLookup 0 t9.locals = some ret := by
    rw [hloc]; exact sptLookup_sptInsert_same 0 ret .ln
  have cut : wordSemCutEnvs ((.ls () : Spt Unit), (.ln : Spt Unit)) t9.locals = some (.ls ret, .ln) := by
    have sub1 : LoopSemStateFiniteExact.sptSubsetLive (.ls () : Spt Unit) t9.locals := by
      intro key hk
      rw [sptMem_ls] at hk
      subst hk
      exact (sptMem_iff_lookup _ _).2 ⟨_, l0⟩
    have sub2 : LoopSemStateFiniteExact.sptSubsetLive (.ln : Spt Unit) t9.locals := by
      intro key hk; simp at hk
    have inter : sptInter t9.locals (.ls () : Spt Unit) = .ls ret := by
      rw [hloc]; simp [sptInter]
    simp only [wordSemCutEnvs, wordSemCutNames, sub1, sub2, if_true, inter]
    cases t9.locals <;> simp [sptInter]
  have nonempty : ¬ sptDomainEmpty (.ls () : Spt Unit) := by
    intro e; exact e 0 (by rw [sptMem_ls])
  have al : sptToAList (.ls ret) = [(0, ret)] := by simp [sptToAList, sptFoldi]
  have un : sptUnion (sptFromAList ([] : List (Nat × WordLocW width)))
      (sptFromAList [(0, ret)]) = .ls ret := by
    simp [sptFromAList, sptUnion]
  have deu : sptDomainEqUnion (.ls ret) (.ls ret) (.ln : Spt (WordLocW width)) := by
    intro k; simp
  have ev : WordSemStateFiniteExact.evaluate
      (.call (some ([1], ((.ls () : Spt Unit), (.ln : Spt Unit)), .skip, anyArithLocation, 3))
        (some bignumLocation) [] none) t9 = (none, afterCallState t9 F2 ret) := by
    rw [WordSemStateFiniteExact.evaluate]
    simp [WordSemStateFiniteExact.getVars, wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode,
      hcode, cut, c0, nonempty]
    unfold bignumCallState at hrun hstack
    have hfc := congrArg (fun p => WordSemStateFiniteExact.fixClock (WordSemStateFiniteExact.callEnv
      [.loc anyArithLocation 3] (sptLookup bignumLocation t9.stackSize)
      (WordSemStateFiniteExact.pushEnv (.ls ret, .ln) none (WordSemStateFiniteExact.decClock t9))) p) hrun
    split
    case h_6 =>
      exfalso
      rename_i n1 n2 n3 n4 n5
      exact n1 _ _ _ hfc
    all_goals rename_i heq
    all_goals rw [hrun] at heq
    all_goals simp only [WordSemStateFiniteExact.fixClock, Prod.mk.injEq] at heq
    case h_1 x ys s2 =>
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
      have hst : F2.stack = WordSemStackFrame.stackFrame t9.localsSize [(0, ret)] [] none :: t9.stack := by
        simpa [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, envToList_ln, al,
          WordSemStateFiniteExact.decClock] using hstack
      simp only [not_true_eq_false, List.length_singleton, false_or, if_false]
      split
      · rename_i hp
        simp [WordSemStateFiniteExact.popEnv, hst] at hp
      rename_i s1 hp
      simp [WordSemStateFiniteExact.popEnv, hst] at hp
      subst hp
      simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, envToList_ln, al,
        WordSemStateFiniteExact.decClock, un, deu, WordSemStateFiniteExact.setVars,
        LoopSemStateFiniteExact.sptAlistInsert, WordSemStateFiniteExact.evaluate, afterCallState]
    all_goals simp at heq
  rw [evaluate_seq_of_none _ _ _ _ ev]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
