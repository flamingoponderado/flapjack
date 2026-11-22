module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.LongDiv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.WordBignum.Proofs.StateRel

@[expose] public section

/-! The data-to-word state relation provides the division-code assumption of
the bignum compiler proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Misc.Multiword

namespace DivCodeAssumWitness
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end DivCodeAssumWitness

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private theorem longDivStubMembers {width : Nat} [NeZero width] (c : Config) :
    (longDivLocation, 4, longDivCode c) ∈ stubs (width := width) c ∧
    (longDiv1Location, 7, longDiv1Code c) ∈ stubs (width := width) c := by
  simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
      fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
      replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
      divLocation, modLocation, compare1Location, compareLocation, equal1Location,
      equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
      byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
      installLocation, installCodeLocation, installDataLocation, dummyLocation,
      appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
      unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]

private theorem seqNone {width : Nat} [NeZero width] {C F : Type}
    (s s1 : WordSemStateFiniteExact width C F) (q p : WordLangProgHOL (BitVec width))
    (h : WordSemStateFiniteExact.evaluate q s = (none, s1)) :
    WordSemStateFiniteExact.evaluate (.seq q p) s =
      WordSemStateFiniteExact.evaluate p
        { s1 with clock := if s.clock < s1.clock then s.clock else s1.clock,
                  termdep := s.termdep } := by
  rw [WordSemStateFiniteExact.evaluate]
  simp [h, WordSemStateFiniteExact.fixClock]

private theorem mustTerminateRun {width : Nat} [NeZero width] {C F : Type}
    (s s1 : WordSemStateFiniteExact width C F) (p : WordLangProgHOL (BitVec width))
    (h0 : ¬ s.termdep = 0)
    (h : WordSemStateFiniteExact.evaluate p
      { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } = (none, s1)) :
    WordSemStateFiniteExact.evaluate (.mustTerminate p) s =
      (none, { s1 with clock := s.clock, termdep := s.termdep }) := by
  rw [WordSemStateFiniteExact.evaluate, dif_neg h0, h]

/-- Related target code satisfies the division-code assumption used by the
bignum compiler proof. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "div_code_assum_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem divCodeAssum_thm {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) :
    stateRel c l1 l2 s t none locs → WordBignum.divCodeAssum (C := C) (F := F) t.code := by
  intro rel
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  have mem := longDivStubMembers (width := width) c
  have code0 : sptLookup longDivLocation t.code = some (4, longDivCode c) :=
    rel.2.2.2.2.1.2.1 _ mem.1
  have code1 : sptLookup longDiv1Location t.code = some (7, longDiv1Code c) :=
    rel.2.2.2.2.1.2.1 _ mem.2
  have loc : WordBignum.divLocation = longDivLocation := rfl
  intro t1 n l i0 i1 i2 i3 i4 w3 w4 w5 retVal
    ⟨p0, p1, p2, p3, p4, nodup, codeEq, td, g0, pre⟩
  rcases hsd : singleDiv w3 w4 w5 with ⟨d1, m1⟩
  have d23 : i2 ≠ i3 := by intro e; simp [e] at nodup
  have d24 : i2 ≠ i4 := by intro e; simp [e] at nodup
  have d34 : i3 ≠ i4 := by intro e; simp [e] at nodup
  have d01 : i0 ≠ i1 := by intro e; simp [e] at nodup
  let L := sptInsert i2 (.word w3) (sptInsert i3 (.word w4) (sptInsert i4 (.word w5) t1.locals))
  have l0 : sptLookup 0 L = some retVal := by
    simp only [L]
    rw [sptLookup_sptInsert_ne _ _ _ _ (by omega), sptLookup_sptInsert_ne _ _ _ _ (by omega),
      sptLookup_sptInsert_ne _ _ _ _ (by omega)]
    exact g0
  have lw3 : sptLookup i2 L = some (.word w3) := by simp [L, sptLookup_sptInsert_same]
  have lw4 : sptLookup i3 L = some (.word w4) := by
    simp only [L]; rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm d23)]; simp [sptLookup_sptInsert_same]
  have lw5 : sptLookup i4 L = some (.word w5) := by
    simp only [L]
    rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm d24), sptLookup_sptInsert_ne _ _ _ _ (Ne.symm d34)]
    simp [sptLookup_sptInsert_same]
  let T : WordSemStateFiniteExact width C F := { t1 with locals := L }
  let T' : WordSemStateFiniteExact width C F :=
    { T with clock := wordSemMustTerminateLimit width, termdep := T.termdep - 1 }
  let vals : List (WordLocW width) := [.loc n l, .word w3, .word w4, .word w5]
  let X := WordSemStateFiniteExact.callEnv vals (sptLookup longDivLocation T'.stackSize)
    (WordSemStateFiniteExact.pushEnv (.ls retVal, .ln) none (WordSemStateFiniteExact.decClock T'))
  have mtl : 2 ^ width + 1 < wordSemMustTerminateLimit width := by
    simp only [wordSemMustTerminateLimit]
    have h1 : 1 ≤ 2 ^ width := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ width * 2 ^ width := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  obtain ⟨ck, mx, hrun, _⟩ := evaluateLongDivCode' X n l c () w3 w4 w5 d1 m1
    ⟨pre, hsd, by simpa [X, T', T, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock, codeEq] using code1,
      by simp [X, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
      by simp [X, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
      by simp [X, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
      by simp [X, vals, WordSemStateFiniteExact.callEnv, sptFromList2, sptInsert, sptLookup],
      by simp [X, T', T, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock]; omega,
      good⟩
  refine ⟨mx, ?_⟩
  have tdT : ¬ T.termdep = 0 := td
  have hfc := congrArg (fun p => WordSemStateFiniteExact.fixClock X p) hrun
  have nonempty : ¬ sptDomainEmpty (.ls () : Spt Unit) := by
    intro e; exact e 0 (by rw [sptMem_ls])
  have cut : wordSemCutEnvs ((.ls (), .ln) : Spt Unit × Spt Unit) L = some (.ls retVal, .ln) := by
    have sub1 : LoopSemStateFiniteExact.sptSubsetLive (.ls () : Spt Unit) L := by
      intro key hk
      rw [sptMem_ls] at hk
      subst hk
      exact (sptMem_iff_lookup _ _).2 ⟨_, l0⟩
    have sub2 : LoopSemStateFiniteExact.sptSubsetLive (.ln : Spt Unit) L := by
      intro key hk; simp at hk
    have i1 : sptInter L (.ls ()) = .ls retVal := by
      cases hL : L with
      | ln => rw [hL] at l0; simp [sptLookup] at l0
      | ls y => rw [hL] at l0; simp [sptLookup] at l0; subst l0; simp [sptInter]
      | bn a b => rw [hL] at l0; simp [sptLookup] at l0
      | bs a y b => rw [hL] at l0; simp [sptLookup] at l0; subst l0; simp [sptInter]
    have i2' : sptInter L (.ln : Spt Unit) = .ln := by cases L <;> simp [sptInter]
    simp only [wordSemCutEnvs, wordSemCutNames, sub1, sub2, if_true, i1, i2']
  -- The returning call into the long-division stub.
  let R : WordSemStateFiniteExact width C F :=
    { X with clock := ck, locals := .ln, localsSize := some 0,
             store := X.store.updateEq (.temp 28, .word m1), stackMax := mx }
  let R2 : WordSemStateFiniteExact width C F :=
    { R with clock := if X.clock < R.clock then X.clock else R.clock, termdep := X.termdep }
  let P : WordSemStateFiniteExact width C F :=
    { R2 with locals := sptUnion (sptFromAList ([] : List (Nat × WordLocW width)))
                (sptFromAList [(0, retVal)]),
              stack := T'.stack, localsSize := T'.localsSize }
  have envl : wordSemEnvToList (.ln : Spt (WordLocW width)) T'.permute =
      ([], fun n => T'.permute (n + 1)) := by
    have e1 : sptToAList (.ln : Spt (WordLocW width)) = [] := by simp [sptToAList, sptFoldi]
    have e2 : Basis.Pure.MlList.sort wordSemKeyValCompare
        ([] : List (Nat × WordLocW width)) = [] := by
      simp [Basis.Pure.MlList.sort, Basis.Pure.MlList.mergesortTail,
        Basis.Pure.MlList.mergesortNTail]
    simp [wordSemEnvToList, e1, e2, wordSemListRearrange]
  have al : sptToAList (.ls retVal) = [(0, retVal)] := by simp [sptToAList, sptFoldi]
  have un : sptUnion (sptFromAList ([] : List (Nat × WordLocW width)))
      (sptFromAList [(0, retVal)]) = .ls retVal := by simp [sptFromAList, sptUnion]
  have deu : sptDomainEqUnion (.ls retVal) (.ls retVal) (.ln : Spt (WordLocW width)) := by
    intro k; simp
  have hcall : WordSemStateFiniteExact.evaluate
      (.call (some ([i0], (.ls (), .ln), .skip, n, l)) (some WordBignum.divLocation)
        [i2, i3, i4] none) T' = (none, P.setVars [i0] [.word d1]) := by
    have c0 : T'.clock ≠ 0 := Nat.ne_of_gt (Nat.lt_trans (Nat.succ_pos _) mtl)
    have gv : WordSemStateFiniteExact.getVars [i2, i3, i4] T' =
        some [.word w3, .word w4, .word w5] := by
      simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, T', T, lw3, lw4, lw5]
    have codeT : sptLookup WordBignum.divLocation T'.code = some (4, longDivCode c) := by
      simpa [T', T, codeEq, loc] using code0
    rw [WordSemStateFiniteExact.evaluate]
    simp only [gv, wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode, codeT]
    simp [nonempty, c0, T', T, cut]
    split
    case h_6 =>
      exfalso
      rename_i n1 n2 n3 n4 n5
      exact n1 _ _ _ hfc
    case h_1 x ys s2 heq =>
      have heq' : WordSemStateFiniteExact.fixClock X
          (WordSemStateFiniteExact.evaluate (longDivCode c) X) = (some (.result x ys), s2) := heq
      rw [hrun] at heq'
      simp only [WordSemStateFiniteExact.fixClock, Prod.mk.injEq] at heq'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq'
      simp [WordSemStateFiniteExact.popEnv, X, P, R2, R,
        WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, envl, al,
        WordSemStateFiniteExact.decClock, un, deu, WordSemStateFiniteExact.evaluate]
      rfl
    all_goals
      rename_i heq
      exfalso
      revert heq
      show WordSemStateFiniteExact.fixClock X
        (WordSemStateFiniteExact.evaluate (longDivCode c) X) = _ → False
      rw [hrun]; simp [WordSemStateFiniteExact.fixClock]
  have temp28 : (P.setVars [i0] [.word d1]).store.lookup (.temp 28) = some (.word m1) := by
    simp [P, R2, R, X, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  rw [WordBignum.divCode, mustTerminateRun T _ _ tdT (by
    rw [seqNone _ _ _ _ hcall, WordSemStateFiniteExact.evaluate]
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore]
    rfl)]
  simp only [Prod.mk.injEq, true_and]
  simp [P, R2, R, X, T', T, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
    WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.callEnv,
    WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock,
    LoopSemStateFiniteExact.sptAlistInsert]
  constructor
  · rw [un, ← sptInsert_ln_zero, sptInsert_swap i0 0 _ _ _ (by omega),
      sptInsert_swap i1 0 _ _ _ (by omega)]
  · exact congrArg Prod.snd envl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
