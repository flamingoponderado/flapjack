module

public import Flapjack.Compiler.Backend.DataToWord.Stubs
public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.FromList
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! Correctness of the `FromList` runtime stubs (`FromList1_code_thm`,
`FromList_thm`) and of `assign` for `FromList`. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace FromListWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end FromListWitness

private theorem flSeqAssign {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : Nat) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign k e) p) t =
      WordSemStateFiniteExact.evaluate p (t.setVar k v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

private theorem flSeqStore {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (e : WordLangExpHOL (BitVec width)) (v : Nat)
    (a : BitVec width) (w : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some (.word a)) (hv : WordSemStateFiniteExact.getVar v t = some w)
    (dom : t.mdomain a = true) :
    WordSemStateFiniteExact.evaluate (.seq (.store e v) p) t =
      WordSemStateFiniteExact.evaluate p
        { t with memory := fun x => if x = a then w else t.memory x } := by
  simp [WordSemStateFiniteExact.evaluate, read, hv, WordSemStateFiniteExact.memStore, dom,
    WordSemStateFiniteExact.fixClock]

private theorem flEvalCall {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (loc arity : Nat) (prog : WordLangProgHOL (BitVec width))
    (args : List Nat) (vals : List (WordLocW width))
    (hcode : sptLookup loc t.code = some (arity, prog)) (hclock : t.clock ≠ 0)
    (hvals : WordSemStateFiniteExact.getVars args t = some vals) (hlen : vals.length = arity)
    (res : WordSemResult width) (s : WordSemStateFiniteExact width C F)
    (hrun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv vals (sptLookup loc t.stackSize)
        (WordSemStateFiniteExact.decClock t)) = (some res, s))
    (hres : wordSemBadFunReturn (some res) = false) :
    WordSemStateFiniteExact.evaluate (.call none (some loc) args none) t = (some res, s) := by
  simp [WordSemStateFiniteExact.evaluate, hvals, wordSemBadDestArgs, wordSemAddRetLoc,
    wordSemFindCode, hcode, hlen, hclock, hrun, hres]

private theorem flUpdateEq {width : Nat} [NeZero width]
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (v : WordLocW width) :
    st.updateEq (.nextFree, v) = st.update (.nextFree, v) := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  by_cases h : key = .nextFree
  · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE, h]
  · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE, h, Ne.symm h]

private theorem flOptMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
  cases x <;> cases y <;> rfl

private theorem flOptAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
  cases x <;> cases y <;> rfl

private theorem flMaxIdem (x y : Option Nat) :
    Option.map₂ max (Option.map₂ max x y) y = Option.map₂ max x y := by
  cases x <;> cases y <;> simp [Option.map₂]

set_option linter.unusedSimpArgs false in
/-- The generated `FromList1` loop copies the remaining list cells into the
fresh block, then sets `NextFree` and returns. HOL's free `c`, `b1`, `l1`,
`l2` and `ret_val` are explicit leading binders. The evaluator inherits the
real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "FromList1_code_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem fromList1Code_thm {width : Nat} [NeZero width] {C F : Type} (c : Config)
    (b1 : BitVec width) (l1 l2 : Nat) (ret_val : WordLocW width) :
    ∀ (k : Nat) (a : WordLocW width) (b : BitVec width) (r : WordSemStateFiniteExact width C F)
      (x : WordLocW width) (m1 : BitVec width → WordLocW width) (a1 a2 a3 a4 a5 a6 : Nat),
      sptLookup fromList1Location r.code = some (6, fromList1Code c) ∧
      copyList c r.store k (a, x, b, r.memory, r.mdomain) = some (b1, m1) ∧
      shiftLength c < width ∧ goodDimindex width ∧
      WordSemStateFiniteExact.getVar a1 r = some (.loc l1 l2) ∧
      WordSemStateFiniteExact.getVar a2 r = some (.word b) ∧
      WordSemStateFiniteExact.getVar a3 r = some a ∧
      WordSemStateFiniteExact.getVar a4 r = some (.word (BitVec.ofNat width (4 * k))) ∧
      WordSemStateFiniteExact.getVar a5 r = some ret_val ∧
      WordSemStateFiniteExact.getVar a6 r = some x ∧
      4 * k < 2 ^ width ∧ k < r.clock →
      WordSemStateFiniteExact.evaluate
          (.call none (some fromList1Location) [a1, a2, a3, a4, a5, a6] none) r =
        (some (.result (.loc l1 l2) [ret_val]),
          { r with memory := m1, clock := r.clock - k - 1, locals := .ln,
                   localsSize := some 0, store := r.store.update (.nextFree, .word b1),
                   stackMax := Option.map₂ max r.stackMax
                     (Option.map₂ (· + ·) (wordSemStackSize r.stack)
                       (sptLookup fromList1Location r.stackSize)) }) := by
  intro k
  induction k with
  | zero =>
    intro a b r x m1 a1 a2 a3 a4 a5 a6
      ⟨hcode, hcopy, hshift, good, h1, h2, h3, h4, h5, h6, hbound, hclock⟩
    by_cases dom : r.mdomain b = true
    case neg => rw [copyList.eq_def] at hcopy; simp [dom] at hcopy
    rw [copyList.eq_def] at hcopy
    simp only [dom, if_true, Option.some.injEq, Prod.mk.injEq] at hcopy
    obtain ⟨rfl, rfl⟩ := hcopy
    let vals : List (WordLocW width) :=
      [.loc l1 l2, .word b, a, .word (BitVec.ofNat width (4 * 0)), ret_val, x]
    let s0 := WordSemStateFiniteExact.callEnv vals (sptLookup fromList1Location r.stackSize)
      (WordSemStateFiniteExact.decClock r)
    have hrun : WordSemStateFiniteExact.evaluate (fromList1Code c) s0 =
        (some (.result (.loc l1 l2) [ret_val]),
          { r with memory := fun key => if key = b then x else r.memory key,
                   clock := r.clock - 0 - 1, locals := .ln,
                   localsSize := some 0,
                   store := r.store.update (.nextFree, .word (b + StackRemove.bytesInWord width)),
                   stackMax := Option.map₂ max r.stackMax
                     (Option.map₂ (· + ·) (wordSemStackSize r.stack)
                       (sptLookup fromList1Location r.stackSize)) }) := by
      simp [fromList1Code, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVarImm,
        WordSemStateFiniteExact.memStore, WordSemStateFiniteExact.fixClock,
        WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore,
        WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.callEnv,
        WordSemStateFiniteExact.decClock, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
        sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp, vals, s0, dom]
      exact ⟨flUpdateEq _ _, by rw [flOptMax, flOptAdd]⟩
    exact flEvalCall r fromList1Location 6 _ [a1, a2, a3, a4, a5, a6] vals hcode (by omega)
      (by simp [vals, WordSemStateFiniteExact.getVars, h1, h2, h3, h4, h5, h6]) rfl _ _ hrun rfl
  | succ k ih =>
    intro a b r x m1 a1 a2 a3 a4 a5 a6
      ⟨hcode, hcopy, hshift, good, h1, h2, h3, h4, h5, h6, hbound, hclock⟩
    rw [copyList.eq_def] at hcopy
    simp only [show k + 1 ≠ 0 by omega, if_false] at hcopy
    cases a with
    | loc p q => simp at hcopy
    | word aw =>
    cases hra : getRealAddr c r.store aw with
    | none => simp [hra] at hcopy
    | some ra =>
    simp only [hra] at hcopy
    split at hcopy
    case isFalse => simp at hcopy
    rename_i hc
    obtain ⟨domb, dom2, dom1⟩ := hc
    let B : BitVec width := wordSemBytesInWord
    let m' : BitVec width → WordLocW width := fun key => if key = b then x else r.memory key
    let vals : List (WordLocW width) :=
      [.loc l1 l2, .word b, .word aw, .word (BitVec.ofNat width (4 * (k + 1))), ret_val, x]
    let s0 := WordSemStateFiniteExact.callEnv vals (sptLookup fromList1Location r.stackSize)
      (WordSemStateFiniteExact.decClock r)
    let s1 : WordSemStateFiniteExact width C F :=
      { s0 with memory := fun key => if key = b then x else s0.memory key }
    let s2 := s1.setVar 2 (.word (b + B))
    let s3 := s2.setVar 4 (.word ra)
    let s4 := s3.setVar 10 (m' (ra + B))
    let s5 := s4.setVar 4 (m' (ra + 2 * B))
    let s6 := s5.setVar 6 (.word (BitVec.ofNat width (4 * k)))
    have sub4 : BitVec.ofNat width (4 * (k + 1)) - 4 = BitVec.ofNat width (4 * k) := by
      rw [show 4 * (k + 1) = 4 * k + 4 by ring, ← BitVec.ofNat_add_ofNat]
      exact BitVec.add_sub_cancel _ _
    have ne0 : (BitVec.ofNat width (4 * (k + 1)) == (0 : BitVec width)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at this
      simp at this
    have ihEq := ih (m' (ra + 2 * B)) (b + B) s6 (m' (ra + B)) m1 0 2 4 6 8 10
      ⟨by simpa [s6, s5, s4, s3, s2, s1, s0, WordSemStateFiniteExact.setVar,
          WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using hcode,
       hcopy,
       hshift, good,
       by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, sptFromList2,
          sptInsert, sptLookup],
       by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, sptFromList2,
          sptInsert, sptLookup],
       by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, sptFromList2,
          sptInsert, sptLookup],
       by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, sptFromList2,
          sptInsert, sptLookup],
       by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, sptFromList2,
          sptInsert, sptLookup],
       by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, sptFromList2,
          sptInsert, sptLookup],
       by omega,
       by simp [s6, s5, s4, s3, s2, s1, s0, WordSemStateFiniteExact.setVar,
          WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]; omega⟩
    have body : WordSemStateFiniteExact.evaluate (fromList1Code c) s0 =
        WordSemStateFiniteExact.evaluate
          (.call none (some fromList1Location) [0, 2, 4, 6, 8, 10] none) s6 := by
      simp only [fromList1Code, wordListSeq]
      rw [flSeqStore s0 (.var 2) 10 b x _ (by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp]) (by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp])
        (by simpa [s0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using domb)]
      rw [flSeqAssign s1 2 _ (.word (b + B)) _ (by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp, B, wordSemBytesInWord])]
      rw [WordSemStateFiniteExact.evaluate]
      simp only [show WordSemStateFiniteExact.getVar 6 (s1.setVar 2 (.word (b + B))) =
          some (.word (BitVec.ofNat width (4 * (k + 1)))) by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp],
        WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, ne0]
      rw [flSeqAssign s2 4 (realAddr c 4) (.word ra) _
        (Bignum.getRealAddr_lemma c 4 s2 aw ra ⟨hshift, good, by simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp], by simpa [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp] using hra⟩)]
      rw [flSeqAssign s3 10 _ (m' (ra + B)) _ (by
        simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.memLoad, B, wordSemBytesInWord]
        exact ⟨dom1, rfl⟩)]
      rw [flSeqAssign s4 4 _ (m' (ra + 2 * B)) _ (by
        simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.memLoad, B, wordSemBytesInWord]
        exact ⟨dom2, rfl⟩)]
      rw [flSeqAssign s5 6 _ (.word (BitVec.ofNat width (4 * k))) _ (by
        simp [s6, s5, s4, s3, s2, s1, s0, vals, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
          sptFromList2, sptInsert, sptLookup, theWords, wordOpHOL, wordOp]
        exact sub4)]
    rw [flEvalCall r fromList1Location 6 _ [a1, a2, a3, a4, a5, a6] vals hcode (by omega)
      (by simp [vals, WordSemStateFiniteExact.getVars, h1, h2, h3, h4, h5, h6]) rfl _ _
      (body.trans ihEq) rfl]
    simp [s6, s5, s4, s3, s2, s1, s0, WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.setVar, flOptMax, flOptAdd, flMaxIdem]
    omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
