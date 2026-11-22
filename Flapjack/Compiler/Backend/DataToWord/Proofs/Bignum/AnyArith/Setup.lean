module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Split
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.Replicate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StoreList
public import Flapjack.Compiler.Backend.WordBignum.Proofs.WordSemClauses
public import Flapjack.Misc.SetSep.Read

@[expose] public section

/-! `AnyArith_thm`: the header stores and the `Replicate` call that clears
the output array (Flapjack-only helpers following the HOL proof). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.WordSemStateFiniteExact.BignumClauses

/-- The `Replicate` and header-store segment of `AnyArith_code`. -/
def setupCode {width : Nat} [NeZero width] (rest : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  .seq (.get 1 (.temp 11)) (.seq (.store (.lookup .otherHeap) 1)
  (.seq (.get 1 (.temp 12)) (.seq (.store (.lookup .nextFree) 1)
  (.seq (.get 1 (.temp 29)) (.seq (.assign 2 (.lookup .nextFree))
  (.seq (.set (.temp 29) (.var 2)) (.seq (.set (.temp 3) (shiftN .lsr (.var 6) 2))
  (.seq (.assign 3 (.const 0))
  (.seq (.call (some ([0], (.ls (), .ln), .skip, anyArithLocation, 2)) (some replicateLocation)
      [2, 3, 1, 0] none)
  (.seq (.set (.temp 29) (.op .add [.lookup (.temp 29), .const wordSemBytesInWord])) rest))))))))))

/-- The state after `setupCode`. -/
def setupState {width : Nat} [NeZero width] {C F : Type} (s9 : WordSemStateFiniteExact width C F)
    (u w3 : BitVec width) (m2 : BitVec width → WordLocW width) (n : Nat) (ret : WordLocW width)
    (maxStack : Option Nat) : WordSemStateFiniteExact width C F :=
  { s9 with store := ((s9.store.updateEq (.temp 29, .word u)).updateEq (.temp 3, .word w3)).updateEq
               (.temp 29, .word (u + wordSemBytesInWord)),
            memory := m2, clock := s9.clock - n - 1, locals := sptInsert 0 ret .ln,
            stackMax := maxStack, permute := fun k => s9.permute (k + 1) }

private theorem memStore_eq {width : Nat} [NeZero width] {C F : Type}
    (S : WordSemStateFiniteExact width C F) (a : BitVec width) (v : WordLocW width)
    (h : S.mdomain a = true) :
    WordSemStateFiniteExact.memStore a v S =
      some { S with memory := fun x => if x = a then v else S.memory x } := by
  simp [WordSemStateFiniteExact.memStore, h]

/-- Classical and decidable point updates agree. -/
private theorem update_eq {width : Nat} [NeZero width] (m : BitVec width → WordLocW width) (a : BitVec width)
    (v : WordLocW width) :
    (fun x => @ite _ (x = a) (Classical.propDecidable _) v (m x)) =
      (fun x => if x = a then v else m x) := by
  funext x; by_cases h : x = a <;> simp [h]

/-- Evaluation of `setupCode`. -/
theorem setup_step {width : Nat} [NeZero width] {C F : Type}
    {s9 : WordSemStateFiniteExact width C F} {u other a3 a3' w3 : BitVec width} {n op : Nat}
    {ret x0 ow : WordLocW width} {xs : List (WordLocW width)}
    {FR : ((BitVec width × WordLocW width) → Prop) → Prop}
    (h11 : s9.store.lookup (.temp 11) = some (.word a3'))
    (h12 : s9.store.lookup (.temp 12) = some (.word a3))
    (h29 : s9.store.lookup (.temp 29) = some (.word (BitVec.ofNat width (4 * n))))
    (hoth : s9.store.lookup .otherHeap = some (.word other))
    (hnf : s9.store.lookup .nextFree = some (.word u))
    (h6 : sptLookup 6 s9.locals = some (.word (BitVec.ofNat width (4 * op))))
    (hsh : wordShiftHOL .lsr (BitVec.ofNat width (4 * op)) (BitVec.ofNat width 2).toNat = some w3)
    (h0 : sptLookup 0 s9.locals = some ret)
    (hcode : sptLookup replicateLocation s9.code = some (5, replicateCode))
    (hn : xs.length = n) (hb : 4 * n < 2 ^ width) (hc : n < s9.clock)
    (H : SetSep.star (Misc.wordList (u + wordSemBytesInWord) xs)
      (SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow)) FR))
      (SetSep.fun2Set (s9.memory, fun x => s9.mdomain x = true)))
    (rest : WordLangProgHOL (BitVec width)) :
    ∃ (m2 : BitVec width → WordLocW width) (maxStack : Option Nat),
      WordSemStateFiniteExact.evaluate (setupCode rest) s9 =
        WordSemStateFiniteExact.evaluate rest (setupState s9 u w3 m2 n ret maxStack) ∧
      SetSep.star (Misc.wordList (u + wordSemBytesInWord) (List.replicate n (.word 0)))
        (SetSep.star (SetSep.one (u, .word a3))
          (SetSep.star (SetSep.one (other, .word a3')) FR))
        (SetSep.fun2Set (m2, fun x => s9.mdomain x = true)) := by
  -- reading the two header cells' domain membership
  have dOther : s9.mdomain other = true := by
    rw [show SetSep.star (Misc.wordList (u + wordSemBytesInWord) xs)
      (SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow)) FR)) =
      SetSep.star (SetSep.one (other, ow)) (SetSep.star (SetSep.one (u, x0))
        (SetSep.star (Misc.wordList (u + wordSemBytesInWord) xs) FR)) by ac_rfl] at H
    exact (SetSep.readFun2Set _ _ _ _ _ H).2
  have dU : s9.mdomain u = true := by
    rw [show SetSep.star (Misc.wordList (u + wordSemBytesInWord) xs)
      (SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow)) FR)) =
      SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow))
        (SetSep.star (Misc.wordList (u + wordSemBytesInWord) xs) FR)) by ac_rfl] at H
    exact (SetSep.readFun2Set _ _ _ _ _ H).2
  set b : BitVec width := wordSemBytesInWord
  set dmP : BitVec width → Prop := fun x => s9.mdomain x = true
  set m4 : BitVec width → WordLocW width := fun x => if x = other then .word a3' else s9.memory x
  set m5 : BitVec width → WordLocW width := fun x => if x = u then .word a3 else m4 x
  have H5 : SetSep.star (Misc.wordList (u + b) xs)
      (SetSep.star (SetSep.one (u, .word a3)) (SetSep.star (SetSep.one (other, .word a3')) FR))
      (SetSep.fun2Set (m5, dmP)) := by
    have H1 := H
    rw [show SetSep.star (Misc.wordList (u + b) xs)
      (SetSep.star (SetSep.one (u, x0)) (SetSep.star (SetSep.one (other, ow)) FR)) =
      SetSep.star (SetSep.one (other, ow)) (SetSep.star (Misc.wordList (u + b) xs)
        (SetSep.star (SetSep.one (u, x0)) FR)) by ac_rfl] at H1
    have H2 := SetSep.writeFun2Set (WordLocW.word a3') other ow _ _ _ H1
    rw [update_eq] at H2
    rw [show SetSep.star (SetSep.star (Misc.wordList (u + b) xs) (SetSep.star (SetSep.one (u, x0)) FR))
        (SetSep.one (other, WordLocW.word a3')) =
      SetSep.star (SetSep.one (u, x0)) (SetSep.star (Misc.wordList (u + b) xs)
        (SetSep.star (SetSep.one (other, WordLocW.word a3')) FR)) by ac_rfl] at H2
    have H3 := SetSep.writeFun2Set (WordLocW.word a3) u x0 _ _ _ H2
    rw [update_eq] at H3
    rw [show SetSep.star (SetSep.star (Misc.wordList (u + b) xs)
        (SetSep.star (SetSep.one (other, WordLocW.word a3')) FR)) (SetSep.one (u, WordLocW.word a3)) =
      SetSep.star (Misc.wordList (u + b) xs)
        (SetSep.star (SetSep.one (u, .word a3)) (SetSep.star (SetSep.one (other, .word a3')) FR)) by
        ac_rfl] at H3
    exact H3
  obtain ⟨m2, hst, H6⟩ := wordList_storeList xs (u + b) _ m5 s9.mdomain H5
  rw [hn] at hst H6
  set S1 := s9.setVar 1 (.word a3')
  set S2 : WordSemStateFiniteExact width C F := { S1 with memory := m4 }
  set S3 := S2.setVar 1 (.word a3)
  set S4 : WordSemStateFiniteExact width C F := { S3 with memory := m5 }
  set S5 := S4.setVar 1 (.word (BitVec.ofNat width (4 * n)))
  set S6 := S5.setVar 2 (.word u)
  set S7 := S6.setStore (.temp 29) (.word u)
  set S8 := S7.setStore (.temp 3) (.word w3)
  set S9 := S8.setVar 3 (.word 0)
  have e1 : WordSemStateFiniteExact.evaluate (.get 1 (.temp 11)) s9 = (none, S1) := by
    rw [evaluate_get, WordSemStateFiniteExact.getStore, h11]
  have e2 : WordSemStateFiniteExact.evaluate (.store (.lookup .otherHeap) 1) S1 = (none, S2) := by
    rw [evaluate_store, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore]
    rw [show S1.store = s9.store from rfl, hoth]
    rw [show WordSemStateFiniteExact.getVar 1 S1 = some (.word a3') by
      simp [S1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]]
    dsimp only
    rw [memStore_eq S1 other _ dOther]
    rfl
  have gv : ∀ (S : WordSemStateFiniteExact width C F) (k : Nat) (v : WordLocW width),
      WordSemStateFiniteExact.getVar k (S.setVar k v) = some v := by
    intro S k v
    simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  have gvne : ∀ (S : WordSemStateFiniteExact width C F) (k k' : Nat) (v : WordLocW width), k' ≠ k →
      WordSemStateFiniteExact.getVar k' (S.setVar k v) = WordSemStateFiniteExact.getVar k' S := by
    intro S k k' v h
    simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ h]
  have gvs : ∀ (S : WordSemStateFiniteExact width C F) (k : WordStoreHOL) (v : WordLocW width) (n : Nat),
      WordSemStateFiniteExact.getVar n (S.setStore k v) = WordSemStateFiniteExact.getVar n S :=
    fun _ _ _ _ => rfl
  have gvm : ∀ (S : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) (n : Nat),
      WordSemStateFiniteExact.getVar n { S with memory := m } = WordSemStateFiniteExact.getVar n S :=
    fun _ _ _ => rfl
  have e3 : WordSemStateFiniteExact.evaluate (.get 1 (.temp 12)) S2 = (none, S3) := by
    rw [evaluate_get, WordSemStateFiniteExact.getStore, show S2.store = s9.store from rfl, h12]
  have e4 : WordSemStateFiniteExact.evaluate (.store (.lookup .nextFree) 1) S3 = (none, S4) := by
    rw [evaluate_store, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
      show S3.store = s9.store from rfl, hnf, gv]
    dsimp only
    rw [memStore_eq S3 u _ dU]
    rfl
  have e5 : WordSemStateFiniteExact.evaluate (.get 1 (.temp 29)) S4 = (none, S5) := by
    rw [evaluate_get, WordSemStateFiniteExact.getStore, show S4.store = s9.store from rfl, h29]
  have e6 : WordSemStateFiniteExact.evaluate (.assign 2 (.lookup .nextFree)) S5 = (none, S6) := by
    rw [evaluate_assign, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
      show S5.store = s9.store from rfl, hnf]
  have e7 : WordSemStateFiniteExact.evaluate (.set (.temp 29) (.var 2)) S6 = (none, S7) := by
    rw [evaluate_set, if_neg (by simp), WordSemStateFiniteExact.wordExp, gv]
  have g6 : WordSemStateFiniteExact.getVar 6 S7 = some (.word (BitVec.ofNat width (4 * op))) := by
    simp only [S7, S6, S5, S4, S3, S2, S1, gvs, gvm, gvne _ _ _ _ (by decide : (6 : Nat) ≠ 2),
      gvne _ _ _ _ (by decide : (6 : Nat) ≠ 1)]
    exact h6
  have e8 : WordSemStateFiniteExact.evaluate (.set (.temp 3) (shiftN .lsr (.var 6) 2)) S7 =
      (none, S8) := by
    rw [evaluate_set, if_neg (by simp), shiftN, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.wordExp, g6]
    simp only [hsh, Option.map_some]
    rfl
  have e9 : WordSemStateFiniteExact.evaluate (.assign 3 (.const 0)) S8 = (none, S9) := by
    rw [evaluate_assign, WordSemStateFiniteExact.wordExp]
  have fl : (Spt.ls () : NumSet) = sptFromList [()] := by simp [sptFromList]
  have r2 : WordSemStateFiniteExact.getVar 2 S9 = some (.word u) := by
    simp only [S9, S8, S7, S6, gvs, gvne _ _ _ _ (by decide : (2 : Nat) ≠ 3), gv]
  have r3 : WordSemStateFiniteExact.getVar 3 S9 = some (.word 0) := gv _ _ _
  have r1 : WordSemStateFiniteExact.getVar 1 S9 = some (.word (BitVec.ofNat width (4 * n))) := by
    simp only [S9, S8, S7, S6, S5, gvs, gvne _ _ _ _ (by decide : (1 : Nat) ≠ 3),
      gvne _ _ _ _ (by decide : (1 : Nat) ≠ 2), gv]
  have r0 : WordSemStateFiniteExact.getVar 0 S9 = some ret := by
    simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, gvs, gvm,
      gvne _ _ _ _ (by decide : (0 : Nat) ≠ 3), gvne _ _ _ _ (by decide : (0 : Nat) ≠ 2),
      gvne _ _ _ _ (by decide : (0 : Nat) ≠ 1)]
    exact h0
  obtain ⟨ms, e10⟩ := replicateCode_alt_thm (β := Unit) (δ := Unit) (ε := Unit) (.word 0)
    anyArithLocation 2 ret n u S9 m2 () 2 3 1 () () ⟨hcode, hst, r2, r3, r1, r0, hb, hc⟩
  rw [← fl] at e10
  refine ⟨m2, ms, ?_, H6⟩
  rw [setupCode, evaluate_seq_of_none _ _ _ _ e1, evaluate_seq_of_none _ _ _ _ e2,
    evaluate_seq_of_none _ _ _ _ e3, evaluate_seq_of_none _ _ _ _ e4,
    evaluate_seq_of_none _ _ _ _ e5, evaluate_seq_of_none _ _ _ _ e6,
    evaluate_seq_of_none _ _ _ _ e7, evaluate_seq_of_none _ _ _ _ e8,
    evaluate_seq_of_none _ _ _ _ e9, evaluate_seq_of_none _ _ _ _ e10]
  apply evaluate_seq_of_none
  rw [evaluate_set, if_neg (by simp)]
  have ex : WordSemStateFiniteExact.wordExp
      { S9 with memory := m2, clock := S9.clock - n - 1, locals := sptInsert 0 ret .ln,
                stackMax := ms, permute := fun k => S9.permute (k + 1) }
      (.op .add [.lookup (.temp 29), .const wordSemBytesInWord]) = some (.word (u + b)) := by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, S9, S8, S7,
      WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, FUPDATE_HOL, theWords,
      wordOpHOL, wordOp, b]
  rw [ex]
  rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
