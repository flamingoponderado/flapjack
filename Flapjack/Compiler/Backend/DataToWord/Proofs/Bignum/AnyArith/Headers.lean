module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Alloc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyHeader

@[expose] public section

/-! `AnyArith_thm`, the two `AnyHeader` steps (Flapjack-only helpers following
the HOL proof). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.WordSemStateFiniteExact.BignumClauses

/-- What `AnyHeader_thm` reports about one operand: its payload address `a2`
and, for a small operand, its single payload word `a3`. -/
def HeaderFacts {width : Nat} [NeZero width] {C F : Type} (c : Config) (i : Int) (other : Bool)
    (r : Nat) (t : WordSemStateFiniteExact width C F) (a2 a3 : BitVec width) : Prop :=
  (i = 0 → a2 = 0 ∧ a3 = 0) ∧
  (smallInt width i ∧ i ≠ 0 →
    (Misc.Multiword.i2mw i : Bool × List (BitVec width)) = (decide (i < 0), [a3]) ∧
    t.store.lookup (if other then .otherHeap else .nextFree) = some (.word a2)) ∧
  (¬ smallInt width i → ∃ w x : BitVec width,
    WordSemStateFiniteExact.getVar (adjustVar r) t = some (.word w) ∧
    getRealAddr c t.store w = some x ∧ a2 = x + wordSemBytesInWord)

/-- The state after both header computations. -/
def headerState {width : Nat} [NeZero width] {C F : Type} (s1 : WordSemStateFiniteExact width C F)
    (i j : Int) (a2 a3 a2' a3' : BitVec width) (tmp tmp' : WordLocW width) :
    WordSemStateFiniteExact width C F :=
  (((((((s1.setVar 7 tmp).setStore (.temp 12) (.word a3)).setStore (.temp 31) (.word a2)).setStore
    (.temp 0) (.word (Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width))))).setVar
    7 tmp').setStore (.temp 11) (.word a3')).setStore (.temp 30) (.word a2')).setStore (.temp 1)
    (.word (Misc.Multiword.mcHeader (Misc.Multiword.i2mw j : Bool × List (BitVec width))))

private theorem getVar_setStore {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : WordStoreHOL) (v : WordLocW width) (n : Nat) :
    (t.setStore k v).getVar n = t.getVar n := rfl

private theorem getVar_setVar7 {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (v : WordLocW width) (n : Nat) (h : n ≠ 7) :
    (t.setVar 7 v).getVar n = t.getVar n := by
  simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ h]

private theorem store_setVar {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (n : Nat) (v : WordLocW width) :
    (t.setVar n v).store = t.store := rfl

private theorem lookup_setStore_temp {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : BitVec 5) (v : WordLocW width) (n : WordStoreHOL)
    (h : ∀ r, n ≠ .temp r) : (t.setStore (.temp k) v).store.lookup n = t.store.lookup n := by
  simp [WordSemStateFiniteExact.setStore, FUPDATE_HOL, (h k)]

private theorem getRealAddr_setStore_temp {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (t : WordSemStateFiniteExact width C F) (k : BitVec 5) (v : WordLocW width) (w : BitVec width) :
    getRealAddr c (t.setStore (.temp k) v).store w = getRealAddr c t.store w := by
  simp only [getRealAddr, lookup_setStore_temp t k v .currHeap (by intro r h; cases h)]

/-- Both `AnyHeader` calls of `AnyArith_code`. -/
theorem headers_step {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 : Nat}
    {s0 : DataSem.State C F} {s1 : WordSemStateFiniteExact width C F} {locs : List (Nat × Nat)}
    {i j : Int} (rel : stateRel c l1 l2 s0 s1 none locs)
    (hi : DataSem.getVar 0 s0.locals = some (.number i))
    (hj : DataSem.getVar 1 s0.locals = some (.number j)) (rest : WordLangProgHOL (BitVec width)) :
    ∃ (a2 a3 a2' a3' : BitVec width) (tmp tmp' : WordLocW width),
      WordSemStateFiniteExact.evaluate
          (.seq (anyHeader c 2 false 0 31 12) (.seq (anyHeader c 4 true 1 30 11) rest)) s1 =
        WordSemStateFiniteExact.evaluate rest (headerState s1 i j a2 a3 a2' a3' tmp tmp') ∧
      stateRel c l1 l2 s0 (headerState s1 i j a2 a3 a2' a3' tmp tmp') none locs ∧
      HeaderFacts c i false 0 s1 a2 a3 ∧ HeaderFacts c j true 1 s1 a2' a3' := by
  obtain ⟨a2, a3, tmp, ev1, z1, sm1, bg1⟩ :=
    anyHeader_thm (w2 := width) c l1 l2 s0 s1 locs i false 0 31 12 0 ⟨rel, hi, by decide⟩
  set s8 := ((((s1.setVar 7 tmp).setStore (.temp 12) (.word a3)).setStore (.temp 31)
    (.word a2)).setStore (.temp 0)
    (.word (Misc.Multiword.mcHeader (Misc.Multiword.i2mw i : Bool × List (BitVec width))))) with hs8
  have rel8 : stateRel c l1 l2 s0 s8 none locs := by
    rw [hs8, stateRel_setStore_temp, stateRel_setStore_temp, stateRel_setStore_temp]
    exact (stateRel_insert_7 c l1 l2 s0 s1 none locs _).symm ▸ rel
  obtain ⟨a2', a3', tmp', ev2, z2, sm2, bg2⟩ :=
    anyHeader_thm (w2 := width) c l1 l2 s0 s8 locs j true 1 30 11 1 ⟨rel8, hj, by decide⟩
  refine ⟨a2, a3, a2', a3', tmp, tmp', ?_, ?_, ?_, ?_⟩
  · rw [evaluate_seq_of_none _ _ _ _
      (show WordSemStateFiniteExact.evaluate (anyHeader c 2 false 0 31 12) s1 = _ from ev1),
      evaluate_seq_of_none _ _ _ _
      (show WordSemStateFiniteExact.evaluate (anyHeader c 4 true 1 30 11) s8 = _ from ev2)]
    rfl
  · show stateRel c l1 l2 s0 ((((s8.setVar 7 tmp').setStore (.temp 11) (.word a3')).setStore
      (.temp 30) (.word a2')).setStore (.temp 1) _) none locs
    rw [stateRel_setStore_temp, stateRel_setStore_temp, stateRel_setStore_temp]
    exact (stateRel_insert_7 c l1 l2 s0 s8 none locs _).symm ▸ rel8
  · exact ⟨fun h => ⟨(z1 h).2.2.1, (z1 h).2.2.2⟩, sm1, bg1⟩
  · refine ⟨fun h => ⟨(z2 h).2.2.1, (z2 h).2.2.2⟩, fun h => ?_, fun h => ?_⟩
    · obtain ⟨e, st⟩ := sm2 h
      refine ⟨e, ?_⟩
      rw [hs8] at st
      simpa [lookup_setStore_temp, store_setVar] using st
    · obtain ⟨w, x, gv, ra, ax⟩ := bg2 h
      refine ⟨w, x, ?_, ?_, ax⟩
      · rw [hs8, getVar_setStore, getVar_setStore, getVar_setStore,
          getVar_setVar7 _ _ _ (by decide)] at gv
        exact gv
      · rw [hs8, getRealAddr_setStore_temp, getRealAddr_setStore_temp,
          getRealAddr_setStore_temp, store_setVar] at ra
        exact ra

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
