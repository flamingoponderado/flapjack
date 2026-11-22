module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.CallBignum
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StateRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Preliminaries

@[expose] public section

/-! `AnyArith_thm`: locating a large operand's payload inside the heap
(Flapjack-only helpers following the HOL proof's `impl_tac (E)`-`(G)` steps). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A bignum cell's payload words are a separate part of its word heap. -/
theorem wordHeap_bignum_payload {width : Nat} [NeZero width] (c : Config)
    (H : ValueHeap width) (index : Nat) (i : Int) (curr : BitVec width)
    (found : heapLookup index H = some (bignumRep i)) :
    ∃ R, wordHeap curr H c = SetSep.star
      (Misc.wordList (curr + StackRemove.bytesInWord width * BitVec.ofNat width index +
        StackRemove.bytesInWord width)
        ((Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.map WordLocW.word)) R := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split H index (bignumRep i) found
  subst H
  subst index
  rw [wordHeapAppend]
  simp only [wordHeap, wordEl, bignumRep, wordPayload, wordList_cons]
  have shape : ∀ (A O W K Bk : ((BitVec width × WordLocW width) → Prop) → Prop),
      SetSep.star A (SetSep.star (SetSep.star (SetSep.star O W) K) Bk) =
        SetSep.star W (SetSep.star A (SetSep.star O (SetSep.star K Bk))) := by
    intro A O W K Bk; ac_rfl
  rw [shape]
  exact ⟨_, rfl⟩


/-- A large operand's payload lies in the untouched part of the heap
(HOL: `word_ml_inv_get_var_IMP`, `get_real_addr_get_addr`, `heap_lookup_SPLIT`
and `heap_lookup_Unused_Bignum` in `AnyArith_thm`'s `impl_tac`). -/
theorem operand_payload {width : Nat} [NeZero width] {c : Config} {be : Bool} {ts : Nat}
    {refs : Spt (BvlSem.Ref DataSem.Value)} {heap : ValueHeap width} {limit a sp sp1 : Nat}
    {gens : GcCombined.GenState} {vars : List (DataSem.Value × WordLocW width)}
    {store : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    {ha hb : ValueHeap width} {n k : Nat} {curr other w x : BitVec width} {i : Int}
    (wml : wordMlInv (heap, be, a, sp, sp1, gens) limit ts c refs ((.number i, .word w) :: vars))
    (large : ¬ smallInt width i) (good : goodDimindex width)
    (hlen : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength c)
    (hcurr : store.lookup .currHeap = some (.word curr))
    (hx : getRealAddr c store w = some x)
    (hheap : heap = ha ++ .unused (n + k) :: hb) :
    ∃ R, splitFrame c curr other ha hb n k limit = SetSep.star
      (Misc.wordList (x + StackRemove.bytesInWord width)
        ((Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.map WordLocW.word)) R := by
  obtain ⟨roots, inv, addresses⟩ := wml
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  obtain ⟨ptr, wEq, cell⟩ : ∃ ptr, w = getAddr c ptr (.word 0) ∧
      heapLookup ptr heap = some (bignumRep i) := by
    cases roots with
    | nil => cases values
    | cons root rest =>
      cases values with
      | cons related _ =>
        cases addresses with
        | cons projected _ =>
          have num := (valueInv_number c i refs root f tf heap).mp related
          simp only [large, ↓reduceIte] at num
          obtain ⟨ptr, rootEq, cell⟩ := num
          rw [rootEq] at projected
          simp [wordAddr] at projected
          exact ⟨ptr, projected.symm, cell⟩
  have addr := (getRealAddr_getAddr c store heap ptr _ curr (.word 0) ⟨hlen, cell, hcurr, good⟩).2
  rw [← wEq, hx] at addr
  have xEq : x = curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr := by
    have := Option.some.inj addr; rw [this]; ring
  subst xEq
  set b := StackRemove.bytesInWord width
  rw [hheap, heapLookup_append] at cell
  unfold splitFrame
  dsimp only
  by_cases lt : ptr < heapLength ha
  · rw [if_pos lt] at cell
    obtain ⟨R, hR⟩ := wordHeap_bignum_payload c ha ptr i curr cell
    rw [hR]
    have shape : ∀ (W R Wk B O : ((BitVec width × WordLocW width) → Prop) → Prop),
        SetSep.star (SetSep.star W R) (SetSep.star Wk (SetSep.star B O)) =
          SetSep.star W (SetSep.star R (SetSep.star Wk (SetSep.star B O))) := by
      intro W R Wk B O; ac_rfl
    rw [shape]
    exact ⟨_, rfl⟩
  · rw [if_neg lt, heapLookup_unused_bignum] at cell
    obtain ⟨ge, cell⟩ := cell
    set p' := ptr - heapLength ha - (n + k + 1)
    obtain ⟨R, hR⟩ := wordHeap_bignum_payload c hb p' i
      (curr + b * BitVec.ofNat width (heapLength ha) + b + b * BitVec.ofNat width n +
        b * BitVec.ofNat width k) cell
    have hp : ptr = heapLength ha + 1 + n + k + p' := by omega
    have eaddr : curr + b * BitVec.ofNat width (heapLength ha) + b + b * BitVec.ofNat width n +
        b * BitVec.ofNat width k + b * BitVec.ofNat width p' = curr + b * BitVec.ofNat width ptr := by
      rw [hp]; simp only [BitVec.ofNat_add]
      rw [show (1#width : BitVec width) = 1 from rfl]; ring
    rw [eaddr] at hR
    rw [hR]
    have shape : ∀ (A Wk W R O : ((BitVec width × WordLocW width) → Prop) → Prop),
        SetSep.star A (SetSep.star Wk (SetSep.star (SetSep.star W R) O)) =
          SetSep.star W (SetSep.star A (SetSep.star Wk (SetSep.star R O))) := by
      intro A Wk W R O; ac_rfl
    rw [shape]
    exact ⟨_, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
