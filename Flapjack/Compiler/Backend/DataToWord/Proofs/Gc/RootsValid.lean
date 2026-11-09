module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRoots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveRoots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorFilter
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DecodedRoots

@[expose] public section

/-! Valid collector locations supplied by the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "loc_ok_word_addr"
  (words_as_type_indexed_bitvec)]
theorem locOk_wordAddr {width : Nat} [NeZero width] (conf : Config)
    (address : HeapAddress (WordLocW width)) : locOk (Memory.wordAddr conf address) = true := by
  cases address with
  | pointer index value => simp [Memory.wordAddr, locOk]
  | data value => cases value <;> simp [Memory.wordAddr, locOk]

/-- Every word represented by a word-level ML invariant has a valid code
location. This is a consequence of the checked address relation. -/
theorem wordMlInv_roots_locOk {width : Nat} [NeZero width]
    (heap : Memory.ValueHeap width) (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit next : Nat) (conf : Config) (refs : Spt (BvlSem.Ref DataSem.Value))
    (vars : List (DataSem.Value × WordLocW width))
    (inv : Memory.wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs vars) :
    ∀ word ∈ vars.map Prod.snd, locOk word = true := by
  obtain ⟨roots, _, related⟩ := inv
  have all : ∀ {roots : List (HeapAddress (WordLocW width))} {words : List (WordLocW width)},
      List.Forall₂ (fun address word => Memory.wordAddr conf address = word) roots words →
      ∀ word ∈ words, locOk word = true := by
    intro roots words related
    induction related with
    | nil => simp
    | @cons address word roots words equal tail ih =>
      intro value member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rw [← equal]
        exact locOk_wordAddr conf address
      · exact ih value member
  exact all related

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
