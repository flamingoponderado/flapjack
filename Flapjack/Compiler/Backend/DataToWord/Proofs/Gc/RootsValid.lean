import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorFilter
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DecodedRoots

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

/-- The candidate data-to-word state relation supplies valid locations for
the encoded word stack and the separately stored global root. -/
theorem stateRel64_gcRoots_locOk {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) :
    (holFapply target.store .globals :: wordSemEncStack target.stack).all locOk = true := by
  have stackRel := related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have memoryRel := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, _, inv, _, _⟩ := memoryRel
  have valid := wordMlInv_roots_locOk heap target.be a sp sp1 gens limit (holThe source.tstamps)
    conf source.refs _ inv
  have encoded := flatStack_values_eq_encStack source.stack target.stack stackRel
  apply List.all_eq_true.mpr
  intro word member
  apply valid word
  simp only [Option.getD_none, List.nil_append, List.map_append, List.map_cons, List.map_nil] at valid ⊢
  simp only [List.mem_cons] at member
  rcases member with global | stack
  · subst word
    simp
  · rw [← encoded] at stack
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr stack

/-- A successful production collector call admits a decoded stack whose
frame relations, saved locations, and paired data roots agree with the
collector's actual result. The separate existence and memory-correctness
obligations for collection remain open. -/
theorem stateRel64_gc_decode {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (moved : List (WordLocW 64)) (memory : BitVec 64 → WordLocW 64)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (run : target.gcFun (wordSemEncStack target.stack, target.memory, target.mdomain, target.store) =
      some (moved, memory, store)) :
    ∃ stack, wordSemDecStack moved target.stack = some stack ∧
      List.Forall₂ stackRel source.stack stack ∧ List.Forall₂ containsLoc stack locs ∧
      flatStack source.stack stack = ((flatStack source.stack target.stack).map Prod.fst).zip moved := by
  have gcEq := related.2.2.2.1
  have stackRel := related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have locations := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have valid : (wordSemEncStack target.stack).all locOk = true := by
    have all := stateRel64_gcRoots_locOk conf l1 l2 source target locs related
    simp only [List.all_cons, Bool.and_eq_true] at all
    exact all.2
  have run' : WordGcFunctions.wordGcFun conf
      (wordSemEncStack target.stack, target.memory, target.mdomain, target.store) = some (moved, memory, store) := by
    simpa [gcEq] using run
  have filtered := wordGcFun_imp_filter conf _ moved target.memory memory target.mdomain target.store store run' valid
  have merged := wordGcFun_locMerge conf _ (moved.filter wordSemIsWordLoc) target.memory memory
    target.mdomain target.store store filtered valid
  rw [run'] at merged
  have rootsEq : moved = locMerge (wordSemEncStack target.stack) (moved.filter wordSemIsWordLoc) := by
    simpa only [Option.some.injEq, Prod.mk.injEq, true_and, and_true] using merged
  obtain ⟨stack, decoded⟩ := decStack_locMerge_encStack target.stack (moved.filter wordSemIsWordLoc)
  have stackFacts := stackRel_decStack_locMerge target.stack (moved.filter wordSemIsWordLoc)
    source.stack stack locs stackRel locations decoded
  have rootRel := WordGcFunctions.word_gc_IMP_EVERY2 run'
  have convert : ∀ {xs ys : List (WordLocW 64)},
      ListRel WordGcFunctions.gcRootRel xs ys →
      List.Forall₂ (fun x y => wordSemIsWordLoc x = wordSemIsWordLoc y ∧
        (wordSemIsWordLoc x = false → x = y)) xs ys := by
    intro xs ys relation
    induction relation with
    | nil => exact .nil
    | @cons x y xs ys head tail ih =>
      refine .cons ⟨head.1, ?_⟩ ih
      intro notWord
      cases x with
      | word w => simp [wordSemIsWordLoc] at notWord
      | loc a b => exact head.2 (by rfl)
  have flatRel := convert rootRel
  rw [← flatStack_values_eq_encStack source.stack target.stack stackRel] at flatRel
  have flat := wordGcFun_decStack_flat source.stack target.stack stack moved stackFacts.1 flatRel decoded stackRel
  exact ⟨stack, by rw [rootsEq]; exact decoded, stackFacts.1, stackFacts.2, flat⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
