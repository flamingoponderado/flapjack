module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRoots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveRoots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorFilter
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DecodedRoots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HeapLimit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute

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

/-- Flapjack-specific packaging of the root preparation in HOL's
`state_rel_gc_gen` proof: the state relation supplies the collector invariant
for the global value and flattened stack, the matching heap limit, and valid
encoded roots.
There is no separately named HOL theorem for this combined step. -/
theorem stateRel_gcRoots {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target none locs) :
    ∃ heap limit a sp sp1 gens,
      Memory.heapInMemoryStore heap a sp sp1 gens conf target.store target.memory target.mdomain limit ∧
      Memory.wordMlInv (heap, target.be, a, sp, sp1, gens) limit (holThe source.tstamps)
        conf source.refs ((theGlobal source.global, holFapply target.store .globals) ::
          flatStack source.stack target.stack) ∧
      (limit + 3) * (width / 8) + 1 < 2 ^ width ∧ source.space ≤ sp ∧
      source.limits.heapLimit = limit ∧
      (∀ word ∈ wordSemEncStack target.stack, locOk word = true) := by
  rcases related with ⟨_, _, _, _, _, _, hgood, _, _, _, _, _, hstack, _, _, _, _, _, hlim, hmem⟩
  simp only [Option.getD_none, List.nil_append] at hmem
  obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hinv, hbound, hspace⟩ := hmem
  have selected : Memory.wordMlInv (heap, target.be, a, sp, sp1, gens) limit
      (holThe source.tstamps) conf source.refs
      ((theGlobal source.global, holFapply target.store .globals) :: flatStack source.stack target.stack) := by
    apply Memory.wordMlInv_rearrange heap target.be a sp sp1 gens limit (holThe source.tstamps)
      conf source.refs _ _ ?_ hinv
    intro pair member
    simp only [List.mem_cons, List.mem_append] at member ⊢
    rcases member with rfl | member
    · simp
    · exact Or.inr member
  have limitEq := limitsInv_heapInMemoryStore_limit source.limits conf heap target.be a sp sp1
    limit (holThe source.tstamps) gens source.refs _ target.store target.memory target.mdomain
    target.stackLimit hgood hlim hstore selected
  refine ⟨heap, limit, a, sp, sp1, gens, hstore, selected, hbound, hspace, limitEq, ?_⟩
  intro word member
  apply wordMlInv_roots_locOk heap target.be a sp sp1 gens limit (holThe source.tstamps)
    conf source.refs _ selected word
  simp only [List.map_cons, List.mem_cons]
  right
  exact stackRel_imp_subset source.stack target.stack hstack member

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
