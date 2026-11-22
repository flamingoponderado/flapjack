module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.WordBignum.Proofs.StateRel
public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileCode
public import Flapjack.Compiler.Backend.WordBignum.Generate

@[expose] public section

/-! The data-to-word state relation installs the generated bignum code. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace CodeRelWitness
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end CodeRelWitness

private theorem holAlookup_mem {α β : Type} [DecidableEq α] :
    ∀ (xs : List (α × β)) (k : α) (v : β), holAlookup xs k = some v → (k, v) ∈ xs := by
  intro xs
  induction xs with
  | nil => intro k v h; simp [holAlookup] at h
  | cons x xs ih =>
    intro k v h
    obtain ⟨a, b⟩ := x
    by_cases e : a = k
    · subst e; simp [holAlookup] at h; subst h; simp
    · simp only [holAlookup, e, if_false] at h
      exact List.mem_cons_of_mem _ (ih k v h)

/-- The generated bignum entries of a related target code table satisfy the
bignum compiler's code relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "IMP_bignum_code_rel"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem impBignumCodeRel {width : Nat} [NeZero width] {C F : Type}
    (xx1 : WordLangProgHOL (BitVec width)) (xx2 xx3 xx4 : Nat)
    (xx5 : List (WordBignum.Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)))
    (c : Config) (l1 l2 : Nat) (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) :
    WordBignum.compile bignumLocation 2 1 (bignumLocation + 1, [])
        (WordBignum.mcIopCode width) = (xx1, xx2, xx3, xx4, xx5) ∧
      stateRel c l1 l2 s t none locs →
    WordBignum.codeRel (xx4, xx5) t.code := by
  rintro ⟨hc, rel⟩ prog n p2 hlook
  have hmem := holAlookup_mem xx5 prog (n, p2) hlook
  obtain ⟨cs1, l2', i2, cs2, hcomp, hsub⟩ :=
    WordBignum.compile_NIL_IMP bignumLocation 2 1 (bignumLocation + 1) (WordBignum.mcIopCode width)
      xx1 xx2 xx3 (xx4, xx5) hc prog n p2 hmem
  refine ⟨cs1, l2', i2, cs2, hcomp, ?_, hsub⟩
  refine rel.2.2.2.2.1.2.1 (n, 1, .seq p2 (.return 0 [0])) ?_
  simp only [stubs, List.mem_append]
  right
  simp only [WordBignum.generatedBignumStubs, hc, List.mem_cons, List.mem_map]
  right
  exact ⟨(prog, n, p2), hmem, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
