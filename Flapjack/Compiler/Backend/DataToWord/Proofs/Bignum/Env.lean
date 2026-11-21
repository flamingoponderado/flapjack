module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Misc.Sptree.FromList
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

@[expose] public section

/-! Environment pushes and cuts used by the data-to-word bignum proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend

namespace EnvWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EnvWitnesses

/-- Pushing a handler-free frame keeps the code store. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "push_env_code"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_code {width : Nat} [NeZero width] {C F : Type}
    (y : Spt (WordLocW width) × Spt (WordLocW width)) (t : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.pushEnv y none t).code = t.code := by
  simp only [WordSemStateFiniteExact.pushEnv]

/-- Pushing a frame holding only variable zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "push_env_insert_0"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_insert_0 {width : Nat} [NeZero width] {C F : Type}
    (x : WordLocW width) (t : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.pushEnv (sptInsert 0 x .ln, .ln) none t =
      { t with
        stack := .stackFrame t.localsSize [(0, x)] [] none :: t.stack
        stackMax := wordSemOptionMax t.stackMax
          (wordSemStackSize (.stackFrame t.localsSize [(0, x)] [] none :: t.stack))
        permute := fun n => t.permute (n + 1) } := by
  have ins : sptInsert 0 x .ln = .ls x := by simp
  have empty : (wordSemEnvToList (.ln : Spt (WordLocW width)) t.permute).1 = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    have source := (wordSemEnvToList_mem_iff (.ln : Spt (WordLocW width)) t.permute entry).mp member
    simp at source
  have single : sptToAList (Spt.ls x) = [(0, x)] := by simp [sptToAList, sptFoldi]
  rw [ins]
  simp only [WordSemStateFiniteExact.pushEnv, single]
  rw [empty]
  rfl

/-- Cutting a frame holding only variable zero to the name zero keeps it. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "cut_env_fromList_sing"
  (words_as_type_indexed_bitvec)]
theorem cutEnv_fromList_sing {width : Nat} [NeZero width] (l1 l2 : Nat) :
    DataSem.cutEnv (sptFromList [()]) (sptInsert 0 (WordLocW.loc l1 l2 : WordLocW width) .ln) =
      some (sptInsert 0 (WordLocW.loc l1 l2) .ln) := by
  classical
  have ins : ∀ {β : Type} (v : β), sptInsert 0 v .ln = .ls v := by
    intro β v
    simp
  have names : sptFromList [()] = .ls () := by
    simp [sptFromList, ins]
  rw [ins, names]
  unfold DataSem.cutEnv
  rw [if_pos]
  · simp [sptInter, sptMkWf]
  · intro key member
    cases key <;> simp_all [sptMem, sptDomain, sptLookup]
end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
