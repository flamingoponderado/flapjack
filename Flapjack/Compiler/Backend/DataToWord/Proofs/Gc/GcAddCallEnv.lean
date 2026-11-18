module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc

@[expose] public section

/-! Garbage collection is insensitive to the temporary call environment. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack WordSemStateFiniteExact

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- The extra call environment is discarded by the subsequent pop. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_add_call_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gcAddCallEnv {width resultWidth : Nat} [NeZero width] [NeZero resultWidth] {C F : Type}
    (y : Spt (WordLocW width) × Spt (WordLocW width))
    (t5 x t : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (f : WordSemStateFiniteExact width C F →
      Option (WordSemResult resultWidth) × WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult resultWidth))
    (h : (match gc (pushEnv y none t5) with
      | none => (some .error, x)
      | some s => match popEnv s with
        | none => (some .error, flushState true s)
        | some s => f s) = (res, t)) :
    (match gc (WordSemStateFiniteExact.callEnv [.loc l1 l2] (some 0) (pushEnv y none t5)) with
      | none => (some .error, x)
      | some s => match popEnv s with
        | none => (some .error, flushState true s)
        | some s => f s) = (res, t) := by
  simp only [gc, WordSemStateFiniteExact.callEnv, pushEnv, wordSemEncStack,
    wordSemDecStack] at h ⊢
  generalize hg : t5.gcFun ((wordSemEnvToList y.2 t5.permute).1.map Prod.snd ++
    wordSemEncStack t5.stack, t5.memory, t5.mdomain, t5.store) = g at h ⊢
  cases g with
  | none => simpa using h
  | some g =>
    rcases g with ⟨wl, mem, store⟩
    by_cases short : wl.length < (wordSemEnvToList y.2 t5.permute).1.length
    · simpa [short] using h
    · simp only [short, ↓reduceIte] at h ⊢
      cases dec : wordSemDecStack (wl.drop (wordSemEnvToList y.2 t5.permute).1.length) t5.stack with
      | none => simpa [dec] using h
      | some stack =>
        simp only [dec, popEnv] at h ⊢
        cases hm : t5.stackMax <;>
          cases hs : wordSemStackSize (.stackFrame t5.localsSize (sptToAList y.1)
            (wordSemEnvToList y.2 t5.permute).1 none :: t5.stack) <;>
          simpa [wordSemOptionMax, wordSemOptionAdd, hm, hs, Nat.max_assoc, Nat.max_self] using h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
