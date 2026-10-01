import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.CutState

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace FfiWitnesses

/-- Canonical imported state carrier roundtrip for this case. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end FfiWitnesses

/-- HOL evaluate_apply_colour FFI case (2182-2205), with the original three
premises and full existential postcondition. Input reads and cut success are
derived from source execution and the scoped relation; no callback, successful
run, or target-result assumption is added. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_FFI {width : Nat} [NeZero width] {C F : Type}
    (ffiIndex : Flapjack.Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat)
    (n1 n2 : NumSet) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.ffi ffiIndex ptr1 len1 ptr2 len2 (n1, n2) : WordLangProgHOL (BitVec width)) live lt ∧
        wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.ffi ffiIndex ptr1 len1 ptr2 len2 (n1, n2) : WordLangProgHOL (BitVec width)) live lt))
          st.locals cst.locals →
      applyColourPost f (.ffi ffiIndex ptr1 len1 ptr2 len2 (n1, n2) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  rw [evaluate] at he ⊢
  rw [evaluate]
  split at he
  · rename_i w w2 w3 w4 hlen1 hptr1 hlen2 hptr2
    have read (r : Nat) (v : WordLocW width)
        (hm : sptDomain (getLive (.ffi ffiIndex ptr1 len1 ptr2 len2 (n1, n2) : WordLangProgHOL (BitVec width)) live lt) r)
        (hv : getVar r st = some v) : getVar (f r) cst = some v :=
      strongLocalsRelGetVar f _ st cst r v ⟨hr, hm, hv⟩
    have a := read len1 (.word w) (by simp [getLive, sptDomain_ins]) hlen1
    have b := read ptr1 (.word w2) (by simp [getLive, sptDomain_ins]) hptr1
    have c := read len2 (.word w3) (by simp [getLive, sptDomain_ins]) hlen2
    have d := read ptr2 (.word w4) (by simp [getLive, sptDomain_ins]) hptr2
    rw [a, b, c, d]
    cases hcut : wordSemCutEnv (n1, n2) st.locals with
    | none => simp [hcut] at he
    | some env =>
      have cutLive (k : Nat) (hk : sptDomain n1 k ∨ sptDomain n2 k) :
          sptDomain (getLive (.ffi ffiIndex ptr1 len1 ptr2 len2 (n1, n2) : WordLangProgHOL (BitVec width)) live lt) k := by
        simp only [getLive, sptDomain_ins, sptDomain_uni]
        exact Or.inr (Or.inr (Or.inr (Or.inr hk)))
      have hinj : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) →
          (sptDomain n1 b ∨ sptDomain n2 b) → f a = f b → a = b := by
        simp only [colouringOk] at hok
        exact fun a b ha hb heq => hok.1 a b (cutLive a ha) (cutLive b hb) heq
      obtain ⟨target, ht, _, hlocals, _, hdomain⟩ :=
        cutEnvLemma n1 n2 st.locals cst.locals env f
          ⟨hinj, hcut, slrMono hr (fun k hk => cutLive k hk)⟩
      have hlive : strongLocalsRel f (sptDomain live) env target :=
        strongLocalsRelExtendAux f _ _ env target
          ⟨fun k hk => by simpa only [hdomain] using hk, hlocals⟩
      rw [ht]
      simp only [hcut] at he
      dsimp only at he ⊢
      have hm : cst.memory = st.memory := by simp_all [wordStateEqRel]
      have hd : cst.mdomain = st.mdomain := by simp_all [wordStateEqRel]
      have hb : cst.be = st.be := by simp_all [wordStateEqRel]
      have hf : cst.ffi = st.ffi := by simp_all [wordStateEqRel]
      rw [hm, hd, hb, hf]
      cases hbytes : readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact st.memory st.mdomain st.be) with
      | none => simp [hbytes] at he
      | some bytes =>
        cases hbytes2 : readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact st.memory st.mdomain st.be) with
        | none => simp [hbytes, hbytes2] at he
        | some bytes2 =>
          dsimp only
          cases hcall : callFFIHOL st.ffi (.extCall ffiIndex) bytes bytes2 with
          | final outcome =>
            exact ⟨rfl, wsrFlush true hs, rfl⟩
          | ret newFfi newBytes =>
            refine ⟨rfl, ?_, hlive⟩
            simp_all [wordStateEqRel]
  · contradiction

end Flapjack.WordAlloc
