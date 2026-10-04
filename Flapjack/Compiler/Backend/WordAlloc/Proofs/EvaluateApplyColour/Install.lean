import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.CutState

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace InstallWitnesses

/-- Canonical imported state carrier roundtrip for this case. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end InstallWitnesses

/-- HOL evaluate_apply_colour Install case (2133-2162), with the original
three premises and full existential result; successful installation is derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_Install {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen : Nat) (n1 n2 : NumSet) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.install ptr len dptr dlen (n1, n2) : WordLangProgHOL (BitVec width)) live lt ∧
        wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.install ptr len dptr dlen (n1, n2) : WordLangProgHOL (BitVec width)) live lt))
          st.locals cst.locals →
      applyColourPost f (.install ptr len dptr dlen (n1, n2) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour]
  rw [evaluate] at he ⊢
  rw [evaluate]
  cases hcut : wordSemCutEnv (n1, n2) st.locals with
  | none => simp [hcut] at he
  | some env =>
    have cutLive (k : Nat) (hk : sptDomain n1 k ∨ sptDomain n2 k) :
        sptDomain (getLive (.install ptr len dptr dlen (n1, n2) : WordLangProgHOL (BitVec width)) live lt) k := by
      simp only [getLive, sptListInsert, sptDomain_ins, sptDomain_uni]
      exact Or.inr (Or.inr (Or.inr (Or.inr hk)))
    have hinj : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) →
        (sptDomain n1 b ∨ sptDomain n2 b) → f a = f b → a = b := by
      simp only [colouringOk] at hok
      exact fun a b ha hb heq => hok.1 a b (cutLive a ha) (cutLive b hb) heq
    obtain ⟨target, ht, _, hlocals, _, hdomain⟩ :=
      cutEnvLemma n1 n2 st.locals cst.locals env f
        ⟨hinj, hcut, slrMono hr (fun k hk => cutLive k hk)⟩
    rw [ht]
    simp only [hcut] at he
    split at he
    · rename_i w1 w2 w3 w4 hp hl hdp hdl
      have read (r : Nat) (v : WordLocW width)
          (hm : sptDomain (getLive (.install ptr len dptr dlen (n1, n2) : WordLangProgHOL (BitVec width)) live lt) r)
          (hv : getVar r st = some v) : getVar (f r) cst = some v :=
        strongLocalsRelGetVar f _ st cst r v ⟨hr, hm, hv⟩
      have a := read ptr (.word w1) (by simp [getLive, sptListInsert, sptDomain_ins]) hp
      have b := read len (.word w2) (by simp [getLive, sptListInsert, sptDomain_ins]) hl
      have c := read dptr (.word w3) (by simp [getLive, sptListInsert, sptDomain_ins]) hdp
      have d := read dlen (.word w4) (by simp [getLive, sptListInsert, sptDomain_ins]) hdl
      rw [a, b, c, d]
      have ho : cst.compileOracle = st.compileOracle := by simp_all [wordStateEqRel]
      have hc : cst.compile = st.compile := by simp_all [wordStateEqRel]
      have hcb : cst.codeBuffer = st.codeBuffer := by simp_all [wordStateEqRel]
      have hdb : cst.dataBuffer = st.dataBuffer := by simp_all [wordStateEqRel]
      rw [ho, hc, hcb, hdb]
      dsimp only at he ⊢
      split at he
      · split at he
        · split at he
          · rename_i hchecks
            simp only [if_pos hchecks]
            refine ⟨trivial, ?_, ?_⟩
            · simp_all [wordStateEqRel]
            · simp only [applyColourLocals]
              apply strongLocalsRelInsert f ptr (sptDomain live) env target
              refine ⟨?_, ?_⟩
              · simp only [colouringOk, getWrites] at hok
                exact injInsertOfIset hok.2
              · apply strongLocalsRelExtendAux f _ _ env target
                exact ⟨fun k hk => by simpa only [hdomain] using hk, hlocals⟩
          · contradiction
        · contradiction
      · contradiction
    · contradiction

end Flapjack.WordAlloc
