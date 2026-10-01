import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

/-!
# `evaluate_apply_colour` `ShareInst` case

The `ShareInst` case of `word_allocProofScript.sml:1105-1130`
`evaluate_apply_colour` (`Resume evaluate_apply_colour[ShareInst]`,
`word_allocProofScript.sml:2207` onward). The shared-memory operations read
only the related `sh_mdomain` and `ffi` fields; stores additionally read the
live stored variable and loads write the destination variable. The untagged
helpers below are Flapjack proof infrastructure for the tagged case.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateApplyColourShareInstWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateApplyColourShareInstWitnesses

open EvaluateApplyColourShareInstWitnesses

section ShareInstCase

variable {width : Nat} [NeZero width] {C F : Type}

/-- The common shape of the four shared-memory stores (Flapjack
infrastructure; each `sh_mem_store*` unfolds to it). -/
def shStoreGen (d : BitVec width) (cfg bytes : List (BitVec 8))
    (s : WordSemStateFiniteExact width C F) :
    Option (WordSemResult width) × WordSemStateFiniteExact width C F :=
  if s.shMdomain d then
    match callFFIHOL s.ffi (.sharedMem .mappedWrite) cfg bytes with
    | .final outcome => (some (.finalFfi outcome), flushState true s)
    | .ret newFfi _ => (none, { s with ffi := newFfi })
  else (some .error, s)

/-- `word_state_eq_rel` survives an equal FFI update (Flapjack infrastructure). -/
theorem wsrFfi {s t : WordSemStateFiniteExact width C F} (x : HolFfiState F)
    (h : wordStateEqRel s t) : wordStateEqRel { s with ffi := x } { t with ffi := x } := by
  unfold wordStateEqRel at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18, h19,
    h20, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl, h16, h17, h18, h19,
    h20, h21⟩

/-- `sh_mdomain` is related (Flapjack infrastructure). -/
theorem wsr_shMdomain {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t) :
    t.shMdomain = s.shMdomain := by
  unfold wordStateEqRel at h; exact h.2.2.2.2.2.2.2.2.2.1

/-- `ffi` is related (Flapjack infrastructure). -/
theorem wsr_ffi {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t) :
    t.ffi = s.ffi := by
  unfold wordStateEqRel at h; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Simulation of a shared-memory store between related states. -/
theorem shStoreGen_sim {st cst : WordSemStateFiniteExact width C F} (hs : wordStateEqRel st cst)
    (f : Nat → Nat) (live : NumSet) (lt : List (NumSet × NumSet))
    (hl : strongLocalsRel f (sptDomain live) st.locals cst.locals)
    (d : BitVec width) (cfg bytes : List (BitVec 8))
    (he : (shStoreGen d cfg bytes st).1 ≠ some .error) :
    (shStoreGen d cfg bytes st).1 = (shStoreGen d cfg bytes cst).1 ∧
      wordStateEqRel (shStoreGen d cfg bytes st).2 (shStoreGen d cfg bytes cst).2 ∧
      applyColourLocals f live lt (shStoreGen d cfg bytes st).1
        (shStoreGen d cfg bytes st).2.locals (shStoreGen d cfg bytes cst).2.locals := by
  unfold shStoreGen at he ⊢
  by_cases hd : st.shMdomain d = true
  · have hd' : cst.shMdomain d = true := by rw [wsr_shMdomain hs]; exact hd
    rw [if_pos hd, if_pos hd', wsr_ffi hs]
    cases callFFIHOL st.ffi (.sharedMem .mappedWrite) cfg bytes with
    | final outcome => exact ⟨rfl, wsrFlush true hs, rfl⟩
    | ret newFfi _ => exact ⟨rfl, wsrFfi _ hs, hl⟩
  · rw [if_neg hd] at he; exact absurd rfl he

/-- Simulation of `sh_mem_set_var` for a load result shared by related states. -/
theorem shMemSetVar_sim {st cst : WordSemStateFiniteExact width C F} (hs : wordStateEqRel st cst)
    (f : Nat → Nat) (live : NumSet) (lt : List (NumSet × NumSet)) (v : Nat)
    (hinj : ∀ a b, (a = v ∨ sptDomain live a) → (b = v ∨ sptDomain live b) → f a = f b → a = b)
    (hl : strongLocalsRel f (fun k => sptDomain live k ∧ k ≠ v) st.locals cst.locals)
    (o : Option (HolFfiResult F))
    (he : (shMemSetVar (rw := width) o v st).1 ≠ some .error) :
    (shMemSetVar (rw := width) o v st).1 = (shMemSetVar (rw := width) o (f v) cst).1 ∧
      wordStateEqRel (shMemSetVar (rw := width) o v st).2
        (shMemSetVar (rw := width) o (f v) cst).2 ∧
      applyColourLocals f live lt (shMemSetVar (rw := width) o v st).1
        (shMemSetVar (rw := width) o v st).2.locals
        (shMemSetVar (rw := width) o (f v) cst).2.locals := by
  cases o with
  | none => exact absurd rfl he
  | some r =>
  cases r with
  | final outcome => exact ⟨rfl, wsrFlush true hs, rfl⟩
  | ret nf bytes =>
    refine ⟨rfl, wsrLocals _ _ (wsrFfi nf hs), ?_⟩
    exact strongLocalsRelInsert f v (sptDomain live) _ _ _ ⟨hinj, hl⟩

end ShareInstCase

/-- HOL `evaluate_apply_colour`, `ShareInst` case (`Resume
evaluate_apply_colour[ShareInst]`, `word_allocProofScript.sml:2207` onward): the
three HOL premises at `ShareInst op v exp` and the HOL existential conclusion;
no sub-program, so no induction hypothesis and no extra premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_ShareInst {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width)) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.shareInst op v exp : WordLangProgHOL (BitVec width)) live lt ∧
        wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.shareInst op v exp : WordLangProgHOL (BitVec width))
          live lt)) st.locals cst.locals →
      applyColourPost f (.shareInst op v exp : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  rw [applyColour.eq_def]
  dsimp only
  rw [evaluate] at he ⊢
  rw [evaluate]
  have hsub : ∀ k, sptDomain (getLiveExp exp) k →
      sptDomain (getLive (.shareInst op v exp : WordLangProgHOL (BitVec width)) live lt) k := by
    intro k hk
    simp only [getLive]
    split <;> exact (sptDomain_uni _ _ k).mpr (Or.inl hk)
  cases hw : wordExp st exp with
  | none => rw [hw] at he; exact absurd rfl he
  | some x =>
  cases x with
  | loc _ _ => rw [hw] at he; exact absurd rfl he
  | word ad =>
  have hcw := applyColourExpLemma st exp cst f (.word ad) ⟨hw, hs, slrMono hr hsub⟩
  rw [hcw]
  rw [hw] at he
  dsimp only at he ⊢
  have hlive : ∀ k, sptDomain live k → (op = .store ∨ op = .store8 ∨ op = .store16 ∨
      op = .store32) →
      sptDomain (getLive (.shareInst op v exp : WordLangProgHOL (BitVec width)) live lt) k := by
    intro k hk hop
    simp only [getLive, if_pos hop]
    exact (sptDomain_uni _ _ k).mpr (Or.inr ((sptDomain_ins _ _ _ k).mpr (Or.inr hk)))
  have hvlive : (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) →
      sptDomain (getLive (.shareInst op v exp : WordLangProgHOL (BitVec width)) live lt) v := by
    intro hop
    simp only [getLive, if_pos hop]
    exact (sptDomain_uni _ _ v).mpr (Or.inr ((sptDomain_ins _ _ _ v).mpr (Or.inl rfl)))
  have hdel : ¬ (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) →
      strongLocalsRel f (fun k => sptDomain live k ∧ k ≠ v) st.locals cst.locals := by
    intro hop
    refine slrMono hr (fun k hk => ?_)
    simp only [getLive, if_neg hop]
    exact (sptDomain_uni _ _ k).mpr (Or.inr ((sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩))
  have hinjL : ¬ (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) →
      ∀ a b, (a = v ∨ sptDomain live a) → (b = v ∨ sptDomain live b) → f a = f b → a = b := by
    intro hop a b ha hb hab
    have hi := hok.2
    refine hi a b ?_ ?_ hab
    · rw [sptDomain_uni]
      rcases ha with ha | ha
      · left; subst ha; cases op <;> simp_all [getWrites, sptDomain_ins]
      · exact Or.inr ha
    · rw [sptDomain_uni]
      rcases hb with hb | hb
      · left; subst hb; cases op <;> simp_all [getWrites, sptDomain_ins]
      · exact Or.inr hb
  have hstoreCase : (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) →
      ∀ w, getVar v st = some (.word w) → getVar (f v) cst = some (.word w) := fun hop w h =>
    strongLocalsRelGetVar f _ st cst v _ ⟨hr, hvlive hop, h⟩
  have hlv : (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) →
      strongLocalsRel f (sptDomain live) st.locals cst.locals :=
    fun hop => slrMono hr (fun k hk => hlive k hk hop)
  cases op
  case load =>
    have hL : shMemLoad ad cst = shMemLoad ad st := by
      unfold shMemLoad; rw [wsr_shMdomain hs, wsr_ffi hs]
    simp only [shareInst] at he ⊢
    rw [hL]
    exact shMemSetVar_sim hs f live lt v (hinjL (by simp)) (hdel (by simp)) _ he
  case load8 =>
    have hL : shMemLoadByte ad cst = shMemLoadByte ad st := by
      unfold shMemLoadByte; rw [wsr_shMdomain hs, wsr_ffi hs]
    simp only [shareInst] at he ⊢
    rw [hL]
    exact shMemSetVar_sim hs f live lt v (hinjL (by simp)) (hdel (by simp)) _ he
  case load16 =>
    have hL : shMemLoad16 ad cst = shMemLoad16 ad st := by
      unfold shMemLoad16; rw [wsr_shMdomain hs, wsr_ffi hs]
    simp only [shareInst] at he ⊢
    rw [hL]
    exact shMemSetVar_sim hs f live lt v (hinjL (by simp)) (hdel (by simp)) _ he
  case load32 =>
    have hL : shMemLoad32 ad cst = shMemLoad32 ad st := by
      unfold shMemLoad32; rw [wsr_shMdomain hs, wsr_ffi hs]
    simp only [shareInst] at he ⊢
    rw [hL]
    exact shMemSetVar_sim hs f live lt v (hinjL (by simp)) (hdel (by simp)) _ he
  all_goals
    simp only [shareInst] at he ⊢
    cases hv : getVar v st with
    | none => rw [hv] at he; exact absurd rfl he
    | some x =>
    cases x with
    | loc _ _ => rw [hv] at he; exact absurd rfl he
    | word w =>
    rw [hv] at he
    rw [hstoreCase (by simp) w hv]
    dsimp only at he ⊢
    exact shStoreGen_sim hs f live lt (hlv (by simp)) _ _ _ he

end Flapjack.WordAlloc
