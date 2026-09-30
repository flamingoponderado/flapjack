import Flapjack.Compiler.Backend.Semantics.StackSem.Labels

/-! Kernel replay of the direct HOL observations in
`scripts/hol-probes/stacksem_labels_probe.out`. The loc_check positive
nonzero-offset case supplies the explicit existential code key and stored
program; its negative cases rule out missing keys and absent labels. -/

open Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSem

private abbrev TestProg := ProgM (BitVec 8)
private abbrev leaf : TestProg := .locValue 1 4 5
private abbrev ret : TestProg := .call (some (leaf, 13, 4, 5)) (.inl 0) none
private abbrev ret2 : TestProg := .call (some (leaf, 13, 7, 8)) (.inl 0) none
private abbrev loopBody : TestProg := .call (some (leaf, 13, 9, 10)) (.inl 0) none
private abbrev nested : TestProg := .call (some (leaf, 13, 16, 17)) (.inl 0) none
private abbrev retAndHandler : TestProg :=
  .call (some (leaf, 13, 11, 12)) (.inl 0) (some (ret2, 14, 15))
private abbrev handlerWithoutReturn : TestProg :=
  .call none (.inl 0) (some (ret2, 14, 15))

-- locvalue_label
example : ¬ getLabels leaf (4,5) := by simp [getLabels, leaf]
-- seq_left / seq_right
example : getLabels (.seq ret ret2) (4,5) := by simp [getLabels, ret, ret2, leaf]
example : getLabels (.seq ret ret2) (7,8) := by simp [getLabels, ret, ret2, leaf]
-- if_right
example : getLabels (.ite .equal 0 (.imm 0) ret ret2) (7,8) := by simp [getLabels, ret, ret2, leaf]
-- loop_body
example : getLabels (.loop loopBody) (9,10) := by simp [getLabels, loopBody, leaf]
-- call_return_direct / call_return_nested
example : getLabels (.call (some (leaf, 13, 11, 12)) (.inl 0) none) (11,12) := by simp [getLabels, leaf]
example : getLabels (.call (some (nested, 13, 11, 12)) (.inl 0) none) (16,17) := by simp [getLabels, nested, leaf]
-- call_handler_direct / call_handler_nested
example : getLabels retAndHandler (14,15) := by simp [getLabels, retAndHandler, ret2, leaf]
example : getLabels retAndHandler (7,8) := by simp [getLabels, retAndHandler, ret2, leaf]
-- HOL's handler arm is nested below a SOME return continuation.
example : ¬ getLabels handlerWithoutReturn (14,15) := by simp [getLabels, handlerWithoutReturn, ret2, leaf]
-- call_empty / halt_empty
example : ¬ getLabels (.call none (.inl 0) none : TestProg) (1,2) := by simp [getLabels]
example : ¬ getLabels (.halt 0 : TestProg) (1,2) := by simp [getLabels]

private abbrev code : Flapjack.Spt TestProg :=
  Flapjack.sptInsert 3 ret Flapjack.Spt.ln

-- loccheck_zero_present
example : locCheck code (3,0) := by
  exact Or.inl ⟨rfl, by simp [code, Flapjack.sptMem, Flapjack.sptDomain,
    Flapjack.sptLookup_sptInsert_same]⟩
-- loccheck_zero_absent
example : ¬ locCheck (Flapjack.Spt.ln : Flapjack.Spt TestProg) (3,0) := by
  simp [locCheck, Flapjack.sptMem, Flapjack.sptDomain, Flapjack.sptLookup]
-- loccheck_label_present: the nonzero-offset existential code lookup.
example : locCheck code (4,5) := by
  exact Or.inr ⟨3, ret,
    by simpa [code] using (Flapjack.sptLookup_sptInsert_same 3 ret Flapjack.Spt.ln),
    by simp [getLabels, ret, leaf]⟩
-- loccheck_label_absent
example : ¬ locCheck code (8,5) := by
  simp only [locCheck]
  intro h
  rcases h with ⟨hzero, _⟩ | ⟨key, program, hlookup, hlabel⟩
  · omega
  · by_cases hkey : key = 3
    · subst key
      rw [Flapjack.sptLookup_sptInsert_same] at hlookup
      cases hlookup
      simp [getLabels, ret, leaf] at hlabel
    · rw [Flapjack.sptLookup_sptInsert_ne 3 key ret Flapjack.Spt.ln hkey] at hlookup
      simp [Flapjack.sptLookup] at hlookup
