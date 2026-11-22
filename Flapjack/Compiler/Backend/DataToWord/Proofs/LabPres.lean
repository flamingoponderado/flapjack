module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Labels
public import Flapjack.Compiler.Backend.DataToWord.Total
public import Flapjack.Compiler.Backend.DataToWord.Proofs.NoShareInst

@[expose] public section

set_option autoImplicit false

/-! Label preservation of data-to-word compilation
(`data_to_wordProofScript.sml` lines 1991-2040). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- The label shape returned by `comp` from counter `l` (Flapjack
infrastructure for `data_to_word_lab_pres_lem`). -/
def LabPres {width : Nat} (secn l : Nat) (r : WordLangProgHOL (BitVec width) × Nat) : Prop :=
  l ≤ r.2 ∧ (∀ q ∈ extractLabels r.1, q.1 = secn ∧ l ≤ q.2 ∧ q.2 < r.2) ∧
    (extractLabels r.1).Nodup

/-- The unfolding set for the assignment label analysis. -/
local macro "lab_simp" : tactic => `(tactic| simp [LabPres, extractLabels, extractLabels_wordListSeq, extractLabels_storeEach,
      extractLabels_memEqList, extractLabels_storeAnyConsts, extractLabels_wordOp64On32,
      extractLabels_wordShift64On32,
      assignConst, assignSetGlobalsPtr, assignGlobal, assignSetGlobal, assignBuild,
      assignFromList, assignListAppend, assignBoolNot, assignLengthBlock, assignLenEq,
      assignTagLenEq, assignTagEq, assignBoolTest, assignEqual, assignEqualConst,
      assignLessConstSmall, assignLess, assignLessEq, assignAdd, assignSub, assignAddSub,
      assignMult, assignDiv, assignMod, assignWordTest, assignFpCmp, assignFpBop, assignFpUop,
      assignFpTop, assignWordOpW8, assignWordOpW64, assignWordShiftW8, assignWordShiftW64,
      assignWordFromWord, assignWordFromInt, assignWordToInt, assignBoundsCheckBlock,
      assignCons, assignConsExtend, assignElemAt, assignFfi, assignBoundsCheckArray,
      assignStringCmp, assignBoundsCheckByte, assignRefByte, assignEl, assignLength,
      assignLengthByte, assignDerefByte, assignUpdateByte, assignRef, assignRefArray,
      assignCopyByte, assignConfigGC, assignXorByte, assignMutCons, assignFinaliseCons,
      assignUpdate, assignAllocThunk, assignUpdateThunk, assignInstall,
      setBool, assignCmp, boolResult, silentFfi, giveUp, bignumHalt, allocVar,
      loadWord64, loadBignum, writeWord64, writeWord64On32, writeWord32On32,
      maxoutBitsCode, makePtrBitsCode, fpOperand, fpLoads, fpResult])

/-- Assignment code labels lie in the counter range it consumes (Flapjack infrastructure; the `Assign` case of `data_to_word_lab_pres_lem`). -/
theorem compileAssign_labPres {width : Nat} [NeZero width] (conf : Config) (secn l dest : Nat)
    (op : ClosLang.Op) (args : List Nat) (names : Option NumSet) :
    LabPres secn l (compileAssign (width := width) conf secn l dest op args names) := by
  unfold compileAssign
  split <;> (try simp only [arg1, arg2, arg3, arg4]) <;> (repeat' split) <;>
    (try lab_simp) <;> (repeat' split) <;> (try lab_simp) <;> (repeat' split) <;>
    (try lab_simp) <;> omega

/-- Force code labels lie in the counter range it consumes (Flapjack infrastructure; the `Force` case of `data_to_word_lab_pres_lem`). -/
theorem forceThunk_labPres {width : Nat} [NeZero width] {α : Type} (conf : Config)
    (secn l : Nat) (ret : Option (Nat × Spt α)) (loc v : Nat) :
    LabPres secn l (forceThunk (width := width) conf secn l ret loc v) := by
  unfold forceThunk
  (repeat' split) <;> (try lab_simp) <;> (repeat' split) <;> (try lab_simp) <;> omega

/-- Concatenating label lists from consecutive counter ranges (Flapjack
infrastructure). -/
theorem labRange_append (secn l l1 l2 : Nat) (L1 L2 : List (Nat × Nat))
    (h1 : ∀ q ∈ L1, q.1 = secn ∧ l ≤ q.2 ∧ q.2 < l1) (n1 : L1.Nodup)
    (h2 : ∀ q ∈ L2, q.1 = secn ∧ l1 ≤ q.2 ∧ q.2 < l2) (n2 : L2.Nodup) (hl : l ≤ l1)
    (hl2 : l1 ≤ l2) :
    (∀ q ∈ L1 ++ L2, q.1 = secn ∧ l ≤ q.2 ∧ q.2 < l2) ∧ (L1 ++ L2).Nodup := by
  refine ⟨fun q hq => ?_, List.nodup_append.2 ⟨n1, n2, fun a ha b hb hab => ?_⟩⟩
  · rcases List.mem_append.1 hq with hq | hq
    · have := h1 q hq; exact ⟨this.1, this.2.1, by omega⟩
    · have := h2 q hq; exact ⟨this.1, by omega, this.2.2⟩
  · subst hab; have := h1 a ha; have := h2 a hb; omega

/-- Label shape of the option-valued traversal (Flapjack infrastructure for `data_to_word_lab_pres_lem`). -/
theorem compileControl?_labPres {width : Nat} [NeZero width] (conf : Config) (secn l : Nat)
    (p : DataLang.Prog) :
    ∀ r, compileControl? (width := width) conf secn l p = some r → LabPres secn l r := by
  fun_induction compileControl? (width := width) conf secn l p with
  | case6 l x y ihx ihy | case7 l _ x y ihx ihy =>
    intro r hr
    rcases hx : compileControl? (width := width) conf secn l x with _ | ⟨px, l1⟩
    · simp [hx] at hr
    rcases hy : compileControl? (width := width) conf secn l1 y with _ | ⟨py, l2⟩
    · simp [hx, hy] at hr
    simp [hx, hy] at hr
    subst hr
    obtain ⟨a1, b1, c1⟩ := ihx _ hx
    obtain ⟨a2, b2, c2⟩ := ihy l1 _ hy
    have := labRange_append secn l l1 l2 _ _ b1 c1 b2 c2 a1 a2
    exact ⟨by simp only at a1 a2 ⊢; omega, by simpa [extractLabels] using this.1,
      by simpa [extractLabels] using this.2⟩
  | case13 l ns names target args n handler ih =>
    intro r hr
    rcases hh : compileControl? (width := width) conf secn (l + 2) handler with _ | ⟨ph, l1⟩
    · simp [hh] at hr
    simp [hh] at hr
    subst hr
    obtain ⟨a1, b1, c1⟩ := ih _ hh
    refine ⟨by simp only at a1 ⊢; omega, ?_, ?_⟩
    · intro q hq
      simp only [extractLabels, List.mem_append, List.mem_cons] at hq
      rcases hq with ((rfl | rfl | hq) | hq) | hq
      · dsimp only at a1 ⊢; omega
      · dsimp only at a1 ⊢; omega
      · simp at hq
      · simp at hq
      · have := b1 q hq; simp only at this ⊢; omega
    · simp only [extractLabels, List.append_nil, List.cons_append, List.nil_append]
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, c1⟩⟩
      · intro hm
        rcases List.mem_cons.1 hm with hm | hm
        · simp at hm
        · have := b1 _ hm; simp only at this; omega
      · intro hm; have := b1 _ hm; simp only at this; omega
  | case9 l dest op args names =>
    intro r hr; simp only [Option.some.injEq] at hr; subst hr
    exact compileAssign_labPres conf secn l dest op args names
  | case10 l ret loc v =>
    intro r hr; simp only [Option.some.injEq] at hr; subst hr
    exact forceThunk_labPres conf secn l ret loc v
  | _ =>
    intro r hr; simp only [Option.some.injEq] at hr; subst hr
    (try lab_simp) <;> (repeat' split) <;> (try lab_simp) <;> omega

/-- Exact HOL `data_to_word_lab_pres_lem` (`data_to_wordProofScript.sml:1990-2040`).
`comp` is the reviewed `compileControl`; `EVERY (λ(l1,l2). ...)` is a membership
forall over the label pairs and `ALL_DISTINCT` is `List.Nodup`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_to_word_lab_pres_lem"
  (words_as_type_indexed_bitvec)]
theorem dataToWord_labPresLem {width : Nat} [NeZero width] :
    ∀ (c : Config) (n l : Nat) (p : DataLang.Prog), l ≠ 0 →
      let (cp, l') : WordLangProgHOL (BitVec width) × Nat := compileControl c n l p
      l ≤ l' ∧ (∀ q ∈ extractLabels cp, q.1 = n ∧ l ≤ q.2 ∧ q.2 < l') ∧
        (extractLabels cp).Nodup := by
  intro c n l p _
  have h := compileControl?_labPres (width := width) c n l p _ (compileControl_option c n l p)
  rcases hc : compileControl (width := width) c n l p with ⟨cp, l'⟩
  rw [hc] at h
  exact h

/-- The unfolding set for the assignment `no_share_inst` analysis. -/
local macro "share_simp" : tactic => `(tactic| simp [noShareInstSubprogsHOL,
      notCreatedSubprogsWithMemOp, wordListSeq,
      assignConst, assignSetGlobalsPtr, assignGlobal, assignSetGlobal, assignBuild,
      assignFromList, assignListAppend, assignBoolNot, assignLengthBlock, assignLenEq,
      assignTagLenEq, assignTagEq, assignBoolTest, assignEqual, assignEqualConst,
      assignLessConstSmall, assignLess, assignLessEq, assignAdd, assignSub, assignAddSub,
      assignMult, assignDiv, assignMod, assignWordTest, assignFpCmp, assignFpBop, assignFpUop,
      assignFpTop, assignWordOpW8, assignWordOpW64, assignWordShiftW8, assignWordShiftW64,
      assignWordFromWord, assignWordFromInt, assignWordToInt, assignBoundsCheckBlock,
      assignCons, assignConsExtend, assignElemAt, assignFfi, assignBoundsCheckArray,
      assignStringCmp, assignBoundsCheckByte, assignRefByte, assignEl, assignLength,
      assignLengthByte, assignDerefByte, assignUpdateByte, assignRef, assignRefArray,
      assignCopyByte, assignConfigGC, assignXorByte, assignMutCons, assignFinaliseCons,
      assignUpdate, assignAllocThunk, assignUpdateThunk, assignInstall,
      setBool, assignCmp, boolResult, silentFfi, giveUp, bignumHalt, allocVar,
      loadWord64, loadBignum, writeWord64, writeWord64On32, writeWord32On32,
      wordOp64On32, wordShift64On32,
      maxoutBitsCode, makePtrBitsCode, fpOperand, fpLoads, fpResult, forceThunk])

/-- Assignment code has no `ShareInst` (Flapjack infrastructure; the `Assign` case of `comp_no_share_inst`). -/
theorem compileAssign_noShareInst {width : Nat} [NeZero width] (conf : Config)
    (secn l dest : Nat) (op : ClosLang.Op) (args : List Nat) (names : Option NumSet) :
    noShareInstSubprogsHOL (compileAssign (width := width) conf secn l dest op args names).1 =
      true := by
  unfold compileAssign
  split <;> (try simp only [arg1, arg2, arg3, arg4]) <;> (repeat' split) <;>
    (try share_simp) <;> (repeat' split) <;> (try share_simp) <;>
    first
      | exact storeAnyConsts_noShareInst _ _ _ _ _
      | exact memEqList_noShareInst _ _
      | exact storeEach_noShareInst _ _ _
      | (refine ⟨?_, ?_⟩ <;> first
          | exact storeAnyConsts_noShareInst _ _ _ _ _
          | exact memEqList_noShareInst _ _
          | exact storeEach_noShareInst _ _ _)

/-- The option-valued traversal produces no `ShareInst` (Flapjack infrastructure for `comp_no_share_inst`). -/
theorem compileControl?_noShareInst {width : Nat} [NeZero width] (conf : Config)
    (secn l : Nat) (p : DataLang.Prog) :
    ∀ r, compileControl? (width := width) conf secn l p = some r →
      noShareInstSubprogsHOL r.1 = true := by
  fun_induction compileControl? (width := width) conf secn l p with
  | case6 l x y ihx ihy | case7 l _ x y ihx ihy =>
    intro r hr
    rcases hx : compileControl? (width := width) conf secn l x with _ | ⟨px, l1⟩
    · simp [hx] at hr
    rcases hy : compileControl? (width := width) conf secn l1 y with _ | ⟨py, l2⟩
    · simp [hx, hy] at hr
    simp [hx, hy] at hr
    subst hr
    have a := ihx _ hx
    have b := ihy l1 _ hy
    simp only [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] at a b ⊢
    simp [a, b]
  | case13 l ns names target args n handler ih =>
    intro r hr
    rcases hh : compileControl? (width := width) conf secn (l + 2) handler with _ | ⟨ph, l1⟩
    · simp [hh] at hr
    simp [hh] at hr
    subst hr
    have a := ih _ hh
    simp only [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp] at a ⊢
    simp [a]
  | case9 l dest op args names =>
    intro r hr; simp only [Option.some.injEq] at hr; subst hr
    exact compileAssign_noShareInst conf secn l dest op args names
  | _ =>
    intro r hr; simp only [Option.some.injEq] at hr; subst hr
    (try share_simp) <;> (repeat' split) <;> (try share_simp)

/-- Exact HOL `comp_no_share_inst` (`data_to_wordProofScript.sml:2116-2172`).
HOL `no_share_inst` is the reviewed Boolean `noShareInstSubprogsHOL`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "comp_no_share_inst"
  (words_as_type_indexed_bitvec)]
theorem comp_noShareInst {width : Nat} [NeZero width] :
    ∀ (c : Config) (secn l : Nat) (prog : DataLang.Prog)
      (prog' : WordLangProgHOL (BitVec width)) (l' : Nat),
      compileControl c secn l prog = (prog', l') → noShareInstSubprogsHOL prog' = true := by
  intro c secn l prog prog' l' h
  have := compileControl?_noShareInst (width := width) c secn l prog _
    (compileControl_option c secn l prog)
  rw [h] at this
  exact this

end Flapjack.Compiler.Backend.DataToWord.Proofs
