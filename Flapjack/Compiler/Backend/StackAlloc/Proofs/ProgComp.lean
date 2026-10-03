import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Submap
import Flapjack.Compiler.Backend.Semantics.StackSem.Control
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-!
# `stack_allocProof` code-lookup lemmas used by `comp_correct`

`get_var_imm_case`, `prog_comp_lemma`, `FST_prog_comp`,
`lookup_IMP_lookup_compile`, `find_code_IMP_lookup`, `find_code_regs_SUBMAP`,
`get_labels_comp`, `loc_check_compile`, `ALOOKUP_prog_comp` and
`lookup_fromAList_prog_comp` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml`, over the exact
`HolProg width` carrier, the native StackSem state and the `Spt` code tree.
HOL `fromAList`/`toAList`/`ALOOKUP` on numeric keys are `sptFromAList`,
`sptToAList` and `sptAListLookup`; label sets are predicates.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang

namespace ProgCompSupport

/-- Canonical codec for the imported owning StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- HOL `ALOOKUP_toAList` on the `Spt` carrier (external HOL library). -/
theorem sptAListLookup_sptToAList {α : Type} (key : Nat) (tree : Spt α) :
    sptAListLookup key (sptToAList tree) = sptLookup key tree := by
  rw [← sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList]

/-- First-match lookup through `MAP prog_comp` (HOL `ALOOKUP_MAP_2` with
`prog_comp_lemma`). -/
theorem sptAListLookup_map_progComp {width : Nat} [NeZero width] (key : Nat) :
    ∀ xs : List (Nat × HolProg width),
      sptAListLookup key (xs.map progComp) =
        (sptAListLookup key xs).map (fun p => (comp key (nextLabHOL p 2) p).1)
  | [] => rfl
  | (k, p) :: xs => by
      by_cases h : key = k
      · subst h; simp [sptAListLookup, progComp]
      · simp [sptAListLookup, progComp, h, sptAListLookup_map_progComp key xs]

end ProgCompSupport

open ProgCompSupport

/-- Exact HOL `get_var_imm_case` (`stack_allocProofScript.sml:66-73`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "get_var_imm_case"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_var_imm_case {width : Nat} [NeZero width] {C F : Type}
    {ri : WordRegImm (BitVec width)} {s : StackSemStateFiniteExact width C F} :
    StackSemStateOps.getVarImm ri s =
      match ri with
      | .reg n => StackSemStateOps.getVar n s
      | .imm w => some (.word w) := by
  cases ri <;> rfl

/-- Exact HOL `prog_comp_lemma` (`stack_allocProofScript.sml:75-79`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "prog_comp_lemma"
  (words_as_type_indexed_bitvec)]
theorem prog_comp_lemma {width : Nat} [NeZero width] :
    (progComp : Nat × HolProg width → Nat × HolProg width) =
      fun np => (np.1, (comp np.1 (nextLabHOL np.2 2) np.2).1) := by
  funext np
  obtain ⟨n, p⟩ := np
  rfl

/-- Exact HOL `FST_prog_comp` (`stack_allocProofScript.sml:81-85`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "FST_prog_comp"
  (words_as_type_indexed_bitvec)]
theorem FST_prog_comp {width : Nat} [NeZero width] {pp : Nat × HolProg width} :
    (progComp pp).1 = pp.1 := by
  obtain ⟨n, p⟩ := pp
  rfl

/-- Exact HOL `lookup_IMP_lookup_compile` (`stack_allocProofScript.sml:87-98`):
a non-stub function of the source code is found, compiled by `comp`, in the
compiled code. HOL's free `dest s x c` are implicit. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lookup_IMP_lookup_compile"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem lookup_IMP_lookup_compile {width : Nat} [NeZero width] {C F : Type}
    {dest : Nat} {s : StackSemStateFiniteExact width C F} {x : HolProg width}
    {c : DataToWord.Config} :
    sptLookup dest s.code = some x ∧ dest ≠ gcStubLocation →
    ∃ m1 n1, sptLookup dest (sptFromAList (compile c (sptToAList s.code))) =
      some (comp m1 n1 x).1 := by
  rintro ⟨hl, hd⟩
  refine ⟨dest, nextLabHOL x 2, ?_⟩
  rw [sptLookup_sptFromAList, compile, stubs]
  simp [sptAListLookup, hd, sptAListLookup_map_progComp, sptAListLookup_sptToAList, hl]

/-- Exact HOL `find_code_IMP_lookup` (`stack_allocProofScript.sml:5137-5144`):
a successful `find_code` is a lookup at one fixed key. The code payload and the
register key type keep HOL's polymorphism. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "find_code_IMP_lookup"
  (fmap_as_finite_support_relation := [regs]) (words_as_type_indexed_bitvec)]
theorem find_code_IMP_lookup {width : Nat} [NeZero width] {κ α : Type}
    {dest : Sum Nat κ} {regs : HolFiniteMapExact κ (WordLocW width)} {s : Spt α} {x : α} :
    StackSemControl.findCode dest regs s = some x →
    ∃ k, sptLookup k s = some x ∧
      (StackSemControl.findCode dest regs : Spt α → Option α) = sptLookup k := by
  intro h
  cases dest with
  | inl k => exact ⟨k, h, rfl⟩
  | inr r =>
      simp only [StackSemControl.findCode] at h
      split at h
      · rename_i k hk
        refine ⟨k, h, ?_⟩
        funext t
        simp [StackSemControl.findCode, hk]
      · simp at h

/-- Exact HOL `find_code_regs_SUBMAP` (`stack_allocProofScript.sml:5159-5168`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "find_code_regs_SUBMAP"
  (fmap_as_finite_support_relation := [r1, r2]) (words_as_type_indexed_bitvec)]
theorem find_code_regs_SUBMAP {width : Nat} [NeZero width] {κ α : Type}
    {r1 : HolFiniteMapExact κ (WordLocW width)} {r2 : HolFiniteMapExact κ (WordLocW width)}
    {dest : Sum Nat κ} {c : Spt α} {x : α} :
    r1.submap r2 ∧ StackSemControl.findCode dest r1 c = some x →
    StackSemControl.findCode dest r2 c = some x := by
  rintro ⟨hs, h⟩
  cases dest with
  | inl k => exact h
  | inr r =>
      simp only [StackSemControl.findCode] at h ⊢
      split at h
      · rename_i k hk
        rw [hs _ _ hk]
        exact h
      · simp at h

/-- Exact HOL `get_labels_comp` (`stack_allocProofScript.sml:5170-5180`):
`comp` keeps every label of its input program. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "get_labels_comp"
  (words_as_type_indexed_bitvec)]
theorem get_labels_comp {width : Nat} [NeZero width] :
    ∀ (n p : Nat) (e : HolProg width) (l : Nat × Nat),
      StackSem.getLabelsExact e l → StackSem.getLabelsExact (comp n p e).1 l
  | n, p, .seq a b, l, hl => by
      rw [StackSem.getLabelsExact] at hl
      simp only [comp]
      rw [StackSem.getLabelsExact]
      rcases hl with hl | hl
      · exact Or.inl (get_labels_comp n p a l hl)
      · exact Or.inr (get_labels_comp n _ b l hl)
  | n, p, .ite cmp r ri a b, l, hl => by
      rw [StackSem.getLabelsExact] at hl
      simp only [comp]
      rw [StackSem.getLabelsExact]
      rcases hl with hl | hl
      · exact Or.inl (get_labels_comp n p a l hl)
      · exact Or.inr (get_labels_comp n _ b l hl)
  | n, p, .loop body, l, hl => by
      rw [StackSem.getLabelsExact] at hl
      simp only [comp]
      rw [StackSem.getLabelsExact]
      exact get_labels_comp n p body l hl
  | n, p, .call none dest handler, l, hl => by
      simp [StackSem.getLabelsExact] at hl
  | n, p, .call (some (rp, lr, l1, l2)) dest none, l, hl => by
      simp only [StackSem.getLabelsExact] at hl
      simp only [comp]
      rw [StackSem.getLabelsExact]
      rcases hl with hl | hl | hl
      · exact Or.inl hl
      · exact Or.inr (Or.inl (get_labels_comp n p rp l hl))
      · exact hl.elim
  | n, p, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), l, hl => by
      simp only [StackSem.getLabelsExact] at hl
      simp only [comp]
      rw [StackSem.getLabelsExact]
      rcases hl with hl | hl | hl | hl
      · exact Or.inl hl
      · exact Or.inr (Or.inl (get_labels_comp n p rp l hl))
      · exact Or.inr (Or.inr (Or.inl hl))
      · exact Or.inr (Or.inr (Or.inr (get_labels_comp n _ hp l hl)))
  | n, p, .skip, l, hl | n, p, .halt _, l, hl | n, p, .tick, l, hl | n, p, .ret _, l, hl
  | n, p, .raise _, l, hl | n, p, .break _, l, hl | n, p, .continue _, l, hl
  | n, p, .inst _, l, hl | n, p, .get _ _, l, hl | n, p, .set _ _, l, hl
  | n, p, .opCurrHeap _ _ _, l, hl | n, p, .alloc _, l, hl
  | n, p, .storeConsts _ _ _, l, hl | n, p, .jumpLower _ _ _, l, hl
  | n, p, .rawCall _, l, hl | n, p, .install _ _ _ _ _, l, hl
  | n, p, .shMemOp _ _ _, l, hl | n, p, .codeBufferWrite _ _, l, hl
  | n, p, .dataBufferWrite _ _, l, hl | n, p, .ffi _ _ _ _ _ _, l, hl
  | n, p, .locValue _ _ _, l, hl | n, p, .stackAlloc _, l, hl | n, p, .stackFree _, l, hl
  | n, p, .stackLoad _ _, l, hl | n, p, .stackLoadAny _ _, l, hl
  | n, p, .stackStore _ _, l, hl | n, p, .stackStoreAny _ _, l, hl
  | n, p, .stackGetSize _, l, hl | n, p, .stackSetSize _, l, hl
  | n, p, .bitmapLoad _ _, l, hl => by
      simp [StackSem.getLabelsExact] at hl
termination_by _ _ e => sizeOf e
decreasing_by all_goals simp_wf <;> omega

/-- Exact HOL `loc_check_compile` (`stack_allocProofScript.sml:5182-5204`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "loc_check_compile"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem loc_check_compile {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} {l1 l2 : Nat} {c : DataToWord.Config} :
    StackSem.locCheckExact s.code (l1, l2) ∧
      (∀ k prog, sptLookup k s.code = some prog → k ≠ gcStubLocation) →
    StackSem.locCheckExact (sptFromAList (compile c (sptToAList s.code))) (l1, l2) := by
  rintro ⟨hl, hk⟩
  have hlook : ∀ k prog, sptLookup k s.code = some prog →
      sptLookup k (sptFromAList (compile c (sptToAList s.code))) =
        some (comp k (nextLabHOL prog 2) prog).1 := by
    intro k prog hp
    rw [sptLookup_sptFromAList, compile, stubs]
    simp [sptAListLookup, hk k prog hp, sptAListLookup_map_progComp,
      sptAListLookup_sptToAList, hp]
  rcases hl with ⟨h0, hm⟩ | ⟨k, e, he, hlab⟩
  · obtain ⟨v, hv⟩ := (sptMem_iff_lookup _ _).1 hm
    exact Or.inl ⟨h0, (sptMem_iff_lookup _ _).2 ⟨_, hlook _ _ hv⟩⟩
  · exact Or.inr ⟨k, _, hlook k e he, get_labels_comp _ _ e _ hlab⟩

/-- Exact HOL `ALOOKUP_prog_comp` (`stack_allocProofScript.sml:5278-5285`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "ALOOKUP_prog_comp"
  (words_as_type_indexed_bitvec)]
theorem ALOOKUP_prog_comp {width : Nat} [NeZero width] :
    ∀ (xs : List (Nat × HolProg width)) (a : Nat) (y : HolProg width),
      sptAListLookup a xs = some y →
      sptAListLookup a (xs.map progComp) = some (comp a (nextLabHOL y 2) y).1 := by
  intro xs a y h
  simp [sptAListLookup_map_progComp, h]

/-- Exact HOL `lookup_fromAList_prog_comp` (`stack_allocProofScript.sml:5287-5295`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "lookup_fromAList_prog_comp"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem lookup_fromAList_prog_comp {width : Nat} [NeZero width] {C F : Type}
    {x : Nat} {s : StackSemStateFiniteExact width C F} {p : HolProg width} :
    sptLookup x s.code = some p →
    sptLookup x (sptFromAList ((sptToAList s.code).map progComp)) =
      some (comp x (nextLabHOL p 2) p).1 := by
  intro h
  rw [sptLookup_sptFromAList]
  exact ALOOKUP_prog_comp _ _ _ (by rw [sptAListLookup_sptToAList]; exact h)

end Flapjack.Compiler.Backend.StackAlloc
