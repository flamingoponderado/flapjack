module

public import Flapjack.Pancake.Proofs.WordConvs.NotCreatedPasses
public import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.Sequence

@[expose] public section

namespace Flapjack.WordConvs
open Flapjack.Compiler.Backend.WordSimp

/-- Full original push-out-if label relation, including branch permutations.
The native auxiliary traversal preserves all label occurrences up to permutation;
no distinct-output or successful-pass premise is introduced. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_push_out_if"
  (words_as_type_indexed_bitvec)]
theorem labelsRelPushOutIf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    labelsRel (extractLabels program) (extractLabels (pushOutIf program)) := by
  unfold pushOutIf
  fun_induction pushOutIfAux program <;>
    simp_all only [extractLabels, List.nil_append, List.append_nil]
  all_goals first
    | exact labelsRel_refl _
    | solve | apply labelsRel_append <;> first | assumption | exact labelsRel_refl _
    | apply labelsRelAppendImp; apply labelsRel_append <;> assumption

/-- Original code-label containment of the push-out-if traversal: the emitted
program keeps only source labels, including every branch permutation. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_push_out_if" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_pushOutIf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (pushOutIf program) ⊆ getCodeLabelsHOL program := by
  unfold pushOutIf
  fun_induction pushOutIfAux program <;>
    try simp_all only [getCodeLabelsHOL]
  case case2 =>
    exact Set.Subset.refl _
  case case3 =>
    exact Set.Subset.refl _
  case case4 =>
    exact Set.Subset.refl _
  case case5 cmp r1 ri c1 c2 c1' c2' h2 h1 ih2 ih1 =>
    exact Set.union_subset (ih2.trans Set.subset_union_left)
      (ih1.trans Set.subset_union_right)
  case case6 cmp r1 ri c1 c2 c1' c2' h2 h1 ih2 ih1 =>
    simp only [Set.empty_union]
    exact Set.union_subset (ih1.trans Set.subset_union_right)
      (ih2.trans Set.subset_union_left)
  case case7 cmp r1 ri c1 c2 c1' c2' h2 h1 ih2 ih1 =>
    simp only [Set.union_empty]
    exact Set.union_subset (ih2.trans Set.subset_union_left)
      (ih1.trans Set.subset_union_right)
  case case8 cmp r1 ri c1 c2 c1' c2' h2 h1 ih2 ih1 =>
    exact Set.union_subset (ih2.trans Set.subset_union_left)
      (ih1.trans Set.subset_union_right)
  case case9 c1 c2 c1' h ih1 =>
    exact Set.union_subset (ih1.trans Set.subset_union_left) Set.subset_union_right
  case case10 c1 c2 c1' h2 c b h ih2 ih1 =>
    exact Set.union_subset (ih2.trans Set.subset_union_left)
      (ih1.trans Set.subset_union_right)
  case case12 =>
    exact Set.Subset.refl _

end Flapjack.WordConvs
