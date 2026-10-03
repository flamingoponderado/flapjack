import Flapjack.Pancake.Proofs.PanSimp.SeqAssocExact

/-! The assembled original `evaluate_seq_assoc`
(pan_simpProofScript.sml:117-135) from its case pieces, by the source's
`seq_assoc_ind` recursion, realised as strong induction on the size of the
second program (the measure `seq_assoc` itself decreases). -/
namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace SeqAssocAssemblySupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end SeqAssocAssemblySupport

@[hol "cakeml/pancake/proofs/pan_simpProofScript.sml" "evaluate_seq_assoc"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateSeqAssocHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p q : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      evaluateHOLFiniteState s (seqAssocHOL p q) = evaluateHOLFiniteState s (.seq p q) := by
  suffices h : ∀ (n : Nat) (q : ProgHOL width), sizeOf q = n → ∀ (p : ProgHOL width)
      (s : PanSemStateFiniteExact width σ),
      evaluateHOLFiniteState s (seqAssocHOL p q) = evaluateHOLFiniteState s (.seq p q) from
    fun p q s => h _ q rfl p s
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro q hq p s
  have IH : ∀ q', sizeOf q' < sizeOf q → ∀ (p : ProgHOL width)
      (s : PanSemStateFiniteExact width σ),
      evaluateHOLFiniteState s (seqAssocHOL p q') = evaluateHOLFiniteState s (.seq p q') :=
    fun q' hlt p s => ih _ (hq ▸ hlt) q' rfl p s
  cases q with
  | skip => exact evaluateSeqAssocSkipHOL p s
  | dec name shape value body =>
    exact evaluateSeqAssocDecHOL p body name shape value
      (fun s => IH body (by simp; omega) .skip s) s
  | assign kind name value => exact evaluateSeqAssocAssignHOL p kind name value s
  | primitive name operator args => exact evaluateSeqAssocPrimitiveHOL p name operator args s
  | store address value => exact evaluateSeqAssocStoreHOL p address value s
  | store32 address value => exact evaluateSeqAssocStore32HOL p address value s
  | storeByte address value => exact evaluateSeqAssocStoreByteHOL p address value s
  | seq first second =>
    exact evaluateSeqAssocSeqHOL p first second
      (fun s => IH first (by simp; omega) p s)
      (fun s => IH second (by simp; omega) _ s) s
  | ite condition thenBranch elseBranch =>
    exact evaluateSeqAssocIfHOL p thenBranch elseBranch condition
      (fun s => IH thenBranch (by simp; omega) .skip s)
      (fun s => IH elseBranch (by simp; omega) .skip s) s
  | «while» condition body =>
    exact evaluateSeqAssocWhileHOL p body condition
      (fun s => IH body (by simp; omega) .skip s) s
  | «break» => exact evaluateSeqAssocBreakHOL p s
  | «continue» => exact evaluateSeqAssocContinueHOL p s
  | call info function arguments =>
    rcases info with _ | ⟨returns, _ | ⟨exception, handlerVar, handler⟩⟩
    · exact evaluateSeqAssocCallNoneHOL p function arguments s
    · exact evaluateSeqAssocCallNoHandlerHOL p returns function arguments s
    · exact evaluateSeqAssocCallHandlerHOL p handler returns exception handlerVar function
        arguments (fun s => IH handler (by simp; omega) .skip s) s
  | decCall name shape function arguments body =>
    exact evaluateSeqAssocDecCallHOL p body name shape function arguments
      (fun s => IH body (by simp; omega) .skip s) s
  | extCall function configuration configurationLength array arrayLength =>
    exact evaluateSeqAssocExtCallHOL p function configuration configurationLength array
      arrayLength s
  | raise exception value => exact evaluateSeqAssocRaiseHOL p exception value s
  | «return» value => exact evaluateSeqAssocReturnHOL p value s
  | shMemLoad size kind name address => exact evaluateSeqAssocShMemLoadHOL p size kind name address s
  | shMemStore size address value => exact evaluateSeqAssocShMemStoreHOL p size address value s
  | tick => exact evaluateSeqAssocTickHOL p s
  | annot tag text => exact evaluateSeqAssocAnnotHOL p tag text s

end Flapjack
