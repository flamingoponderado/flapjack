module

public import Flapjack.Compiler.Backend.BvlToBvi.SourcePipeline
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileLabels
public import Flapjack.Compiler.Backend.BvlInline.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BviInline.Proofs.CodeLabels
@[expose] public section

/-! Whole BVL-to-BVI code-label containment. -/
open Flapjack Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
/-- The complete whole-pass compiler references only emitted, translated, or allocated labels. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_get_code_labels"]
theorem compile_getCodeLabels (start : Nat) (c : BvlToBvi.Config) (names : Spt MlString)
    (prog : List (Nat × Nat × Bvl.Exp)) (loc : Nat) (code : List (Nat × Nat × Bvi.Exp))
    (inlines : Spt (Nat × Bvl.Exp)) (bviInlines : Spt (Nat × Bvi.Exp))
    (n1 n2 n3 : Nat) (namesOut : Spt MlString)
    (run : compileSource start c names prog = (loc, code, inlines, bviInlines, n1, n2, n3, namesOut)) :
    (⋃₀ (BviProps.getCodeLabels '' {e | e ∈ code.map (fun q => q.2.2)})) ⊆
      insert (bvlNumStubs + start * bvlToBviNamespaces)
        ({label | label ∈ code.map Prod.fst} ∪
          ((fun k => bvlNumStubs + k * bvlToBviNamespaces) ''
            (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ prog.map (fun q => q.2.2)}))) ∪
          {label | ∃ k, label = bvlNumStubs + 2 + k * bvlToBviNamespaces ∧
            bvlNumStubs + 2 + k * bvlToBviNamespaces < n2} ∪
          {label | ∃ k, label = bvlNumStubs + 3 + k * bvlToBviNamespaces ∧
            bvlNumStubs + 3 + k * bvlToBviNamespaces < n3}) := by
  rcases hi : BvlInline.compileProg c.inlineSizeLimit c.splitMainAtSeq c.expCut prog with ⟨ic, pi⟩
  rcases hl : compileProgSource start 0 pi with ⟨l, p, a⟩
  rcases ht : BviTailrec.compileProgSource c.doTailrec (bvlNumStubs + 2) p with ⟨b, pt⟩
  rcases hm : BviTmc.compileProgSource c.doTmc (bvlNumStubs + 3) pt with ⟨d, pm⟩
  rcases hb : BviInline.compileProgSource pm with ⟨bc, po⟩
  simp only [compileSource, hi, hl, ht, hm, hb, Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have inlineKeys : po.map Prod.fst = pm.map Prod.fst :=
    BviInline.Proofs.compileInc_mapFst .ln bc pm po (by simpa [BviInline.compileProgSource] using hb)
  have kept : ∀ x ∈ p.map Prod.fst, x ∈ po.map Prod.fst := by
    intro x hx
    have htKeep := BviTailrec.Proofs.compileProg_keepsNames c.doTailrec (bvlNumStubs + 2) p b pt x ⟨ht, hx⟩
    have hmKeep := BviTmc.Proofs.compileProg_keepsNames c.doTmc (bvlNumStubs + 3) pt d pm x ⟨hm, htKeep⟩
    simpa only [inlineKeys] using hmKeep
  have inlineBound := BvlInline.Proofs.compileProg_codeLabels c.inlineSizeLimit c.splitMainAtSeq c.expCut prog ic pi hi
  have sourceBound :
      (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ pi.map (fun q => q.2.2)})) ⊆
      (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ prog.map (fun q => q.2.2)})) := by
    simp [Set.subset_def] at inlineBound ⊢
    intro label body name arity member has
    obtain ⟨i, j, e, mem, found⟩ := inlineBound label name arity body member has
    exact ⟨e, ⟨i, j, mem⟩, found⟩
  have lowered := compileProg_getCodeLabels start 0 pi l p a hl
  have finalInline := BviInline.Proofs.compileProg_codeLabels pm po bc hb
  let allowed : Set Nat := insert (bvlNumStubs + start * bvlToBviNamespaces)
        ({label | label ∈ po.map Prod.fst} ∪
          ((fun k => bvlNumStubs + k * bvlToBviNamespaces) ''
            (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ prog.map (fun q => q.2.2)}))) ∪
          {label | ∃ k, label = bvlNumStubs + 2 + k * bvlToBviNamespaces ∧
            bvlNumStubs + 2 + k * bvlToBviNamespaces < b} ∪
          {label | ∃ k, label = bvlNumStubs + 3 + k * bvlToBviNamespaces ∧
            bvlNumStubs + 3 + k * bvlToBviNamespaces < d})
  change _ ⊆ allowed
  apply Set.Subset.trans finalInline
  apply BviTmc.Proofs.compileProg_goodCodeLabels c.doTmc (bvlNumStubs + 3) pt d pm allowed
  refine ⟨hm, ?_, ?_⟩
  · apply BviTailrec.Proofs.compileProg_goodCodeLabels c.doTailrec (bvlNumStubs + 2) p b pt allowed
    refine ⟨ht, ?_, ?_⟩
    · intro x hx
      have h := lowered hx
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image] at h ⊢
      dsimp [allowed]
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image]
      rcases h with h | h | ⟨z, hz, rfl⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl (Or.inl (kept x h))))
      · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨z, sourceBound hz, rfl⟩)))
    · intro x hx
      dsimp [allowed]
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq]
      exact Or.inr (Or.inl (Or.inr hx))
  · intro x hx
    dsimp [allowed]
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq]
    exact Or.inr (Or.inr hx)
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
