module

public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation
public import Flapjack.Compiler.Backend.Semantics.BviProps.CodeLabels

@[expose] public section

/-! Source-shaped label accounting for the BVI tail-recursion pass. -/
namespace Flapjack.Compiler.Backend.BviTailrec.Proofs

private theorem freshCoverage (code : List (Nat × Nat × Bvi.Exp)) (next k : Nat)
    (bounded : next + k * bvlToBviNamespaces < (compileEachSource next code).1) :
    next + k * bvlToBviNamespaces ∈ (compileEachSource next code).2.map Prod.fst := by
  induction code generalizing next k with
  | nil => simp [compileEachSource] at bounded; omega
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases compiled : compileExpSource loc next arity body with
    | none =>
      cases tail : compileEachSource next rest with
      | mk last output =>
        simp only [compileEachSource, compiled, tail] at bounded ⊢
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (by simpa [tail] using ih next k (by simpa [tail] using bounded))
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      cases tail : compileEachSource (next + bvlToBviNamespaces) rest with
      | mk last output =>
        simp only [compileEachSource, compiled, tail] at bounded ⊢
        simp only [List.map_cons, List.mem_cons]
        cases k with
        | zero => simp
        | succ k =>
          have same : next + (k + 1) * bvlToBviNamespaces =
              (next + bvlToBviNamespaces) + k * bvlToBviNamespaces := by
            simp only [Nat.add_mul, Nat.one_mul]; omega
          right; right
          rw [same] at bounded ⊢
          simpa [tail] using ih (next + bvlToBviNamespaces) k (by simpa [tail] using bounded)

/-- The emitted function labels are exactly the original labels plus the
worker labels allocated in the traversed interval. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "compile_each_labels"]
theorem compileEach_labels (next1 : Nat) (code1 : List (Nat × Nat × Bvi.Exp))
    (next2 : Nat) (code2 : List (Nat × Nat × Bvi.Exp))
    (compiled : compileEachSource next1 code1 = (next2, code2)) :
    ({label | label ∈ code1.map Prod.fst} ∪
      {label | ∃ k, label = next1 + k * bvlToBviNamespaces ∧ next1 + k * bvlToBviNamespaces < next2}) =
      {label | label ∈ code2.map Prod.fst} ∧ next1 ≤ next2 := by
  have mono := compileEachSource_next_mono next1 code1
  simp only [compiled] at mono
  constructor
  · ext label
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro member
      rcases member with original | ⟨k, rfl, bound⟩
      · have h := compileEachSource_preserves_labels code1 next1 label original
        simpa only [compiled] using h
      · have h := freshCoverage code1 next1 k (by simpa only [compiled] using bound)
        simpa only [compiled] using h
    · intro member
      have h := compileEachSource_mem code1 next1 label (by simpa only [compiled] using member)
      simp only [compiled] at h
      rcases h with original | ⟨lo, hi, k, eq⟩
      · exact Or.inl original
      · exact Or.inr ⟨k, eq, by simpa [eq] using hi⟩
  · obtain ⟨k, h⟩ := mono
    omega

/-- Function-list compilation retains every original label. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "compile_each_keeps_names"]
theorem compileEach_keepsNames (next : Nat) (xs : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (ys : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (assumptions : compileEachSource next xs = (next', ys) ∧ x ∈ xs.map Prod.fst) :
    x ∈ ys.map Prod.fst := by
  have h := compileEachSource_preserves_labels xs next x assumptions.2
  simpa only [assumptions.1] using h

/-- The whole-program tail-recursion pass retains every original label. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "compile_prog_keeps_names"]
theorem compileProg_keepsNames (enabled : Bool) (next : Nat) (xs : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (ys : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (assumptions : compileProgSource enabled next xs = (next', ys) ∧ x ∈ xs.map Prod.fst) :
    x ∈ ys.map Prod.fst := by
  cases enabled with
  | false =>
    simp only [compileProgSource, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at assumptions
    simpa [← assumptions.1.2] using assumptions.2
  | true =>
    simp only [compileProgSource, ↓reduceIte] at assumptions
    exact compileEach_keepsNames next xs next' ys x assumptions

/-- The wrapper refers exactly to labels in its identity and body. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "get_code_labels_let_wrap"]
theorem letWrap_getCodeLabels (arity : Nat) (identity body : Bvi.Exp) :
    BviProps.getCodeLabels (letWrap arity identity body) = BviProps.getCodeLabels identity ∪ BviProps.getCodeLabels body := by
  ext label
  simp [letWrap, BviProps.getCodeLabels, BviProps.getCodeLabelsList_eq]

end Flapjack.Compiler.Backend.BviTailrec.Proofs
