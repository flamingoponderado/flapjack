module

public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Misc.Sptree.InsertProperty
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Label-free invariants for known-function approximations. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open Flapjack ClosLang ClosProps

/-- Inlined bodies in an approximation obey the label-free predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_no_Labels_def"]
def valApproxNoLabels : ValApprox → Prop
  | .clos _ _ body _ => noLabels body
  | .tuple _ values => ∀ value ∈ values, valApproxNoLabels value
  | _ => True
termination_by a => sizeOf a
decreasing_by
  all_goals
    have := List.sizeOf_lt_of_mem ‹_›
    simp_wf
    omega

/-- Every stored global approximation is label-free. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_no_Labels_def"]
def globalsApproxNoLabels (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxNoLabels a

/-- Merging approximations preserves their label-free invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_no_Labels_merge"]
theorem valApproxNoLabelsMerge (a b : ValApprox)
    (safe : valApproxNoLabels a ∧ valApproxNoLabels b) :
    valApproxNoLabels (mergeHOL a b) := by
  obtain ⟨ha, hb⟩ := safe
  induction a using (measure (fun a : ValApprox => sizeOf a)).wf.induction generalizing b with
  | h a ih =>
    cases a <;> cases b <;> simp_all [mergeHOL, valApproxNoLabels]
    all_goals split <;> simp_all [valApproxNoLabels]
    rw [mergeListHOL_eq_zip]
    intro z member
    obtain ⟨⟨x, y⟩, paired, rfl⟩ := List.mem_map.mp member
    obtain ⟨hx, hy⟩ := List.of_mem_zip paired
    have smaller := List.sizeOf_lt_of_mem hx
    exact ih x (by simp_wf; omega) y (ha x hx) (hb y hy)

/-- Primitive approximation preserves label-free value and global approximations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_no_Labels"]
theorem knownOpNoLabels (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (h : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxNoLabels x) ∧ globalsApproxNoLabels g0) :
    valApproxNoLabels a ∧ globalsApproxNoLabels g := by
  obtain ⟨known, safe, globals⟩ := h
  cases op with
  | globOp op =>
    cases op with
    | global index =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        cases h : sptLookup index g0 with
        | none => exact ⟨by simp [valApproxNoLabels], globals⟩
        | some value => exact ⟨by simpa [h] using globals index value h, globals⟩
      | cons x xs =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxNoLabels], globals⟩
    | setGlobal index =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxNoLabels], globals⟩
      | cons x xs =>
        have xSafe := safe x (by simp)
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        constructor
        · simp [valApproxNoLabels]
        · apply sptInsert_preservesProperty _ _ _ _ _ globals
          cases h : sptLookup index g0 with
          | none => exact xSafe
          | some old => exact valApproxNoLabelsMerge old x ⟨globals index old h, xSafe⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxNoLabels], globals⟩
  | blockOp op =>
    cases op with
    | cons tag =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simpa [valApproxNoLabels] using safe, globals⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxNoLabels], globals⟩
  | intOp op =>
    cases op <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
      rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxNoLabels], globals⟩
  | memOp op =>
    cases op with
    | el =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxNoLabels], globals⟩
      | cons x xs =>
        cases xs with
        | nil =>
          cases x <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
            rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxNoLabels], globals⟩
        | cons y ys =>
          cases ys with
          | nil =>
            cases x <;> cases y <;> simp only [knownOpHOL, Prod.mk.injEq] at known
            all_goals try (rcases known with ⟨rfl, rfl⟩; exact ⟨by simp [valApproxNoLabels], globals⟩)
            split at known <;> simp_all [valApproxNoLabels]
            all_goals rcases known with ⟨rfl, rfl⟩
            · exact safe _ (List.getElem_mem ..)
            · simp [valApproxNoLabels]
          | cons z zs =>
            cases x <;> cases y <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
              rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxNoLabels], globals⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxNoLabels], globals⟩
  | _ =>
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    exact ⟨by simp [valApproxNoLabels], globals⟩


/-- A body selected from a label-free approximation is label-free. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_no_Labels"]
theorem decideInlineNoLabels {L : Type} (c : Config) (approx : ValApprox)
    (loc : Option L) (arity : Nat) (e : Exp)
    (h : valApproxNoLabels approx ∧ decideInlineHOL c approx loc arity = .letInline e) :
    noLabels e := by
  obtain ⟨safe, decision⟩ := h
  cases approx <;> simp [decideInlineHOL] at decision
  case closNoInline target n => split at decision <;> simp_all
  case clos target n body size =>
    split at decision <;> simp_all [valApproxNoLabels]
    split at decision <;> simp_all

/-- Non-inlineable recursive closures obey the label-free predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "clos_gen_no_inline_no_Labels"]
theorem closGenNoInline_noLabels (xs : List (Nat × Exp)) (n x : Nat) :
    ∀ approx ∈ closGenNoInline x n xs, valApproxNoLabels approx := by
  induction xs generalizing n with
  | nil => simp [closGenNoInline]
  | cons p xs ih =>
    cases p
    simpa [closGenNoInline, valApproxNoLabels] using ih (n + 1)

end Flapjack.Compiler.Backend.ClosKnown
