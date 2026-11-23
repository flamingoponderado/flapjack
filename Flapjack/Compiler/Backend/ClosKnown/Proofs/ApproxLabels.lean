module

public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Misc.Sptree.InsertProperty
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGeneric
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

/-- The source simplification bundle for approximations without bodies. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_no_Labels_simp"]
theorem valApproxNoLabelsSimp :
    (∀ n m, valApproxNoLabels (.closNoInline m n) ↔ True) ∧
    (∀ i, valApproxNoLabels (.int i) ↔ True) ∧
    (valApproxNoLabels .other ↔ True) ∧
    (valApproxNoLabels .impossible ↔ True) := by
  simp [valApproxNoLabels]

/-- Every stored global approximation is label-free. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_no_Labels_def"]
def globalsApproxNoLabels (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxNoLabels a

/-- `valApproxNoLabels` agrees with the parameterised invariant of the four
source approximation predicates. -/
private theorem valApproxNoLabels_iff (a : ValApprox) :
    valApproxNoLabels a ↔ valApproxAll noLabels a := by
  induction a using (measure (fun a : ValApprox => sizeOf a)).wf.induction with
  | h a ih =>
    cases a with
    | clos loc arity body size => simp [valApproxNoLabels, valApproxAll]
    | tuple tag xs =>
      simp only [valApproxNoLabels, valApproxAll]
      exact ⟨fun h v hv => (ih v (sizeOf_lt_of_mem_tuple hv)).mp (h v hv),
             fun h v hv => (ih v (sizeOf_lt_of_mem_tuple hv)).mpr (h v hv)⟩
    | _ => simp [valApproxNoLabels, valApproxAll]

/-- Merging approximations preserves their label-free invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_no_Labels_merge"]
theorem valApproxNoLabelsMerge (a b : ValApprox)
    (safe : valApproxNoLabels a ∧ valApproxNoLabels b) :
    valApproxNoLabels (mergeHOL a b) := by
  obtain ⟨ha, hb⟩ := safe
  have h' : valApproxAll noLabels a ∧ valApproxAll noLabels b :=
    ⟨(valApproxNoLabels_iff a).mp ha, (valApproxNoLabels_iff b).mp hb⟩
  exact (valApproxNoLabels_iff (mergeHOL a b)).mpr (valApproxAllMerge noLabels a b h')

/-- Primitive approximation preserves label-free value and global approximations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_no_Labels"]
theorem knownOpNoLabels (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (h : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxNoLabels x) ∧ globalsApproxNoLabels g0) :
    valApproxNoLabels a ∧ globalsApproxNoLabels g := by
  obtain ⟨known, safe, globals⟩ := h
  have h' : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxAll noLabels x) ∧
      globalsApproxAll noLabels g0 :=
    ⟨known, fun x hx => (valApproxNoLabels_iff x).mp (safe x hx),
     fun n v hv => (valApproxNoLabels_iff v).mp (globals n v hv)⟩
  obtain ⟨ha, hg⟩ := knownOpAll noLabels op args g0 a g h'
  exact ⟨(valApproxNoLabels_iff a).mpr ha,
    fun n v hv => (valApproxNoLabels_iff v).mpr (hg n v hv)⟩


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
