module

public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Misc.Sptree.InsertProperty
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGeneric
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Application-arity invariants for known-function approximations. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open Flapjack ClosLang ClosProps

/-- Inlined bodies in an approximation obey the application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_obeys_max_app_def"]
def valApproxObeysMaxApp (limit : Nat) : ValApprox → Prop
  | .clos _ _ body _ => obeysMaxApp limit body
  | .tuple _ values => ∀ value ∈ values, valApproxObeysMaxApp limit value
  | _ => True
termination_by a => sizeOf a
decreasing_by
  all_goals
    have := List.sizeOf_lt_of_mem ‹_›
    simp_wf
    omega

/-- Every stored global approximation obeys the bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_obeys_max_app_def"]
def globalsApproxObeysMaxApp (limit : Nat) (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxObeysMaxApp limit a

/-- `valApproxObeysMaxApp` agrees with the parameterised invariant of the four
source approximation predicates. -/
private theorem valApproxObeysMaxApp_iff (limit : Nat) (a : ValApprox) :
    valApproxObeysMaxApp limit a ↔ valApproxAll (obeysMaxApp limit) a := by
  induction a using (measure (fun a : ValApprox => sizeOf a)).wf.induction with
  | h a ih =>
    cases a with
    | clos loc arity body size => simp [valApproxObeysMaxApp, valApproxAll]
    | tuple tag xs =>
      simp only [valApproxObeysMaxApp, valApproxAll]
      exact ⟨fun h v hv => (ih v (sizeOf_lt_of_mem_tuple hv)).mp (h v hv),
             fun h v hv => (ih v (sizeOf_lt_of_mem_tuple hv)).mpr (h v hv)⟩
    | _ => simp [valApproxObeysMaxApp, valApproxAll]

/-- Merging approximations preserves their application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_obeys_max_app_merge"]
theorem valApproxObeysMaxAppMerge (limit : Nat) (a b : ValApprox)
    (safe : valApproxObeysMaxApp limit a ∧ valApproxObeysMaxApp limit b) :
    valApproxObeysMaxApp limit (mergeHOL a b) := by
  obtain ⟨ha, hb⟩ := safe
  have h' : valApproxAll (obeysMaxApp limit) a ∧ valApproxAll (obeysMaxApp limit) b :=
    ⟨(valApproxObeysMaxApp_iff limit a).mp ha, (valApproxObeysMaxApp_iff limit b).mp hb⟩
  exact (valApproxObeysMaxApp_iff limit (mergeHOL a b)).mpr
    (valApproxAllMerge (obeysMaxApp limit) a b h')

/-- Primitive approximation preserves value and global application bounds. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_obeys_max_app"]
theorem knownOpObeysMaxApp (limit : Nat) (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (h : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxObeysMaxApp limit x) ∧ globalsApproxObeysMaxApp limit g0) :
    valApproxObeysMaxApp limit a ∧ globalsApproxObeysMaxApp limit g := by
  obtain ⟨known, safe, globals⟩ := h
  have h' : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxAll (obeysMaxApp limit) x) ∧
      globalsApproxAll (obeysMaxApp limit) g0 :=
    ⟨known, fun x hx => (valApproxObeysMaxApp_iff limit x).mp (safe x hx),
     fun n v hv => (valApproxObeysMaxApp_iff limit v).mp (globals n v hv)⟩
  obtain ⟨ha, hg⟩ := knownOpAll (obeysMaxApp limit) op args g0 a g h'
  exact ⟨(valApproxObeysMaxApp_iff limit a).mpr ha,
    fun n v hv => (valApproxObeysMaxApp_iff limit v).mpr (hg n v hv)⟩


/-- A body selected for inlining obeys the approximation's application bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_obeys_max_app"]
theorem decideInlineObeysMaxApp {L : Type} (limit : Nat) (c : Config) (approx : ValApprox)
    (loc : Option L) (arity : Nat) (e : Exp)
    (h : valApproxObeysMaxApp limit approx ∧ decideInlineHOL c approx loc arity = .letInline e) :
    obeysMaxApp limit e := by
  obtain ⟨safe, decision⟩ := h
  cases approx <;> simp [decideInlineHOL] at decision
  case closNoInline target n => split at decision <;> simp_all
  case clos target n body size =>
    split at decision <;> simp_all [valApproxObeysMaxApp]
    split at decision <;> simp_all

/-- Non-inlineable recursive closures obey every application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "clos_gen_no_inline_obeys_max_app"]
theorem closGenNoInline_obeysMaxApp (limit : Nat) (xs : List (Nat × Exp)) (n x : Nat) :
    ∀ approx ∈ closGenNoInline x n xs, valApproxObeysMaxApp limit approx := by
  induction xs generalizing n with
  | nil => simp [closGenNoInline]
  | cons p xs ih =>
    cases p
    simpa [closGenNoInline, valApproxObeysMaxApp] using ih (n + 1)

end Flapjack.Compiler.Backend.ClosKnown
