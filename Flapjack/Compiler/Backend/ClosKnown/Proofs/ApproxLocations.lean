module

public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGeneric
public import Flapjack.Compiler.Backend.ClosKnown.Inline
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
public import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties
public import Flapjack.Misc.Sptree.InsertProperty

@[expose] public section

/-! Function-location safety of known-function approximations. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps

/-- Inlined bodies in an approximation have present function locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_every_Fn_SOME_def"]
def valApproxLocations : ValApprox → Prop
  | .clos _ _ body _ => everyFnLocationSome [body]
  | .tuple _ values => ∀ value ∈ values, valApproxLocations value
  | _ => True
termination_by a => sizeOf a
decreasing_by all_goals have := List.sizeOf_lt_of_mem ‹_›; simp_wf; omega

/-- All stored global approximations satisfy the closure-body invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_every_Fn_SOME_def"]
def globalsApproxLocations (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxLocations a

/-- `valApproxLocations` agrees with the parameterised invariant of the four
source approximation predicates. -/
private theorem valApproxLocations_iff (a : ValApprox) :
    valApproxLocations a ↔ valApproxAll (fun body => everyFnLocationSome [body]) a := by
  induction a using (measure (fun a : ValApprox => sizeOf a)).wf.induction with
  | h a ih =>
    cases a with
    | clos loc arity body size => simp [valApproxLocations, valApproxAll]
    | tuple tag xs =>
      simp only [valApproxLocations, valApproxAll]
      exact ⟨fun h v hv => (ih v (sizeOf_lt_of_mem_tuple hv)).mp (h v hv),
             fun h v hv => (ih v (sizeOf_lt_of_mem_tuple hv)).mpr (h v hv)⟩
    | _ => simp [valApproxLocations, valApproxAll]

/-- Merging two safe approximations preserves closure-body safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_every_Fn_SOME_merge"]
theorem valApproxLocationsMerge (a b : ValApprox)
    (safe : valApproxLocations a ∧ valApproxLocations b) : valApproxLocations (mergeHOL a b) := by
  obtain ⟨ha, hb⟩ := safe
  have h' : valApproxAll (fun body => everyFnLocationSome [body]) a ∧
      valApproxAll (fun body => everyFnLocationSome [body]) b :=
    ⟨(valApproxLocations_iff a).mp ha, (valApproxLocations_iff b).mp hb⟩
  exact (valApproxLocations_iff (mergeHOL a b)).mpr
    (valApproxAllMerge (fun body => everyFnLocationSome [body]) a b h')

/-- Primitive approximation preserves both value and global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_every_Fn_SOME"]
theorem knownOpLocations (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (h : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxLocations x) ∧ globalsApproxLocations g0) :
    valApproxLocations a ∧ globalsApproxLocations g := by
  obtain ⟨known, safe, globals⟩ := h
  have h' : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxAll (fun body => everyFnLocationSome [body]) x) ∧
      globalsApproxAll (fun body => everyFnLocationSome [body]) g0 :=
    ⟨known, fun x hx => (valApproxLocations_iff x).mp (safe x hx),
     fun n v hv => (valApproxLocations_iff v).mp (globals n v hv)⟩
  obtain ⟨ha, hg⟩ := knownOpAll (fun body => everyFnLocationSome [body]) op args g0 a g h'
  exact ⟨(valApproxLocations_iff a).mpr ha,
    fun n v hv => (valApproxLocations_iff v).mpr (hg n v hv)⟩


/-- The inlining decision only extracts bodies with present function locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_every_Fn_SOME"]
theorem decideInlineLocations {L : Type} (c : Config) (approx : ValApprox) (loc : Option L)
    (arity : Nat) (e : ClosLang.Exp)
    (h : valApproxLocations approx ∧ decideInlineHOL c approx loc arity = .letInline e) :
    everyFnLocationSome [e] := by
  obtain ⟨safe, decision⟩ := h
  cases approx <;> simp [decideInlineHOL] at decision
  case closNoInline target n => split at decision <;> simp_all
  case clos target n body size =>
    split at decision <;> simp_all [valApproxLocations]
    split at decision <;> simp_all

/-- Non-inlining recursive approximations contain no closure bodies. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "clos_gen_no_inline_every_Fn_SOME"]
theorem closGenNoInlineLocations (fns : List (Nat × ClosLang.Exp)) (n x : Nat) :
    ∀ a ∈ closGenNoInline x n fns, valApproxLocations a := by
  induction fns generalizing n with
  | nil => simp [closGenNoInline]
  | cons fn rest ih =>
    cases fn with
    | mk arity body =>
      simp only [closGenNoInline, List.mem_cons, forall_eq_or_imp, valApproxLocations, true_and]
      exact ih (n + 1)

end Flapjack.Compiler.Backend.ClosKnown
