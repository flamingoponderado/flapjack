module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownOpCorrect

@[expose] public section


/-! Known-global replacement in the optimizer operation simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Global
open ClosSem ClosProps

/-- A nontrivial known global read has no arguments, leaves the state and
approximation tree unchanged, and returns a value described by the computed
approximation. This is Flapjack proof infrastructure for the original
optimizer operation case. -/
theorem knownGlobalReadShape {C F : Type} (index : Nat) (approxs : List ValApprox)
    (g0 g : Spt ValApprox) (a : ValApprox) (vs : List Value)
    (s0 s : State C F) (v : Value)
    (known : knownOpHOL (.globOp (.global index)) approxs g0 = (a, g))
    (nontrivial : a ≠ .other) (approxRel : List.Forall₂ ValApproxVal approxs vs)
    (globals : stateGlobalsApprox s0 g0)
    (run : doApp (.globOp (.global index)) vs s0 = .val (v, s)) :
    approxs = [] ∧ vs = [] ∧ g = g0 ∧ s = s0 ∧ ValApproxVal a v := by
  have result := KnownOpCorrect.knownOpCorrectApproxGlobal index approxs g0 a g vs s0 v s
    known run approxRel globals
  cases approxs with
  | cons first rest =>
    simp [knownOpHOL] at known
    exact False.elim (nontrivial known.1.symm)
  | nil =>
    cases approxRel
    simp only [knownOpHOL, Prod.mk.injEq] at known
    have treeEq : g = g0 := known.2.symm
    cases found : getGlobal index s0.globals with
    | none => simp [doApp, applyGlobal, found] at run
    | some value =>
      cases value with
      | none => simp [doApp, applyGlobal, found] at run
      | some value =>
        simp [doApp, applyGlobal, found] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, treeEq, rfl, result.2⟩

/-- Integer global replacement returns the exact runtime integer and does not
change the source state. This is Flapjack proof infrastructure. -/
theorem knownGlobalIntShape {C F : Type} (index : Nat) (approxs : List ValApprox)
    (g0 g : Spt ValApprox) (i : Int) (vs : List Value) (s0 s : State C F) (v : Value)
    (known : knownOpHOL (.globOp (.global index)) approxs g0 = (.int i, g))
    (approxRel : List.Forall₂ ValApproxVal approxs vs) (globals : stateGlobalsApprox s0 g0)
    (run : doApp (.globOp (.global index)) vs s0 = .val (v, s)) :
    approxs = [] ∧ vs = [] ∧ g = g0 ∧ s = s0 ∧ v = .number i := by
  obtain ⟨a, b, c, d, rel⟩ := knownGlobalReadShape index approxs g0 g (.int i) vs s0 s v
    known (by simp) approxRel globals run
  cases rel
  exact ⟨a, b, c, d, rfl⟩

/-- Empty-tuple global replacement returns the exact runtime block and does
not change the source state. This is Flapjack proof infrastructure. -/
theorem knownGlobalEmptyTupleShape {C F : Type} (index : Nat) (approxs : List ValApprox)
    (g0 g : Spt ValApprox) (tag : Nat) (vs : List Value) (s0 s : State C F) (v : Value)
    (known : knownOpHOL (.globOp (.global index)) approxs g0 = (.tuple tag [], g))
    (approxRel : List.Forall₂ ValApproxVal approxs vs) (globals : stateGlobalsApprox s0 g0)
    (run : doApp (.globOp (.global index)) vs s0 = .val (v, s)) :
    approxs = [] ∧ vs = [] ∧ g = g0 ∧ s = s0 ∧ v = .block tag [] := by
  obtain ⟨a, b, c, d, rel⟩ := knownGlobalReadShape index approxs g0 g (.tuple tag []) vs s0 s v
    known (by simp) approxRel globals run
  cases rel with
  | tuple _ _ values rel => cases rel; exact ⟨a, b, c, d, rfl⟩


end Flapjack.Compiler.Backend.ClosKnown.Simulation.Global
