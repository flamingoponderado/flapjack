import Flapjack.Compiler.Backend.ClosKnown.KnownOp
import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateGlobalsApprox
import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply

/-! Cases of the known-operation approximation correctness theorem. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem

namespace KnownOpCorrect
/-- The closure state's finite maps roundtrip through their lookup view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The constructor operation preserves the global invariant and relates its
tuple approximation to the block of argument values. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxCons {C F : Type} (tag : Nat) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox) (vs : List Value)
    (s0 : State C F) (v : Value) (s : State C F)
    (known : knownOpHOL (.blockOp (.cons tag)) args g0 = (a, g))
    (run : doApp (.blockOp (.cons tag)) vs s0 = .val (v, s))
    (rel : List.Forall₂ ValApproxVal args vs) (globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  simp only [knownOpHOL, Prod.mk.injEq] at known
  simp only [doApp, applyBlock, SemanticPrimitivesHOL.Result.val.injEq,
    Prod.mk.injEq] at run
  rcases known with ⟨rfl, rfl⟩
  rcases run with ⟨rfl, rfl⟩
  exact ⟨globals, .tuple _ _ _ rel⟩

/-- Integer constants are represented by the corresponding integer value. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxIntConst {C F : Type} (i : Int) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox) (vs : List Value)
    (s0 : State C F) (v : Value) (s : State C F)
    (known : knownOpHOL (.intOp (.const i)) args g0 = (a, g))
    (run : doApp (.intOp (.const i)) vs s0 = .val (v, s))
    (_rel : List.Forall₂ ValApproxVal args vs) (globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  simp only [knownOpHOL, Prod.mk.injEq] at known
  rcases known with ⟨rfl, rfl⟩
  cases vs with
  | nil =>
    simp only [doApp, applyNumeric, doIntApp, Option.map, SemanticPrimitivesHOL.Result.val.injEq,
      Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨globals, .int _⟩
  | cons x xs => simp [doApp, applyNumeric, doIntApp] at run

/-- Reading a global uses the approximation invariant when an approximation
is present; otherwise the optimizer returns the unrestricted approximation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxGlobal {C F : Type} (index : Nat) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox) (vs : List Value)
    (s0 : State C F) (v : Value) (s : State C F)
    (known : knownOpHOL (.globOp (.global index)) args g0 = (a, g))
    (run : doApp (.globOp (.global index)) vs s0 = .val (v, s))
    (rel : List.Forall₂ ValApproxVal args vs) (globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  cases args with
  | nil =>
    cases rel
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    cases h : getGlobal index s0.globals with
    | none => simp [doApp, applyGlobal, h] at run
    | some value =>
      cases value with
      | none => simp [doApp, applyGlobal, h] at run
      | some value =>
        simp only [doApp, applyGlobal, h, Option.join, Option.map] at run
        rcases run with ⟨rfl, rfl⟩
        constructor
        · exact globals
        · cases found : sptLookup index g0 with
          | none => exact ValApproxVal.other _
          | some approx =>
            simp only [Option.getD_some]
            exact globals index v approx ⟨h, found⟩
  | cons arg args =>
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    cases vs with
    | nil => cases rel
    | cons x xs =>
      cases xs with
      | nil =>
        cases x <;> simp_all [doApp, applyGlobal]
        all_goals (try split at run) <;> simp_all [ValApproxVal.other]
      | cons x xs => simp [doApp, applyGlobal] at run

/-- Updating an empty runtime global and its approximation preserves the
invariant. This is proof infrastructure for the global-write case. -/
private theorem globalsSet {C F : Type} (s : State C F) (g : Spt ValApprox)
    (index : Nat) (value : Value) (approx : ValApprox)
    (slot : getGlobal index s.globals = some none)
    (related : ValApproxVal approx value) (globals : stateGlobalsApprox s g) :
    stateGlobalsApprox {s with globals := s.globals.set index (some value)}
      (sptInsert index (match sptLookup index g with
        | none => approx
        | some old => mergeHOL old approx) g) := by
  intro k v a ⟨get, lookup⟩
  by_cases same : k = index
  · subst k
    change s.globals[index]? = some none at slot
    simp [getGlobal, List.getElem?_set_self', slot] at get
    subst v
    rw [sptLookup_sptInsert_same] at lookup
    cases found : sptLookup index g with
    | none => simp only [found, Option.some.injEq] at lookup; subst a; exact related
    | some old =>
      simp only [found, Option.some.injEq] at lookup
      subst a
      exact valApproxValMerge old value approx (Or.inr related)
  · rw [sptLookup_sptInsert_ne index k _ g same] at lookup
    apply globals k v a
    exact ⟨by simpa [getGlobal, List.getElem?_set_ne (Ne.symm same)] using get, lookup⟩

/-- A successful global write preserves the invariant and returns unit. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxSetGlobal {C F : Type} (index : Nat) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox) (vs : List Value)
    (s0 : State C F) (v : Value) (s : State C F)
    (known : knownOpHOL (.globOp (.setGlobal index)) args g0 = (a, g))
    (run : doApp (.globOp (.setGlobal index)) vs s0 = .val (v, s))
    (rel : List.Forall₂ ValApproxVal args vs) (globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  cases args with
  | nil => cases rel; simp [doApp, applyGlobal] at run
  | cons approx rest =>
    cases vs with
    | nil => cases rel
    | cons value restValues =>
      cases restValues with
      | cons x xs => simp [doApp, applyGlobal] at run
      | nil =>
        cases rel with
        | cons related tail =>
          simp only [knownOpHOL, Prod.mk.injEq] at known
          rcases known with ⟨rfl, rfl⟩
          cases slot : getGlobal index s0.globals with
          | none => simp [doApp, applyGlobal, slot] at run
          | some old =>
            cases old with
            | some old => simp [doApp, applyGlobal, slot] at run
            | none =>
              simp only [doApp, applyGlobal, slot, SemanticPrimitivesHOL.Result.val.injEq,
                Prod.mk.injEq] at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨globalsSet s0 g0 index value approx slot related globals, .other _⟩

/-- Appending empty slots cannot introduce an initialized global. -/
private theorem globalsAlloc {C F : Type} (s : State C F) (g : Spt ValApprox) (count : Nat)
    (globals : stateGlobalsApprox s g) :
    stateGlobalsApprox {s with globals := s.globals ++ List.replicate count none} g := by
  intro k v a ⟨get, lookup⟩
  by_cases bound : k < s.globals.length
  · apply globals k v a
    exact ⟨by simpa [getGlobal, List.getElem?_append_left bound] using get, lookup⟩
  · simp [getGlobal, List.getElem?_append_right (Nat.le_of_not_gt bound),
      List.getElem?_replicate] at get

/-- Allocating empty global slots preserves all known approximations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxAllocGlobal {C F : Type} (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox) (vs : List Value)
    (s0 : State C F) (v : Value) (s : State C F)
    (known : knownOpHOL (.globOp .allocGlobal) args g0 = (a, g))
    (run : doApp (.globOp .allocGlobal) vs s0 = .val (v, s))
    (_rel : List.Forall₂ ValApproxVal args vs) (globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  simp only [knownOpHOL, Prod.mk.injEq] at known
  rcases known with ⟨rfl, rfl⟩
  cases vs with
  | nil => simp [doApp, applyGlobal] at run
  | cons value values =>
    cases values with
    | cons v vs => simp [doApp, applyGlobal] at run
    | nil =>
      cases value with
      | number i =>
        by_cases negative : i < 0
        · simp [doApp, applyGlobal, negative] at run
        · simp only [doApp, applyGlobal, negative, ↓reduceIte,
            SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨globalsAlloc s0 g0 i.toNat globals, .other _⟩
      | _ => simp [doApp, applyGlobal] at run

end KnownOpCorrect
end Flapjack.Compiler.Backend.ClosKnown
