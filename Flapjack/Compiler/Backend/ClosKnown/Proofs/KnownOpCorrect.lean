module

public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateGlobalsApprox
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
public import Flapjack.Compiler.Backend.ClosInterp.Proofs.PrimitiveRelation

@[expose] public section

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

/-- The tuple-and-integer branch of indexed lookup preserves the relation at
the selected element, including the optimizer's out-of-bounds fallback. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxElTuple {C F : Type} (tag : Nat) (elements : List ValApprox)
    (index : Int) (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (vs : List Value) (s0 : State C F) (v : Value) (s : State C F)
    (known : knownOpHOL (.memOp .el) [.tuple tag elements, .int index] g0 = (a, g))
    (run : doApp (.memOp .el) vs s0 = .val (v, s))
    (rel : List.Forall₂ ValApproxVal [.tuple tag elements, .int index] vs)
    (globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  cases rel with
  | cons first rest =>
    cases rest with
    | cons second rest =>
      cases rest
      cases first with
      | tuple _ _ values elementsRel =>
        cases second with
        | int _ =>
          by_cases bounds : 0 ≤ index ∧ index < Int.ofNat elements.length
          · have ibound : index.toNat < elements.length := (Int.toNat_lt bounds.1).2 bounds.2
            have vbound : index.toNat < values.length := by simpa [elementsRel.length_eq] using ibound
            simp only [knownOpHOL, bounds] at known
            rcases known with ⟨rfl, rfl⟩
            have notneg : ¬index < 0 := by omega
            simp only [doApp, applyMemory, notneg, ↓reduceIte,
              List.getElem?_eq_getElem vbound, Option.bind_some,
              SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨globals, elementsRel.get _ _⟩
          · simp only [knownOpHOL, bounds, ↓reduceDIte, Prod.mk.injEq] at known
            rcases known with ⟨rfl, rfl⟩
            by_cases negative : index < 0
            · simp [doApp, applyMemory, negative] at run
            · have nonnegative : 0 ≤ index := by omega
              have outside : ¬index.toNat < values.length := by
                intro inside
                have inside' : index.toNat < elements.length := by
                  simpa [elementsRel.length_eq] using inside
                exact bounds ⟨nonnegative, (Int.toNat_lt nonnegative).1 inside'⟩
              have missing : values[index.toNat]? = none :=
                List.getElem?_eq_none (Nat.le_of_not_gt outside)
              simp [doApp, applyMemory, negative, missing] at run

/-- An impossible approximation cannot describe the first runtime argument. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxElImpossibleFirst {C F : Type} (rest : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (vs : List Value) (s0 : State C F) (v : Value) (s : State C F)
    (_known : knownOpHOL (.memOp .el) (.impossible :: rest) g0 = (a, g))
    (_run : doApp (.memOp .el) vs s0 = .val (v, s))
    (rel : List.Forall₂ ValApproxVal (.impossible :: rest) vs)
    (_globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  cases rel with
  | cons first _ => cases first

/-- An impossible approximation cannot describe the second runtime argument. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxElImpossibleSecond {C F : Type} (first : ValApprox)
    (rest : List ValApprox) (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (vs : List Value) (s0 : State C F) (v : Value) (s : State C F)
    (_known : knownOpHOL (.memOp .el) (first :: .impossible :: rest) g0 = (a, g))
    (_run : doApp (.memOp .el) vs s0 = .val (v, s))
    (rel : List.Forall₂ ValApproxVal (first :: .impossible :: rest) vs)
    (_globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  cases rel with
  | cons _ tail =>
    cases tail with
    | cons second _ => cases second

/-- A successful indexed read leaves the closure state unchanged. This is
proof infrastructure for the indexed-read optimizer case. -/
private theorem elState {C F : Type} (vs : List Value) (s0 s : State C F) (v : Value)
    (run : doApp (.memOp .el) vs s0 = .val (v, s)) : s = s0 := by
  have successful : applyMemory .el vs s0 = some (v, s) := by
    cases h : applyMemory .el vs s0 with
    | none => simp [doApp, h] at run
    | some pair =>
      have eq : pair = (v, s) := by simpa [doApp, h] using run
      exact congrArg some eq
  cases vs with
  | nil => simp [applyMemory] at successful
  | cons x xs =>
    cases xs with
    | nil => simp [applyMemory] at successful
    | cons y ys =>
      cases ys with
      | cons z zs => simp [applyMemory] at successful
      | nil =>
        cases x <;> cases y <;> simp [applyMemory] at successful
        all_goals repeat' (split at successful <;> simp_all)
        all_goals rcases successful with ⟨_, successful⟩
        all_goals obtain ⟨_, _, eq⟩ := Option.bind_eq_some_iff.mp successful
        all_goals cases eq; rfl

/-- Indexed reads preserve global approximations and soundly approximate the
selected value for all argument lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApproxEl {C F : Type} (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (vs : List Value) (s0 : State C F) (v : Value) (s : State C F)
    (known : knownOpHOL (.memOp .el) args g0 = (a, g))
    (run : doApp (.memOp .el) vs s0 = .val (v, s))
    (rel : List.Forall₂ ValApproxVal args vs) (globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  have state := elState vs s0 s v run
  subst s
  cases args with
  | nil =>
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    exact ⟨globals, .other _⟩
  | cons first rest =>
    cases first with
    | impossible => exact knownOpCorrectApproxElImpossibleFirst rest g0 a g vs s0 v s0 known run rel globals
    | _ =>
      cases rest with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨globals, .other _⟩
      | cons second tail =>
        cases second with
        | impossible => exact knownOpCorrectApproxElImpossibleSecond _ tail g0 a g vs s0 v s0 known run rel globals
        | _ =>
          cases tail with
          | cons next tail =>
            simp only [knownOpHOL, Prod.mk.injEq] at known
            rcases known with ⟨rfl, rfl⟩
            exact ⟨globals, .other _⟩
          | nil =>
            first
            | exact knownOpCorrectApproxElTuple _ _ _ g0 a g vs s0 v s0 known run rel globals
            | simp only [knownOpHOL, Prod.mk.injEq] at known
              rcases known with ⟨rfl, rfl⟩
              exact ⟨globals, .other _⟩

/-- Lift a successful block primitive's global-store frame to the dispatcher. -/
private theorem blockGlobals {C F : Type} (op : ClosLang.BlockOp) (vs : List Value)
    (s0 s : State C F) (v : Value)
    (run : doApp (.blockOp op) vs s0 = .val (v, s)) : s.globals = s0.globals := by
  cases h : applyBlock op vs s0 with
  | none => simp [doApp, h] at run
  | some pair =>
    have eq : pair = (v, s) := by simpa [doApp, h] using run
    subst pair
    exact ClosInterp.applyBlock_globals op vs s0 s v h

/-- Lift a successful memory primitive's global-store frame to the dispatcher. -/
private theorem memoryGlobals {C F : Type} (op : ClosLang.MemOp) (vs : List Value)
    (s0 s : State C F) (v : Value)
    (run : doApp (.memOp op) vs s0 = .val (v, s)) : s.globals = s0.globals := by
  cases h : applyMemory op vs s0 with
  | none => simp [doApp, h] at run
  | some pair =>
    have eq : pair = (v, s) := by simpa [doApp, h] using run
    subst pair
    exact ClosInterp.applyMemory_globals op vs s0 s v h

/-- Lift a successful integer primitive's global-store frame to the dispatcher. -/
private theorem intGlobals {C F : Type} (op : ClosLang.IntOp) (vs : List Value)
    (s0 s : State C F) (v : Value)
    (run : doApp (.intOp op) vs s0 = .val (v, s)) : s.globals = s0.globals := by
  cases h : applyNumeric (.intOp op) vs s0 with
  | none => simp [doApp, h] at run
  | some pair =>
    have eq : pair = (v, s) := by simpa [doApp, h] using run
    subst pair
    exact ClosInterp.applyNumeric_globals _ vs s0 s v h

/-- Lift a successful word primitive's global-store frame to the dispatcher. -/
private theorem wordGlobals {C F : Type} (op : ClosLang.WordOp) (vs : List Value)
    (s0 s : State C F) (v : Value)
    (run : doApp (.wordOp op) vs s0 = .val (v, s)) : s.globals = s0.globals := by
  cases h : applyNumeric (.wordOp op) vs s0 with
  | none => simp [doApp, h] at run
  | some pair =>
    have eq : pair = (v, s) := by simpa [doApp, h] using run
    subst pair
    exact ClosInterp.applyNumeric_globals _ vs s0 s v h

/-- A state with the same globals satisfies the same approximation invariant. -/
private theorem globalsFrame {C F : Type} (s0 s : State C F) (g : Spt ValApprox)
    (same : s.globals = s0.globals) (globals : stateGlobalsApprox s0 g) :
    stateGlobalsApprox s g := by
  simpa [stateGlobalsApprox, same] using globals

/-- The known-operation approximation is sound for every successful
primitive application. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownOpCorrectApprox {C F : Type} (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (vs : List Value) (s0 : State C F) (v : Value) (s : State C F)
    (known : knownOpHOL op args g0 = (a, g))
    (run : doApp op vs s0 = .val (v, s))
    (rel : List.Forall₂ ValApproxVal args vs) (globals : stateGlobalsApprox s0 g0) :
    stateGlobalsApprox s g ∧ ValApproxVal a v := by
  cases op with
  | globOp op =>
    cases op with
    | global index => exact knownOpCorrectApproxGlobal index args g0 a g vs s0 v s known run rel globals
    | setGlobal index => exact knownOpCorrectApproxSetGlobal index args g0 a g vs s0 v s known run rel globals
    | allocGlobal => exact knownOpCorrectApproxAllocGlobal args g0 a g vs s0 v s known run rel globals
    | globalsPtr | setGlobalsPtr => cases vs <;> simp [doApp, applyGlobal] at run
  | blockOp op =>
    cases op with
    | cons tag => exact knownOpCorrectApproxCons tag args g0 a g vs s0 v s known run rel globals
    | _ =>
      have same := blockGlobals _ vs s0 s v run
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨globalsFrame s0 s g0 same globals, .other _⟩
  | memOp op =>
    cases op with
    | el => exact knownOpCorrectApproxEl args g0 a g vs s0 v s known run rel globals
    | _ =>
      have same := memoryGlobals _ vs s0 s v run
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨globalsFrame s0 s g0 same globals, .other _⟩
  | intOp op =>
    cases op with
    | const i => exact knownOpCorrectApproxIntConst i args g0 a g vs s0 v s known run rel globals
    | _ =>
      have same := intGlobals _ vs s0 s v run
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨globalsFrame s0 s g0 same globals, .other _⟩
  | wordOp op =>
    have same := wordGlobals op vs s0 s v run
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    exact ⟨globalsFrame s0 s g0 same globals, .other _⟩
  | ffi name =>
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all [stateGlobalsApprox, ValApproxVal.other]
    all_goals aesop
  | thunkOp op =>
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all [stateGlobalsApprox, ValApproxVal.other]
    all_goals aesop
  | label | install => simp [doApp] at run

end KnownOpCorrect
end Flapjack.Compiler.Backend.ClosKnown
