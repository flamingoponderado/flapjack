import Flapjack.Compiler.Backend.ClosKnown.KnownOp
import Flapjack.Compiler.Backend.ClosKnown.Fuel
import Flapjack.Compiler.Backend.ClosKnown.Inline
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties
import Flapjack.Misc.Sptree

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

/-- Pairwise merge preserves a property when it holds for each paired input. -/
private theorem mergeListSafe (xs ys : List ValApprox)
    (step : ∀ x ∈ xs, ∀ y ∈ ys, valApproxLocations (mergeHOL x y)) :
    ∀ z ∈ mergeListHOL xs ys, valApproxLocations z := by
  induction xs generalizing ys with
  | nil => simp [mergeListHOL]
  | cons x xs ih =>
    cases ys with
    | nil => simp [mergeListHOL]
    | cons y ys =>
      simp only [mergeListHOL, List.mem_cons, forall_eq_or_imp]
      constructor
      · exact step x (by simp) y (by simp)
      · exact ih ys (fun a ha b hb => step a (by simp [ha]) b (by simp [hb]))

/-- Merging two safe approximations preserves closure-body safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_every_Fn_SOME_merge"]
theorem valApproxLocationsMerge (a b : ValApprox)
    (safe : valApproxLocations a ∧ valApproxLocations b) : valApproxLocations (mergeHOL a b) := by
  have all : ∀ n (a b : ValApprox), sizeOf a < n →
      valApproxLocations a → valApproxLocations b → valApproxLocations (mergeHOL a b) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b bound ha hb
      cases a <;> cases b <;> simp_all [mergeHOL, valApproxLocations]
      all_goals split <;> simp_all [valApproxLocations]
      apply mergeListSafe
      intro x hx y hy
      have smaller := List.sizeOf_lt_of_mem hx
      have xbound : sizeOf x + 1 < n := by omega
      exact ih (sizeOf x + 1) xbound x y (by omega) (ha x hx) (hb y hy)
  exact all (sizeOf a + 1) a b (by omega) safe.1 safe.2

/-- Inserting a safe approximation preserves safety of the map. -/
private theorem globalsInsertSafe (g : Spt ValApprox) (index : Nat) (a : ValApprox)
    (safe : valApproxLocations a) (globals : globalsApproxLocations g) :
    globalsApproxLocations (sptInsert index a g) := by
  intro key value lookup
  by_cases same : key = index
  · subst key
    rw [sptLookup_sptInsert_same] at lookup
    cases lookup
    exact safe
  · rw [sptLookup_sptInsert_ne index key a g same] at lookup
    exact globals key value lookup

/-- Primitive approximation preserves both value and global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_every_Fn_SOME"]
theorem knownOpLocations (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (h : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxLocations x) ∧ globalsApproxLocations g0) :
    valApproxLocations a ∧ globalsApproxLocations g := by
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
        | none => exact ⟨by simp [valApproxLocations], globals⟩
        | some value => exact ⟨by simpa [h] using globals index value h, globals⟩
      | cons x xs =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxLocations], globals⟩
    | setGlobal index =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxLocations], globals⟩
      | cons x xs =>
        have xSafe := safe x (by simp)
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        constructor
        · simp [valApproxLocations]
        · apply globalsInsertSafe _ _ _ _ globals
          cases h : sptLookup index g0 with
          | none => exact xSafe
          | some old => exact valApproxLocationsMerge old x ⟨globals index old h, xSafe⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxLocations], globals⟩
  | blockOp op =>
    cases op with
    | cons tag =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simpa [valApproxLocations] using safe, globals⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxLocations], globals⟩
  | intOp op =>
    cases op <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
      rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxLocations], globals⟩
  | memOp op =>
    cases op with
    | el =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxLocations], globals⟩
      | cons x xs =>
        cases xs with
        | nil =>
          cases x <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
            rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxLocations], globals⟩
        | cons y ys =>
          cases ys with
          | nil =>
            cases x <;> cases y <;> simp only [knownOpHOL, Prod.mk.injEq] at known
            all_goals try (rcases known with ⟨rfl, rfl⟩; exact ⟨by simp [valApproxLocations], globals⟩)
            split at known <;> simp_all [valApproxLocations]
            all_goals rcases known with ⟨rfl, rfl⟩
            · exact safe _ (List.getElem_mem ..)
            · simp [valApproxLocations]
          | cons z zs =>
            cases x <;> cases y <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
              rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxLocations], globals⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxLocations], globals⟩
  | _ =>
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    exact ⟨by simp [valApproxLocations], globals⟩


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
