import Flapjack.Compiler.Backend.ClosKnown.KnownOp
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Flapjack.Misc.Sptree

/-! Global-write safety of known-function approximations. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps
open FlatProps (emptyGlobalBag)

/-- Inlined bodies in an approximation do not write globals. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_sgc_free_def" 248]
def valApproxSgcFree : ValApprox → Prop
  | .clos _ _ body _ => setGlobals body = emptyGlobalBag
  | .tuple _ values => ∀ value ∈ values, valApproxSgcFree value
  | _ => True
termination_by a => sizeOf a
decreasing_by all_goals have := List.sizeOf_lt_of_mem ‹_›; simp_wf; omega

/-- All stored global approximations satisfy the closure-body invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_sgc_free_def"]
def globalsApproxSgcFree (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxSgcFree a

/-- Pairwise merge preserves a property when it holds for each paired input. -/
private theorem mergeListSafe (xs ys : List ValApprox)
    (step : ∀ x ∈ xs, ∀ y ∈ ys, valApproxSgcFree (mergeHOL x y)) :
    ∀ z ∈ mergeListHOL xs ys, valApproxSgcFree z := by
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
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_sgc_free_merge"]
theorem valApproxSgcFreeMerge (a b : ValApprox)
    (safe : valApproxSgcFree a ∧ valApproxSgcFree b) : valApproxSgcFree (mergeHOL a b) := by
  have all : ∀ n (a b : ValApprox), sizeOf a < n →
      valApproxSgcFree a → valApproxSgcFree b → valApproxSgcFree (mergeHOL a b) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b bound ha hb
      cases a <;> cases b <;> simp_all [mergeHOL, valApproxSgcFree]
      all_goals split <;> simp_all [valApproxSgcFree]
      apply mergeListSafe
      intro x hx y hy
      have smaller := List.sizeOf_lt_of_mem hx
      have xbound : sizeOf x + 1 < n := by omega
      exact ih (sizeOf x + 1) xbound x y (by omega) (ha x hx) (hb y hy)
  exact all (sizeOf a + 1) a b (by omega) safe.1 safe.2

/-- Inserting a safe approximation preserves safety of the map. -/
private theorem globalsInsertSafe (g : Spt ValApprox) (index : Nat) (a : ValApprox)
    (safe : valApproxSgcFree a) (globals : globalsApproxSgcFree g) :
    globalsApproxSgcFree (sptInsert index a g) := by
  intro key value lookup
  by_cases same : key = index
  · subst key
    rw [sptLookup_sptInsert_same] at lookup
    cases lookup
    exact safe
  · rw [sptLookup_sptInsert_ne index key a g same] at lookup
    exact globals key value lookup

/-- Primitive approximation preserves both value and global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_preserves_esgc_free"]
theorem knownOpPreservesEsgcFree (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (known : knownOpHOL op args g0 = (a, g))
    (safe : ∀ x ∈ args, valApproxSgcFree x) (globals : globalsApproxSgcFree g0) :
    valApproxSgcFree a ∧ globalsApproxSgcFree g := by
  cases op with
  | globOp op =>
    cases op with
    | global index =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        cases h : sptLookup index g0 with
        | none => exact ⟨by simp [valApproxSgcFree], globals⟩
        | some value => exact ⟨by simpa [h] using globals index value h, globals⟩
      | cons x xs =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxSgcFree], globals⟩
    | setGlobal index =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxSgcFree], globals⟩
      | cons x xs =>
        have xSafe := safe x (by simp)
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        constructor
        · simp [valApproxSgcFree]
        · apply globalsInsertSafe _ _ _ _ globals
          cases h : sptLookup index g0 with
          | none => exact xSafe
          | some old => exact valApproxSgcFreeMerge old x ⟨globals index old h, xSafe⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxSgcFree], globals⟩
  | blockOp op =>
    cases op with
    | cons tag =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simpa [valApproxSgcFree] using safe, globals⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxSgcFree], globals⟩
  | intOp op =>
    cases op <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
      rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxSgcFree], globals⟩
  | memOp op =>
    cases op with
    | el =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxSgcFree], globals⟩
      | cons x xs =>
        cases xs with
        | nil =>
          cases x <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
            rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxSgcFree], globals⟩
        | cons y ys =>
          cases ys with
          | nil =>
            cases x <;> cases y <;> simp only [knownOpHOL, Prod.mk.injEq] at known
            all_goals try (rcases known with ⟨rfl, rfl⟩; exact ⟨by simp [valApproxSgcFree], globals⟩)
            split at known <;> simp_all [valApproxSgcFree]
            all_goals rcases known with ⟨rfl, rfl⟩
            · exact safe _ (List.getElem_mem ..)
            · simp [valApproxSgcFree]
          | cons z zs =>
            cases x <;> cases y <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
              rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxSgcFree], globals⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxSgcFree], globals⟩
  | _ =>
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    exact ⟨by simp [valApproxSgcFree], globals⟩

end Flapjack.Compiler.Backend.ClosKnown
