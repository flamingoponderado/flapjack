module

public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Misc.Sptree.InsertProperty

@[expose] public section

/-! A parameterised form of the four approximation invariants.

The source `clos_knownProofScript.sml` states four separate primitive-operation
preservation results, one per approximation invariant: `val_approx_obeys_max_app`,
`val_approx_no_Labels`, `val_approx_every_Fn_SOME` and `val_approx_every_Fn_vs_NONE`.
All four share the same recursive shape over `val_approx`, differing only in the
predicate carried by a closure body. This module abstracts that shared shape once;
the four source theorems are recovered from it in their own modules. -/

namespace Flapjack.Compiler.Backend.ClosKnown
open Flapjack ClosLang

/-- A parameterised approximation invariant: a closure carries a leaf predicate
on its body, a tuple requires the invariant of every element, and every other
constructor is trivially safe. This is Flapjack infrastructure that abstracts the
common shape of the four source invariants; it has no single source original. -/
def valApproxAll (leaf : ClosLang.Exp → Prop) : ValApprox → Prop
  | .clos _ _ body _ => leaf body
  | .tuple _ values => ∀ value ∈ values, valApproxAll leaf value
  | _ => True
termination_by a => sizeOf a
decreasing_by
  all_goals
    have := List.sizeOf_lt_of_mem ‹_›
    simp_wf
    omega

/-- Every stored global approximation satisfies the parameterised invariant. -/
def globalsApproxAll (leaf : ClosLang.Exp → Prop) (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxAll leaf a

/-- A tuple element is strictly smaller than the tuple, for the measure induction.
This is Flapjack infrastructure for the parameterised invariant; it has no HOL
original. -/
theorem sizeOf_lt_of_mem_tuple {tag : Nat} {xs : List ValApprox} {v : ValApprox}
    (hv : v ∈ xs) : sizeOf v < sizeOf (ValApprox.tuple tag xs) := by
  have h := List.sizeOf_lt_of_mem hv
  simp_wf
  omega

/-- Merging preserves the parameterised invariant. -/
theorem valApproxAllMerge (leaf : ClosLang.Exp → Prop) (a b : ValApprox)
    (safe : valApproxAll leaf a ∧ valApproxAll leaf b) :
    valApproxAll leaf (mergeHOL a b) := by
  obtain ⟨ha, hb⟩ := safe
  induction a using (measure (fun a : ValApprox => sizeOf a)).wf.induction generalizing b with
  | h a ih =>
    cases a
    all_goals cases b
    all_goals simp_all [mergeHOL, valApproxAll]
    all_goals split
    all_goals simp_all [valApproxAll]
    rw [mergeListHOL_eq_zip]
    intro z member
    obtain ⟨⟨x, y⟩, paired, rfl⟩ := List.mem_map.mp member
    obtain ⟨hx, hy⟩ := List.of_mem_zip paired
    exact ih x (sizeOf_lt_of_mem_tuple hx) y (ha x hx) (hb y hy)

/-- Primitive approximation preserves the parameterised invariant. This is the
single proof shared by the four source `known_op_*` preservation theorems. -/
theorem knownOpAll (leaf : ClosLang.Exp → Prop) (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (h : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxAll leaf x) ∧ globalsApproxAll leaf g0) :
    valApproxAll leaf a ∧ globalsApproxAll leaf g := by
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
        | none => exact ⟨by simp [valApproxAll], globals⟩
        | some value => exact ⟨by simpa [h] using globals index value h, globals⟩
      | cons x xs => grind [knownOpHOL, valApproxAll]
    | setGlobal index =>
      cases args with
      | nil => grind [knownOpHOL, valApproxAll]
      | cons x xs =>
        have xSafe := safe x (by simp)
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        constructor
        · simp [valApproxAll]
        · apply sptInsert_preservesProperty _ _ _ _ _ globals
          cases h : sptLookup index g0 with
          | none => exact xSafe
          | some old => exact valApproxAllMerge leaf old x ⟨globals index old h, xSafe⟩
    | _ => grind [knownOpHOL, valApproxAll]
  | blockOp op =>
    cases op with
    | cons tag =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simpa [valApproxAll] using safe, globals⟩
    | _ => grind [knownOpHOL, valApproxAll]
  | intOp op =>
    cases op
    all_goals grind [knownOpHOL, valApproxAll]
  | memOp op =>
    cases op with
    | el =>
      cases args with
      | nil => grind [knownOpHOL, valApproxAll]
      | cons x xs =>
        cases xs with
        | nil =>
          cases x
          all_goals grind [knownOpHOL, valApproxAll]
        | cons y ys =>
          cases ys with
          | nil =>
            cases x with
            | tuple tag xs' =>
              cases y with
              | int i =>
                simp only [knownOpHOL] at known
                split at known
                · rcases known with ⟨rfl, rfl⟩
                  have hmem : valApproxAll leaf (.tuple tag xs') := safe _ (by simp)
                  simp only [valApproxAll] at hmem
                  exact ⟨hmem _ (List.getElem_mem ..), globals⟩
                · rcases known with ⟨rfl, rfl⟩
                  exact ⟨by simp [valApproxAll], globals⟩
              | _ =>
                simp only [knownOpHOL, Prod.mk.injEq] at known
                rcases known with ⟨rfl, rfl⟩
                exact ⟨by simp [valApproxAll], globals⟩
            | _ =>
              cases y
              all_goals simp only [knownOpHOL, Prod.mk.injEq] at known
              all_goals rcases known with ⟨rfl, rfl⟩
              all_goals exact ⟨by simp [valApproxAll], globals⟩
          | cons z zs =>
            cases x
            all_goals cases y
            all_goals grind [knownOpHOL, valApproxAll]
    | _ => grind [knownOpHOL, valApproxAll]
  | _ => grind [knownOpHOL, valApproxAll]

end Flapjack.Compiler.Backend.ClosKnown
