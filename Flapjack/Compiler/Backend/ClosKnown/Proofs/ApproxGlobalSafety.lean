module

public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
public import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties
public import Flapjack.Misc.Sptree.InsertProperty

@[expose] public section

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

/-- A body selected from a globally safe approximation writes no globals. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_inlD_LetInline_sgc_free"]
theorem decideInlineSgcFree {L : Type} (c : Config) (a : ValApprox) (loc : Option L)
    (n : Nat) (body : ClosLang.Exp)
    (h : decideInlineHOL c a loc n = .letInline body ∧ valApproxSgcFree a) :
    setGlobals body = emptyGlobalBag := by
  obtain ⟨decision, safe⟩ := h
  cases a <;> simp [decideInlineHOL] at decision
  case closNoInline target arity => split at decision <;> simp_all
  case clos target arity source size =>
    split at decision <;> simp_all [valApproxSgcFree]
    split at decision <;> simp_all

/-- All stored global approximations satisfy the closure-body invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_sgc_free_def"]
def globalsApproxSgcFree (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxSgcFree a

/-- Merging two safe approximations preserves closure-body safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_sgc_free_merge"]
theorem valApproxSgcFreeMerge (a b : ValApprox)
    (safe : valApproxSgcFree a ∧ valApproxSgcFree b) : valApproxSgcFree (mergeHOL a b) := by
  obtain ⟨ha, hb⟩ := safe
  induction a using (measure (fun a : ValApprox => sizeOf a)).wf.induction generalizing b with
  | h a ih =>
    cases a <;> cases b <;> simp_all [mergeHOL, valApproxSgcFree]
    all_goals split <;> simp_all [valApproxSgcFree]
    rw [mergeListHOL_eq_zip]
    intro z member
    obtain ⟨⟨x, y⟩, paired, rfl⟩ := List.mem_map.mp member
    obtain ⟨hx, hy⟩ := List.of_mem_zip paired
    have smaller := List.sizeOf_lt_of_mem hx
    exact ih x (by simp_wf; omega) y (ha x hx) (hb y hy)

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
        · apply sptInsert_preservesProperty _ _ _ _ _ globals
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

/-- A list has no global writes exactly when none of its expressions does. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "elist_globals_empty"]
theorem elistGlobalsEmpty (es : List ClosLang.Exp) :
    elistGlobals es = emptyGlobalBag ↔ ∀ e ∈ es, setGlobals e = emptyGlobalBag := by
  induction es with
  | nil => simp [elistGlobals]
  | cons e es ih => simp [elistGlobals, FlatProps.unionGlobalBag_eq_empty, ih]

/-- Generated non-inline closure approximations cannot contain global writes. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "clos_gen_noinline_val_approx_sgc_free"]
theorem closGenNoInlineSafe {α : Type} (n i : Nat) (fns : List (Nat × α)) :
    ∀ a ∈ closGenNoInline n i fns, valApproxSgcFree a := by
  induction fns generalizing i with
  | nil => simp [closGenNoInline]
  | cons fn rest ih =>
    cases fn with
    | mk arity body =>
      simp only [closGenNoInline, List.mem_cons, forall_eq_or_imp, valApproxSgcFree, true_and]
      exact ih (i + 1)

/-- A positive inline decision comes from a closure approximation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_LetInline_IMP_Clos"]
theorem decideInlineLetInlineImpClos {α : Type} (c : Config) (approx : ValApprox)
    (loc : Option α) (arity : Nat) (body : ClosLang.Exp)
    (h : decideInlineHOL c approx loc arity = .letInline body) :
    ∃ m size, approx = .clos m arity body size := by
  cases loc <;> cases approx <;> simp_all [decideInlineHOL]
  all_goals split at h <;> simp_all
  all_goals split at h <;> simp_all

/-- A positive inline decision also agrees with any supplied location. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_LetInline_IMP_Clos_lopt"]
theorem decideInlineLetInlineImpClosLoc (c : Config) (approx : ValApprox)
    (loc : Option Nat) (arity : Nat) (body : ClosLang.Exp)
    (h : decideInlineHOL c approx loc arity = .letInline body) :
    ∃ m size, approx = .clos m arity body size ∧ (loc = none ∨ loc = some m) := by
  cases loc with
  | none =>
    obtain ⟨m, size, eq⟩ := decideInlineLetInlineImpClos c approx none arity body h
    exact ⟨m, size, eq, Or.inl rfl⟩
  | some loc => cases approx <;> simp [decideInlineHOL] at h

end Flapjack.Compiler.Backend.ClosKnown
