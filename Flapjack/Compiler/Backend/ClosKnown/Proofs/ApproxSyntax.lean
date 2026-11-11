module

public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Compiler.Backend.ClosKnown.Inline
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties
public import Flapjack.Misc.Sptree

@[expose] public section

/-! Closure annotation safety of known-function approximations. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps

/-- Inlined bodies in an approximation have no capture annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_every_Fn_vs_NONE_def"]
def valApproxVarsNone : ValApprox → Prop
  | .clos _ _ body _ => everyFnVarsNone [body]
  | .tuple _ values => ∀ value ∈ values, valApproxVarsNone value
  | _ => True
termination_by a => sizeOf a
decreasing_by all_goals have := List.sizeOf_lt_of_mem ‹_›; simp_wf; omega

/-- All stored global approximations satisfy the closure-body invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_every_Fn_vs_NONE_def"]
def globalsApproxVarsNone (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxVarsNone a

/-- Merging two safe approximations preserves closure-body safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_every_Fn_vs_NONE_merge"]
theorem valApproxVarsNoneMerge (a b : ValApprox)
    (safe : valApproxVarsNone a ∧ valApproxVarsNone b) : valApproxVarsNone (mergeHOL a b) := by
  obtain ⟨ha, hb⟩ := safe
  induction a using (measure (fun a : ValApprox => sizeOf a)).wf.induction generalizing b with
  | h a ih =>
    cases a <;> cases b <;> simp_all [mergeHOL, valApproxVarsNone]
    all_goals split <;> simp_all [valApproxVarsNone]
    rw [mergeListHOL_eq_zip]
    intro z member
    obtain ⟨⟨x, y⟩, paired, rfl⟩ := List.mem_map.mp member
    obtain ⟨hx, hy⟩ := List.of_mem_zip paired
    have smaller := List.sizeOf_lt_of_mem hx
    exact ih x (by simp_wf; omega) y (ha x hx) (hb y hy)

/-- Inserting a safe approximation preserves safety of the map. -/
private theorem globalsInsertSafe (g : Spt ValApprox) (index : Nat) (a : ValApprox)
    (safe : valApproxVarsNone a) (globals : globalsApproxVarsNone g) :
    globalsApproxVarsNone (sptInsert index a g) := by
  intro key value lookup
  by_cases same : key = index
  · subst key
    rw [sptLookup_sptInsert_same] at lookup
    cases lookup
    exact safe
  · rw [sptLookup_sptInsert_ne index key a g same] at lookup
    exact globals key value lookup

/-- Primitive approximation preserves both value and global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_every_Fn_vs_NONE"]
theorem knownOpVarsNone (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox)
    (h : knownOpHOL op args g0 = (a, g) ∧
      (∀ x ∈ args, valApproxVarsNone x) ∧ globalsApproxVarsNone g0) :
    valApproxVarsNone a ∧ globalsApproxVarsNone g := by
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
        | none => exact ⟨by simp [valApproxVarsNone], globals⟩
        | some value => exact ⟨by simpa [h] using globals index value h, globals⟩
      | cons x xs =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxVarsNone], globals⟩
    | setGlobal index =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxVarsNone], globals⟩
      | cons x xs =>
        have xSafe := safe x (by simp)
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        constructor
        · simp [valApproxVarsNone]
        · apply globalsInsertSafe _ _ _ _ globals
          cases h : sptLookup index g0 with
          | none => exact xSafe
          | some old => exact valApproxVarsNoneMerge old x ⟨globals index old h, xSafe⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxVarsNone], globals⟩
  | blockOp op =>
    cases op with
    | cons tag =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simpa [valApproxVarsNone] using safe, globals⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxVarsNone], globals⟩
  | intOp op =>
    cases op <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
      rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxVarsNone], globals⟩
  | memOp op =>
    cases op with
    | el =>
      cases args with
      | nil =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        exact ⟨by simp [valApproxVarsNone], globals⟩
      | cons x xs =>
        cases xs with
        | nil =>
          cases x <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
            rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxVarsNone], globals⟩
        | cons y ys =>
          cases ys with
          | nil =>
            cases x <;> cases y <;> simp only [knownOpHOL, Prod.mk.injEq] at known
            all_goals try (rcases known with ⟨rfl, rfl⟩; exact ⟨by simp [valApproxVarsNone], globals⟩)
            split at known <;> simp_all [valApproxVarsNone]
            all_goals rcases known with ⟨rfl, rfl⟩
            · exact safe _ (List.getElem_mem ..)
            · simp [valApproxVarsNone]
          | cons z zs =>
            cases x <;> cases y <;> simp only [knownOpHOL, Prod.mk.injEq] at known <;>
              rcases known with ⟨rfl, rfl⟩ <;> exact ⟨by simp [valApproxVarsNone], globals⟩
    | _ =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      exact ⟨by simp [valApproxVarsNone], globals⟩
  | _ =>
    simp only [knownOpHOL, Prod.mk.injEq] at known
    rcases known with ⟨rfl, rfl⟩
    exact ⟨by simp [valApproxVarsNone], globals⟩


/-- The inlining decision only extracts bodies with absent annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_every_Fn_vs_NONE"]
theorem decideInlineVarsNone {L : Type} (c : Config) (approx : ValApprox) (loc : Option L)
    (arity : Nat) (e : ClosLang.Exp)
    (h : valApproxVarsNone approx ∧ decideInlineHOL c approx loc arity = .letInline e) :
    everyFnVarsNone [e] := by
  obtain ⟨safe, decision⟩ := h
  cases approx <;> simp [decideInlineHOL] at decision
  case closNoInline target n => split at decision <;> simp_all
  case clos target n body size =>
    split at decision <;> simp_all [valApproxVarsNone]
    split at decision <;> simp_all

/-- Non-inlining recursive approximations contain no closure bodies. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "clos_gen_no_inline_every_Fn_vs_NONE"]
theorem closGenNoInlineVarsNone (fns : List (Nat × ClosLang.Exp)) (n x : Nat) :
    ∀ a ∈ closGenNoInline x n fns, valApproxVarsNone a := by
  induction fns generalizing n with
  | nil => simp [closGenNoInline]
  | cons fn rest ih =>
    cases fn with
    | mk arity body =>
      simp only [closGenNoInline, List.mem_cons, forall_eq_or_imp, valApproxVarsNone, true_and]
      exact ih (n + 1)

end Flapjack.Compiler.Backend.ClosKnown
