import Flapjack.HolRef
import Flapjack.FiniteMap
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.EventsMono
import Flapjack.Pancake.Semantics.CrepSem.AddClock
import Flapjack.Pancake.PanCommon
import Flapjack.Pancake.Semantics.PanCommonProps

/-!
Crepe language properties from `cakeml/pancake/semantics/crepPropsScript.sml`.

This module depends on the language definitions and helpers in `CrepLang`;
the language module does not depend on these semantic properties.
-/

namespace Flapjack

universe u

/-- Faithful port of Cake `crepProps$cexp_heads_simp_def`
    (`cakeml/pancake/semantics/crepPropsScript.sml:11`). HOL rejects the
    argument when any inner list is empty, then maps total `HD` over the lists.
    The Lean default `.var 0` gives `headD` a total empty-list value; the guard
    makes that value unreachable in the result.

    FLAPJACK-SPECIFIC (not an exact HOL port): generic over `CrepExp α`, while
    HOL `crepLang$exp` is indexed by the word length. The exact width-indexed
    tag is on `cexpHeadsSimpW` below. -/
def cexpHeadsSimp : List (List (CrepExp α)) → Option (List (CrepExp α))
  | expressions =>
      if expressions.any List.isEmpty then none
      else some (expressions.map (fun expression => expression.headD (.var 0)))

/-- Exact width-indexed counterpart of HOL `cexp_heads_simp_def` over
    `CrepExp (BitVec width)`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "cexp_heads_simp_def"]
def cexpHeadsSimpW {width : Nat} [NeZero width]
    (expressions : List (List (CrepExp (BitVec width)))) :
    Option (List (CrepExp (BitVec width))) :=
  cexpHeadsSimp expressions

mutual
/-- Faithful port of Cake `crepProps$every_exp` from
    `cakeml/pancake/semantics/crepPropsScript.sml:1300`: `every_exp P e`
    holds when `P` holds of `e` and of every subexpression of `e`.

    FLAPJACK-SPECIFIC (not an exact HOL port): generic over `CrepExp α`, while
    HOL `crepLang$exp` is indexed by the word length. The exact width-indexed
    tag is on `crepEveryExpW` below. -/
def crepEveryExp (predicate : CrepExp α → Bool) : CrepExp α → Bool
  | .const value => predicate (.const value)
  | .var name => predicate (.var name)
  | .load address => predicate (.load address) && crepEveryExp predicate address
  | .load32 address => predicate (.load32 address) && crepEveryExp predicate address
  | .loadByte address => predicate (.loadByte address) && crepEveryExp predicate address
  | .loadGlob address => predicate (.loadGlob address)
  | .op operator arguments =>
      predicate (.op operator arguments) && crepEveryExpList predicate arguments
  | .crepOp operator arguments =>
      predicate (.crepOp operator arguments) && crepEveryExpList predicate arguments
  | .cmp operator left right =>
      predicate (.cmp operator left right) && crepEveryExp predicate left &&
        crepEveryExp predicate right
  | .shift operator left right =>
      predicate (.shift operator left right) && crepEveryExp predicate left &&
        crepEveryExp predicate right
  | .baseAddr => predicate .baseAddr
  | .topAddr => predicate .topAddr
/-- Cake's `EVERY (every_exp P)` list traversal. -/
def crepEveryExpList (predicate : CrepExp α → Bool) : List (CrepExp α) → Bool
  | [] => true
  | expression :: expressions =>
      crepEveryExp predicate expression && crepEveryExpList predicate expressions
end

/-- Exact width-indexed counterpart of HOL `every_exp_def` over
    `CrepExp (BitVec width)`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "every_exp_def"]
def crepEveryExpW {width : Nat} [NeZero width]
    (predicate : CrepExp (BitVec width) → Bool)
    (expression : CrepExp (BitVec width)) : Bool :=
  crepEveryExp predicate expression

/-- HOL `map_var_cexp_eq_var`: mapping `Var` over a list and flattening each
    expression's variable list recovers the original list. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type,
-- while HOL `prog`/`exp` are indexed by the word length.  The exact width-indexed
-- tag is on the corresponding `map_var_crepExpVars_eqW` declaration below.
theorem map_var_crepExpVars_eq {α : Type} (names : List Nat) :
    (names.map (CrepExp.var (α := α))).flatMap crepExpVars = names := by
  induction names with
  | nil => rfl
  | cons name names ih => simp [crepExpVars_var, ih]

/-- Flapjack-specific infrastructure: the length result for the pipeline's
    general-stride `loadShape`.  This is not a HOL port, because it quantifies an
    explicit stride; the exact HOL counterpart is `length_loadShape_eq_shape`. -/
theorem loadShape_length [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value : CrepExp α) :
    (loadShape address stride count value).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShape, ih]

/-- Faithful port of Cake `crepProps$length_load_shape_eq_shape`
    (`cakeml/pancake/semantics/crepPropsScript.sml:30`), stated over the fixed
    `byte$bytes_in_word` stride.  The `CrepBytesInWord` instance supplies the
    fixed byte width, so the explicit quantified variables are HOL's `n a e`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type.
-- HOL's exact expression-carrier theorem is `length_loadShapeHOLW` in
-- this module below; this production helper remains useful for generic code.
theorem length_loadShape_eq_shape [BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]
    (count : Nat) (address : α) (value : CrepExp α) :
    (loadShapeBytes address count value).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShapeBytes, ih]

/-! Faithful port of Cake `crepProps$length_load_globals_eq_read_size`
    (`cakeml/pancake/semantics/crepPropsScript.sml:467`). -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type,
-- while HOL `prog`/`exp` are indexed by the word length.  The exact width-indexed
-- tag is on the corresponding `loadGlobals_lengthW` declaration below.
theorem loadGlobals_length {α : Type u}
    (address : BitVec 5) (count : Nat) :
    (loadGlobals (α := α) address count).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadGlobals, ih]

/-! Faithful port of Cake
    `crepProps$el_load_globals_elem`
    (`cakeml/pancake/semantics/crepPropsScript.sml:474`). The Lean `BitVec`
    specializes HOL's polymorphic word, `BitVec.ofNat` represents `n2w`, and
    the bound lets Lean use total list indexing just as HOL's `EL` does. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type,
-- while HOL `prog`/`exp` are indexed by the word length.  The exact width-indexed
-- tag is on the corresponding `loadGlobals_getElemW` declaration below.
theorem loadGlobals_getElem
    (address : BitVec 5) (count n : Nat) (h : n < count) :
    (loadGlobals (α := α) address count)[n]'(by
      simpa only [loadGlobals_length] using h) =
        .loadGlob (address + BitVec.ofNat 5 n) := by
  induction count generalizing address n with
  | zero => omega
  | succ count ih =>
      cases n with
      | zero => simp [loadGlobals]
      | succ n =>
          have hlt : n < count := by omega
          simp only [loadGlobals, List.getElem_cons_succ]
          rw [ih (address := address + 1) (n := n) hlt]
          have haddr :
              (address + 1) + BitVec.ofNat 5 n =
                address + BitVec.ofNat 5 (n + 1) := by
            rw [BitVec.ofNat_add]
            simp
            ac_rfl
          rw [haddr]

/-- Faithful port of Cake `crepProps$var_cexp_load_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:698`): the loads generated by
    `load_globals` contain no local variables. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): generic over the word element type,
-- while HOL `prog`/`exp` are indexed by the word length.  The exact width-indexed
-- tag is on the corresponding `loadGlobals_crepExpVars_emptyW` declaration below.
theorem loadGlobals_crepExpVars_empty {α : Type u}
    (address : BitVec 5) (count : Nat) :
    (loadGlobals (α := α) address count).flatMap crepExpVars = [] := by
  induction count generalizing address with
  | zero => simp [loadGlobals]
  | succ count ih => simp [loadGlobals, ih, crepExpVars]

/-! Flapjack analogue of Cake
    `crepProps$assigned_free_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:458`). Its width-specialized
    counterpart below still uses String-backed function names in `CrepProg`,
    unlike HOL's `mlstring` identifiers, so neither declaration is tagged. -/
theorem crepAssignedFreeVars_nestedSeq_storeGlobals {α : Type u}
    (address : BitVec 5) (values : List (CrepExp α)) :
    crepAssignedFreeVars (crepNestedSeq (storeGlobals (α := α) address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobals, crepNestedSeq, crepAssignedFreeVars]
  | cons value values ih =>
      simp [storeGlobals, crepNestedSeq, crepAssignedFreeVars, ih]

/-! Flapjack analogue of Cake `crepProps$assigned_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:449`). Its width-specialized
    counterpart below still uses String-backed function names in `CrepProg`,
    unlike HOL's `mlstring` identifiers, so neither declaration is tagged. -/
theorem crepAssignedVars_nestedSeq_storeGlobals {α : Type u}
    (address : BitVec 5) (values : List (CrepExp α)) :
    crepAssignedVars (crepNestedSeq (storeGlobals (α := α) address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobals, crepNestedSeq, crepAssignedVars]
  | cons value values ih =>
      simp [storeGlobals, crepNestedSeq, crepAssignedVars, ih]

/-- Flapjack analogue of Cake
    `crepProps$assigned_free_vars_IMP_assigned_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:373`): every free variable of
    a program is an assigned variable of that program. Its width-specialized
    counterpart below still uses String-backed function names in `CrepProg`,
    unlike HOL's `mlstring` identifiers, so neither declaration is tagged; the
    exact `mlstring`/width-indexed port is
    `crepAssignedFreeVarsHOL_imp_crepAssignedVarsHOL` below. -/
theorem mem_crepAssignedFreeVars_imp_mem_crepAssignedVars (program : CrepProg α) (name : Nat)
    (h : name ∈ crepAssignedFreeVars program) : name ∈ crepAssignedVars program := by
  revert h
  induction program using crepAssignedFreeVars.induct with
  | case1 => intro h; simp [crepAssignedFreeVars] at h
  | case2 => intro h; simp_all [crepAssignedFreeVars, crepAssignedVars]
  | case3 => intro h; simpa [crepAssignedFreeVars, crepAssignedVars] using h
  | case4 => intro h; simpa [crepAssignedFreeVars, crepAssignedVars] using h
  | case5 =>
      intro h
      simp only [crepAssignedFreeVars, crepAssignedVars, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case6 =>
      intro h
      simp only [crepAssignedFreeVars, crepAssignedVars, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case7 => intro h; simp_all [crepAssignedFreeVars, crepAssignedVars]
  | case8 =>
      intro h
      simp only [crepAssignedFreeVars, crepAssignedVars, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case9 => intro h; simpa [crepAssignedFreeVars, crepAssignedVars] using h
  | case10 => intro h; simpa [crepAssignedFreeVars, crepAssignedVars] using h
  | case11 => intro h; simp [crepAssignedFreeVars] at h

/-- Exact port of Cake `crepProps$assigned_free_vars_IMP_assigned_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:373-378`) over the exact
    `CrepProgHOL` carrier (MlString function names and width-indexed words):
    every free variable of a program is an assigned variable of that program. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_IMP_assigned_vars"]
theorem crepAssignedFreeVarsHOL_imp_crepAssignedVarsHOL {width : Nat} [NeZero width]
    (program : CrepProgHOL width) (name : Nat)
    (h : name ∈ crepAssignedFreeVarsHOL program) : name ∈ crepAssignedVarsHOL program := by
  revert h
  induction program using crepAssignedFreeVarsHOL.induct with
  | case1 => intro h; simp [crepAssignedFreeVarsHOL] at h
  | case2 => intro h; simp_all [crepAssignedFreeVarsHOL, crepAssignedVarsHOL]
  | case3 => intro h; simpa [crepAssignedFreeVarsHOL, crepAssignedVarsHOL] using h
  | case4 => intro h; simpa [crepAssignedFreeVarsHOL, crepAssignedVarsHOL] using h
  | case5 =>
      intro h
      simp only [crepAssignedFreeVarsHOL, crepAssignedVarsHOL, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case6 =>
      intro h
      simp only [crepAssignedFreeVarsHOL, crepAssignedVarsHOL, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case7 => intro h; simp_all [crepAssignedFreeVarsHOL, crepAssignedVarsHOL]
  | case8 =>
      intro h
      simp only [crepAssignedFreeVarsHOL, crepAssignedVarsHOL, List.mem_append] at h ⊢
      rcases h with h | h <;> simp_all
  | case9 => intro h; simpa [crepAssignedFreeVarsHOL, crepAssignedVarsHOL] using h
  | case10 => intro h; simpa [crepAssignedFreeVarsHOL, crepAssignedVarsHOL] using h
  | case11 => intro h; simp [crepAssignedFreeVarsHOL] at h

/-- Production bridge: transporting the exact HOL theorem across `crepProgToHOL`
    recovers the executable `CrepProg` implication, so the exact-carrier port and
    the production property agree. -/
theorem crepAssignedFreeVars_imp_crepAssignedVars_via_HOL {width : Nat} [NeZero width]
    (program : CrepProg (BitVec width)) (name : Nat)
    (h : name ∈ crepAssignedFreeVars program) : name ∈ crepAssignedVars program := by
  have hhol : name ∈ crepAssignedFreeVarsHOL (crepProgToHOL program) := by
    simpa [crepProgToHOL_crepAssignedFreeVars] using h
  have hmem := crepAssignedFreeVarsHOL_imp_crepAssignedVarsHOL (crepProgToHOL program) name hhol
  simpa [crepProgToHOL_crepAssignedVars] using hmem

/-- Flapjack analogue of Cake `crepProps$nested_seq_assigned_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:411`): the assignments
    generated by `nested_seq (MAP2 Assign ns vs)` assign exactly `ns`.

    This and its width-specialized `...W` wrapper remain untagged: both use the
    production `CrepProg` carrier, whose `Call`/`ExtCall` names are Lean
    `String`, while HOL `prog` uses `mlstring`. The exact `CrepProgHOL` carrier
    exists, but `assigned_vars` and this theorem have not yet been ported over
    it. The direct HOL rows in `crep_assigned_vars_probe.out` check concrete
    observations only; they do not bridge the carrier mismatch. -/
theorem crepAssignedVars_nestedSeq_assign_zipWith (names : List Nat)
    (values : List (CrepExp α)) (h : names.length = values.length) :
    crepAssignedVars
        (crepNestedSeq
          (names.zipWith (fun name value => CrepProg.assign name value) values)) =
      names := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => simp [crepNestedSeq, crepAssignedVars]
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.zipWith_cons_cons, List.length_cons] at h ⊢
          simp [crepNestedSeq, crepAssignedVars, ih values (by omega)]

/-- Flapjack analogue of Cake
    `crepProps$nested_seq_assigned_free_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:420`): the assignments
    generated by `nested_seq (MAP2 Assign ns vs)` assign exactly `ns`. Its
    width-specialized counterpart below still uses String-backed function names
    in `CrepProg`, unlike HOL's `mlstring` identifiers, so neither declaration
    is tagged. -/
theorem crepAssignedFreeVars_nestedSeq_assign_zipWith {α : Type u} (names : List Nat)
    (values : List (CrepExp α)) (h : names.length = values.length) :
    crepAssignedFreeVars
        (crepNestedSeq
          (names.zipWith (fun name value => CrepProg.assign name value) values)) =
      names := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => simp [crepNestedSeq, crepAssignedFreeVars]
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.zipWith_cons_cons, List.length_cons] at h ⊢
          simp [crepNestedSeq, crepAssignedFreeVars, ih values (by omega)]

/-- Variable-form of `nested_seq_assigned_free_vars_eq`: assigning each name
    from a temporary variable still assigns exactly the names. This is the form
    emitted by the non-`distinctLists` branch of `compileProgHOL`. -/
theorem crepAssignedFreeVars_nestedSeq_assign_var_zipWith {α : Type u}
    (names temporaries : List Nat) (h : names.length = temporaries.length) :
    crepAssignedFreeVars
        (crepNestedSeq
          (names.zipWith
            (fun name temporary => CrepProg.assign name (.var temporary : CrepExp α))
            temporaries)) =
      names := by
  induction names generalizing temporaries with
  | nil =>
      cases temporaries with
      | nil => simp [crepNestedSeq, crepAssignedFreeVars]
      | cons temporary temporaries => simp at h
  | cons name names ih =>
      cases temporaries with
      | nil => simp at h
      | cons temporary temporaries =>
          simp only [List.zipWith_cons_cons, List.length_cons] at h ⊢
          simp [crepNestedSeq, crepAssignedFreeVars, ih temporaries (by omega)]

/-- Untagged production adapter: writing a `word_lab` global cell on the
    14-field `CrepRuntimeState` leaves every local binding unchanged. HOL's
    exact `FLOOKUP_set_globals` (crepPropsScript.sml:297) is over the 11-field
    state; the same field equation is proved below over Flapjack's state, whose
    code map still has a String/`mlstring` carrier mismatch. -/
theorem flookup_setCrepRuntimeGlobals_locals {α σ : Type}
    (gv : BitVec 5) (w : PanWordLab α) (s : CrepRuntimeState α σ) (n : Nat) :
    FLOOKUP (setCrepRuntimeGlobals gv w s).locals n = FLOOKUP s.locals n :=
  rfl

/-- Generic-`α` analogue of `crepProps$FLOOKUP_set_globals`, deliberately
    untagged because HOL's state code map is keyed by `mlstring` and stores
    `mlstring`-bearing programs, while Flapjack uses `String`. The width-indexed
    analogue is `flookup_setCrepHolGlobals_localsW` below.
    `FLOOKUP (set_globals gv w s).locals n = FLOOKUP s.locals n`
    (crepPropsScript.sml:297). -/
theorem flookup_setCrepHolGlobals_locals {α σ : Type}
    (gv : BitVec 5) (w : PanWordLab α) (s : CrepHolState α σ) (n : Nat) :
    FLOOKUP (setCrepHolGlobals gv w s).locals n = FLOOKUP s.locals n :=
  rfl

/-- Flapjack width-specialized analogue of Cake `crepProps$FLOOKUP_set_globals`
    (`cakeml/pancake/semantics/crepPropsScript.sml:297-301`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.101`.
    The HOL equation `FLOOKUP (set_globals gv w s).locals n = FLOOKUP s.locals n`
    holds pointwise here (`rfl`), because `setCrepHolGlobalsW` updates only the
    `globals` component, exactly as HOL's `set_globals_def` does
    (crepSemScript.sml:61-63). The mismatch is the quantified whole-state carrier:
    `CrepHolState (BitVec width)` stores `locals`/`globals`/`code` as unrestricted
    `Nat -> Option`, `BitVec 5 -> Option` and `FunName -> Option` functions that
    admit infinite support, a strict superset of HOL's finite maps, and `code` is
    keyed by `FunName = String` rather than `funname = mlstring`
    (crepSemScript.sml:19-32). Because the quantifier ranges over a whole state,
    `names_as_string` cannot qualify the identifier and no `NameRanged` byte
    witness applies. The underlying update boundary is pinned directly by the
    `set_globals_direct=(SOME (Word 22w),SOME (Word 7w),NONE)` row of
    `scripts/hol-probes/crep_store_global_probe.out` (writing global `4w` leaves
    local lookups `3` and `9` unchanged) and sampled by
    `Flapjack/Test/CrepGlobalShapeParity.lean:110-116`. Restoring the tag depends
    on the exact finite-support Crep carrier tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
theorem flookup_setCrepHolGlobals_localsW {width : Nat} [NeZero width] {σ : Type}
    (gv : BitVec 5) (w : PanWordLab (BitVec width))
    (s : CrepHolState (BitVec width) σ) (n : Nat) :
    FLOOKUP (setCrepHolGlobalsW gv w s).locals n = FLOOKUP s.locals n :=
  rfl

/-- Kernel-checked bridge: the width-indexed `FLOOKUP_set_globals` analogue
    agrees with the generic production statement at `BitVec width`. -/
theorem flookup_setCrepHolGlobals_localsW_eq_generic {width : Nat} [NeZero width] {σ : Type}
    (gv : BitVec 5) (w : PanWordLab (BitVec width))
    (s : CrepHolState (BitVec width) σ) (n : Nat) :
    FLOOKUP (setCrepHolGlobalsW gv w s).locals n =
      FLOOKUP (setCrepHolGlobals gv w s).locals n :=
  rfl

/-! Membership equations for `crepAssignedFreeVars`, exposing Cake's
`assigned_free_vars_def` (`cakeml/pancake/crepLangScript.sml:149`) clause by
clause.  These keep the `not_mem_context_assigned_mem_gt` induction from
unfolding the well-founded definition at every `compileProgHOL` branch. -/

theorem mem_crepAssignedFreeVars_assign {α : Type u} (name : Nat)
    (value : CrepExp α) (x : Nat) :
    x ∈ crepAssignedFreeVars (.assign name value : CrepProg α) ↔ x = name := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_primitive {α : Type u} (names : List Nat)
    (operator : PrimOp) (arguments : List Nat) (x : Nat) :
    x ∈ crepAssignedFreeVars (.primitive names operator arguments : CrepProg α) ↔
      x ∈ names := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_seq {α : Type u} (first second : CrepProg α)
    (x : Nat) :
    x ∈ crepAssignedFreeVars (.seq first second) ↔
      x ∈ crepAssignedFreeVars first ∨ x ∈ crepAssignedFreeVars second := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_ite {α : Type u} (condition : CrepExp α)
    (thenBranch elseBranch : CrepProg α) (x : Nat) :
    x ∈ crepAssignedFreeVars (.ite condition thenBranch elseBranch) ↔
      x ∈ crepAssignedFreeVars thenBranch ∨ x ∈ crepAssignedFreeVars elseBranch := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_while {α : Type u} (condition : CrepExp α)
    (body : CrepProg α) (x : Nat) :
    x ∈ crepAssignedFreeVars (.while condition body) ↔
      x ∈ crepAssignedFreeVars body := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_shMem {α : Type u} (operator : CrepMemOp)
    (name : Nat) (address : CrepExp α) (x : Nat) :
    x ∈ crepAssignedFreeVars (.shMem operator name address) ↔ x = name := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_call_some_some {α : Type u} (returns : List Nat)
    (code : α) (handler : CrepProg α) (name : FunName)
    (arguments : List (CrepExp α)) (x : Nat) :
    x ∈ crepAssignedFreeVars (.call (some (returns, some (code, handler))) name arguments) ↔
      x ∈ returns ∨ x ∈ crepAssignedFreeVars handler := by
  simp [crepAssignedFreeVars]

theorem mem_crepAssignedFreeVars_call_some_none {α : Type u} (returns : List Nat)
    (name : FunName) (arguments : List (CrepExp α)) (x : Nat) :
    x ∈ crepAssignedFreeVars (.call (some (returns, none)) name arguments) ↔
      x ∈ returns := by
  simp [crepAssignedFreeVars]

/-- CakeML's `flookup_res_var_distinct_zip_eq` (`crepPropsScript.sml:777`):
    folding `res_var` over the zip of a key list with its values leaves a key
    that is not in the key list untouched. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL quantifies the key type freely, but this
-- statement requires [BEq α] [LawfulBEq α] because `resVar` uses Boolean key equality.
-- The raw function carrier also admits infinite support. Faithful finite-support port tracked by
-- bead flapjack-pxn.18.5.5.19 / flapjack-pxn.18.3.7.1.3.1.1.3.1.
theorem flookup_res_var_distinct_zip_eq [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List (Option β)) (fm : FiniteMap α β) (x : α)
    (hlen : xs.length = ys.length) (hx : x ∉ xs) :
    FLOOKUP ((xs.zip ys).foldl resVar fm) x = FLOOKUP fm x :=
  FLOOKUP_foldl_resVar_zip_not_mem xs ys fm x hlen hx

/-- HOL-equality (`=`) form of CakeML's `flookup_res_var_distinct_zip_eq`
    (`crepPropsScript.sml:777`) over the raw function carrier.  FLAPJACK-SPECIFIC
    (not an exact HOL port): `DecidableEq` removes the Boolean-`BEq` side
    condition, but `FiniteMap α β := α → Option β` admits infinite-support
    inhabitants whereas HOL `α |-> β` is finite-support, so the statement still
    ranges over functions HOL cannot represent.  Kept untagged; identical raw
    function endpoints are also an unsound surrogate for HOL `FUPDATE`/`res_var`.
    Faithful finite-support port tracked by bead
    `flapjack-pxn.18.3.7.1.3.1.1.3.1` (over `HolFiniteMapExact`). -/
theorem flookup_res_var_distinct_zip_eq_hol {α : Type} {β : Type} [DecidableEq α]
    (xs : List α) (ys : List (Option β)) (fm : FiniteMap α β) (x : α)
    (hlen : xs.length = ys.length) (hx : x ∉ xs) :
    FLOOKUP ((xs.zip ys).foldl resVarHOL fm) x = FLOOKUP fm x :=
  FLOOKUP_foldl_resVarHOL_zip_not_mem xs ys fm x hlen hx

/-- Flapjack analogue of Cake `crepProps$dec_clock_simp`
    (`cakeml/pancake/semantics/crepPropsScript.sml:267-278`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.105`.
    The clause set matches HOL's ten field equations exactly: locals, globals,
    code, memory, memaddrs, sh_memaddrs, be, ffi, base_addr and top_addr are all
    preserved by the clock decrement (`decCrepHolClockW`, itself the analogue of
    `dec_clock_def`). The mismatch is the quantified whole-state carrier:
    `CrepHolState (BitVec width)` stores `locals`/`globals` as unrestricted
    `Nat → Option` / `BitVec 5 → Option` functions and `code` as
    `FunName → Option`, where HOL's `crepSem$state` uses finite maps and
    `funname = mlstring` (crepSemScript.sml:19-32). A whole-state result also
    cannot be authorized by `names_as_string`, and no `NameRanged` byte witness
    applies. Direct HOL rows `dec_clock_clock` / `dec_clock_globals` /
    `dec_clock_be` / `dec_clock_top` are in
    `scripts/hol-probes/crep_dec_clock_simp_probe.out`, and the clause shapes are
    sampled by `Flapjack/Test/CrepGlobalShapeParity.lean:601-605`. No exact
    finite-support carrier exists yet; restoring the tag depends on
    `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
theorem decCrepHolClock_simp {width : Nat} [NeZero width] {σ : Type} (s : CrepHolState (BitVec width) σ) :
    (decCrepHolClockW s).locals = s.locals ∧
      (decCrepHolClockW s).globals = s.globals ∧
      (decCrepHolClockW s).code = s.code ∧
      (decCrepHolClockW s).memory = s.memory ∧
      (decCrepHolClockW s).memaddrs = s.memaddrs ∧
      (decCrepHolClockW s).shMemaddrs = s.shMemaddrs ∧
      (decCrepHolClockW s).bigEndian = s.bigEndian ∧
      (decCrepHolClockW s).ffi = s.ffi ∧
      (decCrepHolClockW s).baseAddress = s.baseAddress ∧
      (decCrepHolClockW s).topAddress = s.topAddress := by
  simp [decCrepHolClockW]

/-- Flapjack analogue of Cake `crepProps$empty_locals_simp`
    (`cakeml/pancake/semantics/crepPropsScript.sml:282-294`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.106`.
    The clause set matches HOL's ten field equations exactly: globals, code,
    memory, memaddrs, sh_memaddrs, clock, be, ffi, base_addr and top_addr are all
    preserved when `locals` is cleared (`emptyCrepHolLocalsW`, itself the
    analogue of `empty_locals_def`). The mismatch is again the quantified
    whole-state carrier: `CrepHolState (BitVec width)` stores `locals`/`globals`
    as unrestricted `Nat → Option` / `BitVec 5 → Option` functions and `code` as
    `FunName → Option`, where HOL's `crepSem$state` uses finite maps and
    `funname = mlstring` (crepSemScript.sml:19-32). A whole-state result also
    cannot be authorized by `names_as_string`, and no `NameRanged` byte witness
    applies. Direct HOL rows `empty_locals_locals` / `empty_locals_clock` /
    `empty_locals_memory` are in
    `scripts/hol-probes/crep_dec_clock_simp_probe.out`, with
    `empty_locals_none` / `empty_locals_fields_preserved` in
    `scripts/hol-probes/crep_local_updates_probe.out`; the clause shapes are
    sampled by `Flapjack/Test/CrepGlobalShapeParity.lean:608-612`. No exact
    finite-support carrier exists yet; restoring the tag depends on
    `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
theorem emptyCrepHolLocals_simp {width : Nat} [NeZero width] {σ : Type} (s : CrepHolState (BitVec width) σ) :
    (emptyCrepHolLocalsW s).globals = s.globals ∧
      (emptyCrepHolLocalsW s).code = s.code ∧
      (emptyCrepHolLocalsW s).memory = s.memory ∧
      (emptyCrepHolLocalsW s).memaddrs = s.memaddrs ∧
      (emptyCrepHolLocalsW s).shMemaddrs = s.shMemaddrs ∧
      (emptyCrepHolLocalsW s).clock = s.clock ∧
      (emptyCrepHolLocalsW s).bigEndian = s.bigEndian ∧
      (emptyCrepHolLocalsW s).ffi = s.ffi ∧
      (emptyCrepHolLocalsW s).baseAddress = s.baseAddress ∧
      (emptyCrepHolLocalsW s).topAddress = s.topAddress := by
  simp [emptyCrepHolLocalsW]

/-! ## Width-indexed crepProps counterparts

HOL `crepPropsScript.sml` `exp`/`prog` are word-length indexed (`'a word`), so
the generic-over-`α` helper theorems above need positive-width specializations.
Expression-only wrappers below retain exact tags because `CrepExp` contains no
String-backed identifiers. The later program-property counterparts are
untagged: `CrepProg` embeds `FunName = String` in its `Call` and `ExtCall`
constructors, whereas HOL uses `funname = mlstring`. A width-indexed word payload
does not repair that identifier-carrier mismatch. -/

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "map_var_cexp_eq_var"]
theorem map_var_crepExpVars_eqW {width : Nat} [NeZero width] (names : List Nat) :
    (names.map (CrepExp.var (α := BitVec width))).flatMap crepExpVarsW = names :=
  map_var_crepExpVars_eq names

/-! Exact expression-carrier corollary of HOL
    `crepProps$length_load_shape_eq_shape` (`crepPropsScript.sml:30`). -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "length_load_shape_eq_shape"]
theorem length_loadShapeHOLW {width : Nat} [NeZero width]
    (count : Nat) (address : BitVec width) (value : CrepExpHOL width) :
    (loadShapeBytesHOLW address count value).length = count := by
  induction count generalizing address <;> simp [loadShapeBytesHOLW, *]

/-- BitVec stride algebra used by the exact `eval_load_shape_el_rel` port:
    advancing the running address by one `bytes_in_word` matches HOL's closed
    form `a + bytes_in_word * n2w n`. -/
private theorem loadShape_stride_step {width : Nat}
    (address stride : BitVec width) (n : Nat) :
    (address + stride) + stride * BitVec.ofNat width n =
      address + stride * BitVec.ofNat width (n + 1) := by
  rw [BitVec.ofNat_add, BitVec.mul_add]
  simp only [BitVec.mul_one]
  ac_rfl

/-- The zero-address special case: HOL `load_shape 0 _ e` emits the bare
    `Load e`, which evaluates exactly like `Load (Op Add [e; Const 0])`. -/
private theorem eval_load_op_add_zero {width : Nat} [NeZero width] {σ : Type}
    (targetState : CrepSemHOLState width σ) [DecidablePred targetState.memaddrs]
    (value : CrepExpHOL width) :
    evalCrepSemHOLExp targetState
        (.load (.op .add [value, .const (0 : BitVec width)])) =
      evalCrepSemHOLExp targetState (.load value) := by
  cases h : evalCrepSemHOLExp targetState value with
  | none => simp [evalCrepSemHOLExp, h]
  | some lab =>
      cases lab with
      | word w => simp [evalCrepSemHOLExp, h, wordOpHOL, wordOp]

/-- Exact width-indexed counterpart of HOL `crepProps$eval_load_shape_el_rel`
    (`cakeml/pancake/semantics/crepPropsScript.sml:40`): for `n < count`, the
    `n`-th generated load of `loadShapeBytesHOLW` evaluates exactly like the
    strided `Load (Op Add [e; Const (a + bytes_in_word * n2w n)])`, where the
    byte stride `bytes_in_word` is `n2w (width DIV 8)` and `n2w` is
    `BitVec.ofNat`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "eval_load_shape_el_rel"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem eval_loadShapeBytesHOLW_getElem {width : Nat} [NeZero width] {σ : Type}
    (targetState : CrepSemHOLState width σ) [DecidablePred targetState.memaddrs]
    (address : BitVec width) (count : Nat) (value : CrepExpHOL width) (n : Nat)
    (hn : n < count) :
    evalCrepSemHOLExp targetState
        ((loadShapeBytesHOLW address count value)[n]'(by
          simpa only [length_loadShapeHOLW] using hn)) =
      evalCrepSemHOLExp targetState
        (.load (.op .add [value,
          .const (address + BitVec.ofNat width (width / 8) * BitVec.ofNat width n)])) := by
  induction count generalizing address n with
  | zero => omega
  | succ count ih =>
      simp only [loadShapeBytesHOLW]
      cases n with
      | zero =>
          simp only [List.getElem_cons_zero]
          split
          · rename_i hcond
            have haddr : address = 0 := by simpa only [beq_iff_eq] using hcond
            subst haddr
            exact (eval_load_op_add_zero targetState value).symm
          · simp
      | succ n =>
          have hn' : n < count := by omega
          rw [List.getElem_cons_succ]
          rw [ih (address := address + BitVec.ofNat width (width / 8)) (n := n) hn']
          rw [loadShape_stride_step]

theorem length_loadShape_eq_shapeW {width : Nat} [NeZero width]
    (count : Nat) (address : BitVec width) (value : CrepExp (BitVec width)) :
    (loadShapeBytesW address count value).length = count := by
  simpa [loadShapeBytesW] using length_loadShape_eq_shape count address value

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "length_load_globals_eq_read_size"]
theorem loadGlobals_lengthW {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) :
    (loadGlobalsW (width := width) address count).length = count :=
  loadGlobals_length address count

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "el_load_globals_elem"]
theorem loadGlobals_getElemW {width : Nat} [NeZero width]
    (address : BitVec 5) (count n : Nat) (h : n < count) :
    (loadGlobalsW (width := width) address count)[n]'(by
      simpa only [loadGlobals_lengthW] using h) =
        .loadGlob (address + BitVec.ofNat 5 n) :=
  loadGlobals_getElem address count n h

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "var_cexp_load_globals_empty"]
theorem loadGlobals_crepExpVars_emptyW {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) :
    (loadGlobalsW (width := width) address count).flatMap crepExpVarsW = [] :=
  loadGlobals_crepExpVars_empty address count

/-- Flapjack width-specialized analogue of Cake
    `crepProps$assigned_free_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:458-465`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.103`.
    HOL proves `!es ad. assigned_free_vars (nested_seq (store_globals ad es)) = []`;
    the Lean equation over `crepNestedSeqW`/`storeGlobalsW` matches it
    pointwise, since `storeGlobals` builds only `StoreGlob` programs, whose
    `assigned_free_vars` clause is empty (crepLangScript.sml:149-162). The
    mismatch is the imported programme carrier: HOL's `crepLang$prog` embeds
    `funname = mlstring` in `Call`/`ExtCall`, while Lean's `CrepProg` embeds
    `FunName = String`; because the quantifier ranges over a `CrepProg`, its
    function names can differ from HOL's and no `mlstring` identifier exists for
    `names_as_string`, nor a `NameRanged` byte witness. The `store_globals` list
    shape is pinned by `empty`/`one`/`two` rows of
    `scripts/hol-probes/crep_store_globals_probe.out` and sampled by
    `Flapjack/Test/CrepAssignedVarsParity.lean:84-86,108-111`. Restoring the tag
    depends on the exact mlstring-carrier port `flapjack-pxn.18.3.5.8.8`. -/
theorem crepAssignedFreeVars_nestedSeq_storeGlobalsW {width : Nat} [NeZero width]
    (address : BitVec 5) (values : List (CrepExp (BitVec width))) :
    crepAssignedFreeVarsW (crepNestedSeqW (storeGlobalsW address values)) = [] :=
  crepAssignedFreeVars_nestedSeq_storeGlobals address values

/-- Flapjack width-specialized analogue of Cake
    `crepProps$assigned_vars_store_globals_empty`
    (`cakeml/pancake/semantics/crepPropsScript.sml:449-456`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.104`.
    HOL proves `!es ad. assigned_vars (nested_seq (store_globals ad es)) = []`;
    the Lean equation over `crepNestedSeqW`/`storeGlobalsW` matches it pointwise,
    since `storeGlobals` builds only `StoreGlob` programs, whose `assigned_vars`
    clause is empty. The mismatch is the imported programme carrier: HOL's
    `crepLang$prog` embeds `funname = mlstring` in `Call`/`ExtCall`, while Lean's
    `CrepProg` embeds `FunName = String`, so the quantified programmes need not
    agree and no `mlstring` identifier or `NameRanged` byte witness is available.
    The `store_globals` list shape is pinned by
    `scripts/hol-probes/crep_store_globals_probe.out` and sampled by
    `Flapjack/Test/CrepAssignedVarsParity.lean:88-90,111`. Restoring the tag
    depends on the exact mlstring-carrier port `flapjack-pxn.18.3.5.8.8`. -/
theorem crepAssignedVars_nestedSeq_storeGlobalsW {width : Nat} [NeZero width]
    (address : BitVec 5) (values : List (CrepExp (BitVec width))) :
    crepAssignedVarsW (crepNestedSeqW (storeGlobalsW address values)) = [] :=
  crepAssignedVars_nestedSeq_storeGlobals address values

/-- Flapjack width-specialized analogue of Cake
    `crepProps$assigned_free_vars_IMP_assigned_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:373-378`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.102`.
    HOL proves `!prog x. MEM x (assigned_free_vars prog) ==> MEM x (assigned_vars prog)`;
    the Lean implication over `crepAssignedFreeVarsW`/`crepAssignedVarsW` matches
    it pointwise. The mismatch is the imported programme carrier: HOL's
    `crepLang$prog` embeds `funname = mlstring` in `Call`/`ExtCall`, while Lean's
    `CrepProg` embeds `FunName = String`, so the quantified `prog` ranges over a
    carrier whose function names can differ from HOL's. The quantifiers are a
    whole `CrepProg` and a `varname = num` name, so no `mlstring` identifier
    exists for `names_as_string`, and no `NameRanged` byte witness applies.
    Direct HOL rows `imp_mem=T` and `imp_mem_absent=T` are in
    `scripts/hol-probes/crep_assigned_vars_probe.out` (probe header cites
    crepPropsScript.sml:373) and sampled by
    `Flapjack/Test/CrepAssignedVarsParity.lean:50-62`. Restoring the tag depends
    on the exact mlstring-carrier port `flapjack-pxn.18.3.5.8.8`. -/
theorem mem_crepAssignedFreeVars_imp_mem_crepAssignedVarsW {width : Nat} [NeZero width]
    (program : CrepProg (BitVec width)) (name : Nat)
    (h : name ∈ crepAssignedFreeVarsW program) : name ∈ crepAssignedVarsW program :=
  mem_crepAssignedFreeVars_imp_mem_crepAssignedVars program name h

/-- Width-specialized analogue of Cake
    `crepProps$nested_seq_assigned_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:410-415`). It has the same
    list-length premise and assigned-variable equation, but stays untagged
    because it uses production `CrepProg (BitVec width)`: `Call`/`ExtCall`
    names are `String`, whereas HOL `prog` uses `mlstring`. The exact
    `CrepProgHOL` carrier exists, but `assigned_vars` and this theorem are not
    yet ported over it. Existing HOL oracle rows validate concrete results,
    not a carrier bridge. -/
theorem crepAssignedVars_nestedSeq_assign_zipWithW {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width)))
    (h : names.length = values.length) :
    crepAssignedVarsW
        (crepNestedSeqW
          (names.zipWith (fun name value => CrepProg.assign name value) values)) =
      names :=
  crepAssignedVars_nestedSeq_assign_zipWith names values h

/-- Flapjack analogue of Cake `crepProps$nested_seq_assigned_free_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:420-427`), kept untagged with
    status `documented_mismatch` under audit bead `flapjack-dlc.107`.
    The equation `assigned_free_vars (nested_seq (MAP2 Assign ns vs)) = ns` under
    `LENGTH ns = LENGTH vs` matches the Lean `zipWith`/`crepNestedSeqW` form
    pointwise. The mismatch is the imported program carrier: HOL's
    `crepLang$prog` embeds `funname = mlstring` in its `Call`/`ExtCall`
    constructors, while Lean's `CrepProg` embeds `FunName = String`. Because the
    quantified carrier is a whole `CrepProg` its `Call`/`ExtCall` names can differ
    from HOL's, and the quantifiers here (`names : List Nat` are `varname = num`
    keys, the result is `List Nat`) expose no `mlstring` identifier that
    `names_as_string` could qualify. Direct HOL row `nested_afv=[1; 2]` is in
    `scripts/hol-probes/crep_assigned_vars_probe.out` (probe header cites
    crepPropsScript.sml:420), and the equation is sampled by
    `Flapjack/Test/CrepAssignedVarsParity.lean:103-107`. No exact
    mlstring-carrier programme exists yet; restoring the tag depends on
    `flapjack-pxn.18.3.5.8.8`. -/
theorem crepAssignedFreeVars_nestedSeq_assign_zipWithW {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width)))
    (h : names.length = values.length) :
    crepAssignedFreeVarsW
        (crepNestedSeqW
          (names.zipWith (fun name value => CrepProg.assign name value) values)) =
      names :=
  crepAssignedFreeVars_nestedSeq_assign_zipWith names values h

/-- Exact port of Cake `crepProps$nested_seq_assigned_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:410-415`) over the exact
    `CrepProgHOL` carrier: `assigned_vars (nested_seq (MAP2 Assign ns vs)) = ns`
    when `LENGTH ns = LENGTH vs`. The claim is in `varname = num` keys only, so
    no `mlstring` identifier is inspected. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "nested_seq_assigned_vars_eq"]
theorem crepAssignedVarsHOL_nestedSeq_assign_zipWith {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width))
    (h : names.length = values.length) :
    crepAssignedVarsHOL
        (crepNestedSeqHOL
          (names.zipWith (fun name value => CrepProgHOL.assign name value) values)) =
      names := by
  revert values
  induction names with
  | nil =>
      intro values h
      cases values with
      | nil => simp [List.zipWith, crepNestedSeqHOL, crepAssignedVarsHOL]
      | cons value values => simp at h
  | cons name names ih =>
      intro values h
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [List.zipWith, crepNestedSeqHOL, crepAssignedVarsHOL, ih values h]

/-- Exact port of Cake `crepProps$nested_seq_assigned_free_vars_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:420-427`) over the exact
    `CrepProgHOL` carrier: `assigned_free_vars (nested_seq (MAP2 Assign ns vs)) = ns`
    when `LENGTH ns = LENGTH vs`. The claim is in `varname = num` keys only, so
    no `mlstring` identifier is inspected. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "nested_seq_assigned_free_vars_eq"]
theorem crepAssignedFreeVarsHOL_nestedSeq_assign_zipWith {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width))
    (h : names.length = values.length) :
    crepAssignedFreeVarsHOL
        (crepNestedSeqHOL
          (names.zipWith (fun name value => CrepProgHOL.assign name value) values)) =
      names := by
  revert values
  induction names with
  | nil =>
      intro values h
      cases values with
      | nil => simp [List.zipWith, crepNestedSeqHOL, crepAssignedFreeVarsHOL]
      | cons value values => simp at h
  | cons name names ih =>
      intro values h
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [List.zipWith, crepNestedSeqHOL, crepAssignedFreeVarsHOL, ih values h]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_nested_decs_append"]
theorem crepAssignedVarsHOL_nestedDecs_append {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width)) (body : CrepProgHOL width)
    (h : names.length = values.length) :
    crepAssignedVarsHOL (nestedDecsHOL names values body) =
      names ++ crepAssignedVarsHOL body := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => simp [nestedDecsHOL]
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons] at h
          simp [nestedDecsHOL, crepAssignedVarsHOL, ih values (by omega)]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_nested_decs_append"]
theorem crepAssignedFreeVarsHOL_nestedDecs_append {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width)) (body : CrepProgHOL width)
    (h : names.length = values.length) :
    crepAssignedFreeVarsHOL (nestedDecsHOL names values body) =
      (crepAssignedFreeVarsHOL body).filter
        (fun candidate => decide (candidate ∉ names)) := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil =>
          simp only [nestedDecsHOL, List.not_mem_nil]
          symm
          exact List.filter_eq_self.mpr (fun _ _ => rfl)
      | cons value values => simp at h
  | cons name names ih =>
      cases values with
      | nil => simp at h
      | cons value values =>
          simp only [List.length_cons] at h
          rw [nestedDecsHOL, crepAssignedFreeVarsHOL, ih values (by omega), List.filter_filter]
          congr 1
          funext candidate
          by_cases hc : candidate = name
          · subst hc
            simp
          · simp [hc, List.mem_cons, bne_iff_ne]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_seq_store_empty"]
theorem crepAssignedVarsHOL_nestedSeq_storesHOL {width : Nat} [NeZero width]
    (values : List (CrepExpHOL width)) (address : CrepExpHOL width) (offset : BitVec width) :
    crepAssignedVarsHOL (crepNestedSeqHOL (storesHOL address values offset)) = [] := by
  induction values generalizing offset with
  | nil => simp [storesHOL, crepNestedSeqHOL, crepAssignedVarsHOL]
  | cons value values ih =>
      simp [storesHOL, crepNestedSeqHOL, crepAssignedVarsHOL, ih]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_seq_store_empty"]
theorem crepAssignedFreeVarsHOL_nestedSeq_storesHOL {width : Nat} [NeZero width]
    (values : List (CrepExpHOL width)) (address : CrepExpHOL width) (offset : BitVec width) :
    crepAssignedFreeVarsHOL (crepNestedSeqHOL (storesHOL address values offset)) = [] := by
  induction values generalizing offset with
  | nil => simp [storesHOL, crepNestedSeqHOL, crepAssignedFreeVarsHOL]
  | cons value values ih =>
      simp [storesHOL, crepNestedSeqHOL, crepAssignedFreeVarsHOL, ih]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_store_globals_empty"]
theorem crepAssignedVarsHOL_nestedSeq_storeGlobalsHOL {width : Nat} [NeZero width]
    (values : List (CrepExpHOL width)) (address : BitVec 5) :
    crepAssignedVarsHOL (crepNestedSeqHOL (storeGlobalsHOL address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobalsHOL, crepNestedSeqHOL, crepAssignedVarsHOL]
  | cons value values ih =>
      simp [storeGlobalsHOL, crepNestedSeqHOL, crepAssignedVarsHOL, ih]

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_store_globals_empty"]
theorem crepAssignedFreeVarsHOL_nestedSeq_storeGlobalsHOL {width : Nat} [NeZero width]
    (values : List (CrepExpHOL width)) (address : BitVec 5) :
    crepAssignedFreeVarsHOL (crepNestedSeqHOL (storeGlobalsHOL address values)) = [] := by
  induction values generalizing address with
  | nil => simp [storeGlobalsHOL, crepNestedSeqHOL, crepAssignedFreeVarsHOL]
  | cons value values ih =>
      simp [storeGlobalsHOL, crepNestedSeqHOL, crepAssignedFreeVarsHOL, ih]

theorem crepAssignedVars_nestedDecs_appendW {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width)))
    (body : CrepProg (BitVec width)) (h : names.length = values.length) :
    crepAssignedVarsW (nestedDecsW names values body) = names ++ crepAssignedVarsW body :=
  crepAssignedVars_nestedDecs_append names values body h

theorem crepAssignedFreeVars_nestedDecs_appendW {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width)))
    (body : CrepProg (BitVec width)) (h : names.length = values.length) :
    crepAssignedFreeVarsW (nestedDecsW names values body) =
      (crepAssignedFreeVarsW body).filter (fun candidate => decide (candidate ∉ names)) :=
  crepAssignedFreeVars_nestedDecs_append names values body h

theorem crepAssignedVars_nestedSeq_storesW {width : Nat} [NeZero width]
    (address : CrepExp (BitVec width)) (values : List (CrepExp (BitVec width)))
    (offset : BitVec width) :
    crepAssignedVarsW (crepNestedSeqW (storesW address values offset)) = [] := by
  rw [storesW_eq_stores]
  exact crepAssignedVars_nestedSeq_stores address values offset (BitVec.ofNat width (width / 8))

theorem crepAssignedFreeVars_nestedSeq_storesW {width : Nat} [NeZero width]
    (address : CrepExp (BitVec width)) (values : List (CrepExp (BitVec width)))
    (offset : BitVec width) :
    crepAssignedFreeVarsW (crepNestedSeqW (storesW address values offset)) = [] := by
  rw [storesW_eq_stores]
  exact crepAssignedFreeVars_nestedSeq_stores address values offset (BitVec.ofNat width (width / 8))

@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "var_exp_load_shape"]
theorem crepExpVars_of_mem_loadShapeW {width : Nat} [NeZero width]
    (count : Nat) (address : BitVec width) (value n : CrepExp (BitVec width))
    (h : n ∈ loadShapeBytes address count value) : crepExpVars n = crepExpVars value := by
  rw [← loadShape_eq_loadShapeBytes_of_stride_eq address CrepBytesInWord.bytesInWord count value
    rfl] at h
  exact crepExpVars_of_mem_loadShape address CrepBytesInWord.bytesInWord count value n h

/-- Exact port of Cake `crepProps$exps_of_def`
    (`cakeml/pancake/semantics/crepPropsScript.sml:1282-1299`) over the exact
    `CrepProgHOL`/`CrepExpHOL` carriers. Collects the expressions that occur
    directly in a Crepe program: the `Dec` value, both `Seq` sides, the `If`
    condition and branches, the `While` condition and body, the `Call`
    arguments plus the handler body when present, both store operands, the
    `StoreGlob` value, the `Return` values, the `Assign` value and the
    `ShMem` address; every other constructor contributes nothing. The `Call`
    function name is an `MlString` in both carriers and is ignored by HOL, so
    there is no name-carrier mismatch. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "exps_of_def"]
def crepExpsOfHOL {width : Nat} [NeZero width] : CrepProgHOL width → List (CrepExpHOL width)
  | .dec _ value body => value :: crepExpsOfHOL body
  | .seq first second => crepExpsOfHOL first ++ crepExpsOfHOL second
  | .ite condition thenBranch elseBranch =>
      condition :: (crepExpsOfHOL thenBranch ++ crepExpsOfHOL elseBranch)
  | .while condition body => condition :: crepExpsOfHOL body
  | .call none _ args => args
  | .call (some (_, none)) _ args => args
  | .call (some (_, some (_, handler))) _ args => args ++ crepExpsOfHOL handler
  | .store address value => [address, value]
  | .store32 address value => [address, value]
  | .storeByte address value => [address, value]
  | .storeGlob _ value => [value]
  | .return values => values
  | .assign _ value => [value]
  | .shMem _ _ address => [address]
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! ### Exact finite-support `crepProps` state facts

These restate the Cake `crepPropsScript.sml` whole-state facts over the reviewed
exact `CrepSemHOLState` carrier, whose `locals`/`globals`/`code` fields are the
finite-support `HolFiniteMapExact` translation of HOL's `|->` maps (the carrier
is imported from the `crepSem` counterpart, like the other crepSem helpers).
The `fmap_as_finite_support` qualifier requires a same-module canonical witness,
provided immediately below. -/

namespace CrepPropsFiniteSupport

/-- Canonical same-module witness for the `fmap_as_finite_support` qualifier used
by the tagged `crepProps` state facts in this module. The finite-map fields of
`CrepSemHOLState` are invertibly related to the broad function-backed
`CrepSemBroadState`; the proof is the imported canonical witness. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepPropsFiniteSupport

/-- Exact port of HOL `lookup_locals_eq_map_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml:17-27`): mapping the local
    lookup over a list of variable names equals mapping the exact expression
    evaluator over the corresponding `Var` expressions.  HOL's
    `OPT_MMAP (FLOOKUP t.locals) ns` is Lean's `List.mapM t.locals.lookup` and
    `OPT_MMAP (eval t) (MAP Var ns)` is `List.mapM (evalCrepSemHOLExp t)` over
    `CrepExpHOL.var`; `eval`'s `Var` clause is exactly `.locals.lookup`, so no
    side condition beyond the exact carrier is needed (the `DecidablePred`
    argument is the evaluator encoding).  `CrepSemHOLState width σ` is the
    type-indexed-word crepSem state carrier whose `locals`/`globals`/`code` are
    HOL `|->` fields, hence the combined `fmap_as_finite_support`/words
    qualifiers; the same-module forwarding witness is
    `holFmapAsFiniteSupportWitness` above. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "lookup_locals_eq_map_vars"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem lookupLocalsEqMapVarsHOL {width : Nat} [NeZero width] {σ : Type}
    (ns : List Nat) (t : CrepSemHOLState width σ) [DecidablePred t.memaddrs] :
    ns.mapM t.locals.lookup =
      (ns.map (fun name => CrepExpHOL.var (width := width) name)).mapM
        (evalCrepSemHOLExp t) := by
  induction ns with
  | nil => rfl
  | cons name ns ih => simp [List.mapM_cons, evalCrepSemHOLExp, ih]

/-- Exact HOL `dec_clock_simp` (`crepPropsScript.sml:267-278`) over the exact
finite-support `CrepSemHOLState` carrier: the ten field equations, with HOL
`sh_memaddrs`/`be`/`base_addr`/`top_addr` rendered as `shMemaddrs`/`be`/
`baseAddr`/`topAddr`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "dec_clock_simp"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem decClockCrepSemHOL_simp {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) :
    (decClockCrepSemHOL s).locals = s.locals ∧
      (decClockCrepSemHOL s).globals = s.globals ∧
      (decClockCrepSemHOL s).code = s.code ∧
      (decClockCrepSemHOL s).memory = s.memory ∧
      (decClockCrepSemHOL s).memaddrs = s.memaddrs ∧
      (decClockCrepSemHOL s).shMemaddrs = s.shMemaddrs ∧
      (decClockCrepSemHOL s).be = s.be ∧
      (decClockCrepSemHOL s).ffi = s.ffi ∧
      (decClockCrepSemHOL s).baseAddr = s.baseAddr ∧
      (decClockCrepSemHOL s).topAddr = s.topAddr := by
  simp [decClockCrepSemHOL]

/-- Exact HOL `empty_locals_simp` (`crepPropsScript.sml:282-294`) over the exact
finite-support `CrepSemHOLState` carrier: clearing `locals` to `FEMPTY` preserves
the other nine fields. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "empty_locals_simp"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem emptyLocalsCrepSemHOL_simp {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) :
    (CrepSemHOLState.emptyLocals s).globals = s.globals ∧
      (CrepSemHOLState.emptyLocals s).code = s.code ∧
      (CrepSemHOLState.emptyLocals s).memory = s.memory ∧
      (CrepSemHOLState.emptyLocals s).memaddrs = s.memaddrs ∧
      (CrepSemHOLState.emptyLocals s).shMemaddrs = s.shMemaddrs ∧
      (CrepSemHOLState.emptyLocals s).clock = s.clock ∧
      (CrepSemHOLState.emptyLocals s).be = s.be ∧
      (CrepSemHOLState.emptyLocals s).ffi = s.ffi ∧
      (CrepSemHOLState.emptyLocals s).baseAddr = s.baseAddr ∧
      (CrepSemHOLState.emptyLocals s).topAddr = s.topAddr := by
  simp [CrepSemHOLState.emptyLocals]

/-- Exact HOL `FLOOKUP_set_globals` (`crepPropsScript.sml:297-301`) over the exact
finite-support `CrepSemHOLState` carrier: setting a global leaves the `locals`
finite map unchanged. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "FLOOKUP_set_globals"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem flookupSetGlobalsCrepSemHOL_locals {width : Nat} [NeZero width] {σ : Type}
    (key : BitVec 5) (value : HolWordLab width) (s : CrepSemHOLState width σ)
    (name : Nat) :
    (CrepSemHOLState.setGlobals key value s).locals.lookup name =
      s.locals.lookup name := by
  simp [CrepSemHOLState.setGlobals]

/-- Exact port of HOL `sh_mem_load_FLOOKUP_locals`
    (`crepPropsScript.sml:303-310`) over the exact finite-support
    `CrepSemHOLState` carrier and the exact `crepShMemLoadExactHOL` port of
    `sh_mem_load`: whenever a shared-memory load returns a non-terminal result
    (`NONE`, `SOME (Continue k)`, or `SOME (Break k)`), it leaves the lookup of
    any local distinct from the loaded name unchanged. HOL's `v`/`n` are the
    `Nat` local names `name`/`key`, and the free HOL `k` is the universally
    quantified `label`. HOL's `'a word` addresses are the type-indexed
    `BitVec width` with the `[NeZero width]` discharge, recorded by the combined
    `(fmap_as_finite_support := [locals, globals, code])`
    `(words_as_type_indexed_bitvec)` qualifiers; the same-module forwarding
    witness is `holFmapAsFiniteSupportWitness` above. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "sh_mem_load_FLOOKUP_locals"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepShMemLoadHOL_flookup_locals {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs]
    (res : Option (CrepResultHOLExact width)) (target : CrepSemHOLState width σ)
    (key : Nat) (label : Nat)
    (hstep : crepShMemLoadExactHOL name address nb state = (res, target))
    (hne : key ≠ name)
    (hres : res = none ∨ res = some (.continue label) ∨ res = some (.break label)) :
    target.locals.lookup key = state.locals.lookup key := by
  unfold crepShMemLoadExactHOL at hstep
  repeat' split at hstep
  all_goals
    rcases hstep with ⟨rfl, rfl⟩
  all_goals
    try simp_all
  all_goals
    simp_all [CrepSemHOLState.setVar, FUPDATE_HOL]

/-- Exact port of HOL `sh_mem_store_FLOOKUP_locals`
    (`crepPropsScript.sml:312-317`) over the exact finite-support
    `CrepSemHOLState` carrier and the exact `crepShMemStoreExactHOL` port of
    `sh_mem_store`: a shared-memory store never changes any local lookup
    (`FLOOKUP t.locals n = FLOOKUP s.locals n`, with no side condition). HOL's
    `v`/`n` are the `Nat` local names `name`/`key`. HOL's `'a word` addresses are
    the type-indexed `BitVec width` with the `[NeZero width]` discharge, recorded
    by the combined `(fmap_as_finite_support := [locals, globals, code])`
    `(words_as_type_indexed_bitvec)` qualifiers; the same-module forwarding
    witness is `holFmapAsFiniteSupportWitness` above. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "sh_mem_store_FLOOKUP_locals"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepShMemStoreHOL_flookup_locals {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (address : BitVec width) (nb : Nat)
    (state : CrepSemHOLState width σ) [DecidablePred state.shMemaddrs]
    (res : Option (CrepResultHOLExact width)) (target : CrepSemHOLState width σ)
    (key : Nat)
    (hstep : crepShMemStoreExactHOL name address nb state = (res, target)) :
    target.locals.lookup key = state.locals.lookup key := by
  unfold crepShMemStoreExactHOL at hstep
  repeat' split at hstep
  all_goals
    rcases hstep with ⟨rfl, rfl⟩
  all_goals
    rfl


/-- Exact port of HOL `eval_upd_clock_eq` (`crepPropsScript.sml:858-872`):
the exact `crepSem$eval` expression evaluator never reads the state `clock`
field, so replacing it is invisible. Quantifier order follows HOL's `t, e, ck`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "eval_upd_clock_eq"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evalCrepSemHOLExp_upd_clock_eq {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (expression : CrepExpHOL width) (clock : Nat) :
    evalCrepSemHOLExp { state with clock := clock } expression =
      evalCrepSemHOLExp state expression := by
  refine CrepExpHOL.rec
    (motive_1 := fun expression =>
      evalCrepSemHOLExp { state with clock := clock } expression =
        evalCrepSemHOLExp state expression)
    (motive_2 := fun expressions =>
      expressions.mapM (evalCrepSemHOLExp { state with clock := clock }) =
        expressions.mapM (evalCrepSemHOLExp state))
    (fun value => by simp only [evalCrepSemHOLExp])
    (fun name => by simp only [evalCrepSemHOLExp])
    (fun address ih => by simp only [evalCrepSemHOLExp, ih])
    (fun address ih => by simp only [evalCrepSemHOLExp, ih])
    (fun address ih => by simp only [evalCrepSemHOLExp, ih])
    (fun address => by simp only [evalCrepSemHOLExp])
    (fun operator args ih => by simp only [evalCrepSemHOLExp, ih])
    (fun operator args ih => by simp only [evalCrepSemHOLExp, ih])
    (fun operator left right ihl ihr => by simp only [evalCrepSemHOLExp, ihl, ihr])
    (fun operator left right ihl ihr => by simp only [evalCrepSemHOLExp, ihl, ihr])
    (by simp only [evalCrepSemHOLExp])
    (by simp only [evalCrepSemHOLExp])
    (by simp only [List.mapM_nil])
    (fun head tail ihh iht => by simp only [List.mapM_cons, ihh, iht])
    expression

/-- Flapjack-specific equality helper for exact Crep expression evaluation.
An update of a local absent from `var_cexp` does not change the `eval_def`
result. This stronger equality statement is support for the successful-result
HOL theorem below, and is not a separate HOL declaration. -/
theorem evalCrepSemHOLExp_updateLocals_eq_of_not_vars {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (expression : CrepExpHOL width) (name : Nat) (word : HolWordLab width)
    (hfresh : name ∉ crepExpVarsHOL expression) :
    evalCrepSemHOLExp { state with locals := state.locals.updateEq (name, word) }
        expression = evalCrepSemHOLExp state expression := by
  let updated : CrepSemHOLState width σ :=
    { state with locals := state.locals.updateEq (name, word) }
  letI : DecidablePred updated.memaddrs := fun address => by
    change Decidable (state.memaddrs address)
    exact inferInstance
  change evalCrepSemHOLExp updated expression = evalCrepSemHOLExp state expression
  refine CrepExpHOL.rec
    (motive_1 := fun expression =>
      name ∉ crepExpVarsHOL expression →
        evalCrepSemHOLExp updated expression = evalCrepSemHOLExp state expression)
    (motive_2 := fun expressions =>
      (∀ expression, expression ∈ expressions → name ∉ crepExpVarsHOL expression) →
        expressions.mapM (evalCrepSemHOLExp updated) =
          expressions.mapM (evalCrepSemHOLExp state))
    (fun _ _ => by simp only [evalCrepSemHOLExp])
    (fun variableName hfresh => by
      have hne : variableName ≠ name := by
        intro heq
        subst variableName
        exact hfresh (by simp [crepExpVarsHOL])
      simp [evalCrepSemHOLExp, updated, HolFiniteMapExact.updateEq, FUPDATE_HOL, hne])
    (fun address ih hfresh => by
      have hsub : name ∉ crepExpVarsHOL address := by simpa [crepExpVarsHOL] using hfresh
      simp only [evalCrepSemHOLExp, ih hsub]
      simp [updated])
    (fun address ih hfresh => by
      have hsub : name ∉ crepExpVarsHOL address := by simpa [crepExpVarsHOL] using hfresh
      simp only [evalCrepSemHOLExp, ih hsub]
      simp [updated])
    (fun address ih hfresh => by
      have hsub : name ∉ crepExpVarsHOL address := by simpa [crepExpVarsHOL] using hfresh
      simp only [evalCrepSemHOLExp, ih hsub]
      simp [updated])
    (fun _ _ => by simp [evalCrepSemHOLExp, updated])
    (fun _ args ih hfresh => by
      have hargs : ∀ expression, expression ∈ args → name ∉ crepExpVarsHOL expression := by
        intro expression hmem hvar
        have hmemVars : name ∈ crepExpVarsHOLList args := by
          rw [crepExpVarsHOLList_eq_flatMap]
          exact List.mem_flatMap.mpr ⟨expression, hmem, hvar⟩
        exact hfresh hmemVars
      simp only [evalCrepSemHOLExp, ih hargs])
    (fun _ args ih hfresh => by
      have hargs : ∀ expression, expression ∈ args → name ∉ crepExpVarsHOL expression := by
        intro expression hmem hvar
        have hmemVars : name ∈ crepExpVarsHOLList args := by
          rw [crepExpVarsHOLList_eq_flatMap]
          exact List.mem_flatMap.mpr ⟨expression, hmem, hvar⟩
        exact hfresh hmemVars
      simp only [evalCrepSemHOLExp, ih hargs])
    (fun _ left right ihl ihr hfresh => by
      have ⟨hleft, hright⟩ : name ∉ crepExpVarsHOL left ∧
          name ∉ crepExpVarsHOL right := by simpa [crepExpVarsHOL] using hfresh
      simp only [evalCrepSemHOLExp, ihl hleft, ihr hright])
    (fun _ left right ihl ihr hfresh => by
      have ⟨hleft, hright⟩ : name ∉ crepExpVarsHOL left ∧
          name ∉ crepExpVarsHOL right := by simpa [crepExpVarsHOL] using hfresh
      simp only [evalCrepSemHOLExp, ihl hleft, ihr hright])
    (by simp [evalCrepSemHOLExp, updated])
    (by simp [evalCrepSemHOLExp, updated])
    (fun _ => by simp only [List.mapM_nil])
    (fun head tail ihHead ihTail hfresh => by
      have hhead : name ∉ crepExpVarsHOL head := hfresh head (by simp)
      have htail : ∀ expression, expression ∈ tail → name ∉ crepExpVarsHOL expression := by
        intro expression hmem
        exact hfresh expression (by simp [hmem])
      simp only [List.mapM_cons, ihHead hhead, ihTail htail])
    expression hfresh

/-- Flapjack-only finite-list extension of the exact `var_cexp` noninterference
helper above. A list of HOL-equality local updates whose keys are all absent
from an expression leaves its exact evaluator result unchanged. There is no
separate HOL declaration for this list helper; it supports the induction in
`eval_nested_assign_distinct_eq`. -/
def evalCrepSemHOLExpWithMemDec {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (expression : CrepExpHOL width) : Option (HolWordLab width) := by
  letI : DecidablePred state.memaddrs := memDec
  exact evalCrepSemHOLExp state expression

theorem evalCrepSemHOLExpWithMemDec_updateLocals_eq_of_not_vars
    {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (expression : CrepExpHOL width) (name : Nat) (word : HolWordLab width)
    (hfresh : name ∉ crepExpVarsHOL expression) :
    evalCrepSemHOLExpWithMemDec { state with locals := state.locals.updateEq (name, word) }
        memDec expression = evalCrepSemHOLExpWithMemDec state memDec expression := by
  change evalCrepSemHOLExp
      { state with locals := state.locals.updateEq (name, word) } expression =
    evalCrepSemHOLExp state expression
  letI : DecidablePred state.memaddrs := memDec
  exact evalCrepSemHOLExp_updateLocals_eq_of_not_vars
    state expression name word hfresh

theorem evalCrepSemHOLExp_updateLocalsList_eq_of_not_vars {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (expression : CrepExpHOL width) (entries : List (Nat × HolWordLab width))
    (hfresh : ∀ entry, entry ∈ entries → entry.1 ∉ crepExpVarsHOL expression) :
    evalCrepSemHOLExpWithMemDec
        { state with locals := state.locals.updateListEq entries } memDec expression =
      evalCrepSemHOLExpWithMemDec state memDec expression := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries ih =>
      have hfreshHead : entry.1 ∉ crepExpVarsHOL expression :=
        hfresh entry (by simp)
      have hfreshTail : ∀ item, item ∈ entries →
          item.1 ∉ crepExpVarsHOL expression := by
        intro item hmem
        exact hfresh item (by simp [hmem])
      let updated : CrepSemHOLState width σ :=
        { state with locals := state.locals.updateEq entry }
      have htail := ih updated memDec hfreshTail
      have hhead := evalCrepSemHOLExpWithMemDec_updateLocals_eq_of_not_vars
        state memDec expression entry.1 entry.2 hfreshHead
      have hstate :
          ({ state with locals := state.locals.updateListEq (entry :: entries) } :
            CrepSemHOLState width σ) =
          { updated with locals := updated.locals.updateListEq entries } := by
        cases state
        simp [updated, HolFiniteMapExact.updateListEq,
          HolFiniteMapExact.updateEq, FUPDATE_LIST_HOL_cons]
      cases hstate
      exact htail.trans hhead

/-- Exact port of HOL `crepProps$update_locals_not_vars_eval_eq`
(`crepPropsScript.sml:115-130`): under successful exact Crep expression
evaluation and absence of the assigned local from `var_cexp`, replacing that
local preserves the result. The finite-map qualifier records the exact
`CrepSemHOLState` locals/globals/code carriers. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "update_locals_not_vars_eval_eq"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem updateLocalsNotVarsEvalEqCrepHOL {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (expression : CrepExpHOL width) (value : HolWordLab width)
    (name : Nat) (word : HolWordLab width)
    (hfresh : name ∉ crepExpVarsHOL expression)
    (heval : evalCrepSemHOLExp state expression = some value) :
    evalCrepSemHOLExp { state with locals := state.locals.updateEq (name, word) }
        expression = some value := by
  rw [evalCrepSemHOLExp_updateLocals_eq_of_not_vars state expression name word hfresh, heval]

/-- Exact port of HOL `flookup_res_var_diff_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:249-255`):
    `n <> m ==> FLOOKUP (res_var l (m, v)) n = FLOOKUP l n`.
    HOL `res_var` is rendered as the reviewed `HolFiniteMapExact.resVarEq`
    (`res_var_def`), `FLOOKUP` as the finite-support `.lookup`, and the
    quantified finite map `l` is recorded as a bare finite-support parameter.
    `DecidableEq α` is Lean's encoding of HOL `=`, so the statement is
    polymorphic in the key type exactly as in HOL. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_diff_eq"
  (fmap_as_finite_support_relation := [l])]
theorem flookupResVarDiffEqHOL [DecidableEq α] (l : HolFiniteMapExact α β)
    (m n : α) (v : Option β) (hne : n ≠ m) :
    (HolFiniteMapExact.resVarEq l (m, v)).lookup n = l.lookup n := by
  cases v with
  | none =>
    simp only [HolFiniteMapExact.lookup_resVarEq_none]
    rw [show FDOMSUB_HOL l.lookup m n = FLOOKUP (FDOMSUB_HOL l.lookup m) n from rfl]
    rw [FLOOKUP_FDOMSUB_HOL]
    simp [FLOOKUP, if_neg hne]
  | some value =>
    simp only [HolFiniteMapExact.lookup_resVarEq_some]
    rw [show FUPDATE_HOL l.lookup (m, value) n =
        FLOOKUP (FUPDATE_HOL l.lookup (m, value)) n from rfl]
    rw [FLOOKUP_FUPDATE_HOL]
    simp [FLOOKUP, if_neg hne]

/-- Exact port of HOL `flookup_res_var_thm`
    (`cakeml/pancake/semantics/crepPropsScript.sml:257-263`):
    `FLOOKUP (res_var l (m, v)) n = if n = m then v else FLOOKUP l n`.
    HOL `res_var` is rendered as the reviewed `HolFiniteMapExact.resVarEq`
    (`res_var_def`), `FLOOKUP` as the finite-support `.lookup`, and the
    quantified finite map `l` is recorded as a bare finite-support parameter.
    `DecidableEq α` is Lean's encoding of HOL `=`, so the statement is
    polymorphic in the key type exactly as in HOL. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_thm"
  (fmap_as_finite_support_relation := [l])]
theorem flookupResVarThmHOL [DecidableEq α] (l : HolFiniteMapExact α β)
    (m n : α) (v : Option β) :
    (HolFiniteMapExact.resVarEq l (m, v)).lookup n = if n = m then v else l.lookup n := by
  cases v with
  | none =>
    simp only [HolFiniteMapExact.lookup_resVarEq_none]
    rw [show FDOMSUB_HOL l.lookup m n = FLOOKUP (FDOMSUB_HOL l.lookup m) n from rfl]
    rw [FLOOKUP_FDOMSUB_HOL]
    rfl
  | some value =>
    simp only [HolFiniteMapExact.lookup_resVarEq_some]
    rw [show FUPDATE_HOL l.lookup (m, value) n =
        FLOOKUP (FUPDATE_HOL l.lookup (m, value)) n from rfl]
    rw [FLOOKUP_FUPDATE_HOL]
    rfl

/-- Exact HOL `opt_mmap_eval_upd_clock_eq` (`crepPropsScript.sml:875`): mapping
the exact expression evaluator (after a clock update by `clock + state.clock`)
over a list of expressions equals mapping the original evaluator. The
declaration is width-indexed (`BitVec width` under `[NeZero width]`) so it
carries the word-dimension qualifier, and it consumes the full
`CrepSemHOLState` whose `locals`/`globals`/`code` fields are reviewed
`HolFiniteMapExact` maps that `evalCrepSemHOLExp` reads, matching the sibling
`eval_upd_clock_eq` tag, so it carries the finite-map qualifier too. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "opt_mmap_eval_upd_clock_eq"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evalCrepSemHOLExps_upd_clock_eq {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) [DecidablePred state.memaddrs]
    (expressions : List (CrepExpHOL width)) (clock : Nat) :
    expressions.mapM
        (fun e => evalCrepSemHOLExp { state with clock := clock + state.clock } e) =
      expressions.mapM (fun e => evalCrepSemHOLExp state e) :=
  Flapjack.list_mapM_congr _ _ expressions
    (fun e _ => evalCrepSemHOLExp_upd_clock_eq state e (clock + state.clock))

/-! ## FFI event-prefix monotonicity (HOL `crepPropsScript.sml:957`) -/

/-- Exact port of HOL `Theorem evaluate_io_events_mono`
(`cakeml/pancake/semantics/crepPropsScript.sml:957`):
`!exps s1 res s2. evaluate (exps,s1) = (res,s2) ==> s1.ffi.io_events ≼
s2.ffi.io_events`, where `evaluate` is the exact `crepSem$evaluate` port
`evalCrepSemHOLProgExact`, `exps : CrepProgHOL width` is the source program,
`res : CrepResultHOLExact width option` is HOL's `result option` (unused in the
conclusion but fixed by HOL type inference to carry the same word dimension),
`s2 : CrepSemHOLState width σ` is the result state, and HOL's `IS_PREFIX` (`≼`)
is Lean `List.IsPrefix` (`<+:`). The conclusion is HOL's list prefix on the two
states' `ffi.io_events`; `res` is only present so the hypothesis has HOL's exact
shape.

The `locals`/`globals`/`code` `|->` fields of `CrepSemHOLState` are the reviewed
canonical `HolFiniteMapExact` translation (same-module witness
`CrepPropsFiniteSupport.holFmapAsFiniteSupportWitness`), HOL's type-indexed
`'a word` is `BitVec width` under `[NeZero width]`, and `'ffi` is `σ : Type`;
hence the combined `fmap_as_finite_support`/words qualifiers. The proof mirrors
HOL's `recInduct evaluate_ind` + `IS_PREFIX_TRANS`: the shared-memory and
external-call leaves call `call_FFI`, whose returned/final forms keep or extend
the log, every other clause preserves `ffi`, and the recursive clauses compose
the sub-runs through `evalCrepSemHOLProgExact_ioEvents_prefix`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_io_events_mono"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepPropsEvaluateIoEventsMono {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ)
    (result : Option (CrepResultHOLExact width)) (finalState : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact state program = (result, finalState)) :
    state.ffi.ioEvents <+: finalState.ffi.ioEvents := by
  classical
  have h := evalCrepSemHOLProgExact_ioEvents_prefix state program
  rw [heval] at h
  exact h


private theorem holFiniteMapExact_ext_resVar {α β : Type} {left right : HolFiniteMapExact α β}
    (h : ∀ k, left.lookup k = right.lookup k) : left = right := by
  obtain ⟨l, pl⟩ := left
  obtain ⟨r, pr⟩ := right
  have : l = r := funext h
  subst this
  rfl

private theorem foldl_resVarEq_restore_lookup {α β : Type} [DecidableEq α]
    (lc : HolFiniteMapExact α β) :
    ∀ (keys : List α) (m : HolFiniteMapExact α β) (k : α),
      ((keys.zip (keys.map lc.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry) m).lookup k =
        if k ∈ keys then lc.lookup k else m.lookup k
  | [], m, k => by simp
  | x :: keys, m, k => by
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [foldl_resVarEq_restore_lookup lc keys]
      by_cases hk : k ∈ keys
      · simp [hk]
      · have hres : (HolFiniteMapExact.resVarEq m (x, lc.lookup x)).lookup k =
            if k = x then lc.lookup x else m.lookup k := by
          cases hx : lc.lookup x <;>
            simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
              HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL] <;>
            split <;> simp_all
        rw [hres]
        by_cases hkx : k = x
        · subst hkx; simp [hk]
        · simp [hk, hkx]

private theorem fupdateListHOL_zip_not_mem {α β : Type} [DecidableEq α] (k : α) :
    ∀ (xs : List α) (ys : List β) (f : FiniteMap α β), k ∉ xs →
      FUPDATE_LIST_HOL f (xs.zip ys) k = f k
  | [], _, f, _ => by simp [FUPDATE_LIST_HOL]
  | _ :: _, [], f, _ => by simp [FUPDATE_LIST_HOL]
  | x :: xs, y :: ys, f, hk => by
      simp only [List.mem_cons, not_or] at hk
      rw [List.zip_cons_cons, FUPDATE_LIST_HOL_cons,
        fupdateListHOL_zip_not_mem k xs ys _ hk.2]
      simp [FUPDATE_HOL, hk.1]

/-- Exact port of HOL `crepProps$res_var_lookup_original_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:612-633`):
    `!xs ys lc. ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys ==>
      FOLDL res_var (lc |++ ZIP (xs,ys)) (ZIP (xs,MAP (FLOOKUP lc) xs)) = lc`.
    `res_var` is the tagged `HolFiniteMapExact.resVarEq`, `|++` is `updateListEq`,
    and `FLOOKUP lc` is `lc.lookup`. HOL's polymorphic key/value types are the
    type parameters, with `DecidableEq` for HOL `=`. The standalone map `lc` is
    recorded as a bare relation-qualifier entry. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "res_var_lookup_original_eq"
  (fmap_as_finite_support_relation := [lc])]
theorem resVarLookupOriginalEqHOL {α β : Type} [DecidableEq α] :
    ∀ (xs : List α) (ys : List β) (lc : HolFiniteMapExact α β),
      xs.Nodup ∧ xs.length = ys.length →
      (xs.zip (xs.map lc.lookup)).foldl
          (fun current entry => HolFiniteMapExact.resVarEq current entry)
          (lc.updateListEq (xs.zip ys)) = lc := by
  intro xs ys lc ⟨_, hlen⟩
  apply holFiniteMapExact_ext_resVar
  intro k
  rw [foldl_resVarEq_restore_lookup lc xs]
  split
  · rfl
  · rename_i hk
    simp only [HolFiniteMapExact.lookup_updateListEq]
    exact fupdateListHOL_zip_not_mem k xs ys lc.lookup hk

/-- Exact port of HOL `crepProps$flookup_res_var_distinct_zip_eq`
    (`cakeml/pancake/semantics/crepPropsScript.sml:777-794`):
    `LENGTH xs = LENGTH ys /\ ~MEM x xs ==>
      FLOOKUP (FOLDL res_var fm (ZIP (xs,ys))) x = FLOOKUP fm x`.
    `res_var` is the tagged `HolFiniteMapExact.resVarEq` over HOL's `(key, value
    option)` pairs, and `FLOOKUP` is `.lookup`. HOL's free variables become
    the explicit binders, and HOL `=` on keys is `DecidableEq`. The standalone map
    `fm` is recorded as a bare relation-qualifier entry. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_distinct_zip_eq"
  (fmap_as_finite_support_relation := [fm])]
theorem flookupResVarDistinctZipEqHOL {α β : Type} [DecidableEq α] :
    ∀ (xs : List α) (ys : List (Option β)) (fm : HolFiniteMapExact α β) (x : α),
      xs.length = ys.length ∧ x ∉ xs →
      ((xs.zip ys).foldl (fun current entry => HolFiniteMapExact.resVarEq current entry) fm).lookup x =
        fm.lookup x
  | [], _, fm, x, _ => rfl
  | _ :: _, [], fm, x, ⟨hlen, _⟩ => by simp at hlen
  | k :: xs, y :: ys, fm, x, ⟨hlen, hx⟩ => by
      simp only [List.mem_cons, not_or] at hx
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [flookupResVarDistinctZipEqHOL xs ys _ x ⟨by simpa using hlen, hx.2⟩]
      have hxk : x ≠ k := hx.1
      cases y <;> simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
        HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL, hxk]

end Flapjack
