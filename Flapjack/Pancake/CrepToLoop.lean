module

public import Flapjack.HolRef
public import Flapjack.FiniteMap.Basic
public import Flapjack.Pancake.LoopLang
public import Flapjack.Pancake.PanStatic
public import Flapjack.RiscV.Model

@[expose] public section

/-!
Initial Crepe-to-Loop lowering for the direct executable fragment. This keeps
the IR close to CakeML's `crep_to_loopScript.sml`; expression side effects,
condition materialization, liveness, and arithmetic expansion are subsequent
passes.
-/

namespace Flapjack

abbrev NatInfoMap (α : Type u) := List (Nat × α)

def lookupNatInfo (name : Nat) : NatInfoMap α → Option α
  | [] => none
  | (candidate, value) :: entries =>
      if candidate == name then some value else lookupNatInfo name entries

structure LoopContext (α : Type u) where
  vars : NatInfoMap Nat
  functions : InfoMap (Nat × Nat)
  maxVar : Nat
  target : RiscV.Architecture
  deriving Repr

/-! Source-named port of CakeML Pancake's `make_vmap_def`
    (`crep_to_loopScript.sml:230`).  Cake populates `FEMPTY |++ ZIP (params,
    GENLIST I (LENGTH params))`, a left fold of `|+`, so for a *duplicate*
    parameter name the LAST binding wins.  The list-backed context is consulted
    with `lookupNatInfo`'s first match, so the positional pairs are replayed
    most-recent-first (reversed): the first match then reproduces HOL's
    last-binding-wins behaviour.  `lookupNatInfo_crepMakeVmap_eq_flookup_makeVmapHOL`
    proves the result agrees with the raw-map helper `makeVmapHOL` for every parameter
    list, duplicates included. -/
def crepMakeVmap (params : List Nat) : NatInfoMap Nat :=
  (params.zip (List.range params.length)).reverse

def findLoopVar (context : LoopContext α) (name : Nat) : Nat :=
  match lookupNatInfo name context.vars with
  | some value => value
  | none => 0

/-! The Crepe primitive carries variable *names*, not expressions.  Cake's
    `crep_to_loop$compile` resolves both destination and argument lists with
    `FLOOKUP` and drops the statement if any name is absent.  Keeping an
    option-valued helper here is important: using `findLoopVar`'s defensive
    zero fallback would silently alias an unknown primitive operand with a
    real local and changes liveness and emitted code. -/
def lookupLoopVars (context : LoopContext α) : List Nat → Option (List Nat)
  | [] => some []
  | name :: names => do
      let mapped ← lookupNatInfo name context.vars
      let rest ← lookupLoopVars context names
      pure (mapped :: rest)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

/-! Source-named port of `crep_to_loop$find_var` (`find_var_def`,
    `crep_to_loopScript.sml:20`). -/
def crepFindVar (context : LoopContext α) (name : Nat) : Nat :=
  findLoopVar context name

/-! Source-named port of `crep_to_loop$find_lab` (`find_lab_def`,
    `crep_to_loopScript.sml:27`). -/
def crepFindLab [BEq FunName] (context : LoopContext α) (name : FunName) : Nat :=
  match lookupInfo name context.functions with
  | some (label, _) => label
  | none => 0

/-! CakeML's `num_set` prints in ascending order.  Keep the list-backed live
    sets used by the executable port in that same canonical order when
    translating `prog_if`'s `list_insert` result. -/
def insertNatSorted (name : Nat) : List Nat → List Nat
  | [] => [name]
  | head :: tail =>
      if name < head then name :: head :: tail
      else if name = head then head :: tail
      else head :: insertNatSorted name tail

def loopListInsert (names live : List Nat) : List Nat :=
  names.foldl (fun current name => insertNatSorted name current) live

def loopListUnion (left right : List Nat) : List Nat :=
  loopListInsert (left ++ right) []

/-! CakeML's `num_set` insert operations preserve membership and canonical
    order.  The Flapjack live sets are plain sorted lists, so the corresponding
    facts are stated directly for `insertNatSorted`/`loopListInsert`. -/

/-- Membership in an inserted sorted live set, counterpart of CakeML's
    `domain_list_insert` (`sptreeScript.sml:2042`). -/
theorem insertNatSorted_mem (name : Nat) (live : List Nat) (x : Nat) :
    x ∈ insertNatSorted name live ↔ x = name ∨ x ∈ live := by
  induction live with
  | nil => simp [insertNatSorted]
  | cons head tail ih =>
      by_cases hlt : name < head
      · simp [insertNatSorted, hlt, List.mem_cons]
      · by_cases heq : name = head
        · subst heq; simp [insertNatSorted, List.mem_cons]
        · simp only [insertNatSorted, if_neg hlt, if_neg heq, List.mem_cons, ih]
          by_cases h1 : x = name <;> by_cases h2 : x = head <;> by_cases h3 : x ∈ tail <;>
            simp_all

/-- Inserting the same temporary twice is idempotent, the Flapjack counterpart
    of CakeML's `insert_insert_eq`/`insert_shadow`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:380`). -/
theorem insertNatSorted_idem (name : Nat) (live : List Nat) :
    insertNatSorted name (insertNatSorted name live) = insertNatSorted name live := by
  induction live with
  | nil => simp [insertNatSorted]
  | cons head tail ih =>
      by_cases hlt : name < head
      · simp [insertNatSorted, hlt]
      · by_cases heq : name = head
        · subst heq; simp [insertNatSorted]
        · simp only [insertNatSorted, if_neg hlt, if_neg heq, ih]

/-- CakeML's `list_insert_SNOC`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:386`). -/
theorem loopListInsert_snoc (x : Nat) (ys : List Nat) (live : List Nat) :
    loopListInsert (ys ++ [x]) live = insertNatSorted x (loopListInsert ys live) := by
  simp [loopListInsert, List.foldl_append]

/-- CakeML's `list_insert_append`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:414`), in the foldl
    orientation used by the Flapjack executable port. -/
theorem loopListInsert_append (xs ys : List Nat) (live : List Nat) :
    loopListInsert (xs ++ ys) live = loopListInsert ys (loopListInsert xs live) := by
  simp [loopListInsert, List.foldl_append]

/-- Membership in a folded live set; counterpart of CakeML's
    `domain_list_insert` for `list_insert`. -/
theorem loopListInsert_mem (x : Nat) (names : List Nat) (live : List Nat) :
    x ∈ loopListInsert names live ↔ x ∈ names ∨ x ∈ live := by
  induction names generalizing live with
  | nil => simp [loopListInsert]
  | cons name names ih =>
      rw [show loopListInsert (name :: names) live =
          loopListInsert names (insertNatSorted name live) from rfl]
      rw [ih, insertNatSorted_mem]
      by_cases h1 : x = name <;> by_cases h2 : x ∈ names <;> by_cases h3 : x ∈ live <;>
        simp_all [List.mem_cons]

theorem insertNatSorted_cons_lt {a b : Nat} (l : List Nat) (h : a < b) :
    insertNatSorted a (b :: l) = a :: b :: l := by
  simp [insertNatSorted, h]

theorem insertNatSorted_cons_eq {a b : Nat} (l : List Nat) (h : a = b) :
    insertNatSorted a (b :: l) = b :: l := by
  cases h
  simp [insertNatSorted, Nat.lt_irrefl]

theorem insertNatSorted_cons_gt {a b : Nat} (l : List Nat) (h : b < a) :
    insertNatSorted a (b :: l) = b :: insertNatSorted a l := by
  have hlt : ¬ a < b := Nat.not_lt_of_lt h
  have hne : ¬ a = b := by omega
  simp [insertNatSorted, hlt, hne]

theorem insertNatSorted_nil_comm (x y : Nat) :
    insertNatSorted x (insertNatSorted y []) =
      insertNatSorted y (insertNatSorted x []) := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · have hyx : ¬ y < x := Nat.not_lt_of_lt h
    have hne1 : ¬ x = y := by omega
    have hne2 : ¬ y = x := by omega
    simp only [insertNatSorted, if_pos h, if_neg hyx, if_neg hne1, if_neg hne2]
  · subst h; rfl
  · have hxy : ¬ x < y := Nat.not_lt_of_lt h
    have hne1 : ¬ x = y := by omega
    have hne2 : ¬ y = x := by omega
    simp only [insertNatSorted, if_pos h, if_neg hxy, if_neg hne1, if_neg hne2]

theorem insertNatSorted_comm (x y : Nat) :
    ∀ live : List Nat,
      insertNatSorted x (insertNatSorted y live) =
        insertNatSorted y (insertNatSorted x live) := by
  intro live
  induction live with
  | nil => exact insertNatSorted_nil_comm x y
  | cons head tail ih =>
      rcases Nat.lt_trichotomy x head with hxlt | hxeq | hxgt <;>
      rcases Nat.lt_trichotomy y head with hylt | hyeq | hygt <;>
      rcases Nat.lt_trichotomy x y with hxylt | hxyeq | hxygt <;>
      simp_all only [insertNatSorted_cons_lt, insertNatSorted_cons_eq,
        insertNatSorted_cons_gt] <;>
      try (exfalso; omega)

theorem loopListInsert_insertNatSorted_comm (x : Nat) (names : List Nat)
    (live : List Nat) :
    insertNatSorted x (loopListInsert names live) =
      loopListInsert names (insertNatSorted x live) := by
  induction names generalizing live with
  | nil => simp [loopListInsert]
  | cons name names ih =>
      rw [show loopListInsert (name :: names) live =
          loopListInsert names (insertNatSorted name live) from rfl]
      rw [ih (insertNatSorted name live)]
      rw [show loopListInsert (name :: names) (insertNatSorted x live) =
          loopListInsert names (insertNatSorted name (insertNatSorted x live))
            from rfl]
      rw [insertNatSorted_comm name x]

/-!
This compiler carries the temporary and liveness
state used by the HOL pass. In particular, `Load32`, `LoadByte`, and
comparisons become explicit Loop statements rather than remaining effectful
expressions.
-/

structure LoopCompileExpResult (α : Type u) where
  code : List (LoopProg α)
  expression : LoopExp α
  nextTemp : Nat
  live : List Nat
  deriving Repr

structure LoopCompileExpsResult (α : Type u) where
  expressions : List (LoopExp α)
  code : List (LoopProg α)
  nextTemp : Nat
  live : List Nat
  deriving Repr

def loopTempNames (start count : Nat) : List Nat :=
  (List.range count).map (fun offset => start + offset)

/-! Source-named ports of the small temporary/return-variable helpers from
    `crep_to_loopScript.sml:101-118`. -/
def crepGenTemps (start count : Nat) : List Nat :=
  loopTempNames start count

def crepRtVar (context : NatInfoMap Nat) (value : Option Nat) (nextTemp maxVar : Nat) : Nat :=
  match value with
  | none => nextTemp
  | some name => (lookupNatInfo name context).getD (maxVar + 1)

def crepRtVarsAux (context : NatInfoMap Nat) : List Nat → Option (List Nat)
  | [] => some []
  | name :: names =>
      match lookupNatInfo name context, crepRtVarsAux context names with
      | some value, some values => some (value :: values)
      | _, _ => none

def crepRtVars (context : NatInfoMap Nat) (names : List Nat) (maxVar : Nat) : List Nat :=
  (crepRtVarsAux context names).getD [maxVar + 1]

/-! ## Pure-num helpers of Cake's `crep_to_loop_def`

These four HOL definitions carry no word-typed fields, so they are ported
exactly.  `rt_var`/`rt_vars` are polymorphic in the finite-map key, matching
the un-annotated HOL `Definition`s (`fm : 'a |-> num`). -/

/-- Exact port of HOL `gen_temps_def`
    (`cakeml/pancake/crep_to_loopScript.sml:101`):
    `gen_temps n l = GENLIST (λx. n + x) l`. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "gen_temps_def"]
def genTemps (n l : Nat) : List Nat := (List.range l).map (fun x => n + x)

/-- Exact port of HOL `first_name_def`
    (`cakeml/pancake/crep_to_loopScript.sml:243`): the first generated loop
    function number. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "first_name_def"]
def firstLoopName : Nat := 64


/-! The faithful finite-map HOL `rt_var_def` remains to be ported. -/

/-- Flapjack-specific lookup helper for HOL `rt_vars_def`: a missing variable
    yields `[mx + 1]`. The map is a raw lookup function admitting infinite
    support, so the faithful finite-map definition remains to be ported. -/
def rtVars {κ : Type} (fm : FiniteMap κ Nat) (vs : List κ) (mx : Nat) : List Nat :=
  match vs.mapM (fun v => FLOOKUP fm v) with
  | none => [mx + 1]
  | some m => m

end Flapjack
