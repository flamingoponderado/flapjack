module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap.SizeProperties
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApproxOf
public import Flapjack.HolRef

@[expose] public section

/-!
# `size_of` is bounded by `approx_of`

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:50`
`size_of_approx_of`: the visited-set-aware heap sizing never exceeds the
over-approximating `approx_of`. The proof follows HOL's strengthened induction
(`qsuff_tac`): for every reference tree `refsT` above the starting tree, the
sized result is bounded by `approx_of` at `refsT` and the returned reference
tree stays below `refsT`.

The private helper has no separate HOL original: it is the strengthened
induction statement HOL introduces with `qsuff_tac` before `ho_match_mp_tac
size_of_ind`.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem
open Classical

/-- `approxOf` at a single reference bound to a byte array.
    Flapjack infrastructure for `size_of_approx_of`; no separate HOL original. -/
private theorem approxOf_refPtr_byteArray (limits : Limits) (bit : Bool) (address : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (mode : Bool) (bytes : List (BitVec 8))
    (found : sptLookup address refs = some (.byteArray mode bytes)) :
    approxOf limits [.refPtr bit address] refs = bytes.length / (archSize limits / 8) + 2 := by
  rw [approxOf]
  split
  · rename_i h
    exact absurd h (by simp [found])
  · rename_i _ _ h
    rw [found] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rename_i _ h
    exact absurd h (by simp [found])
  · rename_i _ _ h
    exact absurd h (by simp [found])
  · rename_i _ _ _ _ _ h
    exact absurd h (by simp [found])

/-- `approxOf` at a single reference bound to a value array.
    Flapjack infrastructure for `size_of_approx_of`; no separate HOL original. -/
private theorem approxOf_refPtr_valueArray (limits : Limits) (bit : Bool) (address : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (vals : List DataSem.Value)
    (found : sptLookup address refs = some (.valueArray vals)) :
    approxOf limits [.refPtr bit address] refs =
      approxOf limits vals (sptDelete address refs) + vals.length + 1 := by
  rw [approxOf]
  split
  · rename_i h
    exact absurd h (by simp [found])
  · rename_i _ _ h
    exact absurd h (by simp [found])
  · rename_i _ h
    rw [found] at h
    simp at h
    obtain ⟨rfl⟩ := h
    rfl
  · rename_i _ _ h
    exact absurd h (by simp [found])
  · rename_i _ _ _ _ _ h
    exact absurd h (by simp [found])

/-- `approxOf` at a single reference bound to a thunk.
    Flapjack infrastructure for `size_of_approx_of`; no separate HOL original. -/
private theorem approxOf_refPtr_thunk (limits : Limits) (bit : Bool) (address : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (mode : AstHOL.ThunkMode)
    (value : DataSem.Value)
    (found : sptLookup address refs = some (.thunk mode value)) :
    approxOf limits [.refPtr bit address] refs =
      approxOf limits [value] (sptDelete address refs) + 2 := by
  rw [approxOf]
  split
  · rename_i h
    exact absurd h (by simp [found])
  · rename_i _ _ h
    exact absurd h (by simp [found])
  · rename_i _ h
    exact absurd h (by simp [found])
  · rename_i _ _ h
    rw [found] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rename_i _ _ _ _ _ h
    exact absurd h (by simp [found])

/-- `approxOf` at a single reference bound to a mutable block.
    Flapjack infrastructure for `size_of_approx_of`; no separate HOL original. -/
private theorem approxOf_refPtr_mutBlock (limits : Limits) (bit : Bool) (address : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (tag : Nat) (final : Bool)
    (left : List DataSem.Value) (value : DataSem.Value) (right : List DataSem.Value)
    (found : sptLookup address refs = some (.mutBlock tag final left value right)) :
    approxOf limits [.refPtr bit address] refs =
      approxOf limits (left ++ [value] ++ right) (sptDelete address refs) +
        left.length + right.length + 2 := by
  rw [approxOf]
  split
  · rename_i h
    exact absurd h (by simp [found])
  · rename_i _ _ h
    exact absurd h (by simp [found])
  · rename_i _ h
    exact absurd h (by simp [found])
  · rename_i _ _ h
    exact absurd h (by simp [found])
  · rename_i _ _ _ _ _ h
    rw [found] at h
    injection h with hRef
    injection hRef with hTag hFinal hLeft hCurrent hRight
    rw [← hLeft, ← hCurrent, ← hRight]

/-- Strengthened induction statement of `size_of_approx_of`: the bound holds at
    every reference tree above the starting one, and the returned tree stays
    below it. Flapjack infrastructure for `size_of_approx_of`; no separate HOL
    original (HOL introduces it with `qsuff_tac`). -/
private theorem sizeOfApproxOf_aux (limits : Limits) (values : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (n : Nat) (refs' : Spt (BvlSem.Ref DataSem.Value)) (seen' : Spt Unit)
    (refsT : Spt (BvlSem.Ref DataSem.Value))
    (run : sizeOfValues limits values refs seen = (n, refs', seen'))
    (sub : sptSubspt refs refsT) :
    n ≤ approxOf limits values refsT ∧ sptSubspt refs' refsT := by
  cases values with
  | nil =>
    simp only [sizeOfValues] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨by simp [approxOf], sub⟩
  | cons x xs =>
    cases xs with
    | cons y ys =>
      let first := checkRes refs (sizeOfValues limits (y :: ys) refs seen)
      let second := sizeOfValues limits [x] first.2.1 first.2.2
      have firstEq : first = sizeOfValues limits (y :: ys) refs seen :=
        checkRes_sizeOfValues limits (y :: ys) refs seen
      have firstBound : sptSize first.2.1 ≤ sptSize refs := by
        rw [firstEq]
        exact sizeOfValues_refsBound limits (y :: ys) refs seen
      have ih1 := sizeOfApproxOf_aux limits (y :: ys) refs seen first.1 first.2.1 first.2.2
        refsT firstEq.symm sub
      have ih2 := sizeOfApproxOf_aux limits [x] first.2.1 first.2.2 second.1 second.2.1
        second.2.2 refsT rfl ih1.2
      simp only [sizeOfValues] at run ⊢
      obtain ⟨rfl, rfl, rfl⟩ := run
      dsimp only [first, second] at ih1 ih2 ⊢
      have expand : approxOf limits (x :: y :: ys) refsT =
          approxOf limits [x] refsT + approxOf limits (y :: ys) refsT := by
        simp only [approxOf]
      rw [expand]
      exact ⟨by omega, ih2.2⟩
    | nil =>
      cases x with
      | number value =>
        simp only [sizeOfValues, approxOf] at run ⊢
        obtain ⟨rfl, rfl, rfl⟩ := run
        exact ⟨Nat.le_refl _, sub⟩
      | word64 w =>
        simp only [sizeOfValues, approxOf] at run ⊢
        obtain ⟨rfl, rfl, rfl⟩ := run
        exact ⟨Nat.le_refl _, sub⟩
      | codePtr c =>
        simp only [sizeOfValues, approxOf] at run ⊢
        obtain ⟨rfl, rfl, rfl⟩ := run
        exact ⟨Nat.le_refl _, sub⟩
      | refPtr bit address =>
        have subDel : sptSubspt (sptDelete address refs) (sptDelete address refsT) := by
          apply (sptSubsptLookup _ _).mpr
          intro key inner lookup
          rw [sptLookup_sptDelete] at lookup ⊢
          by_cases same : key = address
          · rw [if_pos same] at lookup
            simp at lookup
          · rw [if_neg same] at lookup ⊢
            exact (sptSubsptLookup _ _).mp sub key inner lookup
        simp only [sizeOfValues] at run
        split at run
        · rename_i hNone
          obtain ⟨rfl, rfl, rfl⟩ := run
          exact ⟨Nat.zero_le _, sub⟩
        · rename_i mode bytes hSome
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by simp [hSome])
          obtain ⟨rfl, rfl, rfl⟩ := run
          have hT : sptLookup address refsT = some (.byteArray mode bytes) :=
            (sptSubsptLookup _ _).mp sub address (.byteArray mode bytes) hSome
          rw [approxOf_refPtr_byteArray limits bit address refsT mode bytes hT]
          exact ⟨Nat.le_refl _,
            sptSubsptTrans _ _ _ ⟨sptDelete_subspt refs address, sub⟩⟩
        · rename_i vals hSome
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by simp [hSome])
          obtain ⟨rfl, rfl, rfl⟩ := run
          have hT : sptLookup address refsT = some (.valueArray vals) :=
            (sptSubsptLookup _ _).mp sub address (.valueArray vals) hSome
          have ih := sizeOfApproxOf_aux limits vals (sptDelete address refs) seen
            (sizeOfValues limits vals (sptDelete address refs) seen).1
            (sizeOfValues limits vals (sptDelete address refs) seen).2.1
            (sizeOfValues limits vals (sptDelete address refs) seen).2.2
            (sptDelete address refsT) rfl subDel
          rw [approxOf_refPtr_valueArray limits bit address refsT vals hT]
          exact ⟨by omega,
            sptSubsptTrans _ _ _ ⟨ih.2, sptDelete_subspt refsT address⟩⟩
        · rename_i mode value hSome
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by simp [hSome])
          obtain ⟨rfl, rfl, rfl⟩ := run
          have hT : sptLookup address refsT = some (.thunk mode value) :=
            (sptSubsptLookup _ _).mp sub address (.thunk mode value) hSome
          have ih := sizeOfApproxOf_aux limits [value] (sptDelete address refs) seen
            (sizeOfValues limits [value] (sptDelete address refs) seen).1
            (sizeOfValues limits [value] (sptDelete address refs) seen).2.1
            (sizeOfValues limits [value] (sptDelete address refs) seen).2.2
            (sptDelete address refsT) rfl subDel
          rw [approxOf_refPtr_thunk limits bit address refsT mode value hT]
          exact ⟨by omega,
            sptSubsptTrans _ _ _ ⟨ih.2, sptDelete_subspt refsT address⟩⟩
        · rename_i tag final left current right hSome
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by simp [hSome])
          obtain ⟨rfl, rfl, rfl⟩ := run
          have hT :
              sptLookup address refsT = some (.mutBlock tag final left current right) :=
            (sptSubsptLookup _ _).mp sub address
              (.mutBlock tag final left current right) hSome
          have ih := sizeOfApproxOf_aux limits (left ++ [current] ++ right)
            (sptDelete address refs) seen
            (sizeOfValues limits (left ++ [current] ++ right) (sptDelete address refs) seen).1
            (sizeOfValues limits (left ++ [current] ++ right) (sptDelete address refs) seen).2.1
            (sizeOfValues limits (left ++ [current] ++ right) (sptDelete address refs) seen).2.2
            (sptDelete address refsT) rfl subDel
          rw [approxOf_refPtr_mutBlock limits bit address refsT tag final left current right hT]
          exact ⟨by omega,
            sptSubsptTrans _ _ _ ⟨ih.2, sptDelete_subspt refsT address⟩⟩
      | block timestamp tag vals =>
        cases vals with
        | nil =>
          simp only [sizeOfValues, approxOf] at run ⊢
          obtain ⟨rfl, rfl, rfl⟩ := run
          exact ⟨Nat.zero_le _, sub⟩
        | cons value rest =>
          simp only [sizeOfValues, approxOf] at run ⊢
          by_cases visited : (sptLookup timestamp seen).isSome = true
          · rw [if_pos visited] at run
            obtain ⟨rfl, rfl, rfl⟩ := run
            exact ⟨Nat.zero_le _, sub⟩
          · rw [if_neg visited] at run
            have ih := sizeOfApproxOf_aux limits (value :: rest) refs (sptInsert timestamp () seen)
              (sizeOfValues limits (value :: rest) refs (sptInsert timestamp () seen)).1
              (sizeOfValues limits (value :: rest) refs (sptInsert timestamp () seen)).2.1
              (sizeOfValues limits (value :: rest) refs (sptInsert timestamp () seen)).2.2
              refsT rfl sub
            obtain ⟨rfl, rfl, rfl⟩ := run
            exact ⟨by omega, ih.2⟩
termination_by (sptSize refs, sizeOf values)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals simp_wf
  all_goals
    try
      apply Prod.Lex.right
      omega
  all_goals
    try
      apply Prod.Lex.left
      exact smaller
  have hy : 0 < sizeOf y := by cases y <;> simp_wf <;> omega
  rcases Nat.lt_or_eq_of_le firstBound with hlt | heq
  · apply Prod.Lex.left
    exact hlt
  · rw [heq]
    apply Prod.Lex.right
    omega
/-- The visited-set-aware heap sizing never exceeds the over-approximating
    `approx_of`. Port of HOL `size_of_approx_of`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "size_of_approx_of"]
theorem sizeOfApproxOf (limits : Limits) (values : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (n : Nat) (refs' : Spt (BvlSem.Ref DataSem.Value)) (seen' : Spt Unit)
    (run : sizeOfValues limits values refs seen = (n, refs', seen')) :
    n ≤ approxOf limits values refs :=
  (sizeOfApproxOf_aux limits values refs seen n refs' seen' refs run
    (fun _ member => ⟨member, rfl⟩)).1

end Flapjack.Compiler.Backend.DataProps
