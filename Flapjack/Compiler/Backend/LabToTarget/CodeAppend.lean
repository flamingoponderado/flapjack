import Flapjack.Compiler.Backend.LabToTarget.SectionNavigation
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Misc.FindIndex

/-! Original appended-code navigation and FFI-name laws used by the `Install`
case of `compile_correct` (lab_to_targetProofScript.sml:3027-3051,
6344-6364, 6526-6539). -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_add_if_fresh_thm"]
theorem listAddIfFresh_thm {α : Type} [DecidableEq α] (s : α) (l : List α) :
    listAddIfFresh s l = if s ∈ l then l else l ++ [s] := by
  induction l with
  | nil => simp [listAddIfFresh]
  | cons y ys ih =>
    by_cases h : s = y
    · subst h; simp [listAddIfFresh]
    · simp only [listAddIfFresh, h, ↓reduceIte, ih, List.mem_cons, false_or]
      split <;> simp

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findFfiNames_append {width : Nat} [NeZero width] (l1 l2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    findFfiNames (l1 ++ l2) =
      findFfiNames l2 ++ (findFfiNames l1).filter (fun n => !decide (n ∈ findFfiNames l2)) := by
  fun_induction findFfiNames l1 with
  | case1 => simp
  | case2 k rest ih => simpa [findFfiNames] using ih
  | case3 k xs rest s pos bytes len ih =>
    simp only [List.cons_append, findFfiNames] at ih ⊢
    rw [ih, listAddIfFresh_thm, listAddIfFresh_thm]
    by_cases h2 : HolFfiName.extCall s ∈ findFfiNames l2
    · have : HolFfiName.extCall s ∈ findFfiNames l2 ++
          (findFfiNames (⟨k, xs⟩ :: rest)).filter
            (fun n => !decide (n ∈ findFfiNames l2)) := List.mem_append_left _ h2
      rw [if_pos this]
      split <;> simp [List.filter_append, h2]
    · by_cases h1 : HolFfiName.extCall s ∈ findFfiNames (⟨k, xs⟩ :: rest)
      · have : HolFfiName.extCall s ∈ findFfiNames l2 ++
            (findFfiNames (⟨k, xs⟩ :: rest)).filter
              (fun n => !decide (n ∈ findFfiNames l2)) :=
          List.mem_append_right _ (List.mem_filter.2 ⟨h1, by simp [h2]⟩)
        rw [if_pos this, if_pos h1]
      · have : HolFfiName.extCall s ∉ findFfiNames l2 ++
            (findFfiNames (⟨k, xs⟩ :: rest)).filter
              (fun n => !decide (n ∈ findFfiNames l2)) := by
          simp [h1, h2]
        rw [if_neg this, if_neg h1]
        simp [List.filter_append, h2]
  | case4 k x xs rest hx ih =>
    have hstep : findFfiNames (⟨k, x :: xs⟩ :: (rest ++ l2)) =
        findFfiNames (⟨k, xs⟩ :: (rest ++ l2)) := by
      rcases x with _ | _ | ⟨i, w, b, n⟩
      · simp [findFfiNames]
      · simp [findFfiNames]
      · cases i with
        | callFFI s => exact absurd rfl (hx s w b n)
        | _ => simp [findFfiNames]
    rw [List.cons_append, hstep, ← List.cons_append, ih]

/-- The original statement also binds `conf labs ffis pos`, which do not
occur in it; they are omitted here. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem locToPc_append {width : Nat} [NeZero width] (l1 l2 : Nat) (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ c1 ++ c2, secLabelsOk sec) →
    locToPc l1 l2 (c1 ++ c2) =
      match locToPc l1 l2 c1 with
      | some x => some x
      | none =>
        match locToPc l1 l2 c2 with
        | some x => some (x + (c1.map (fun sec => lenNoLab sec.lines)).sum)
        | none => none := by
  intro hok
  induction c1 with
  | nil =>
    simp only [List.nil_append, List.map_nil, List.sum_nil, Nat.add_zero]
    rw [show locToPc l1 l2 ([] : LabProgHOL width) = none by simp [locToPc]]
    cases locToPc l1 l2 c2 <;> rfl
  | cons sec rest ih =>
    have hrest : ∀ s ∈ rest ++ c2, secLabelsOk s := fun s hs => hok s (by simp_all)
    have hsec : ∀ s ∈ sec :: rest, secLabelsOk s := fun s hs => hok s (by
      rcases List.mem_cons.1 hs with h | h
      · simp [h]
      · simp [h])
    rcases sec with ⟨sid, lines⟩
    rw [List.cons_append, locToPc_sections l1 l2 _ (by simpa using hok),
      locToPc_sections l1 l2 _ hsec]
    dsimp only
    rw [ih hrest]
    simp only [List.map_cons, List.sum_cons]
    cases hr : locToPc l1 l2 rest <;> cases hc : locToPc l1 l2 c2 <;>
      cases hs : secLocToPc l2 lines <;> by_cases he : l1 = sid <;>
      simp [he, Nat.add_comm, Nat.add_left_comm]

end Flapjack.Compiler.Backend.LabToTarget
