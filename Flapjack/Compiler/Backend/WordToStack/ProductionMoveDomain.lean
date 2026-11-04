import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.Compiler.Backend.WordToStack.ProductionFlatCodec
import Flapjack.Compiler.Backend.RegAlloc.ProductionExtraction

/-! Actual move-domain infrastructure. There is no standalone HOL declaration
for the production colouring carrier. Bounds are derived from emitted moves
and the real allocator frame formula, rather than assumed for a caller.
Whole production routing and call/ABI producer coverage remain separate. -/
namespace Flapjack.ProductionMoveDomain
open RiscV RiscV.CakeRegAlloc

private theorem fold_move_maximum (moves : List (Nat × Nat)) (initial : Nat) :
    initial ≤ moves.foldl (fun m p => max m (max p.1 p.2)) initial ∧
    ∀ p ∈ moves, p.1 ≤ moves.foldl (fun m p => max m (max p.1 p.2)) initial ∧
      p.2 ≤ moves.foldl (fun m p => max m (max p.1 p.2)) initial := by
  induction moves generalizing initial with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨floor, members⟩ := ih (max initial (max head.1 head.2))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) floor, ?_⟩
    intro p member
    rcases List.mem_cons.mp member with equal | member
    · subst p
      constructor <;> omega
    · exact members p member

private theorem lookup_member (entries : NatInfoMap Nat) (key value : Nat)
    (found : lookupNatInfo key entries = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookupNatInfo] at found
  | cons entry rest ih =>
      rcases entry with ⟨other, stored⟩
      by_cases equal : other = key
      · subst other
        simp [lookupNatInfo] at found
        subst stored
        exact List.mem_cons_self
      · simp [lookupNatInfo, equal] at found
        exact List.mem_cons_of_mem _ (ih found)

/-- The actual tail-call register-argument producer (`take k`) emits only
indices below the register window, independently of the stack frame. -/
theorem registerArgument_index {α : Type} (arguments : List α) (k index : Nat)
    (member : index ∈ List.range (arguments.take k).length) : index < k := by
  have bound := List.mem_range.mp member
  rw [List.length_take] at bound
  omega

/-- The actual returning-call producer uses `take (k-1)` and ABI base one.
Every emitted destination is therefore below k, even with empty frames. -/
theorem valueArgument_index {α : Type} (arguments : List α) (k index : Nat)
    (member : index ∈ List.range (arguments.take (k - 1)).length) : 1 + index < k := by
  have bound := List.mem_range.mp member
  rw [List.length_take] at bound
  omega

private theorem fold_maximum_member (names : List Nat) (initial name : Nat)
    (member : name ∈ names) : name ≤ names.foldl max initial := by
  have floor : ∀ names : List Nat, ∀ initial : Nat, initial ≤ names.foldl max initial := by
    intro names
    induction names with
    | nil => simp
    | cons head tail ih => intro initial; simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
  induction names generalizing initial with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_trans (Nat.le_max_right _ _) (floor tail _)
      · exact ih _ member

end Flapjack.ProductionMoveDomain
