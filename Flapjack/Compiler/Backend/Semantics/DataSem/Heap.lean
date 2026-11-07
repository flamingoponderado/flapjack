import Flapjack.Compiler.Backend.Semantics.DataSem.State
import Flapjack.Misc.Sptree.SizeDelete
import Flapjack.Misc.Sptree.ToList

/-! Heap-space accounting for the data-language semantics. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack
open Classical

/-- The number of machine-word digits in a natural number. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "bignum_digits_def"]
def bignumDigits (arch64 : Bool) (n : Nat) : Nat :=
  if n = 0 then 0 else
    1 + bignumDigits arch64 (n / 2 ^ (if arch64 then 64 else 32))
termination_by n
decreasing_by
  apply Nat.div_lt_self (by omega)
  cases arch64 <;> decide

/-- One header word plus the magnitude's machine-word digits. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "bignum_size_def"]
def bignumSize (arch64 : Bool) (value : Int) : Nat :=
  1 + bignumDigits arch64 value.natAbs

/-- Discard an intermediate reference tree if it has grown. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "check_res_def"]
def checkRes {α β : Type} (original : Spt α) (result : Nat × Spt α × β) : Nat × Spt α × β :=
  if sptSize result.2.1 ≤ sptSize original then result else (result.1, original, result.2.2)

/-- The reference component of the checked result cannot grow. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "check_res_IMP"]
theorem checkRes_size {α β : Type} (original : Spt α) (n : Nat) (refs : Spt α) (seen : β)
    (result : Nat × Spt α × β) (h : (n, refs, seen) = checkRes original result) :
    sptSize refs ≤ sptSize original := by
  rcases result with ⟨m, tree, other⟩
  by_cases size : sptSize tree ≤ sptSize original
  · simp [checkRes, size] at h
    rcases h with ⟨_, rfl, _⟩
    exact size
  · simp [checkRes, size] at h
    rcases h with ⟨_, rfl, _⟩
    exact Nat.le_refl _


/-- Measure reachable data values, removing visited references and recording
block timestamps so that shared objects are counted only once. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "size_of_def" 112]
noncomputable def sizeOfValues (limits : Limits) (values : List Value)
    (refs : Spt (BvlSem.Ref Value)) (seen : Spt Unit) : Nat × Spt (BvlSem.Ref Value) × Spt Unit :=
  match values with
  | [] => (0, refs, seen)
  | x :: y :: ys =>
      let first := checkRes refs (sizeOfValues limits (y :: ys) refs seen)
      let second := sizeOfValues limits [x] first.2.1 first.2.2
      (first.1 + second.1, second.2.1, second.2.2)
  | [.word64 _] => (3, refs, seen)
  | [.number n] => (if smallNum limits.arch64Bit n then 0 else bignumSize limits.arch64Bit n, refs, seen)
  | [.codePtr _] => (0, refs, seen)
  | [.refPtr _ address] =>
      match h : sptLookup address refs with
      | none => (0, refs, seen)
      | some (.byteArray _ bytes) => (bytes.length / (archSize limits / 8) + 2, sptDelete address refs, seen)
      | some (.valueArray vals) =>
          let (n, rest, visited) := sizeOfValues limits vals (sptDelete address refs) seen
          (n + vals.length + 1, rest, visited)
      | some (.thunk _ value) =>
          let (n, rest, visited) := sizeOfValues limits [value] (sptDelete address refs) seen
          (n + 2, rest, visited)
      | some (.mutBlock _ _ left current right) =>
          let (n, rest, visited) := sizeOfValues limits (left ++ [current] ++ right) (sptDelete address refs) seen
          (n + left.length + right.length + 2, rest, visited)
  | [.block _ _ []] => (0, refs, seen)
  | [.block timestamp _ vals] =>
      if (sptLookup timestamp seen).isSome then (0, refs, seen) else
        let (n, rest, visited) := sizeOfValues limits vals refs (sptInsert timestamp () seen)
        (n + vals.length + 1, rest, visited)
termination_by (sptSize refs, sizeOf values)
decreasing_by
  all_goals simp_wf
  all_goals try (apply Prod.Lex.right; omega)
  all_goals try (apply Prod.Lex.left; apply sptSize_delete_lt; simp_all)
  have hb : sptSize first.2.1 ≤ sptSize refs := by
    dsimp [first, checkRes]
    split <;> simp_all
  dsimp only [first] at hb
  have hy : 0 < sizeOf y := by cases y <;> simp_wf <;> omega
  omega


/-- Values reachable directly from one saved environment. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "extract_stack_def"]
def extractStack : Stack → List Value
  | .env _ env => sptToList env
  | .exc _ env _ => sptToList env

/-- An optional global reference contributes one heap root. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "global_to_vs_def"]
def globalToValues : Option Nat → List Value
  | none => []
  | some address => [.refPtr true address]

/-- Roots from local variables, saved environments, and the global reference. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "stack_to_vs_def"]
def stackToValues {C F : Type} (state : State C F) : List Value :=
  sptToList state.locals ++ state.stack.flatMap extractStack ++ globalToValues state.global

/-- Heap space reachable from the current roots. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "size_of_heap_def"]
noncomputable def sizeOfHeap {C F : Type} (state : State C F) : Nat :=
  (sizeOfValues state.limits (stackToValues state) state.refs .ln).1

/-- Heap space reachable from explicit operation arguments and current roots. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "size_of_heap_args_def"]
noncomputable def sizeOfHeapArgs {C F : Type} (args : List Value) (state : State C F) : Nat :=
  (sizeOfValues state.limits (args ++ stackToValues state) state.refs .ln).1

/-- No reference in the tree is a thunk, regardless of mode or payload. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "no_thunks_in_refs_def"]
def noThunksInRefs {α : Type} (refs : Spt (BvlSem.Ref α)) : Prop :=
  ∀ key mode value, sptLookup key refs ≠ some (.thunk mode value)

/-- Set the available space and update the heap safety and peak observations. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "add_space_def"]
noncomputable def addSpace {C F : Type} (state : State C F) (amount : Nat) : State C F :=
  let safe := state.safeForSpace && decide (noThunksInRefs state.refs ∧
    sizeOfHeap state + amount ≤ state.limits.heapLimit)
  let peak := max state.peakHeapLength (sizeOfHeap state + amount)
  { state with space := amount, safeForSpace := safe, peakHeapLength := peak }

/-- Consume a requested amount of reserved space if it is available. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "consume_space_def"]
def consumeSpace {C F : Type} (amount : Nat) (state : State C F) : Option (State C F) :=
  if state.space < amount then none else some { state with space := state.space - amount }

end Flapjack.Compiler.Backend.DataSem
