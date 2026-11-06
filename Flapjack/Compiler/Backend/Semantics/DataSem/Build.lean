import Flapjack.Compiler.Backend.Semantics.DataSem.State
import Mathlib.Data.Nat.Find

/-! Timestamped values and constant construction in the data semantics. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon

/-- Prepend list cells, advancing the timestamp for each allocated block. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "list_to_v_def"]
def listToValue (timestamp : Nat) (tail : Value) : List Value → Value
  | [] => tail
  | value :: rest => .block timestamp consTag [value, listToValue (timestamp + 1) tail rest]

/-- Supply a fresh timestamp interval, or zero when timestamps are disabled. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "with_fresh_ts_def"]
def withFreshTimestamp {C F R : Type} (state : State C F) (count : Nat) (f : Nat → State C F → R) : R :=
  match state.tstamps with
  | some timestamp => f timestamp { state with tstamps := some (timestamp + count) }
  | none => f 0 state

private theorem natList_bounded (keys : List Nat) : ∃ bound, ∀ key ∈ keys, key < bound := by
  induction keys with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
    obtain ⟨bound, h⟩ := ih
    refine ⟨max first bound + 1, ?_⟩
    intro key member
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have := h key member
      omega

/-- Every sparse tree has an unallocated natural key. -/
theorem unusedRef_exists (refs : Spt (BvlSem.Ref Value)) : ∃ key, sptLookup key refs = none := by
  obtain ⟨bound, bounded⟩ := natList_bounded ((sptToAList refs).map Prod.fst)
  refine ⟨bound, ?_⟩
  cases found : sptLookup bound refs with
  | none => rfl
  | some value =>
    have lookup := (sptLookup_sptFromAList_sptToAList bound refs).trans found
    rw [sptLookup_sptFromAList] at lookup
    have member := sptAListLookup_mem bound (sptToAList refs) value lookup
    have labelMember : bound ∈ (sptToAList refs).map Prod.fst := List.mem_map.mpr ⟨(bound, value), member, rfl⟩
    have impossible := bounded bound labelMember
    omega

/-- The least unused reference index exists because the source tree is finite. -/
noncomputable def leastUnusedRef (refs : Spt (BvlSem.Ref Value)) : Nat := by
  classical
  exact Nat.find (unusedRef_exists refs)

/-- The chosen index is unused in the source tree. -/
theorem leastUnusedRef_unused (refs : Spt (BvlSem.Ref Value)) :
    sptLookup (leastUnusedRef refs) refs = none := by
  classical
  exact Nat.find_spec (unusedRef_exists refs)

/-- Every smaller source-tree index is occupied. -/
theorem leastUnusedRef_minimal (refs : Spt (BvlSem.Ref Value)) (index : Nat)
    (smaller : index < leastUnusedRef refs) : sptLookup index refs ≠ none := by
  classical
  exact Nat.find_min (unusedRef_exists refs) smaller

/-- Construct one constant part, allocating strings at the least unused key. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_part_def"]
noncomputable def doPart (values : Nat → Value) (part : ClosLang.ConstPart)
    (refs : Spt (BvlSem.Ref Value)) (timestamp : Option Nat) : Value × Spt (BvlSem.Ref Value) × Option Nat :=
  match part with
  | .int i => (.number i, refs, timestamp)
  | .w64 w => (.word64 w, refs, timestamp)
  | .con tag indices =>
      if indices = [] then (.block 0 tag [], refs, timestamp)
      else match timestamp with
        | none => (.block 0 tag (indices.map values), refs, none)
        | some t => (.block t tag (indices.map values), refs, some (t + 1))
  | .str text =>
      let ptr := leastUnusedRef refs
      (.refPtr true ptr, sptInsert ptr (.byteArray true text.explode) refs, timestamp)

/-- Build the parts sequentially, retaining the last value and timestamp. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_build_def"]
noncomputable def doBuild (values : Nat → Value) (index : Nat) :
    List ClosLang.ConstPart → Spt (BvlSem.Ref Value) → Option Nat → Value × Spt (BvlSem.Ref Value) × Option Nat
  | [], refs, timestamp => (values (index - 1), refs, timestamp)
  | part :: rest, refs, timestamp =>
      let (value, nextRefs, nextTimestamp) := doPart values part refs timestamp
      doBuild (fun key => if key = index then value else values key) (index + 1) rest nextRefs nextTimestamp

/-- Build a constant with the source's zero-valued initial index function. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_build_const_def"]
noncomputable def doBuildConst (parts : List ClosLang.ConstPart)
    (refs : Spt (BvlSem.Ref Value)) (timestamp : Option Nat) : Value × Spt (BvlSem.Ref Value) × Option Nat :=
  doBuild (fun _ => .number 0) 0 parts refs timestamp

end Flapjack.Compiler.Backend.DataSem
