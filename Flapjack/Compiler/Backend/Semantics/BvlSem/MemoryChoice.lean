import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions
import Aesop

/-! Choice predicates for BVL byte-vector primitives. -/
namespace Flapjack.Compiler.Backend.BvlSem

private theorem byteArrays_pointers (refs : HolFiniteMapExact Nat (Ref Value))
    (values : List Value) (chunks : List (List (BitVec 8)))
    (run : byteArrays refs values = some chunks) :
    ∃ ptrs : List Nat, values = ptrs.map (Value.refPtr true) := by
  induction values generalizing chunks with
  | nil => exact ⟨[], rfl⟩
  | cons value values ih =>
    cases value with
    | number | word64 | block | codePtr => simp [byteArrays] at run
    | refPtr flag ptr =>
      cases flag with
      | false => simp [byteArrays] at run
      | true =>
        cases lookup : refs.lookup ptr with
        | none => simp [byteArrays, lookup] at run
        | some cell =>
          cases cell with
          | valueArray | thunk | mutBlock => simp [byteArrays, lookup] at run
          | byteArray immutable bytes =>
            cases immutable with
            | false => simp [byteArrays, lookup] at run
            | true =>
              simp [byteArrays, lookup, Option.bind_eq_some_iff] at run
              obtain ⟨result, tailRun, _⟩ := run
              obtain ⟨ptrs, equal⟩ := ih result tailRun
              exact ⟨ptr :: ptrs, by simp [equal]⟩

private theorem byteArrays_map (refs : HolFiniteMapExact Nat (Ref Value))
    (ptrs : List Nat) (chunks : List (List (BitVec 8))) :
    byteArrays refs (ptrs.map (Value.refPtr true)) = some chunks ↔
      ptrs.map refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) := by
  induction ptrs generalizing chunks with
  | nil => cases chunks <;> simp [byteArrays]
  | cons ptr ptrs ih =>
    cases chunks with
    | nil =>
      cases lookup : refs.lookup ptr with
      | none => simp [byteArrays, lookup]
      | some cell =>
        cases cell <;> simp_all [byteArrays]
        case byteArray immutable bytes => cases immutable <;> simp_all [Option.bind_eq_some_iff]
    | cons bytes chunks =>
      cases lookup : refs.lookup ptr with
      | none => simp [byteArrays, lookup]
      | some cell =>
        cases cell with
        | valueArray | thunk | mutBlock => simp [byteArrays, lookup]
        | byteArray immutable payload =>
          cases immutable <;> simp_all [byteArrays, Option.bind_eq_some_iff, and_comm]
          aesop

/-- The deterministic traversal satisfies exactly the original pointer and
lookup predicate for a successful byte-vector concatenation. -/
theorem byteArrays_eq_some (refs : HolFiniteMapExact Nat (Ref Value))
    (values : List Value) (chunks : List (List (BitVec 8))) :
    byteArrays refs values = some chunks ↔
      ∃ ptrs : List Nat, values = ptrs.map (Value.refPtr true) ∧
        ptrs.map refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) := by
  constructor
  · intro run
    obtain ⟨ptrs, equal⟩ := byteArrays_pointers refs values chunks run
    refine ⟨ptrs, equal, ?_⟩
    subst values
    exact (byteArrays_map refs ptrs chunks).mp run
  · rintro ⟨ptrs, rfl, lookup⟩
    exact (byteArrays_map refs ptrs chunks).mpr lookup

/-- Decoding the encoded list of immutable byte-array pointers. -/
def byteArrayChunks (refs : HolFiniteMapExact Nat (Ref Value)) (value : Value) :
    Option (List (List (BitVec 8))) := (valueToList value).bind (byteArrays refs)

/-- The decoder's successful result is the original HOL choice predicate. -/
theorem byteArrayChunks_eq_some (refs : HolFiniteMapExact Nat (Ref Value))
    (value : Value) (chunks : List (List (BitVec 8))) :
    byteArrayChunks refs value = some chunks ↔
      ∃ ptrs : List Nat, valueToList value = some (ptrs.map (Value.refPtr true)) ∧
        ptrs.map refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) := by
  simp [byteArrayChunks, Option.bind_eq_some_iff, byteArrays_eq_some]
  aesop

/-- The deterministic decoder equals the guarded HOL choice in the
concatenation branch, including the no-witness case. -/
theorem byteArrayChunks_eq_holChoice (refs : HolFiniteMapExact Nat (Ref Value)) (value : Value) :
    byteArrayChunks refs value = Flapjack.holOptionSome
      (fun chunks : List (List (BitVec 8)) => ∃ ptrs : List Nat,
        valueToList value = some (ptrs.map (Value.refPtr true)) ∧
          ptrs.map refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes))) := by
  exact option_eq_holChoice _ _ (byteArrayChunks_eq_some refs value)

end Flapjack.Compiler.Backend.BvlSem
