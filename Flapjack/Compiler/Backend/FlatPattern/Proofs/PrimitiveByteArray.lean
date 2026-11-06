import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveArray

/-! Byte-array primitive simulations for the proof-side flat pattern relations.
The evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result storeLookup storeAssign storeAlloc)
open Flapjack.SemanticPrimitivesProps (storeValueRel)

/-- A byte-array entry has identical bytes in a related store. -/
theorem stateRel_lookup_bytes {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (states : StateRel cfg source target) (address : Nat) (bytes : List (BitVec 8))
    (found : storeLookup address source.refs = some (.w8array bytes)) :
    storeLookup address target.refs = some (.w8array bytes) := by
  obtain ⟨entry, lookup, relation⟩ := storeValueRel_lookup states.2.1 address (.w8array bytes) found
  cases entry <;> simp [storeValueRel] at relation
  case w8array bytes' => simpa [← relation] using lookup

/-- Byte-array allocation preserves the location and negative-size exception. -/
theorem doApp_byteArrayAlloc_related {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (size : Int) (byte : BitVec 8) (states : StateRel cfg source target) :
    ∃ sourceFinal targetFinal result,
      FlatSem.doApp source (.src .aw8alloc) [.litv (.intLit size), .litv (.word8 byte)] = some (sourceFinal, result) ∧
      FlatSem.doApp target (.src .aw8alloc) [.litv (.intLit size), .litv (.word8 byte)] = some (targetFinal, result) ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result := by
  by_cases negative : size < 0
  · refine ⟨source, target, .err (.raise FlatSem.subscriptExnV), ?_, ?_, states, .error (.raise subscriptExn_related)⟩
    · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.boundsFailure, negative]
    · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.boundsFailure, negative]
  · have lengths : target.refs.length = source.refs.length := (forall₂_length states.2.1).symm
    refine ⟨{ source with refs := source.refs ++ [.w8array (List.replicate size.toNat byte)] },
      { target with refs := target.refs ++ [.w8array (List.replicate size.toNat byte)] },
      .val (.loc true source.refs.length), ?_, ?_, ?_, .value ?_⟩
    · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc, negative]
    · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc, negative, lengths]
    · exact ⟨states.1, forall₂_append_one states.2.1 rfl, states.2.2⟩
    · exact (valueRel_loc true source.refs.length _).2 rfl

/-- Byte-array length agrees for related stores. -/
theorem doApp_byteArrayLength_related {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (flag : Bool) (address : Nat) (bytes : List (BitVec 8)) (states : StateRel cfg source target)
    (found : storeLookup address source.refs = some (.w8array bytes)) :
    ∃ result, FlatSem.doApp source (.src .aw8length) [.loc flag address] = some (source, .val result) ∧
      FlatSem.doApp target (.src .aw8length) [.loc flag address] = some (target, .val result) ∧ ValueRel result result := by
  have found' := stateRel_lookup_bytes cfg source target states address bytes found
  refine ⟨.litv (.intLit bytes.length), ?_, ?_, (valueRel_lit _ _).2 rfl⟩
  · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found]
  · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found']

/-- Reading equal byte arrays preserves the returned byte or bounds exception. -/
theorem readIndexed_bytes_related {C F : Type} (source target : FlatSem.State C F) (unsafeOp : Bool)
    (bytes : List (BitVec 8)) (index : Int) (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.readIndexed source unsafeOp bytes index (.litv ∘ Lit.word8) = some (source, result)) :
    FlatSem.readIndexed target unsafeOp bytes index (.litv ∘ Lit.word8) = some (target, result) ∧
      PrimitiveResultRel result result := by
  by_cases negative : index < 0
  · cases unsafeOp with
    | true => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at run
    | false =>
      simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at run
      subst result
      exact ⟨by simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative], .error (.raise subscriptExn_related)⟩
  · cases found : bytes[index.toNat]? with
    | none =>
      cases unsafeOp with
      | true => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, found] at run
      | false =>
        simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, found] at run
        subst result
        exact ⟨by simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, found], .error (.raise subscriptExn_related)⟩
    | some byte =>
      simp [FlatSem.readIndexed, negative, found] at run
      subst result
      exact ⟨by simp [FlatSem.readIndexed, negative, found], .value ((valueRel_lit _ _).2 rfl)⟩

/-- Byte-array reads preserve checked and unsafe behavior through the dispatcher. -/
theorem doApp_byteArrayRead_related {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (unsafeOp : Bool) (flag : Bool) (address : Nat) (index : Int) (bytes : List (BitVec 8))
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (found : storeLookup address source.refs = some (.w8array bytes))
    (run : FlatSem.doApp source (.src (if unsafeOp then .aw8subUnsafe else .aw8sub))
      [.loc flag address, .litv (.intLit index)] = some (source, result)) :
    FlatSem.doApp target (.src (if unsafeOp then .aw8subUnsafe else .aw8sub))
      [.loc flag address, .litv (.intLit index)] = some (target, result) ∧ PrimitiveResultRel result result := by
  have found' := stateRel_lookup_bytes cfg source target states address bytes found
  have unequal : (Op.aw8sub == Op.aw8subUnsafe) = false := by decide
  have read : FlatSem.readIndexed source unsafeOp bytes index (.litv ∘ Lit.word8) = some (source, result) := by
    cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found, unequal] using run
  obtain ⟨read', related⟩ := readIndexed_bytes_related source target unsafeOp bytes index result read
  refine ⟨?_, related⟩
  cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found', unequal] using read'

/-- Updating equal byte arrays preserves stores and checked bounds errors. -/
theorem updateIndexed_bytes_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (address : Nat) (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (run : FlatSem.updateIndexed source unsafeOp address bytes index byte .w8array = some (sourceFinal, result)) :
    ∃ targetFinal, FlatSem.updateIndexed target unsafeOp address bytes index byte .w8array = some (targetFinal, result) ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result := by
  by_cases bounds : index < 0 ∨ bytes.length ≤ index.toNat
  · cases unsafeOp with
    | true => simp [FlatSem.updateIndexed, FlatSem.boundsFailure, bounds] at run
    | false =>
      simp [FlatSem.updateIndexed, FlatSem.boundsFailure, bounds] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, by simp [FlatSem.updateIndexed, FlatSem.boundsFailure, bounds], states,
        .error (.raise subscriptExn_related)⟩
  · cases assigned : storeAssign address (.w8array (bytes.set index.toNat byte)) source.refs with
    | none => simp [FlatSem.updateIndexed, bounds, assigned] at run
    | some refs =>
      have entries : storeValueRel ValueRel (.w8array (bytes.set index.toNat byte))
          (.w8array (bytes.set index.toNat byte)) := rfl
      obtain ⟨refs', assigned', refsRel⟩ := storeAssign_related states.2.1 address entries assigned
      simp [FlatSem.updateIndexed, bounds, assigned] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ target with refs := refs' }, ?_, ⟨states.1, refsRel, states.2.2⟩, .value ?_⟩
      · simp [FlatSem.updateIndexed, bounds, assigned']
      · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩

/-- Byte-array updates preserve checked and unsafe behavior through the dispatcher. -/
theorem doApp_byteArrayUpdate_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (flag : Bool) (address : Nat) (index : Int) (bytes : List (BitVec 8)) (byte : BitVec 8)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (found : storeLookup address source.refs = some (.w8array bytes))
    (run : FlatSem.doApp source (.src (if unsafeOp then .aw8updateUnsafe else .aw8update))
      [.loc flag address, .litv (.intLit index), .litv (.word8 byte)] = some (sourceFinal, result)) :
    ∃ targetFinal, FlatSem.doApp target (.src (if unsafeOp then .aw8updateUnsafe else .aw8update))
      [.loc flag address, .litv (.intLit index), .litv (.word8 byte)] = some (targetFinal, result) ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result := by
  have found' := stateRel_lookup_bytes cfg source target states address bytes found
  have unequal : (Op.aw8update == Op.aw8updateUnsafe) = false := by decide
  have update : FlatSem.updateIndexed source unsafeOp address bytes index byte .w8array = some (sourceFinal, result) := by
    cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found, unequal] using run
  obtain ⟨targetFinal, update', finalStates, results⟩ :=
    updateIndexed_bytes_related cfg source target sourceFinal unsafeOp address bytes index byte result states update
  refine ⟨targetFinal, ?_, finalStates, results⟩
  cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found', unequal] using update'

end Flapjack.Compiler.Backend.FlatPattern
