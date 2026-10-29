import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveString

/-! String and byte-array copy primitives for the proof-side flat pattern
simulation. The evaluator and relations remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result copyArray xorBytes storeAssign storeLookup)
open Flapjack.SemanticPrimitivesProps (storeValueRel)

/-- A successful string-to-string copy has its three literal operands. -/
theorem copyStrStr_operands {C F : Type} (state next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.doApp state (.src .copyStrStr) values = some (next, result)) :
    ∃ string offset length, values = [.litv (.strLit string), .litv (.intLit offset), .litv (.intLit length)] := by
  simp only [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  repeat' split at run <;> simp_all [FlatSem.boundsFailure]

/-- String slicing preserves the copied bytes and checked bounds exception. -/
theorem doApp_copyStrStr_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .copyStrStr) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .copyStrStr) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  obtain ⟨string, offset, length, rfl⟩ := copyStrStr_operands source sourceFinal values result run
  have equal : values' = [.litv (.strLit string), .litv (.intLit offset), .litv (.intLit length)] := by
    apply related_literal_list related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  subst values'
  cases copied : copyArray (string.explode, offset) length none with
  | none =>
    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
      FlatSem.doAppCopy, FlatSem.boundsFailure, copied] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, .err (.raise FlatSem.subscriptExnV),
      by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData,
        FlatSem.doAppCopy, FlatSem.boundsFailure, copied], states, .error (.raise subscriptExn_related)⟩
  | some chars =>
    simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, copied] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, .val (.litv (.strLit (.implode chars))),
      by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, copied],
      states, .value ((valueRel_lit _ _).2 rfl)⟩

/-- A list of related literals and locations is identical on the target side. -/
theorem related_scalar_list {values values' : List FlatSem.Value} (related : List.Forall₂ ValueRel values values')
    (scalar : ∀ value ∈ values, (∃ literal, value = .litv literal) ∨ (∃ flag index, value = .loc flag index)) :
    values' = values := by
  induction related with
  | nil => rfl
  | @cons value value' tail tail' valueRel tailRel ih =>
    have headEq : value' = value := by
      rcases scalar value (by simp) with ⟨literal, rfl⟩ | ⟨flag, index, rfl⟩
      · exact (valueRel_lit literal value').1 valueRel
      · exact (valueRel_loc flag index value').1 valueRel
    have tailEq := ih (by intro value member; exact scalar value (List.mem_cons_of_mem _ member))
    simp [headEq, tailEq]

/-- A successful byte-array-to-string copy has a location and two integer operands. -/
theorem copyAw8Str_operands {C F : Type} (state next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.doApp state (.src .copyAw8Str) values = some (next, result)) :
    ∃ flag address offset length, values = [.loc flag address, .litv (.intLit offset), .litv (.intLit length)] := by
  simp only [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  repeat' split at run <;> simp_all [FlatSem.boundsFailure]

/-- Copying a byte-array slice to a string preserves bytes and bounds errors. -/
theorem doApp_copyAw8Str_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .copyAw8Str) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .copyAw8Str) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  obtain ⟨flag, address, offset, length, rfl⟩ := copyAw8Str_operands source sourceFinal values result run
  have equal : values' = [.loc flag address, .litv (.intLit offset), .litv (.intLit length)] := by
    apply related_scalar_list related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  subst values'
  cases found : Flapjack.SemanticPrimitivesHOL.storeLookup address source.refs with
  | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found] at run
  | some entry =>
    cases entry with
    | w8array bytes =>
      have found' := stateRel_lookup_bytes cfg source target states address bytes found
      cases copied : copyArray (bytes, offset) length none with
      | none =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy,
          FlatSem.boundsFailure, found, copied] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .err (.raise FlatSem.subscriptExnV),
          by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy,
            FlatSem.boundsFailure, found', copied], states, .error (.raise subscriptExn_related)⟩
      | some chars =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found, copied] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .val (.litv (.strLit (.implode chars))),
          by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found', copied],
          states, .value ((valueRel_lit _ _).2 rfl)⟩
    | refv _ | varray _ | thunk _ _ =>
      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found] at run

/-- A successful byte-array XOR has a location and string operand. -/
theorem xorAw8Str_operands {C F : Type} (state next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.doApp state (.src .xorAw8StrUnsafe) values = some (next, result)) :
    ∃ flag address string, values = [.loc flag address, .litv (.strLit string)] := by
  simp only [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  repeat' split at run <;> simp_all

/-- Byte-array XOR preserves the updated store and returned unit value. -/
theorem doApp_xorAw8Str_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .xorAw8StrUnsafe) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .xorAw8StrUnsafe) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  obtain ⟨flag, address, string, rfl⟩ := xorAw8Str_operands source sourceFinal values result run
  have equal : values' = [.loc flag address, .litv (.strLit string)] := by
    apply related_scalar_list related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  subst values'
  cases found : storeLookup address source.refs with
  | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found] at run
  | some entry =>
    cases entry with
    | w8array bytes =>
      have found' := stateRel_lookup_bytes cfg source target states address bytes found
      cases xored : xorBytes string.explode bytes with
      | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found, xored] at run
      | some output =>
        cases assigned : storeAssign address (.w8array output) source.refs with
        | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found, xored, assigned] at run
        | some refs =>
          have entries : storeValueRel ValueRel (.w8array output) (.w8array output) := rfl
          obtain ⟨refs', assigned', refsRel⟩ := storeAssign_related states.2.1 address entries assigned
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found, xored, assigned] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ target with refs := refs' }, .val FlatSem.unitValue, ?_, ⟨states.1, refsRel, states.2.2⟩, .value ?_⟩
          · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found', xored, assigned']
          · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩
    | refv _ | varray _ | thunk _ _ =>
      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found] at run

/-- A successful string-to-byte-array copy has the original five scalar operands. -/
theorem copyStrAw8_operands {C F : Type} (state next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.doApp state (.src .copyStrAw8) values = some (next, result)) :
    ∃ string offset length flag address destinationOffset,
      values = [.litv (.strLit string), .litv (.intLit offset), .litv (.intLit length),
        .loc flag address, .litv (.intLit destinationOffset)] := by
  simp only [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  repeat' split at run <;> simp_all [FlatSem.boundsFailure]

/-- Copying a string into a byte array preserves both bounds errors and the
updated store. -/
theorem doApp_copyStrAw8_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .copyStrAw8) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .copyStrAw8) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  obtain ⟨string, offset, length, flag, address, dstOffset, rfl⟩ := copyStrAw8_operands source sourceFinal values result run
  have equal : values' = [.litv (.strLit string), .litv (.intLit offset), .litv (.intLit length), .loc flag address, .litv (.intLit dstOffset)] := by
    apply related_scalar_list related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  subst values'
  cases found : storeLookup address source.refs with
  | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found] at run
  | some entry =>
    cases entry with
    | w8array bytes =>
      have found' := stateRel_lookup_bytes cfg source target states address bytes found
      cases copied : copyArray (string.explode, offset) length (some (bytes, dstOffset)) with
      | none =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy,
          FlatSem.boundsFailure, found, copied] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .err (.raise FlatSem.subscriptExnV),
          by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy,
            FlatSem.boundsFailure, found', copied], states, .error (.raise subscriptExn_related)⟩
      | some output =>
        cases assigned : storeAssign address (.w8array output) source.refs with
        | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found, copied, assigned] at run
        | some refs =>
          have entries : storeValueRel ValueRel (.w8array output) (.w8array output) := rfl
          obtain ⟨refs', assigned', refsRel⟩ := storeAssign_related states.2.1 address entries assigned
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found, copied, assigned] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ target with refs := refs' }, .val FlatSem.unitValue, ?_, ⟨states.1, refsRel, states.2.2⟩, .value ?_⟩
          · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found', copied, assigned']
          · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩
    | refv _ | varray _ | thunk _ _ =>
      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, found] at run

/-- A successful byte-array copy has two locations and three integer operands. -/
theorem copyAw8Aw8_operands {C F : Type} (state next : FlatSem.State C F) (values : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.doApp state (.src .copyAw8Aw8) values = some (next, result)) :
    ∃ srcFlag src offset length dstFlag dst dstOffset,
      values = [.loc srcFlag src, .litv (.intLit offset), .litv (.intLit length),
        .loc dstFlag dst, .litv (.intLit dstOffset)] := by
  simp only [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy] at run
  repeat' split at run <;> simp_all [FlatSem.boundsFailure]

/-- Copying between byte arrays preserves bounds errors and the updated store,
including when both locations are the same. -/
theorem doApp_copyAw8Aw8_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .copyAw8Aw8) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .copyAw8Aw8) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  obtain ⟨srcFlag, src, offset, length, dstFlag, dst, dstOffset, rfl⟩ := copyAw8Aw8_operands source sourceFinal values result run
  have equal : values' = [.loc srcFlag src, .litv (.intLit offset), .litv (.intLit length), .loc dstFlag dst, .litv (.intLit dstOffset)] := by
    apply related_scalar_list related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  subst values'
  cases sourceFound : storeLookup src source.refs with
  | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, sourceFound] at run
  | some sourceEntry =>
    cases sourceEntry with
    | w8array bytes =>
      have sourceFound' := stateRel_lookup_bytes cfg source target states src bytes sourceFound
      cases destFound : storeLookup dst source.refs with
      | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, sourceFound, destFound] at run
      | some destEntry =>
        cases destEntry with
        | w8array dstBytes =>
          have destFound' := stateRel_lookup_bytes cfg source target states dst dstBytes destFound
          cases copied : copyArray (bytes, offset) length (some (dstBytes, dstOffset)) with
          | none =>
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy,
              FlatSem.boundsFailure, sourceFound, destFound, copied] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨target, .err (.raise FlatSem.subscriptExnV),
              by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy,
                FlatSem.boundsFailure, sourceFound', destFound', copied], states, .error (.raise subscriptExn_related)⟩
          | some output =>
            cases assigned : storeAssign dst (.w8array output) source.refs with
            | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, sourceFound, destFound, copied, assigned] at run
            | some refs =>
              have entries : storeValueRel ValueRel (.w8array output) (.w8array output) := rfl
              obtain ⟨refs', assigned', refsRel⟩ := storeAssign_related states.2.1 dst entries assigned
              simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, sourceFound, destFound, copied, assigned] at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨{ target with refs := refs' }, .val FlatSem.unitValue, ?_, ⟨states.1, refsRel, states.2.2⟩, .value ?_⟩
              · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, sourceFound', destFound', copied, assigned']
              · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩
        | refv _ | varray _ | thunk _ _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, sourceFound, destFound] at run
    | refv _ | varray _ | thunk _ _ =>
      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, FlatSem.doAppCopy, sourceFound] at run

end Flapjack.Compiler.Backend.FlatPattern
