import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.CutState
import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Raise
import Flapjack.Pancake.Semantics.LoopSemStateExact.ProductionExtCall

/-!
# Concrete byte-array adapter relations for the produced Loop FFI hook

Delivered for bead `flapjack-pxn.18.5.6.30.4.1.2.2.24.1`.  It proves the concrete
read/write byte-array relations between the production `Loop` FFI adapter
`Flapjack.loopReadByteArray`/`Flapjack.loopWriteByteArray`
(`ProductionExtCall.lean`) and the exact HOL-shaped `wordSem` byte operations
over `LoopSemStateFiniteExact`, under the observational `prodRel`.  It also
transports the `FfiBridge` `ExtCall` call lemmas to the `MlString` name used by
the exact FFI clause.

Everything below is Flapjack-specific bridge infrastructure (no `@[hol]` tag):
these are cross-carrier relations between the exact finite-support carrier and
the production carrier, not ports of separate HOL declarations.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.LoopSemStateFiniteExact.EvaluateCases

/-! ## Memory view -/

/-- On the production `memory`, the total exact memory view
    `loopMachineMemoryExact` agrees with the exact memory.  The two private
    word/location codecs in `ProductionExtCall.lean` are inverse on the related
    payload, so no exposed roundtrip lemma is needed. -/
theorem loopMachineMemoryExact_eq {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hmemory : ∀ address, m.memory address = some (loopValueOfWordLocW (s.memory address)))
    (address : BitVec 64) :
    loopMachineMemoryExact m address = s.memory address := by
  unfold loopMachineMemoryExact
  rw [hmemory address]
  cases s.memory address <;> rfl

/-! ## Byte codec round trips -/

/-- The production byte codec is a right inverse of `bitsToByte` on `BitVec 8`. -/
theorem byteToBits_bitsToByte (value : BitVec 8) : byteToBits (bitsToByte value) = value := by
  rw [byteToBits, bitsToByte]
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (BitVec.isLt value), BitVec.ofNat_toNat]
  simp

/-- Re-encoding a projected HOL byte list recovers it. -/
theorem map_byteToBits_bitsToByte (bytes : List (BitVec 8)) :
    (bytes.map bitsToByte).map byteToBits = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte tail ih => simp [byteToBits_bitsToByte byte, ih]

/-! ## (A) Read -/

/-- **Read correspondence.**  Under `prodRel`, the production `loopReadByteArray`
    is exactly the `UInt8` projection of the exact `read_bytearray` over
    `s.memory`/`s.mdomain`/`s.be`, including failure. -/
theorem loopReadByteArray_eq {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hrel : s.prodRel m) (address : BitVec 64) (length : Nat) :
    loopReadByteArray m address length =
      (readBytearrayWordHOL (byteWidth := 8) address length
        (memLoadByteAuxExact s.memory s.mdomain s.be)).map (List.map bitsToByte) := by
  obtain ⟨_, _, hmemory, hmdomain, _, _, hbe, _, _, _, _, _⟩ := hrel
  have hmemfun : loopMachineMemoryExact m = s.memory :=
    funext (loopMachineMemoryExact_eq hmemory)
  unfold loopReadByteArray
  rw [hmemfun, hmdomain, hbe]

/-! ## (B) Write -/

/-- **Write memory correspondence.**  Under `prodRel`, the `memory` of the
    production `loopWriteByteArray` is the `loopValueOfWordLocW` image of the
    exact `write_bytearray` over `s.memory`/`s.mdomain`/`s.be`. -/
theorem loopWriteByteArray_memory_eq {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hmemory : ∀ address, m.memory address = some (loopValueOfWordLocW (s.memory address)))
    (hmdomain : m.mdomain = s.mdomain) (hbe : m.be = s.be)
    (address : BitVec 64) (bytes : List UInt8) :
    ∀ a, (loopWriteByteArray m address bytes).memory a =
      some (loopValueOfWordLocW
        (writeBytearrayExact address (bytes.map byteToBits) s.memory s.mdomain s.be a)) := by
  have hmemfun : loopMachineMemoryExact m = s.memory :=
    funext (loopMachineMemoryExact_eq hmemory)
  intro a
  simp only [loopWriteByteArray]
  rw [hmemfun, hmdomain, hbe]
  cases h : writeBytearrayExact address (bytes.map byteToBits) s.memory s.mdomain s.be a <;> rfl

/-- **Write state correspondence.**  Under `prodRel`, writing the lifted bytes
    through the production `loopWriteByteArray` stays `prodRel`-related to the
    exact `write_bytearray` update; every non-`memory` field is unchanged on
    both sides, so it carries over from `hrel`. -/
theorem loopWriteByteArray_prodRel {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hrel : s.prodRel m) (address : BitVec 64) (bytes : List UInt8) :
    ({ s with memory := writeBytearrayExact address (bytes.map byteToBits) s.memory s.mdomain s.be }).prodRel
      (loopWriteByteArray m address bytes) := by
  obtain ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩ := hrel
  refine ⟨hlocals, hglobals, ?_, hmdomain, hshMdomain, hclock, hbe, hffi, hbaseAddr,
    htopAddr, hcode, hcoverage⟩
  exact loopWriteByteArray_memory_eq hmemory hmdomain hbe address bytes

/-! ## (C) Call transport -/

/-- The `toStringOfBytes` image of an `MlString` is byte-ranged: decoding bytes
    to characters yields codes below 256.  This discharges the `NameRanged`
    premise of the `FfiBridge` `ExtCall` bridges for the executed name path. -/
theorem nameRanged_toStringOfBytes (m : MlString) : NameRanged (toStringOfBytes m) := by
  intro character hmem
  simp only [toStringOfBytes, String.toList_ofList, List.mem_map] at hmem
  obtain ⟨byte, _hbyte, rfl⟩ := hmem
  rw [ofNat_toNat_char byte]
  simpa using byte.isLt

/-- **Call correspondence.**  Under `FfiStateRel`, the production `callFfi` on
    the executed name `toStringOfBytes function` agrees with HOL `callFFIHOL` on
    the exact `MlString` name `function` and the `byteToBits`-lifted byte lists,
    by casing on the oracle outcome and applying the `FfiBridge` per-outcome
    bridges.  The name byte-range premise is discharged by
    `nameRanged_toStringOfBytes`, and `ofString_toStringOfBytes` identifies the
    `FfiBridge` `ofString` name with `function`; no `MlString` byte-range gap
    remains on this path. -/
theorem callFfi_extCall_transport {F : Type}
    (prodState : FfiState F) (holState : HolFfiState F) (hrel : FfiStateRel prodState holState)
    (function : MlString) (configuration bytes : List UInt8) :
    FfiResultRel
      (callFfi prodState (.extCall (toStringOfBytes function)) configuration bytes)
      (callFFIHOL holState (.extCall function)
        (configuration.map byteToBits) (bytes.map byteToBits)) := by
  by_cases hne : toStringOfBytes function = ""
  · have hfun : function = MlString.implode [] := by
      rw [← ofString_toStringOfBytes function, hne]
      rfl
    rw [hfun] at hne ⊢
    rw [hne]
    exact callFfi_empty_extCall_bridge prodState holState hrel configuration bytes
  · cases ho : prodState.oracle (.extCall (toStringOfBytes function)) prodState.state
        configuration bytes with
    | final outcome =>
        simpa only [ofString_toStringOfBytes] using
          callFfi_extCall_oracleFinal_bridge prodState holState hrel
            (toStringOfBytes function) (nameRanged_toStringOfBytes function) hne
            configuration bytes outcome ho
    | returned nextState nextBytes =>
        by_cases hlen : nextBytes.length = bytes.length
        · simpa only [ofString_toStringOfBytes] using
            callFfi_extCall_success_bridge prodState holState hrel
              (toStringOfBytes function) (nameRanged_toStringOfBytes function) hne
              configuration bytes nextState nextBytes ho hlen
        · simpa only [ofString_toStringOfBytes] using
            callFfi_extCall_lengthFailure_bridge prodState holState hrel
              (toStringOfBytes function) (nameRanged_toStringOfBytes function) hne
              configuration bytes nextState nextBytes ho hlen

/-- The `callFfi_extCall_transport` bridge on the `ffi` fields of a
    `prodRel`-related exact/production state pair. -/
theorem loopMachineExtCall_call_bridge {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hrel : s.prodRel m) (function : MlString) (configuration bytes : List UInt8) :
    FfiResultRel
      (callFfi m.ffi (.extCall (toStringOfBytes function)) configuration bytes)
      (callFFIHOL s.ffi (.extCall function)
        (configuration.map byteToBits) (bytes.map byteToBits)) :=
  callFfi_extCall_transport m.ffi s.ffi hrel.2.2.2.2.2.2.2.1 function configuration bytes

/-- Recovering the exact HOL byte list from `BytesRel`: a production byte list
    `BytesRel`-related to a HOL `word8` list determines that HOL list as its
    `byteToBits` image.  Used to identify the exact returned-byte write with the
    production adapter's `bytes.map byteToBits` write. -/
theorem bytesRel_eq_map_byteToBits_probe : ∀ (bytes : List UInt8) (holBytes : List (BitVec 8)),
    BytesRel bytes holBytes → holBytes = bytes.map byteToBits
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [BytesRel] at h
  | _ :: _, [], h => by simp [BytesRel] at h
  | byte :: bytes, holByte :: holBytes, h => by
      simp only [BytesRel, List.map_cons, List.cons.injEq] at h
      obtain ⟨hhead, htail⟩ := h
      rw [List.map_cons, bytesRel_eq_map_byteToBits_probe bytes holBytes htail]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [byteToBits_toNat, hhead]

/-- Frame lemma: replacing the production and exact FFI carriers of a
    `prodRel`-related state pair by a related pair preserves `prodRel`.  Every
    other conjunct is carried over from `hrel`. -/
theorem prodRel_setFfi {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hrel : s.prodRel m) (holFfi : HolFfiState F) (prodFfi : FfiState F)
    (hffi : FfiStateRel prodFfi holFfi) :
    {s with ffi := holFfi}.prodRel {m with ffi := prodFfi} := by
  obtain ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, _,
    hbaseAddr, htopAddr, hcode, hcoverage⟩ := hrel
  exact ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩

/-- The `FFI_return` post-state of `ffiPost` related to the production
    `loopWriteByteArray … with ffi := …` post-state: the returned exact HOL
    bytes are the `byteToBits` image of the production returned bytes, the
    memory update is `loopWriteByteArray_prodRel`, and the new FFI carriers are
    related by the transported `FfiStateRel`. -/
theorem loopWriteByteArray_ffi_prodRel {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hrel : s.prodRel m) (address : BitVec 64) (prodBytes : List UInt8)
    (holBytes : List (BitVec 8)) (hbytes : holBytes = prodBytes.map byteToBits)
    (holFfi : HolFfiState F) (prodFfi : FfiState F)
    (hffi : FfiStateRel prodFfi holFfi) :
    ({ s with
        memory := writeBytearrayExact address holBytes s.memory s.mdomain s.be,
        ffi := holFfi }).prodRel
      ({ loopWriteByteArray m address prodBytes with ffi := prodFfi }) := by
  subst hbytes
  exact prodRel_setFfi (loopWriteByteArray_prodRel hrel address prodBytes) holFfi prodFfi hffi

/-- **Hook realization.**  Under `prodRel`, the production 64-bit Loop `ExtCall`
    adapter `loopMachineExtCall` realizes the exact `ffiPost` computation of the
    tagged HOL `evaluate` FFI clause: the read outcomes agree through
    `loopReadByteArray_eq`, the FFI call outcomes agree through
    `loopMachineExtCall_call_bridge`, and the post-states (the `call_env []`
    empty-local update on `FFI_final`, and the returned-byte write plus new FFI
    carrier on `FFI_return`) agree through `callEnvEmpty_prodRel` and
    `loopWriteByteArray_ffi_prodRel`.  This discharges the `hffi` premise of
    `evaluateFfi_prodRel`. -/
theorem loopMachineExtCall_ffiStepRel {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hrel : s.prodRel m) (function : MlString)
    (configurationSize configurationAddress arraySize arrayAddress : BitVec 64) :
    ffiStepRel
      (ffiPost s function configurationAddress arrayAddress configurationSize arraySize)
      (loopMachineExtCall m (Flapjack.Basis.Pure.MlString.toStringOfBytes function)
        configurationSize configurationAddress arraySize arrayAddress) := by
  unfold ffiStepRel ffiPost loopMachineExtCall
  rw [loopReadByteArray_eq hrel configurationAddress configurationSize.toNat,
    loopReadByteArray_eq hrel arrayAddress arraySize.toNat]
  cases hread1 : readBytearrayWordHOL (byteWidth := 8) configurationAddress
      configurationSize.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
  | none =>
      cases hread2 : readBytearrayWordHOL (byteWidth := 8) arrayAddress
          arraySize.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
      | none =>
          simp only [Option.map_none, ffiResultRel]
          exact ⟨trivial, hrel⟩
      | some bytes2 =>
          simp only [Option.map_none, Option.map_some, ffiResultRel]
          exact ⟨trivial, hrel⟩
  | some bytes =>
      cases hread2 : readBytearrayWordHOL (byteWidth := 8) arrayAddress
          arraySize.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
      | none =>
          simp only [Option.map_none, Option.map_some, ffiResultRel]
          exact ⟨trivial, hrel⟩
      | some bytes2 =>
          have hb := loopMachineExtCall_call_bridge hrel function
            (bytes.map bitsToByte) (bytes2.map bitsToByte)
          rw [map_byteToBits_bitsToByte bytes, map_byteToBits_bitsToByte bytes2] at hb
          cases hhol : callFFIHOL s.ffi (.extCall function) bytes bytes2 with
          | final holEvent =>
              cases hprod : callFfi m.ffi
                  (.extCall (Flapjack.Basis.Pure.MlString.toStringOfBytes function))
                  (bytes.map bitsToByte) (bytes2.map bitsToByte) with
              | final prodEvent =>
                  simp only [hhol, hprod, FfiResultRel] at hb
                  simp only [Option.map_some, hhol, hprod, ffiResultRel]
                  exact ⟨hb, callEnvEmpty_prodRel hrel⟩
              | returned prodFfi prodBytes =>
                  simp only [hhol, hprod, FfiResultRel] at hb
          | ret holFfi holBytes =>
              cases hprod : callFfi m.ffi
                  (.extCall (Flapjack.Basis.Pure.MlString.toStringOfBytes function))
                  (bytes.map bitsToByte) (bytes2.map bitsToByte) with
              | final prodEvent =>
                  simp only [hhol, hprod, FfiResultRel] at hb
              | returned prodFfi prodBytes =>
                  obtain ⟨hffi, hbytes⟩ := by
                    simpa only [hhol, hprod, FfiResultRel] using hb
                  simp only [Option.map_some, hhol, hprod, ffiResultRel]
                  exact ⟨trivial,
                    loopWriteByteArray_ffi_prodRel hrel arrayAddress prodBytes holBytes
                      (bytesRel_eq_map_byteToBits_probe prodBytes holBytes hbytes)
                      holFfi prodFfi hffi⟩

/-- The production `LoopEvaluateHooks.ffi` adapter `loopMachineFfiHook` (which
    ignores the live set and is definitionally `loopMachineExtCall`) inherits the
    hook realization from `loopMachineExtCall_ffiStepRel`. -/
theorem loopMachineFfiHook_ffiStepRel {F : Type}
    {s : LoopSemStateFiniteExact 64 F} {m : LoopMachineState (BitVec 64) F}
    (hrel : s.prodRel m) (function : MlString)
    (configurationSize configurationAddress arraySize arrayAddress : BitVec 64)
    (live : List Nat) :
    ffiStepRel
      (ffiPost s function configurationAddress arrayAddress configurationSize arraySize)
      (loopMachineFfiHook (Flapjack.Basis.Pure.MlString.toStringOfBytes function)
        configurationSize configurationAddress arraySize arrayAddress live m) :=
  loopMachineExtCall_ffiStepRel hrel function configurationSize configurationAddress
    arraySize arrayAddress

end Flapjack
