import Flapjack.Compiler.Backend.Semantics.TargetSem.EncodedBytes
import Flapjack.Compiler.Backend.Semantics.TargetSem.FfiReads
import Flapjack.Compiler.Backend.Semantics.TargetSem.MappedMemory
import Flapjack.Misc.FindIndex
import Flapjack.Misc.ListEl
import Flapjack.Misc.Sptree
import Flapjack.Byte

import Flapjack.Compiler.Backend.Semantics.TargetProps.InterferenceApp

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Flapjack.Compiler.Encoders.Asm Classical

-- Inhabitation only; out-of-range EL remains the shared opaque HOL ARB.
private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

/-- Literal HOL clocked first-interference search (targetPropsScript.sml:112-211). All normal/cache/MMIO/external-FFI guards are retained; the first
interference returns its pre/post application and updated configuration/FFI.
Total holEl uses the in-range list element and holHdNil/shared holArb
HolFfiName past the end, matching original EL/TL/HD. No added index or
list-length premise, bounds guard, or concrete missing-name choice is used. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def findNextInterference {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) : Nat → state → Option (InterferenceApp width state × MachineConfig width state projection × HolFfiState σ)
  | 0, _ => none
  | k + 1, ms =>
    let pc := mc.target.getPc ms
    if mc.progAddresses pc ∧ pc ∉ mc.ffiEntryPcs then
      if encodedBytesInMemHOL mc.target.config pc (mc.target.getByte ms) mc.progAddresses then
        let ms1 := mc.target.next ms
        let (ms2, newOracle) := applyOracleHOL mc.nextInterfer ms1
        let mc := { mc with nextInterfer := newOracle }
        if mc.target.stateOk ms = true ∧ mc.target.stateOk ms1 = true ∧
            mc.target.stateOk ms2 = true ∧
            (∀ x, ¬ mc.progAddresses x → mc.target.getByte ms1 x = mc.target.getByte ms x) then
          findNextInterference mc ffi k ms2
        else none
      else none
    else if pc = mc.haltPc then
      none
    else if pc = mc.ccachePc then
      let (ms1, newOracle) := applyOracleHOL mc.ccacheInterfer
        (mc.target.getReg ms mc.ptrReg, mc.target.getReg ms mc.lenReg, ms)
      some (.ccApp (mc.target.getReg ms mc.ptrReg)
        (mc.target.getReg ms mc.lenReg) ms ms1,
        { mc with ccacheInterfer := newOracle }, ffi)
    else
      match Misc.findIndex pc mc.ffiEntryPcs 0 with
      | none => none
      | some index =>
        let name := holEl index mc.ffiNames
        let finish := fun result =>
          match result with
          | HolFfiResult.final _ => none
          | HolFfiResult.ret newFfi newBytes =>
            let (ms1, newOracle) := applyOracleHOL mc.ffiInterfer (index, newBytes, ms)
            some (.ffiApp index newBytes ms ms1,
              { mc with ffiInterfer := newOracle }, newFfi)
        match name with
        | .sharedMem op =>
          match sptAListLookup index mc.mmioInfo with
          | none => none
          | some (nb, address, reg, returnPc) =>
            match address with
            | .addr r off =>
              let ad := mc.target.getReg ms r + off
              match op with
              | .mappedRead =>
                if (if nb = 0 then ad.toNat % (width / 8) = 0 else True) ∧
                    mc.sharedAddresses ad ∧
                    isValidMappedRead pc nb address reg returnPc mc.target ms mc.progAddresses then
                  finish (callFFIHOL ffi name [nb] (HolByte.wordToBytes ad false))
                else none
              | .mappedWrite =>
                if (if nb = 0 then ad.toNat % (width / 8) = 0 else True) ∧
                    mc.sharedAddresses ad ∧
                    isValidMappedWrite pc nb address reg returnPc mc.target ms mc.progAddresses then
                  let w := mc.target.getReg ms reg
                  finish (callFFIHOL ffi name [nb]
                    ((if nb = 0 then HolByte.wordToBytes w false
                      else HolByte.wordToBytesAux nb.toNat w false) ++ HolByte.wordToBytes ad false))
                else none
        | .extCall _ =>
          match sptAListLookup index mc.mmioInfo with
          | some _ => none
          | none =>
            match readFfiBytearraysHOL mc ms with
            | (some bytes, some bytes2) => finish (callFFIHOL ffi name bytes bytes2)
            | _ => none


end Flapjack.Compiler.Backend.Semantics.TargetProps
