import Flapjack.Compiler.Backend.Semantics.TargetSem.EncodedBytes
import Flapjack.Compiler.Backend.Semantics.TargetSem.FfiReads
import Flapjack.Compiler.Backend.Semantics.TargetSem.MappedMemory
import Flapjack.Misc.FindIndex
import Flapjack.Misc.ListEl
import Flapjack.Misc.Sptree
import Flapjack.Byte

namespace Flapjack
open Flapjack.Compiler.Encoders.Asm
open Classical

-- Inhabitation supplies the shared opaque HOL ARB; it does not select an
-- out-of-range FFI name.
private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

/-- Literal clocked target evaluator. Program addresses excluding FFI entries
have priority over halt/cache addresses. Failed guards retain the original
machine and FFI states; successful calls advance only their own oracle.
Total `holEl` calls `holHd` at index zero and recursively drops a head at
successor indices, matching original EL/TL/HD. In-range names are their list
elements; past the end, `holHdNil` is the shared opaque `holArb HolFfiName`.
The private Nonempty instance proves inhabitation only and selects no concrete
missing name. There is no names/entry-PC length premise, bounds guard, Option
fallback, or assumption that a selected name exists. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "evaluate_def"
  (words_as_type_indexed_bitvec)]
noncomputable def evaluateTargetHOL {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) : Nat → state → MachineResult × state × HolFfiState σ
  | 0, ms => (.timeOut, ms, ffi)
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
          evaluateTargetHOL mc ffi k ms2
        else (.error, ms, ffi)
      else (.error, ms, ffi)
    else if pc = mc.haltPc then
      (.halt (if mc.target.getReg ms mc.ptrReg = 0 then .success else .resourceLimitHit), ms, ffi)
    else if pc = mc.ccachePc then
      let (ms1, newOracle) := applyOracleHOL mc.ccacheInterfer
        (mc.target.getReg ms mc.ptrReg, mc.target.getReg ms mc.lenReg, ms)
      evaluateTargetHOL { mc with ccacheInterfer := newOracle } ffi k ms1
    else
      match Misc.findIndex pc mc.ffiEntryPcs 0 with
      | none => (.error, ms, ffi)
      | some index =>
        let name := holEl index mc.ffiNames
        let finish := fun result =>
          match result with
          | HolFfiResult.final event => (.halt (.ffiOutcome event), ms, ffi)
          | HolFfiResult.ret newFfi newBytes =>
            let (ms1, newOracle) := applyOracleHOL mc.ffiInterfer (index, newBytes, ms)
            evaluateTargetHOL { mc with ffiInterfer := newOracle } newFfi k ms1
        match name with
        | .sharedMem op =>
          match sptAListLookup index mc.mmioInfo with
          | none => (.error, ms, ffi)
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
                else (.error, ms, ffi)
              | .mappedWrite =>
                if (if nb = 0 then ad.toNat % (width / 8) = 0 else True) ∧
                    mc.sharedAddresses ad ∧
                    isValidMappedWrite pc nb address reg returnPc mc.target ms mc.progAddresses then
                  let w := mc.target.getReg ms reg
                  finish (callFFIHOL ffi name [nb]
                    ((if nb = 0 then HolByte.wordToBytes w false
                      else HolByte.wordToBytesAux nb.toNat w false) ++ HolByte.wordToBytes ad false))
                else (.error, ms, ffi)
        | .extCall _ =>
          match sptAListLookup index mc.mmioInfo with
          | some _ => (.error, ms, ffi)
          | none =>
            match readFfiBytearraysHOL mc ms with
            | (some bytes, some bytes2) => finish (callFFIHOL ffi name bytes bytes2)
            | _ => (.error, ms, ffi)

end Flapjack
