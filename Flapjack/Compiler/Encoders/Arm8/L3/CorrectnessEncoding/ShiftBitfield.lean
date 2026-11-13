module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftImmediate

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `BitfieldMove@64`: the `.lsl`/`.lsr`/`.asr` immediate forms of `shift`

`arm8_ast` lowers `Arith (Shift sh d s (Imm v))` for `sh ∈ {Lsl, Lsr, Asr}` to a
single `BitfieldMove@64` instruction guarded by `DecodeBitMasks`:

* `Lsl` emits `BitfieldMove@64 (1, T, F, wmask, tmask, w2n r, w2n s, s, d)` where
  `i = n2w v : word6`, `r = -i`, `s = 63w - i` and
  `DecodeBitMasks (1, s, r, F) = SOME (wmask, tmask)`;
* `Lsr`/`Asr` emit `BitfieldMove@64 (1, T, sh = Asr, wmask, tmask, v, 63, s, d)`
  where `DecodeBitMasks (1, 63w, n2w v, F) = SOME (wmask, tmask)`.

This module records the emitted word, its `Encode`/`Decode` inverse and the
`Run` semantics.  The mask algebra that turns the `BitfieldMove` expression into
the source-side `wordShift` (`arm8_targetProofScript.sml`'s `lsl`, `lsr`, `asr2`)
and the case theorems follow in `ShiftBitfieldCase`.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The `opc` field `Encode` derives from `(inzero, extend)`. -/
def arm8BitfieldOpc (inzero extend : Bool) : Option (BitVec 2) :=
  if inzero then (if extend then some (BitVec.ofNat 2 0) else some (BitVec.ofNat 2 2))
  else (if extend then none else some (BitVec.ofNat 2 1))

/-- The word emitted for `BitfieldMove@64`: HOL's `e_data` term
`sz ++ opc ++ 0b100110 ++ sz ++ immr ++ imms ++ Rn ++ Rd` (Flapjack
infrastructure: a readable abbreviation for a mechanically rendered term). -/
def arm8BitfieldWord (sz : BitVec 1) (opc : BitVec 2) (r s : BitVec 6)
    (rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 (sz ++
    BitVec.setWidth 31 (opc ++
      BitVec.setWidth 29 (BitVec.ofNat 6 38 ++
        BitVec.setWidth 23 (sz ++
          BitVec.setWidth 22 (r ++
            BitVec.setWidth 16 (s ++
              BitVec.setWidth 10 (rn ++ rd)))))))

/-- `e_data` of `BitfieldMove@64` is the bitfield word, provided `Encode`'s
`(inzero, extend)` guard yields `opc` and its `DecodeBitMasks` guard holds
(Flapjack infrastructure; no separately named HOL declaration). -/
theorem arm8EData_bitfieldMove (inzero extend : Bool) (opc : BitVec 2)
    (wmask tmask : BitVec 64) (immr imms : Nat) (rn rd : BitVec 5)
    (hopc : arm8BitfieldOpc inzero extend = some opc)
    (himmr : immr < 64) (himms : imms < 64)
    (hmasks : DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 imms, (BitVec.ofNat 6 immr, false))) =
        some (wmask, tmask)) :
    e_data (.«BitfieldMove@64»
        ((1 : BitVec 64), (inzero, (extend, (wmask, (tmask, (immr, (imms, (rn, rd))))))))) =
      MachineCode.ARM8 (arm8BitfieldWord 1 opc (BitVec.ofNat 6 immr) (BitVec.ofNat 6 imms)
        rn rd) := by
  simp only [e_data, arm8BitfieldWord, e_sf, arm8BitfieldOpc] at hopc ⊢
  rw [hopc]
  simp only [holV2w_one_true, hmasks, himmr, himms, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    beq_self_eq_true, Bool.and_self, ite_true]

/-- `Encode` of `BitfieldMove@64` is the bitfield word. -/
theorem arm8Encode_bitfieldMove (inzero extend : Bool) (opc : BitVec 2)
    (wmask tmask : BitVec 64) (immr imms : Nat) (rn rd : BitVec 5)
    (hopc : arm8BitfieldOpc inzero extend = some opc)
    (himmr : immr < 64) (himms : imms < 64)
    (hmasks : DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 imms, (BitVec.ofNat 6 immr, false))) =
        some (wmask, tmask)) :
    Encode (instruction.Data (.«BitfieldMove@64»
        ((1 : BitVec 64), (inzero, (extend, (wmask, (tmask, (immr, (imms, (rn, rd)))))))))) =
      MachineCode.ARM8 (arm8BitfieldWord 1 opc (BitVec.ofNat 6 immr) (BitVec.ofNat 6 imms)
        rn rd) := by
  simp only [Encode]
  exact arm8EData_bitfieldMove inzero extend opc wmask tmask immr imms rn rd
    hopc himmr himms hmasks

/-- `BitVec.ofNat 1 1` and the `OfNat` literal agree (Flapjack infrastructure). -/
theorem holBitVec_one_eq : BitVec.ofNat 1 1 = (1 : BitVec 1) := by decide

/-- The rendered `Decode` inverts `arm8BitfieldWord` for the `opc = 2` form
(`inzero = true`, `extend = false`), which is what `Lsl` and `Lsr` emit. -/
theorem arm8Decode_bitfieldMove_2 (wmask tmask : BitVec 64) (immr imms : Nat)
    (rn rd : BitVec 5) (himmr : immr < 64) (himms : imms < 64)
    (hmasks : DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 imms, (BitVec.ofNat 6 immr, false))) =
        some (wmask, tmask)) :
    Decode (arm8BitfieldWord 1 (BitVec.ofNat 2 2) (BitVec.ofNat 6 immr) (BitVec.ofNat 6 imms)
        rn rd) =
      instruction.Data (.«BitfieldMove@64»
        ((1 : BitVec 64), (true, (false, (wmask, (tmask, (immr, (imms, (rn, rd))))))))) := by
  simp only [arm8BitfieldWord, Decode, boolify32, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  simp [holV2w_one_true, holV2w_two_two, holV2w_five, holV2w_six, himmr, himms,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [holBitVec_one_eq, hmasks]

/-- The rendered `Decode` inverts `arm8BitfieldWord` for the `opc = 0` form
(`inzero = true`, `extend = true`), which is what `Asr` emits. -/
theorem arm8Decode_bitfieldMove_0 (wmask tmask : BitVec 64) (immr imms : Nat)
    (rn rd : BitVec 5) (himmr : immr < 64) (himms : imms < 64)
    (hmasks : DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 imms, (BitVec.ofNat 6 immr, false))) =
        some (wmask, tmask)) :
    Decode (arm8BitfieldWord 1 (BitVec.ofNat 2 0) (BitVec.ofNat 6 immr) (BitVec.ofNat 6 imms)
        rn rd) =
      instruction.Data (.«BitfieldMove@64»
        ((1 : BitVec 64), (true, (true, (wmask, (tmask, (immr, (imms, (rn, rd))))))))) := by
  simp only [arm8BitfieldWord, Decode, boolify32, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  simp [holV2w_one_true, holV2w_two_zero, holV2w_five, holV2w_six, himmr, himms,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [holBitVec_one_eq, hmasks]

/-- `Run` of `BitfieldMove@64`: HOL's `dfn'BitfieldMove` body with the masks
left symbolic. -/
theorem arm8Run_bitfieldMove (inzero extend : Bool) (wmask tmask : BitVec 64)
    (R S : Nat) (n d : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (.«BitfieldMove@64»
        ((1 : BitVec 64), (inzero, (extend, (wmask, (tmask, (R, (S, (n, d)))))))))) st =
      «write'X»
        (((if extend then Replicate (TN := 64) [(X (TN := 64) n st).getLsbD S]
            else (if inzero then BitVec.ofNat 64 0 else X (TN := 64) d st)) &&& (~~~tmask)) |||
          ((((if inzero then BitVec.ofNat 64 0 else X (TN := 64) d st) &&& (~~~wmask)) |||
            ((BitVec.rotateRight (X (TN := 64) n st) R) &&& wmask)) &&& tmask),
          d) st := by
  simp only [Run, «dfn'BitfieldMove»]

end Flapjack.Compiler.Encoders.Arm8.L3
