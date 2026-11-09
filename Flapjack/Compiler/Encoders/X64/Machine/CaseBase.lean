module

public import Flapjack.Compiler.Encoders.X64.Machine.DecodeCongr
public import Flapjack.Misc.BytesInMemory
public import Flapjack.Compiler.Encoders.AsmProps.PcCoverage

@[expose] public section

/-!
# Bridging encoded bytes in memory to the decoder

Every per-instruction case of `encoder_correct x64Target` starts from
`asm_step`'s `bytes_in_memory` fact: the bytes of `c.encode i` sit at `s.pc`
inside the source memory domain.  This module turns that into the two facts
the closed model needs: the byte addresses lie in the domain (for fetch
safety), and decoding the memory at `PC` gives the same instruction as decoding
the byte list (for the decoder inverses).

Both are Flapjack infrastructure; no declaration here is a HOL port.
-/

namespace Flapjack.Compiler.Encoders.X64

/-- Adding one before the `j`-th byte offset is the `(j + 1)`-th byte offset. -/
theorem x64AddOneOffset (a : BitVec 64) (j : Nat) :
    (a + 1) + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (j + 1) :=
  Flapjack.Compiler.Encoders.AsmProps.addOneOffset a j

/-- The `j`-th byte of a byte list in memory lies in the domain, for every `j`
below the length. -/
theorem bytesInMemoryHOL_domain :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64) (m : BitVec 64 → BitVec 8)
      (d : BitVec 64 → Prop), bytesInMemoryHOL a bs m d →
      ∀ j, j < bs.length → d (a + BitVec.ofNat 64 j) :=
  fun bs a m d h j hj =>
    Flapjack.Compiler.Encoders.AsmProps.byteOffsetInDomain bs a m d h j hj

/-- The `j`-th byte of a byte list in memory is the `j`-th byte of the list,
for every `j` below the length. -/
theorem bytesInMemoryHOL_get :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64) (m : BitVec 64 → BitVec 8)
      (d : BitVec 64 → Prop), bytesInMemoryHOL a bs m d →
      ∀ j, j < bs.length → m (a + BitVec.ofNat 64 j) = bs.getD j 0 :=
  fun _bs _a _m _d h j hj =>
    Flapjack.Compiler.Encoders.AsmProps.bytesInMemoryHOL_get h j hj

/-- Decoding the byte list and decoding the same bytes from memory agree,
provided the decoded instruction's length is within the list. -/
theorem decode_bytesInMemory (bs : List (BitVec 8)) (a : BitVec 64)
    (m : BitVec 64 → BitVec 8) (d : BitVec 64 → Prop)
    (i : X64Insn) (len : Nat)
    (hbm : bytesInMemoryHOL a bs m d)
    (hd : decode (byteListReader bs) = some (i, len))
    (hlen : len ≤ bs.length) :
    decode (fun k => m (a + BitVec.ofNat 64 k)) = some (i, len) := by
  refine decode_congr_upto (byteListReader bs) (fun k => m (a + BitVec.ofNat 64 k)) i len hd ?_
  intro j hj
  rw [bytesInMemoryHOL_get bs a m d hbm j (by omega)]

end Flapjack.Compiler.Encoders.X64
