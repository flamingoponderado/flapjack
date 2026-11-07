module

public import Flapjack.RiscV.Model

@[expose] public section

/-! Proof-only snapshot of the replaced numeric encoder. All definitions are
noncomputable so they generate no executable encoder. The migration theorem
compares native runtime encoding with this historical function, without any
validity or target-run premise. This infrastructure has no HOL original. -/
namespace Flapjack.RiscV.EncodingReference

noncomputable def encodeWord32 (value : Nat) : BitVec 32 := BitVec.ofNat 32 value

noncomputable def lowBits (value : Word width) (bits : Nat) : Nat :=
  value.toNat % 2 ^ bits

noncomputable def registerBits (register : Fin 32) : Nat := register.val

noncomputable def encodeR (opcode funct3 funct7 : Nat)
    (destination sourceLeft sourceRight : Fin 32) : BitVec 32 :=
  encodeWord32 (opcode +
    registerBits destination * 2 ^ 7 +
    funct3 * 2 ^ 12 +
    registerBits sourceLeft * 2 ^ 15 +
    registerBits sourceRight * 2 ^ 20 +
    funct7 * 2 ^ 25)

noncomputable def encodeIValue (opcode funct3 : Nat) (destination source : Fin 32)
    (immediate : Nat) : BitVec 32 :=
  encodeWord32 (opcode +
    registerBits destination * 2 ^ 7 +
    funct3 * 2 ^ 12 +
    registerBits source * 2 ^ 15 +
    (immediate % 2 ^ 12) * 2 ^ 20)

noncomputable def encodeI (opcode funct3 : Nat) (destination source : Fin 32)
    (immediate : Word width) : BitVec 32 :=
  encodeIValue opcode funct3 destination source (lowBits immediate 12)

noncomputable def encodeS (funct3 : Nat) (source address : Fin 32)
    (immediate : Word width) : BitVec 32 :=
  let value := lowBits immediate 12
  encodeWord32 (0x23 +
    (value / 2 ^ 5 % 2 ^ 7) * 2 ^ 25 +
    registerBits source * 2 ^ 20 +
    registerBits address * 2 ^ 15 +
    funct3 * 2 ^ 12 +
    (value % 2 ^ 5) * 2 ^ 7)

noncomputable def encodeB (funct3 : Nat) (sourceLeft sourceRight : Fin 32)
    (offset : Word width) : BitVec 32 :=
  let value := lowBits offset 13
  encodeWord32 (0x63 +
    (value / 2 ^ 12 % 2) * 2 ^ 31 +
    (value / 2 ^ 5 % 2 ^ 6) * 2 ^ 25 +
    registerBits sourceRight * 2 ^ 20 +
    registerBits sourceLeft * 2 ^ 15 +
    funct3 * 2 ^ 12 +
    (value / 2 % 2 ^ 4) * 2 ^ 8 +
    (value / 2 ^ 11 % 2) * 2 ^ 7)

noncomputable def encodeU (opcode : Nat) (destination : Fin 32)
    (immediate : Word width) : BitVec 32 :=
  encodeWord32 (opcode + registerBits destination * 2 ^ 7 +
    lowBits immediate 20 * 2 ^ 12)

noncomputable def encodeJ (destination : Fin 32) (offset : Word width) : BitVec 32 :=
  let value := lowBits offset 21
  encodeWord32 (0x6f + registerBits destination * 2 ^ 7 +
    (value / 2 ^ 12 % 2 ^ 8) * 2 ^ 12 +
    (value / 2 ^ 11 % 2) * 2 ^ 20 +
    (value / 2 ^ 1 % 2 ^ 10) * 2 ^ 21 +
    (value / 2 ^ 20 % 2) * 2 ^ 31)

noncomputable def encodeWordBytesWeighted (value : BitVec 32) : List (BitVec 8) :=
  [ BitVec.ofNat 8 (value.toNat % 256)
  , BitVec.ofNat 8 (value.toNat / 256 % 256)
  , BitVec.ofNat 8 (value.toNat / (256 ^ 2) % 256)
  , BitVec.ofNat 8 (value.toNat / (256 ^ 3) % 256) ]

end Flapjack.RiscV.EncodingReference
