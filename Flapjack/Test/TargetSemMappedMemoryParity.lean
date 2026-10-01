import Flapjack.Compiler.Backend.Semantics.TargetSem.MappedMemory

/-! Identical original mapped-template byte/domain observations, checked in the kernel. -/
namespace Flapjack.Test.TargetSemMappedMemoryParity
open Flapjack Flapjack.Compiler.Encoders.Asm

private def encode {width : Nat} [NeZero width] (i : HolAsm width) : List (BitVec 8) :=
  match i with
    | .inst (.mem op r (.addr b off)) =>
      let marker : BitVec 8 := match op with
        | .load => 10
        | .load8 => 11
        | .load16 => 12
        | .load32 => 14
        | .store => 20
        | .store8 => 21
        | .store16 => 22
        | .store32 => 24
      [marker, BitVec.ofNat 8 r, BitVec.ofNat 8 b, off.setWidth 8]
    | _ => [255]

-- tm_read_0
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 0 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 10 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_0_wrong_opcode
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 0 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 80 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_1
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 1 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 11 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_1_wrong_opcode
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 1 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 81 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_2
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 2 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 12 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_2_wrong_opcode
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 2 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 82 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_4
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 4 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 14 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_4_wrong_opcode
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 4 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 84 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_0
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 0 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 20 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_0_wrong_opcode
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 0 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 90 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_1
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 1 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 21 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_1_wrong_opcode
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 1 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 91 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_2
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 2 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 22 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_2_wrong_opcode
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 2 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 92 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_4
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 4 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 24 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_4_wrong_opcode
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 4 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 94 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_invalid_3
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 3 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 0 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead]
    <;> decide +kernel

-- tm_read_invalid_8
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 8 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 0 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead]
    <;> decide +kernel

-- tm_read_invalid_16
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 16 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 0 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead]
    <;> decide +kernel

-- tm_read_invalid_255
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 255 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 0 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead]
    <;> decide +kernel

-- tm_write_invalid_3
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 3 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 0 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedWrite]
    <;> decide +kernel

-- tm_write_invalid_8
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 8 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 0 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedWrite]
    <;> decide +kernel

-- tm_write_invalid_16
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 16 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 0 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedWrite]
    <;> decide +kernel

-- tm_write_invalid_255
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 255 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 0 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedWrite]
    <;> decide +kernel

-- tm_read_register_mismatch
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 0 (.addr 2 3) 4 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 10 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_base_mismatch
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 0 (.addr 7 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 10 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_offset_mismatch
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 0 (.addr 2 4) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 10 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ False := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_domain_gap
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 4 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 24 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun a => a ≠ 32+2)) ↔ False := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_wrap
example (t : HolAsmTarget 8 Nat Nat) :
    (isValidMappedRead 255 2 (.addr 2 3) 5 (17 : Nat) { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=255 then 12 else if a=255+1 then 5 else if a=255+2 then 2 else if a=255+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_wrap
example (t : HolAsmTarget 8 Nat Nat) :
    (isValidMappedWrite 255 1 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=255 then 21 else if a=255+1 then 5 else if a=255+2 then 2 else if a=255+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_read_empty_domain
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 4 (.addr 2 3) 5 ((true, 17) : Bool × Nat) { t with config := { t.config with encode := fun _ => [] }, getByte := fun _ a => if a=32 then 10 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => False)) ↔ True := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL]
    <;> decide +kernel

-- tm_write_empty_domain
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 2 (.addr 2 3) 5 false { t with config := { t.config with encode := fun _ => [] }, getByte := fun _ a => if a=32 then 10 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => False)) ↔ True := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL]
    <;> decide +kernel

-- tm_read_invalid_empty
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 3 (.addr 2 3) 5 true { t with config := { t.config with encode := fun _ => [] }, getByte := fun _ a => if a=32 then 10 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => False)) ↔ False := by
  simp +decide [isValidMappedRead]
    <;> decide +kernel

-- tm_read_byte_size_wrap
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedRead 32 256 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 10 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedRead, bytesInMemoryHOL, encode]
    <;> decide +kernel

-- tm_write_byte_size_wrap
example (t : HolAsmTarget 64 Nat Nat) :
    (isValidMappedWrite 32 257 (.addr 2 3) 5 true { t with config := { t.config with encode := encode }, getByte := fun _ a => if a=32 then 21 else if a=32+1 then 5 else if a=32+2 then 2 else if a=32+3 then 3 else 0 } 0 (fun _ => True)) ↔ True := by
  simp +decide [isValidMappedWrite, bytesInMemoryHOL, encode]
    <;> decide +kernel

end Flapjack.Test.TargetSemMappedMemoryParity
