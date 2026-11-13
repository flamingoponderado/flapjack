module

public import Flapjack.Compiler.Encoders.X64.Machine.DecodeReads

@[expose] public section

namespace Flapjack.Compiler.Encoders.X64

set_option maxHeartbeats 4000000

theorem parseRM_len_pos (r : Nat → BitVec 8) (off : Nat) (rexB : Bool) (p : ParsedRM)
    (h : parseRM r off rexB = some p) : 1 ≤ p.len := by
  unfold parseRM at h
  dsimp only at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp

theorem binopReg_len (opcode off : Nat) (r : Nat → BitVec 8) (hi : Nat) (rexW rexB : Bool)
    (i : X64Insn) (len : Nat) (hd : binopReg opcode off r hi rexW rexB = some (i, len)) :
    off + 1 ≤ len := by
  unfold binopReg at hd
  dsimp only at hd
  split at hd
  · rename_i p hp
    have hp1 := parseRM_len_pos r off rexB p hp
    split at hd
    · obtain ⟨-, hl⟩ := hd
      omega
    · simp at hd
  · simp at hd

theorem movImm_len (low : Nat) (r : Nat → BitVec 8) (rexB rexW : Bool)
    (i : X64Insn) (len : Nat) (hd : movImm low r rexB rexW = some (i, len)) :
    1 < len := by
  unfold movImm at hd
  dsimp only at hd
  split at hd <;> (simp at hd) <;> omega

theorem binopReg_congr_upto (opcode off : Nat) (r r' : Nat → BitVec 8) (hi : Nat)
    (rexW rexB : Bool) (i : X64Insn) (len : Nat)
    (hd : binopReg opcode off r hi rexW rexB = some (i, len))
    (h : ∀ j, j < len → r j = r' j) :
    binopReg opcode off r' hi rexW rexB = some (i, len) := by
  unfold binopReg at hd
  dsimp only at hd
  cases hp : parseRM r off rexB with
  | none => simp [hp] at hd
  | some p =>
    have hp1 := parseRM_len_pos r off rexB p hp
    rw [hp] at hd
    dsimp only at hd
    by_cases hmod : p.modBits = 3
    · rw [ite_eq_left hmod] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi', hlen⟩ := hd
      have hlen' : len = off + p.len := hlen.symm
      have hpm : parseRM r' off rexB = some p :=
        parseRM_congr_upto r r' off rexB p hp (fun j hj => h j (by omega))
      unfold binopReg
      dsimp only
      rw [hpm]
      try simp only []
      rw [ite_eq_left hmod]
      rw [← hi', hlen']
    · rw [ite_eq_right hmod] at hd
      simp at hd

/-- `decodeRex` reads only the bytes below the length it reports. -/
theorem decodeRex_congr_upto (r r' : Nat → BitVec 8) (rexW rexR rexB : Bool)
    (i : X64Insn) (len : Nat)
    (hd : decodeRex r rexW rexR rexB = some (i, len))
    (h : ∀ j, j < len → r j = r' j) :
    decodeRex r' rexW rexR rexB = some (i, len) := by
  unfold decodeRex at hd
  dsimp only at hd
  unfold decodeRex
  dsimp only
  split at hd
  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0x05 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0x0D from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0x15 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0x1D from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0x25 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0x2D from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0x35 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0x3D from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen6 : len = 6 := hlen.symm
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have himm : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
    rw [show (r' 1).toNat = 0xA9 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hi, hlen⟩ := hd
        have hlen' : len = 2 + p.len := hlen.symm
        have h1 : r 1 = r' 1 := h 1 (by omega)
        have hpm : parseRM r' 2 rexB = some p :=
          parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
        rw [show (r' 1).toNat = 0x88 from by rw [← h1]; exact hb]
        try simp only []
        rw [hpm]
        try simp only []
        rw [ite_eq_left hmod]
        rw [← hi, hlen']
      · rw [ite_eq_right hmod] at hd
        cases hb2 : baseOfRM p.rm with
        | none => simp [hb2] at hd
        | some bd =>
          obtain ⟨base, disp⟩ := bd
          simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 2 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0x88 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_right hmod]
          rw [hb2]
          rw [← hi, hlen']

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hi, hlen⟩ := hd
        have hlen' : len = 2 + p.len := hlen.symm
        have h1 : r 1 = r' 1 := h 1 (by omega)
        have hpm : parseRM r' 2 rexB = some p :=
          parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
        rw [show (r' 1).toNat = 0x89 from by rw [← h1]; exact hb]
        try simp only []
        rw [hpm]
        try simp only []
        rw [ite_eq_left hmod]
        rw [← hi, hlen']
      · rw [ite_eq_right hmod] at hd
        cases hb2 : baseOfRM p.rm with
        | none => simp [hb2] at hd
        | some bd =>
          obtain ⟨base, disp⟩ := bd
          simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 2 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0x89 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_right hmod]
          rw [hb2]
          rw [← hi, hlen']

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        simp at hd
      · rw [ite_eq_right hmod] at hd
        cases hb2 : baseOfRM p.rm with
        | none => simp [hb2] at hd
        | some bd =>
          obtain ⟨base, disp⟩ := bd
          simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 2 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0x8B from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_right hmod]
          rw [hb2]
          rw [← hi, hlen']

  · rename_i hb
    have hl := binopReg_len 0x01 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x01 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x01 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x09 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x09 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x09 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x11 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x11 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x11 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x19 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x19 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x19 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x21 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x21 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x21 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x29 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x29 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x29 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x31 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x31 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x31 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x39 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x39 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x39 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x85 2 r (if rexR then 8 else 0) rexW rexB i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    have hreg := binopReg_congr_upto 0x85 2 r r' (if rexR then 8 else 0) rexW rexB i len hd h
    rw [show (r' 1).toNat = 0x85 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      cases he : binopOfExt p.regBits with
      | none => simp [he] at hd
      | some bop =>
        rw [he] at hd
        dsimp only at hd
        by_cases hmod : p.modBits = 3
        · rw [ite_eq_left hmod] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 3 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          have himm : imm8 r (2 + p.len) = imm8 r' (2 + p.len) :=
            imm8_congr r r' (2 + p.len) (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0x83 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [he]
          try simp only []
          rw [ite_eq_left hmod]
          rw [← himm, ← hi, hlen']
        · rw [ite_eq_right hmod] at hd
          simp at hd

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      cases he : binopOfExt p.regBits with
      | none => simp [he] at hd
      | some bop =>
        rw [he] at hd
        dsimp only at hd
        by_cases hmod : p.modBits = 3
        · rw [ite_eq_left hmod] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 6 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          have himm : imm32 r (2 + p.len) = imm32 r' (2 + p.len) :=
            imm32_congr r r' (2 + p.len) (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0x81 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [he]
          try simp only []
          rw [ite_eq_left hmod]
          rw [← himm, ← hi, hlen']
        · rw [ite_eq_right hmod] at hd
          simp at hd

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      cases he : shiftOfExt p.regBits with
      | none => simp [he] at hd
      | some sh =>
        rw [he] at hd
        dsimp only at hd
        by_cases hmod : p.modBits = 3
        · rw [ite_eq_left hmod] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 3 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          have himm : imm8 r (2 + p.len) = imm8 r' (2 + p.len) :=
            imm8_congr r r' (2 + p.len) (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0xC1 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [he]
          try simp only []
          rw [ite_eq_left hmod]
          rw [← himm, ← hi, hlen']
        · rw [ite_eq_right hmod] at hd
          simp at hd

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      cases he : shiftOfExt p.regBits with
      | none => simp [he] at hd
      | some sh =>
        rw [he] at hd
        dsimp only at hd
        by_cases hmod : p.modBits = 3
        · rw [ite_eq_left hmod] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 2 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0xD1 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [he]
          try simp only []
          rw [ite_eq_left hmod]
          rw [← hi, hlen']
        · rw [ite_eq_right hmod] at hd
          simp at hd

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      cases he : shiftOfExt p.regBits with
      | none => simp [he] at hd
      | some sh =>
        rw [he] at hd
        dsimp only at hd
        by_cases hmod : p.modBits = 3
        · rw [ite_eq_left hmod] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 2 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0xD3 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [he]
          try simp only []
          rw [ite_eq_left hmod]
          rw [← hi, hlen']
        · rw [ite_eq_right hmod] at hd
          simp at hd

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        try dsimp only at hd
        by_cases hr : p.regBits = 0
        · rw [ite_eq_left hr] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 6 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have himm : imm32 r (2 + p.len) = imm32 r' (2 + p.len) :=
            imm32_congr r r' (2 + p.len) (fun j hj => h j (by omega))
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0xF7 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_left hmod]
          rw [ite_eq_left hr]
          rw [← himm, ← hi, hlen']
        · rw [ite_eq_right hr] at hd
          try dsimp only at hd
          cases hg : group3OfExt p.regBits p.rm.regOf with
          | none => simp [hg] at hd
          | some insn =>
            rw [hg] at hd
            simp only [Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨hi, hlen⟩ := hd
            have hlen' : len = 2 + p.len := hlen.symm
            have h1 : r 1 = r' 1 := h 1 (by omega)
            have hpm : parseRM r' 2 rexB = some p :=
              parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
            rw [show (r' 1).toNat = 0xF7 from by rw [← h1]; exact hb]
            try simp only []
            rw [hpm]
            try simp only []
            rw [ite_eq_left hmod]
            rw [ite_eq_right hr]
            rw [hg]
            rw [← hi, hlen']
      · rw [ite_eq_right hmod] at hd
        simp at hd

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        try dsimp only at hd
        cases hg : group5OfExt p.regBits p.rm.regOf with
        | none => simp [hg] at hd
        | some insn =>
          rw [hg] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 2 + p.len := hlen.symm
          have h1 : r 1 = r' 1 := h 1 (by omega)
          have hpm : parseRM r' 2 rexB = some p :=
            parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
          rw [show (r' 1).toNat = 0xFF from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_left hmod]
          rw [hg]
          try simp only []
          rw [← hi, hlen']
      · rw [ite_eq_right hmod] at hd
        simp at hd

  · rename_i hb
    cases hp : parseRM r 2 rexB with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 2 rexB p hp
      rw [hp] at hd
      dsimp only at hd
      cases hrm : p.rm with
      | zm idx base disp =>
        cases idx with
        | none =>
          cases base with
          | noBase =>
            simp only [hrm] at hd
            simp at hd
          | ripBase =>
            simp only [hrm, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨hi, hlen⟩ := hd
            have hlen' : len = 2 + p.len := hlen.symm
            have h1 : r 1 = r' 1 := h 1 (by omega)
            have hpm : parseRM r' 2 rexB = some p :=
              parseRM_congr_upto r r' 2 rexB p hp (fun j hj => h j (by omega))
            rw [show (r' 1).toNat = 0x8D from by rw [← h1]; exact hb]
            try simp only []
            rw [hpm]
            try simp only []
            rw [hrm]
            rw [← hi, hlen']
          | regBase base =>
            simp only [hrm] at hd
            simp at hd
        | some idx' =>
          simp only [hrm] at hd
          simp at hd
      | zr reg =>
        simp only [hrm] at hd
        simp at hd

  · rename_i hb
    have hl := movImm_len 0 r rexB rexW i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    unfold movImm
    dsimp only
    rw [show (r' 1).toNat = 0xb8 from by rw [← h1]; exact hb]
    try simp only []
    by_cases hw : rexW
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_left hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hl64 : le64 r 2 = le64 r' 2 := le64_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_left hw]
      rw [← hl64, ← hi, hlen]
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_right hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hi32 : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_right hw]
      rw [← hi32, ← hi, hlen]

  · rename_i hb
    have hl := movImm_len 1 r rexB rexW i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    unfold movImm
    dsimp only
    rw [show (r' 1).toNat = 0xb9 from by rw [← h1]; exact hb]
    try simp only []
    by_cases hw : rexW
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_left hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hl64 : le64 r 2 = le64 r' 2 := le64_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_left hw]
      rw [← hl64, ← hi, hlen]
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_right hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hi32 : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_right hw]
      rw [← hi32, ← hi, hlen]

  · rename_i hb
    have hl := movImm_len 2 r rexB rexW i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    unfold movImm
    dsimp only
    rw [show (r' 1).toNat = 0xba from by rw [← h1]; exact hb]
    try simp only []
    by_cases hw : rexW
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_left hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hl64 : le64 r 2 = le64 r' 2 := le64_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_left hw]
      rw [← hl64, ← hi, hlen]
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_right hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hi32 : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_right hw]
      rw [← hi32, ← hi, hlen]

  · rename_i hb
    have hl := movImm_len 3 r rexB rexW i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    unfold movImm
    dsimp only
    rw [show (r' 1).toNat = 0xbb from by rw [← h1]; exact hb]
    try simp only []
    by_cases hw : rexW
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_left hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hl64 : le64 r 2 = le64 r' 2 := le64_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_left hw]
      rw [← hl64, ← hi, hlen]
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_right hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hi32 : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_right hw]
      rw [← hi32, ← hi, hlen]

  · rename_i hb
    have hl := movImm_len 4 r rexB rexW i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    unfold movImm
    dsimp only
    rw [show (r' 1).toNat = 0xbc from by rw [← h1]; exact hb]
    try simp only []
    by_cases hw : rexW
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_left hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hl64 : le64 r 2 = le64 r' 2 := le64_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_left hw]
      rw [← hl64, ← hi, hlen]
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_right hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hi32 : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_right hw]
      rw [← hi32, ← hi, hlen]

  · rename_i hb
    have hl := movImm_len 5 r rexB rexW i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    unfold movImm
    dsimp only
    rw [show (r' 1).toNat = 0xbd from by rw [← h1]; exact hb]
    try simp only []
    by_cases hw : rexW
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_left hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hl64 : le64 r 2 = le64 r' 2 := le64_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_left hw]
      rw [← hl64, ← hi, hlen]
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_right hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hi32 : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_right hw]
      rw [← hi32, ← hi, hlen]

  · rename_i hb
    have hl := movImm_len 6 r rexB rexW i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    unfold movImm
    dsimp only
    rw [show (r' 1).toNat = 0xbe from by rw [← h1]; exact hb]
    try simp only []
    by_cases hw : rexW
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_left hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hl64 : le64 r 2 = le64 r' 2 := le64_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_left hw]
      rw [← hl64, ← hi, hlen]
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_right hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hi32 : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_right hw]
      rw [← hi32, ← hi, hlen]

  · rename_i hb
    have hl := movImm_len 7 r rexB rexW i len hd
    have h1 : r 1 = r' 1 := h 1 (by omega)
    unfold movImm
    dsimp only
    rw [show (r' 1).toNat = 0xbf from by rw [← h1]; exact hb]
    try simp only []
    by_cases hw : rexW
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_left hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hl64 : le64 r 2 = le64 r' 2 := le64_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_left hw]
      rw [← hl64, ← hi, hlen]
    · unfold movImm at hd
      dsimp only at hd
      rw [ite_eq_right hw] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hi, hlen⟩ := hd
      have hi32 : imm32 r 2 = imm32 r' 2 := imm32_congr r r' 2 (fun j hj => h j (by omega))
      rw [ite_eq_right hw]
      rw [← hi32, ← hi, hlen]
  · rename_i hb
    try dsimp only at hd
    split at hd
    · rename_i hA
      split at hd
      · rename_i hC
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hi, hlen⟩ := hd
        have hlen7 : len = 7 := hlen.symm
        have h1 : r 1 = r' 1 := h 1 (by omega)
        have h2 : r 2 = r' 2 := h 2 (by omega)
        have himm : imm32 r 3 = imm32 r' 3 := imm32_congr r r' 3 (fun j hj => h j (by omega))
        rw [show (r' 1).toNat = 0x0F from by rw [← h1]; exact hb]
        try simp only []
        rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
        rw [ite_eq_left hA]
        rw [hC]
        try simp only []
        rw [← himm, ← hi, hlen]
      · simp at hd
    · rename_i hA
      split at hd
      · rename_i hB
        cases hp : parseRM r 3 rexB with
        | none => simp [hp] at hd
        | some p =>
          have hp1 := parseRM_len_pos r 3 rexB p hp
          rw [hp] at hd
          try dsimp only at hd
          split at hd
          · rename_i hC
            split at hd
            · rename_i hmod
              simp only [Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨hi, hlen⟩ := hd
              have hlen' : len = 3 + p.len := hlen.symm
              have h1 : r 1 = r' 1 := h 1 (by omega)
              have h2 : r 2 = r' 2 := h 2 (by omega)
              have hpm : parseRM r' 3 rexB = some p :=
                parseRM_congr_upto r r' 3 rexB p hp (fun j hj => h j (by omega))
              rw [show (r' 1).toNat = 0x0F from by rw [← h1]; exact hb]
              try simp only []
              rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
              rw [ite_eq_right hA]
              rw [ite_eq_left hB]
              try simp only []
              rw [hpm]
              try simp only []
              rw [hC]
              try simp only []
              rw [ite_eq_left hmod]
              rw [← hi, hlen']
            · simp at hd
          · simp at hd
      · rename_i hB
        split at hd
        · rename_i hC
          cases hp : parseRM r 3 rexB with
          | none => simp [hp] at hd
          | some p =>
            have hp1 := parseRM_len_pos r 3 rexB p hp
            rw [hp] at hd
            try dsimp only at hd
            cases hb2 : baseOfRM p.rm with
            | none => simp [hb2] at hd
            | some bd =>
              obtain ⟨base, disp⟩ := bd
              simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨hi, hlen⟩ := hd
              have hlen' : len = 3 + p.len := hlen.symm
              have h1 : r 1 = r' 1 := h 1 (by omega)
              have h2 : r 2 = r' 2 := h 2 (by omega)
              have hpm : parseRM r' 3 rexB = some p :=
                parseRM_congr_upto r r' 3 rexB p hp (fun j hj => h j (by omega))
              rw [show (r' 1).toNat = 0x0F from by rw [← h1]; exact hb]
              try simp only []
              rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
              rw [ite_eq_right hA]
              rw [ite_eq_right hB]
              rw [ite_eq_left hC]
              rw [hpm]
              try simp only []
              rw [hb2]
              rw [← hi, hlen']
        · rename_i hC
          split at hd
          · rename_i hD
            cases hp : parseRM r 3 rexB with
            | none => simp [hp] at hd
            | some p =>
              have hp1 := parseRM_len_pos r 3 rexB p hp
              rw [hp] at hd
              try dsimp only at hd
              cases hb2 : baseOfRM p.rm with
              | none => simp [hb2] at hd
              | some bd =>
                obtain ⟨base, disp⟩ := bd
                simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = 3 + p.len := hlen.symm
                have h1 : r 1 = r' 1 := h 1 (by omega)
                have h2 : r 2 = r' 2 := h 2 (by omega)
                have hpm : parseRM r' 3 rexB = some p :=
                  parseRM_congr_upto r r' 3 rexB p hp (fun j hj => h j (by omega))
                rw [show (r' 1).toNat = 0x0F from by rw [← h1]; exact hb]
                try simp only []
                rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
                rw [ite_eq_right hA]
                rw [ite_eq_right hB]
                rw [ite_eq_right hC]
                rw [ite_eq_left hD]
                rw [hpm]
                try simp only []
                rw [hb2]
                rw [← hi, hlen']
          · simp at hd

  · simp at hd



/-- `decodeRex` consumes at least one byte. -/
theorem decodeRex_len_ge1 (r : Nat → BitVec 8) (rexW rexR rexB : Bool)
    (i : X64Insn) (len : Nat)
    (hd : decodeRex r rexW rexR rexB = some (i, len)) : 1 ≤ len := by
  unfold decodeRex at hd
  dsimp only at hd
  repeat' split at hd
  all_goals (try obtain ⟨-, hl⟩ := hd)
  all_goals (try (have hl2 := binopReg_len _ 2 _ _ _ _ _ _ hd; omega))
  all_goals (try (have hl3 := movImm_len _ _ _ _ _ _ hd; omega))
  all_goals omega

/-- `decodeSSE` consumes at least three bytes. -/
theorem decodeSSE_len_ge3 (r : Nat → BitVec 8) (off mandatory : Nat)
    (hasRex rexW rexR rexB : Bool) (i : X64Insn) (len : Nat)
    (hd : decodeSSE r off mandatory hasRex rexW rexR rexB = some (i, len)) : 3 ≤ len := by
  unfold decodeSSE at hd
  dsimp only at hd
  repeat' split at hd
  all_goals (try obtain ⟨-, hl⟩ := hd)
  all_goals omega

/-- `decodeNoRex` reads only the bytes below the length it reports. -/
theorem decodeNoRex_congr_upto (r r' : Nat → BitVec 8) (i : X64Insn) (len : Nat)
    (hd : decodeNoRex r = some (i, len))
    (h : ∀ j, j < len → r j = r' j) :
    decodeNoRex r' = some (i, len) := by
  unfold decodeNoRex at hd
  dsimp only at hd
  unfold decodeNoRex
  dsimp only
  split at hd
  · rename_i hb
    cases hp : parseRM r 1 false with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 1 false p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hi, hlen⟩ := hd
        have hlen' : len = 1 + p.len := hlen.symm
        have h1 : r 0 = r' 0 := h 0 (by omega)
        have hpm : parseRM r' 1 false = some p :=
          parseRM_congr_upto r r' 1 false p hp (fun j hj => h j (by omega))
        rw [show (r' 0).toNat = 0x88 from by rw [← h1]; exact hb]
        try simp only []
        rw [hpm]
        try simp only []
        rw [ite_eq_left hmod]
        rw [← hi, hlen']
      · rw [ite_eq_right hmod] at hd
        cases hb2 : baseOfRM p.rm with
        | none => simp [hb2] at hd
        | some bd =>
          obtain ⟨base, disp⟩ := bd
          simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 1 + p.len := hlen.symm
          have h1 : r 0 = r' 0 := h 0 (by omega)
          have hpm : parseRM r' 1 false = some p :=
            parseRM_congr_upto r r' 1 false p hp (fun j hj => h j (by omega))
          rw [show (r' 0).toNat = 0x88 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_right hmod]
          rw [hb2]
          rw [← hi, hlen']

  · rename_i hb
    cases hp : parseRM r 1 false with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 1 false p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hi, hlen⟩ := hd
        have hlen' : len = 1 + p.len := hlen.symm
        have h1 : r 0 = r' 0 := h 0 (by omega)
        have hpm : parseRM r' 1 false = some p :=
          parseRM_congr_upto r r' 1 false p hp (fun j hj => h j (by omega))
        rw [show (r' 0).toNat = 0x89 from by rw [← h1]; exact hb]
        try simp only []
        rw [hpm]
        try simp only []
        rw [ite_eq_left hmod]
        rw [← hi, hlen']
      · rw [ite_eq_right hmod] at hd
        cases hb2 : baseOfRM p.rm with
        | none => simp [hb2] at hd
        | some bd =>
          obtain ⟨base, disp⟩ := bd
          simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 1 + p.len := hlen.symm
          have h1 : r 0 = r' 0 := h 0 (by omega)
          have hpm : parseRM r' 1 false = some p :=
            parseRM_congr_upto r r' 1 false p hp (fun j hj => h j (by omega))
          rw [show (r' 0).toNat = 0x89 from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_right hmod]
          rw [hb2]
          rw [← hi, hlen']

  · rename_i hb
    cases hp : parseRM r 1 false with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 1 false p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        simp at hd
      · rw [ite_eq_right hmod] at hd
        cases hb2 : baseOfRM p.rm with
        | none => simp [hb2] at hd
        | some bd =>
          obtain ⟨base, disp⟩ := bd
          simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 1 + p.len := hlen.symm
          have h1 : r 0 = r' 0 := h 0 (by omega)
          have hpm : parseRM r' 1 false = some p :=
            parseRM_congr_upto r r' 1 false p hp (fun j hj => h j (by omega))
          rw [show (r' 0).toNat = 0x8B from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_right hmod]
          rw [hb2]
          rw [← hi, hlen']

  · rename_i hb
    have hl := binopReg_len 0x01 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x01 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x01 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x09 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x09 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x09 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x11 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x11 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x11 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x19 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x19 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x19 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x21 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x21 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x21 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x29 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x29 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x29 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x31 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x31 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x31 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x39 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x39 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x39 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    have hl := binopReg_len 0x85 1 r 0 false false i len hd
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have hreg := binopReg_congr_upto 0x85 1 r r' 0 false false i len hd h
    rw [show (r' 0).toNat = 0x85 from by rw [← h1]; exact hb]
    try simp only []
    exact hreg

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 1 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    rw [show (r' 0).toNat = 0x90 from by rw [← h1]; exact hb]
    try simp only []
    rw [← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 1 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    rw [show (r' 0).toNat = 0xF5 from by rw [← h1]; exact hb]
    try simp only []
    rw [← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xE9 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 2 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm8 r 1 = imm8 r' 1 :=
      imm8_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x7A from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x05 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x0D from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x15 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x1D from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x25 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x2D from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x35 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0x3D from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xA9 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xb8 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xb9 from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xba from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xbb from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xbc from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xbd from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xbe from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hi, hlen⟩ := hd
    have hlen' : len = 5 := hlen.symm
    have h1 : r 0 = r' 0 := h 0 (by omega)
    have himm : imm32 r 1 = imm32 r' 1 :=
      imm32_congr r r' 1 (fun j hj => h j (by omega))
    rw [show (r' 0).toNat = 0xbf from by rw [← h1]; exact hb]
    try simp only []
    rw [← himm, ← hi, hlen]

  · rename_i hb
    cases hp : parseRM r 1 false with
    | none => simp [hp] at hd
    | some p =>
      have hp1 := parseRM_len_pos r 1 false p hp
      rw [hp] at hd
      dsimp only at hd
      by_cases hmod : p.modBits = 3
      · rw [ite_eq_left hmod] at hd
        try simp only [] at hd
        cases hg : group5OfExt p.regBits p.rm.regOf with
        | none => simp [hg] at hd
        | some insn =>
          rw [hg] at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨hi, hlen⟩ := hd
          have hlen' : len = 1 + p.len := hlen.symm
          have h1 : r 0 = r' 0 := h 0 (by omega)
          have hpm : parseRM r' 1 false = some p :=
            parseRM_congr_upto r r' 1 false p hp (fun j hj => h j (by omega))
          rw [show (r' 0).toNat = 0xFF from by rw [← h1]; exact hb]
          try simp only []
          rw [hpm]
          try simp only []
          rw [ite_eq_left hmod]
          rw [hg]
          rw [← hi, hlen']
      · rw [ite_eq_right hmod] at hd
        simp at hd

  · rename_i hb
    try dsimp only at hd
    split at hd
    · rename_i hA
      split at hd
      · rename_i hC
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨hi, hlen⟩ := hd
        have hlen6 : len = 6 := hlen.symm
        have h0 : r 0 = r' 0 := h 0 (by omega)
        have h1 : r 1 = r' 1 := h 1 (by omega)
        have himm : imm32 r 2 = imm32 r' 2 :=
          imm32_congr r r' 2 (fun j hj => h j (by omega))
        rw [show (r' 0).toNat = 0x0F from by rw [← h0]; exact hb]
        try simp only []
        rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
        try simp only []
        rw [ite_eq_left hA]
        rw [hC]
        rw [← himm, ← hi, hlen]
      · simp at hd
    · rename_i hA
      split at hd
      · rename_i hB
        cases hp : parseRM r 2 false with
        | none => simp [hp] at hd
        | some p =>
          have hp1 := parseRM_len_pos r 2 false p hp
          rw [hp] at hd
          try simp only [] at hd
          split at hd
          · rename_i hC
            split at hd
            · rename_i hmod
              simp only [Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨hi, hlen⟩ := hd
              have hlen' : len = 2 + p.len := hlen.symm
              have h0 : r 0 = r' 0 := h 0 (by omega)
              have h1 : r 1 = r' 1 := h 1 (by omega)
              have hpm : parseRM r' 2 false = some p :=
                parseRM_congr_upto r r' 2 false p hp (fun j hj => h j (by omega))
              rw [show (r' 0).toNat = 0x0F from by rw [← h0]; exact hb]
              try simp only []
              rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
              try simp only []
              rw [ite_eq_right hA]
              rw [ite_eq_left hB]
              rw [hpm]
              try simp only []
              rw [hC]
              try simp only []
              rw [ite_eq_left hmod]
              rw [← hi, hlen']
            · simp at hd
          · simp at hd
      · rename_i hB
        split at hd
        · rename_i hC
          cases hp : parseRM r 2 false with
          | none => simp [hp] at hd
          | some p =>
            have hp1 := parseRM_len_pos r 2 false p hp
            rw [hp] at hd
            try simp only [] at hd
            cases hb2 : baseOfRM p.rm with
            | none => simp [hb2] at hd
            | some bd =>
              obtain ⟨base, disp⟩ := bd
              simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨hi, hlen⟩ := hd
              have hlen' : len = 2 + p.len := hlen.symm
              have h0 : r 0 = r' 0 := h 0 (by omega)
              have h1 : r 1 = r' 1 := h 1 (by omega)
              have hpm : parseRM r' 2 false = some p :=
                parseRM_congr_upto r r' 2 false p hp (fun j hj => h j (by omega))
              rw [show (r' 0).toNat = 0x0F from by rw [← h0]; exact hb]
              try simp only []
              rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
              try simp only []
              rw [ite_eq_right hA]
              rw [ite_eq_right hB]
              rw [ite_eq_left hC]
              rw [hpm]
              try simp only []
              rw [hb2]
              rw [← hi, hlen']
        · rename_i hC
          split at hd
          · rename_i hD
            cases hp : parseRM r 2 false with
            | none => simp [hp] at hd
            | some p =>
              have hp1 := parseRM_len_pos r 2 false p hp
              rw [hp] at hd
              try simp only [] at hd
              cases hb2 : baseOfRM p.rm with
              | none => simp [hb2] at hd
              | some bd =>
                obtain ⟨base, disp⟩ := bd
                simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = 2 + p.len := hlen.symm
                have h0 : r 0 = r' 0 := h 0 (by omega)
                have h1 : r 1 = r' 1 := h 1 (by omega)
                have hpm : parseRM r' 2 false = some p :=
                  parseRM_congr_upto r r' 2 false p hp (fun j hj => h j (by omega))
                rw [show (r' 0).toNat = 0x0F from by rw [← h0]; exact hb]
                try simp only []
                rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
                try simp only []
                rw [ite_eq_right hA]
                rw [ite_eq_right hB]
                rw [ite_eq_right hC]
                rw [ite_eq_left hD]
                rw [hpm]
                try simp only []
                rw [hb2]
                rw [← hi, hlen']
          · simp at hd

  · rename_i hb
    try dsimp only at hd
    split at hd
    · rename_i hrex
      split at hd
      · rename_i hop
        have hlen3 : 3 ≤ len := decodeSSE_len_ge3 r 3 0x66 true _ _ _ i len hd
        have h0 : r 0 = r' 0 := h 0 (by omega)
        have h1 : r 1 = r' 1 := h 1 (by omega)
        have h2 : r 2 = r' 2 := h 2 (by omega)
        rw [show (r' 0).toNat = 0x66 from by rw [← h0]; exact hb]
        try simp only []
        rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
        try simp only []
        rw [ite_eq_left hrex]
        rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
        rw [ite_eq_left hop]
        exact decodeSSE_congr_upto r r' 3 0x66 true _ _ _ i len (Or.inr ⟨rfl, rfl⟩) hd h
      · rename_i hop
        split at hd
        · rename_i hop89
          cases hp : parseRM r 3 (decide ((r 1).toNat % 2 = 1)) with
          | none => simp [hp] at hd
          | some p =>
            have hp1 := parseRM_len_pos r 3 (decide ((r 1).toNat % 2 = 1)) p hp
            rw [hp] at hd
            try simp only [] at hd
            by_cases hmod : p.modBits = 3
            · rw [ite_eq_left hmod] at hd
              simp only [Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨hi, hlen⟩ := hd
              have hlen' : len = 3 + p.len := hlen.symm
              have h0 : r 0 = r' 0 := h 0 (by omega)
              have h1 : r 1 = r' 1 := h 1 (by omega)
              have h2 : r 2 = r' 2 := h 2 (by omega)
              have hpm : parseRM r' 3 (decide ((r 1).toNat % 2 = 1)) = some p :=
                parseRM_congr_upto r r' 3 (decide ((r 1).toNat % 2 = 1)) p hp (fun j hj => h j (by omega))
              rw [show (r' 0).toNat = 0x66 from by rw [← h0]; exact hb]
              try simp only []
              rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
              try simp only []
              rw [ite_eq_left hrex]
              rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
              rw [ite_eq_right hop]
              rw [ite_eq_left hop89]
              rw [hpm]
              try simp only []
              rw [ite_eq_left hmod]
              rw [← hi, hlen']
            · rw [ite_eq_right hmod] at hd
              cases hb2 : baseOfRM p.rm with
              | none => simp [hb2] at hd
              | some bd =>
                obtain ⟨base, disp⟩ := bd
                simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = 3 + p.len := hlen.symm
                have h0 : r 0 = r' 0 := h 0 (by omega)
                have h1 : r 1 = r' 1 := h 1 (by omega)
                have h2 : r 2 = r' 2 := h 2 (by omega)
                have hpm : parseRM r' 3 (decide ((r 1).toNat % 2 = 1)) = some p :=
                  parseRM_congr_upto r r' 3 (decide ((r 1).toNat % 2 = 1)) p hp (fun j hj => h j (by omega))
                rw [show (r' 0).toNat = 0x66 from by rw [← h0]; exact hb]
                try simp only []
                rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
                try simp only []
                rw [ite_eq_left hrex]
                rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
                rw [ite_eq_right hop]
                rw [ite_eq_left hop89]
                rw [hpm]
                try simp only []
                rw [ite_eq_right hmod]
                rw [hb2]
                rw [← hi, hlen']
        · rename_i hop89
          split at hd
          · rename_i hop8b
            cases hp : parseRM r 3 (decide ((r 1).toNat % 2 = 1)) with
            | none => simp [hp] at hd
            | some p =>
              have hp1 := parseRM_len_pos r 3 (decide ((r 1).toNat % 2 = 1)) p hp
              rw [hp] at hd
              try simp only [] at hd
              by_cases hmod : p.modBits = 3
              · rw [ite_eq_left hmod] at hd
                simp at hd
              · rw [ite_eq_right hmod] at hd
                cases hb2 : baseOfRM p.rm with
                | none => simp [hb2] at hd
                | some bd =>
                  obtain ⟨base, disp⟩ := bd
                  simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
                  obtain ⟨hi, hlen⟩ := hd
                  have hlen' : len = 3 + p.len := hlen.symm
                  have h0 : r 0 = r' 0 := h 0 (by omega)
                  have h1 : r 1 = r' 1 := h 1 (by omega)
                  have h2 : r 2 = r' 2 := h 2 (by omega)
                  have hpm : parseRM r' 3 (decide ((r 1).toNat % 2 = 1)) = some p :=
                    parseRM_congr_upto r r' 3 (decide ((r 1).toNat % 2 = 1)) p hp (fun j hj => h j (by omega))
                  rw [show (r' 0).toNat = 0x66 from by rw [← h0]; exact hb]
                  try simp only []
                  rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
                  try simp only []
                  rw [ite_eq_left hrex]
                  rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
                  rw [ite_eq_right hop]
                  rw [ite_eq_right hop89]
                  rw [ite_eq_left hop8b]
                  rw [hpm]
                  try simp only []
                  rw [ite_eq_right hmod]
                  rw [hb2]
                  rw [← hi, hlen']
          · simp at hd
    · rename_i hrex
      split at hd
      · rename_i hb1
        have hlen3 : 3 ≤ len := decodeSSE_len_ge3 r 2 0x66 false false false false i len hd
        have h0 : r 0 = r' 0 := h 0 (by omega)
        have h1 : r 1 = r' 1 := h 1 (by omega)
        rw [show (r' 0).toNat = 0x66 from by rw [← h0]; exact hb]
        try simp only []
        rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
        try simp only []
        rw [ite_eq_right hrex]
        rw [ite_eq_left hb1]
        exact decodeSSE_congr_upto r r' 2 0x66 false false false false i len (Or.inl ⟨rfl, rfl⟩) hd h
      · rename_i hb1
        split at hd
        · rename_i hb89
          cases hp : parseRM r 2 false with
          | none => simp [hp] at hd
          | some p =>
            have hp1 := parseRM_len_pos r 2 false p hp
            rw [hp] at hd
            try simp only [] at hd
            by_cases hmod : p.modBits = 3
            · rw [ite_eq_left hmod] at hd
              simp only [Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨hi, hlen⟩ := hd
              have hlen' : len = 2 + p.len := hlen.symm
              have h0 : r 0 = r' 0 := h 0 (by omega)
              have h1 : r 1 = r' 1 := h 1 (by omega)
              have hpm : parseRM r' 2 false = some p :=
                parseRM_congr_upto r r' 2 false p hp (fun j hj => h j (by omega))
              rw [show (r' 0).toNat = 0x66 from by rw [← h0]; exact hb]
              try simp only []
              rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
              try simp only []
              rw [ite_eq_right hrex]
              rw [ite_eq_right hb1]
              rw [ite_eq_left hb89]
              rw [hpm]
              try simp only []
              rw [ite_eq_left hmod]
              rw [← hi, hlen']
            · rw [ite_eq_right hmod] at hd
              cases hb2 : baseOfRM p.rm with
              | none => simp [hb2] at hd
              | some bd =>
                obtain ⟨base, disp⟩ := bd
                simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨hi, hlen⟩ := hd
                have hlen' : len = 2 + p.len := hlen.symm
                have h0 : r 0 = r' 0 := h 0 (by omega)
                have h1 : r 1 = r' 1 := h 1 (by omega)
                have hpm : parseRM r' 2 false = some p :=
                  parseRM_congr_upto r r' 2 false p hp (fun j hj => h j (by omega))
                rw [show (r' 0).toNat = 0x66 from by rw [← h0]; exact hb]
                try simp only []
                rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
                try simp only []
                rw [ite_eq_right hrex]
                rw [ite_eq_right hb1]
                rw [ite_eq_left hb89]
                rw [hpm]
                try simp only []
                rw [ite_eq_right hmod]
                rw [hb2]
                rw [← hi, hlen']
        · rename_i hb89
          split at hd
          · rename_i hb8b
            cases hp : parseRM r 2 false with
            | none => simp [hp] at hd
            | some p =>
              have hp1 := parseRM_len_pos r 2 false p hp
              rw [hp] at hd
              try simp only [] at hd
              by_cases hmod : p.modBits = 3
              · rw [ite_eq_left hmod] at hd
                simp at hd
              · rw [ite_eq_right hmod] at hd
                cases hb2 : baseOfRM p.rm with
                | none => simp [hb2] at hd
                | some bd =>
                  obtain ⟨base, disp⟩ := bd
                  simp only [hb2, Option.some.injEq, Prod.mk.injEq] at hd
                  obtain ⟨hi, hlen⟩ := hd
                  have hlen' : len = 2 + p.len := hlen.symm
                  have h0 : r 0 = r' 0 := h 0 (by omega)
                  have h1 : r 1 = r' 1 := h 1 (by omega)
                  have hpm : parseRM r' 2 false = some p :=
                    parseRM_congr_upto r r' 2 false p hp (fun j hj => h j (by omega))
                  rw [show (r' 0).toNat = 0x66 from by rw [← h0]; exact hb]
                  try simp only []
                  rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
                  try simp only []
                  rw [ite_eq_right hrex]
                  rw [ite_eq_right hb1]
                  rw [ite_eq_right hb89]
                  rw [ite_eq_left hb8b]
                  rw [hpm]
                  try simp only []
                  rw [ite_eq_right hmod]
                  rw [hb2]
                  rw [← hi, hlen']
          · simp at hd

  · rename_i hb
    try dsimp only at hd
    split at hd
    · rename_i hrex
      split at hd
      · rename_i hop
        have hlen3 : 3 ≤ len := decodeSSE_len_ge3 r 3 0xF2 true _ _ _ i len hd
        have h0 : r 0 = r' 0 := h 0 (by omega)
        have h1 : r 1 = r' 1 := h 1 (by omega)
        have h2 : r 2 = r' 2 := h 2 (by omega)
        rw [show (r' 0).toNat = 0xF2 from by rw [← h0]; exact hb]
        try simp only []
        rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
        try simp only []
        rw [ite_eq_left hrex]
        rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
        rw [ite_eq_left hop]
        exact decodeSSE_congr_upto r r' 3 0xF2 true _ _ _ i len (Or.inr ⟨rfl, rfl⟩) hd h
      · simp at hd
    · rename_i hrex
      split at hd
      · rename_i hb1
        have hlen3 : 3 ≤ len := decodeSSE_len_ge3 r 2 0xF2 false false false false i len hd
        have h0 : r 0 = r' 0 := h 0 (by omega)
        have h1 : r 1 = r' 1 := h 1 (by omega)
        rw [show (r' 0).toNat = 0xF2 from by rw [← h0]; exact hb]
        try simp only []
        rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
        try simp only []
        rw [ite_eq_right hrex]
        rw [ite_eq_left hb1]
        exact decodeSSE_congr_upto r r' 2 0xF2 false false false false i len (Or.inl ⟨rfl, rfl⟩) hd h
      · simp at hd

  · rename_i hb
    try dsimp only at hd
    split at hd
    · rename_i hrex
      split at hd
      · rename_i hop
        have hlen3 : 3 ≤ len := decodeSSE_len_ge3 r 3 0xF3 true _ _ _ i len hd
        have h0 : r 0 = r' 0 := h 0 (by omega)
        have h1 : r 1 = r' 1 := h 1 (by omega)
        have h2 : r 2 = r' 2 := h 2 (by omega)
        rw [show (r' 0).toNat = 0xF3 from by rw [← h0]; exact hb]
        try simp only []
        rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
        try simp only []
        rw [ite_eq_left hrex]
        rw [show (r' 2).toNat = (r 2).toNat from by rw [← h2]]
        rw [ite_eq_left hop]
        exact decodeSSE_congr_upto r r' 3 0xF3 true _ _ _ i len (Or.inr ⟨rfl, rfl⟩) hd h
      · simp at hd
    · rename_i hrex
      split at hd
      · rename_i hb1
        have hlen3 : 3 ≤ len := decodeSSE_len_ge3 r 2 0xF3 false false false false i len hd
        have h0 : r 0 = r' 0 := h 0 (by omega)
        have h1 : r 1 = r' 1 := h 1 (by omega)
        rw [show (r' 0).toNat = 0xF3 from by rw [← h0]; exact hb]
        try simp only []
        rw [show (r' 1).toNat = (r 1).toNat from by rw [← h1]]
        try simp only []
        rw [ite_eq_right hrex]
        rw [ite_eq_left hb1]
        exact decodeSSE_congr_upto r r' 2 0xF3 false false false false i len (Or.inl ⟨rfl, rfl⟩) hd h
      · simp at hd

  · rename_i hb
    try dsimp only at hd
    split at hd
    · rename_i hrex
      have hl := decodeRex_len_ge1 r _ _ _ i len hd
      have h1 : r 0 = r' 0 := h 0 (by omega)
      rw [show (r' 0).toNat = (r 0).toNat from by rw [← h1]]
      try simp only []
      rw [ite_eq_left hrex]
      exact decodeRex_congr_upto r r' _ _ _ i len hd h
    · simp at hd

/-- Two readers agreeing on the bytes a decoded instruction consumes decode
the same instruction. -/
theorem decode_congr_upto (r r' : Nat → BitVec 8) (i : X64Insn) (len : Nat)
    (hd : decode r = some (i, len))
    (h : ∀ j, j < len → r j = r' j) :
    decode r' = some (i, len) := by
  unfold decode
  exact decodeNoRex_congr_upto r r' i len hd h

end Flapjack.Compiler.Encoders.X64
