import Flapjack.RiscV.L3.Step.Fetch
import Flapjack.RiscV.L3.Defs.ReadInst
namespace Flapjack.Test
open Flapjack.RiscV.L3
-- Original pc_generic_equation, for every complete native state.
example (s : riscv_state) : PC s = s.c_PC s.procID := rfl
-- Original skip_generic_equation, for every word and complete native state.
example (v : BitVec 64) (s : riscv_state) :
    «write'Skip» v s = { s with c_Skip := holUpdate s.procID v s.c_Skip } := rfl

-- Full HOL rawReadInst equation over an arbitrary complete state.
example (a : BitVec 64) (s : riscv_state) :
    rawReadInst a s =
      if (s.MEM8 a).getLsbD 1 && (s.MEM8 a).getLsbD 0 then
        (rawInstType.Word ((s.MEM8 (a + 3)) ++ ((s.MEM8 (a + 2)) ++
          ((s.MEM8 (a + 1)) ++ s.MEM8 a))),
          { s with c_Skip := holUpdate s.procID 4 s.c_Skip })
      else
        (rawInstType.Half ((s.MEM8 (a + 1)) ++ s.MEM8 a),
          { s with c_Skip := holUpdate s.procID 2 s.c_Skip }) := by
  rfl

-- Original raw_17_0; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 0 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4608), 2, 99, 0) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_1; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 1 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4609), 2, 99, 1) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_2; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 2 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4610), 2, 99, 2) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_3; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 3 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253059), 4, 99, 3) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_4; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 4 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4612), 2, 99, 4) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_5; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 5 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4613), 2, 99, 5) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_6; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 6 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4614), 2, 99, 6) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_7; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 7 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253063), 4, 99, 7) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_8; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 8 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4616), 2, 99, 8) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_9; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 9 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4617), 2, 99, 9) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_10; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 10 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4618), 2, 99, 10) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_11; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 11 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253067), 4, 99, 11) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_12; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 12 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4620), 2, 99, 12) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_13; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 13 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4621), 2, 99, 13) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_14; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 14 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4622), 2, 99, 14) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_15; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 15 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253071), 4, 99, 15) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_16; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 16 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4624), 2, 99, 16) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_17; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 17 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4625), 2, 99, 17) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_18; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 18 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4626), 2, 99, 18) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_19; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 19 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253075), 4, 99, 19) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_20; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 20 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4628), 2, 99, 20) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_21; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 21 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4629), 2, 99, 21) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_22; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 22 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4630), 2, 99, 22) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_23; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 23 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253079), 4, 99, 23) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_24; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 24 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4632), 2, 99, 24) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_25; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 25 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4633), 2, 99, 25) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_26; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 26 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4634), 2, 99, 26) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_27; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 27 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253083), 4, 99, 27) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_28; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 28 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4636), 2, 99, 28) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_29; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 29 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4637), 2, 99, 29) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_30; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 30 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4638), 2, 99, 30) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_31; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 31 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253087), 4, 99, 31) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_32; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 32 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4640), 2, 99, 32) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_33; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 33 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4641), 2, 99, 33) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_34; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 34 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4642), 2, 99, 34) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_35; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 35 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253091), 4, 99, 35) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_36; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 36 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4644), 2, 99, 36) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_37; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 37 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4645), 2, 99, 37) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_38; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 38 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4646), 2, 99, 38) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_39; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 39 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253095), 4, 99, 39) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_40; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 40 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4648), 2, 99, 40) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_41; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 41 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4649), 2, 99, 41) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_42; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 42 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4650), 2, 99, 42) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_43; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 43 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253099), 4, 99, 43) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_44; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 44 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4652), 2, 99, 44) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_45; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 45 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4653), 2, 99, 45) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_46; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 46 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4654), 2, 99, 46) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_47; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 47 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253103), 4, 99, 47) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_48; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 48 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4656), 2, 99, 48) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_49; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 49 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4657), 2, 99, 49) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_50; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 50 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4658), 2, 99, 50) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_51; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 51 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253107), 4, 99, 51) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_52; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 52 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4660), 2, 99, 52) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_53; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 53 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4661), 2, 99, 53) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_54; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 54 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4662), 2, 99, 54) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_55; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 55 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253111), 4, 99, 55) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_56; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 56 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4664), 2, 99, 56) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_57; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 57 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4665), 2, 99, 57) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_58; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 58 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4666), 2, 99, 58) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_59; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 59 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253115), 4, 99, 59) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_60; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 60 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4668), 2, 99, 60) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_61; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 61 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4669), 2, 99, 61) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_62; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 62 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4670), 2, 99, 62) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_63; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 63 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253119), 4, 99, 63) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_64; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 64 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4672), 2, 99, 64) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_65; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 65 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4673), 2, 99, 65) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_66; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 66 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4674), 2, 99, 66) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_67; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 67 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253123), 4, 99, 67) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_68; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 68 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4676), 2, 99, 68) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_69; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 69 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4677), 2, 99, 69) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_70; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 70 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4678), 2, 99, 70) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_71; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 71 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253127), 4, 99, 71) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_72; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 72 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4680), 2, 99, 72) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_73; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 73 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4681), 2, 99, 73) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_74; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 74 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4682), 2, 99, 74) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_75; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 75 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253131), 4, 99, 75) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_76; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 76 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4684), 2, 99, 76) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_77; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 77 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4685), 2, 99, 77) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_78; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 78 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4686), 2, 99, 78) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_79; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 79 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253135), 4, 99, 79) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_80; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 80 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4688), 2, 99, 80) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_81; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 81 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4689), 2, 99, 81) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_82; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 82 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4690), 2, 99, 82) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_83; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 83 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253139), 4, 99, 83) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_84; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 84 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4692), 2, 99, 84) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_85; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 85 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4693), 2, 99, 85) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_86; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 86 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4694), 2, 99, 86) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_87; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 87 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253143), 4, 99, 87) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_88; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 88 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4696), 2, 99, 88) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_89; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 89 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4697), 2, 99, 89) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_90; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 90 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4698), 2, 99, 90) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_91; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 91 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253147), 4, 99, 91) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_92; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 92 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4700), 2, 99, 92) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_93; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 93 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4701), 2, 99, 93) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_94; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 94 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4702), 2, 99, 94) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_95; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 95 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253151), 4, 99, 95) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_96; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 96 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4704), 2, 99, 96) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_97; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 97 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4705), 2, 99, 97) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_98; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 98 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4706), 2, 99, 98) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_99; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 99 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253155), 4, 99, 99) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_100; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 100 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4708), 2, 99, 100) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_101; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 101 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4709), 2, 99, 101) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_102; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 102 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4710), 2, 99, 102) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_103; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 103 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253159), 4, 99, 103) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_104; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 104 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4712), 2, 99, 104) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_105; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 105 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4713), 2, 99, 105) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_106; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 106 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4714), 2, 99, 106) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_107; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 107 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253163), 4, 99, 107) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_108; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 108 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4716), 2, 99, 108) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_109; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 109 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4717), 2, 99, 109) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_110; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 110 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4718), 2, 99, 110) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_111; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 111 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253167), 4, 99, 111) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_112; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 112 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4720), 2, 99, 112) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_113; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 113 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4721), 2, 99, 113) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_114; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 114 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4722), 2, 99, 114) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_115; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 115 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253171), 4, 99, 115) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_116; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 116 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4724), 2, 99, 116) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_117; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 117 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4725), 2, 99, 117) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_118; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 118 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4726), 2, 99, 118) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_119; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 119 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253175), 4, 99, 119) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_120; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 120 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4728), 2, 99, 120) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_121; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 121 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4729), 2, 99, 121) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_122; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 122 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4730), 2, 99, 122) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_123; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 123 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253179), 4, 99, 123) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_124; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 124 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4732), 2, 99, 124) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_125; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 125 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4733), 2, 99, 125) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_126; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 126 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4734), 2, 99, 126) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_127; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 127 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253183), 4, 99, 127) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_128; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 128 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4736), 2, 99, 128) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_129; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 129 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4737), 2, 99, 129) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_130; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 130 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4738), 2, 99, 130) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_131; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 131 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253187), 4, 99, 131) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_132; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 132 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4740), 2, 99, 132) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_133; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 133 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4741), 2, 99, 133) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_134; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 134 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4742), 2, 99, 134) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_135; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 135 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253191), 4, 99, 135) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_136; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 136 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4744), 2, 99, 136) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_137; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 137 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4745), 2, 99, 137) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_138; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 138 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4746), 2, 99, 138) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_139; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 139 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253195), 4, 99, 139) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_140; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 140 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4748), 2, 99, 140) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_141; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 141 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4749), 2, 99, 141) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_142; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 142 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4750), 2, 99, 142) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_143; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 143 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253199), 4, 99, 143) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_144; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 144 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4752), 2, 99, 144) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_145; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 145 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4753), 2, 99, 145) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_146; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 146 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4754), 2, 99, 146) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_147; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 147 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253203), 4, 99, 147) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_148; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 148 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4756), 2, 99, 148) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_149; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 149 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4757), 2, 99, 149) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_150; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 150 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4758), 2, 99, 150) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_151; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 151 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253207), 4, 99, 151) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_152; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 152 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4760), 2, 99, 152) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_153; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 153 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4761), 2, 99, 153) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_154; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 154 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4762), 2, 99, 154) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_155; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 155 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253211), 4, 99, 155) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_156; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 156 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4764), 2, 99, 156) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_157; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 157 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4765), 2, 99, 157) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_158; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 158 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4766), 2, 99, 158) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_159; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 159 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253215), 4, 99, 159) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_160; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 160 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4768), 2, 99, 160) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_161; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 161 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4769), 2, 99, 161) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_162; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 162 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4770), 2, 99, 162) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_163; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 163 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253219), 4, 99, 163) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_164; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 164 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4772), 2, 99, 164) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_165; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 165 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4773), 2, 99, 165) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_166; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 166 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4774), 2, 99, 166) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_167; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 167 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253223), 4, 99, 167) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_168; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 168 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4776), 2, 99, 168) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_169; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 169 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4777), 2, 99, 169) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_170; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 170 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4778), 2, 99, 170) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_171; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 171 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253227), 4, 99, 171) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_172; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 172 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4780), 2, 99, 172) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_173; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 173 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4781), 2, 99, 173) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_174; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 174 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4782), 2, 99, 174) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_175; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 175 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253231), 4, 99, 175) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_176; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 176 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4784), 2, 99, 176) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_177; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 177 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4785), 2, 99, 177) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_178; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 178 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4786), 2, 99, 178) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_179; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 179 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253235), 4, 99, 179) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_180; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 180 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4788), 2, 99, 180) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_181; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 181 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4789), 2, 99, 181) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_182; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 182 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4790), 2, 99, 182) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_183; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 183 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253239), 4, 99, 183) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_184; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 184 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4792), 2, 99, 184) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_185; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 185 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4793), 2, 99, 185) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_186; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 186 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4794), 2, 99, 186) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_187; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 187 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253243), 4, 99, 187) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_188; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 188 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4796), 2, 99, 188) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_189; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 189 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4797), 2, 99, 189) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_190; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 190 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4798), 2, 99, 190) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_191; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 191 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253247), 4, 99, 191) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_192; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 192 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4800), 2, 99, 192) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_193; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 193 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4801), 2, 99, 193) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_194; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 194 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4802), 2, 99, 194) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_195; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 195 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253251), 4, 99, 195) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_196; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 196 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4804), 2, 99, 196) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_197; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 197 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4805), 2, 99, 197) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_198; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 198 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4806), 2, 99, 198) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_199; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 199 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253255), 4, 99, 199) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_200; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 200 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4808), 2, 99, 200) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_201; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 201 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4809), 2, 99, 201) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_202; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 202 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4810), 2, 99, 202) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_203; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 203 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253259), 4, 99, 203) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_204; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 204 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4812), 2, 99, 204) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_205; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 205 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4813), 2, 99, 205) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_206; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 206 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4814), 2, 99, 206) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_207; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 207 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253263), 4, 99, 207) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_208; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 208 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4816), 2, 99, 208) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_209; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 209 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4817), 2, 99, 209) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_210; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 210 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4818), 2, 99, 210) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_211; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 211 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253267), 4, 99, 211) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_212; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 212 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4820), 2, 99, 212) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_213; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 213 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4821), 2, 99, 213) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_214; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 214 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4822), 2, 99, 214) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_215; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 215 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253271), 4, 99, 215) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_216; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 216 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4824), 2, 99, 216) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_217; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 217 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4825), 2, 99, 217) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_218; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 218 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4826), 2, 99, 218) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_219; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 219 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253275), 4, 99, 219) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_220; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 220 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4828), 2, 99, 220) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_221; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 221 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4829), 2, 99, 221) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_222; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 222 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4830), 2, 99, 222) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_223; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 223 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253279), 4, 99, 223) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_224; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 224 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4832), 2, 99, 224) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_225; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 225 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4833), 2, 99, 225) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_226; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 226 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4834), 2, 99, 226) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_227; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 227 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253283), 4, 99, 227) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_228; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 228 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4836), 2, 99, 228) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_229; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 229 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4837), 2, 99, 229) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_230; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 230 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4838), 2, 99, 230) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_231; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 231 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253287), 4, 99, 231) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_232; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 232 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4840), 2, 99, 232) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_233; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 233 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4841), 2, 99, 233) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_234; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 234 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4842), 2, 99, 234) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_235; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 235 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253291), 4, 99, 235) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_236; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 236 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4844), 2, 99, 236) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_237; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 237 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4845), 2, 99, 237) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_238; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 238 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4846), 2, 99, 238) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_239; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 239 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253295), 4, 99, 239) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_240; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 240 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4848), 2, 99, 240) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_241; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 241 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4849), 2, 99, 241) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_242; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 242 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4850), 2, 99, 242) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_243; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 243 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253299), 4, 99, 243) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_244; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 244 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4852), 2, 99, 244) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_245; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 245 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4853), 2, 99, 245) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_246; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 246 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4854), 2, 99, 246) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_247; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 247 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253303), 4, 99, 247) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_248; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 248 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4856), 2, 99, 248) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_249; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 249 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4857), 2, 99, 249) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_250; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 250 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4858), 2, 99, 250) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_251; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 251 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253307), 4, 99, 251) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_252; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 252 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4860), 2, 99, 252) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_253; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 253 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4861), 2, 99, 253) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_254; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 254 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4862), 2, 99, 254) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_17_255; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 17
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 255 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253311), 4, 99, 255) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551615_0; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551615
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 0 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4608), 2, 99, 0) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551615_1; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551615
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 1 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4609), 2, 99, 1) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551615_2; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551615
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 2 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4610), 2, 99, 2) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551615_3; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551615
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 3 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253059), 4, 99, 3) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551615_127; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551615
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 127 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253183), 4, 99, 127) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551615_255; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551615
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 255 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253311), 4, 99, 255) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551614_0; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551614
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 0 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4608), 2, 99, 0) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551614_1; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551614
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 1 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4609), 2, 99, 1) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551614_2; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551614
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 2 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4610), 2, 99, 2) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551614_3; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551614
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 3 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253059), 4, 99, 3) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551614_127; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551614
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 127 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253183), 4, 99, 127) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551614_255; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551614
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 255 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253311), 4, 99, 255) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551613_0; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551613
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 0 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4608), 2, 99, 0) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551613_1; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551613
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 1 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4609), 2, 99, 1) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551613_2; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551613
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 2 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((16, 4610), 2, 99, 2) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551613_3; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551613
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 3 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253059), 4, 99, 3) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551613_127; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551613
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 127 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253183), 4, 99, 127) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Original raw_18446744073709551613_255; arbitrary surrounding native state.
example (base : riscv_state) :
    let a : BitVec 64 := 18446744073709551613
    let s := { base with
      procID := 7, totalCore := 1, c_Skip := (fun _ => 99),
      MEM8 := (fun x => if x = a then 255 else if x = a + 1 then 18
        else if x = a + 2 then 52 else if x = a + 3 then 86 else 0) }
    let r := rawReadInst a s
    ((match r.1 with | .Half w => (16, w.toNat) | .Word w => (32, w.toNat)),
      (r.2.c_Skip 7).toNat, (r.2.c_Skip 8).toNat, (r.2.MEM8 a).toNat) =
        ((32, 1446253311), 4, 99, 255) := by
  simp [rawReadInst, boolify8, «write'Skip», holUpdate] <;> decide

-- Complete original step Fetch equation, including the NONE route.
example (s : riscv_state) : Step.Fetch s =
    let (w, s₁) := translateAddr (PC s, fetchType.Instruction, accessType.Read) s
    rawReadInst (holThe w) s₁ := rfl

end Flapjack.Test
