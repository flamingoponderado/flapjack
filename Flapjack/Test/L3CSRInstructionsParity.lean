import Flapjack.RiscV.L3.Defs.CSRInstructions
set_option maxRecDepth 20000
namespace Flapjack.Test.L3CSRInstructionsParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) : riscv_state :=
 {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mcpuid := {(s.c_MCSR id).mcpuid with ArchBase := 2}, mstatus := {(s.c_MCSR id).mstatus with MPRV := 3}, mscratch := 4386}, c_gpr := fun id r => if r = 1 then 17 else s.c_gpr id r}

example (s : riscv_state) : «dfn'CSRRW» (0,0,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 0} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 0} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (1,0,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 0} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 0} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (7,0,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 0} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 0} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (0,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 17} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 17} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (1,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 17} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 17} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (7,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 17} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 17} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (0,0,832) (fixture s) =
 (let t := fixture s; let u := t; u) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (1,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (7,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (0,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4403} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4403} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) := by
  have numeric : ((4386 : BitVec 64) ||| 17) = 4403 := by decide
  have symbolic := (show «dfn'CSRRS» (0,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 17)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 17)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRS» (1,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4403} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4403} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 17) = 4403 := by decide
  have symbolic := (show «dfn'CSRRS» (1,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 17)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 17)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRS» (7,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4403} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4403} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 17) = 4403 := by decide
  have symbolic := (show «dfn'CSRRS» (7,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 17)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 17)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRC» (0,0,832) (fixture s) =
 (let t := fixture s; let u := t; u) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (1,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (7,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (0,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRC» (0,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRC» (1,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRC» (1,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRC» (7,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRC» (7,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRWI» (0,0,832) (fixture s) =
 (let t := fixture s; let u := t; u) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (1,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (7,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (0,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 1} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 1} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (1,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 1} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 1} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (7,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 1} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 1} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (0,0,832) (fixture s) =
 (let t := fixture s; let u := t; u) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (1,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (7,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (0,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4387} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4387} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) := by
  have numeric : ((4386 : BitVec 64) ||| 1) = 4387 := by decide
  have symbolic := (show «dfn'CSRRSI» (0,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 1)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 1)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRSI» (1,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4387} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4387} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 1) = 4387 := by decide
  have symbolic := (show «dfn'CSRRSI» (1,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 1)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 1)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRSI» (7,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4387} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4387} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 1) = 4387 := by decide
  have symbolic := (show «dfn'CSRRSI» (7,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 1)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 1)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRCI» (0,0,832) (fixture s) =
 (let t := fixture s; let u := t; u) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (1,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (7,0,832) (fixture s) =
 (let t := fixture s; let u := t; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (0,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRCI» (0,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; u) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRCI» (1,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRCI» (1,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 1 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRCI» (7,1,832) (fixture s) =
 (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRCI» (7,1,832) (fixture s) = (let t := fixture s; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

/- Whole-state permission guards preserve arbitrary prior exceptions and all other fields. -/
example (s : riscv_state) : «dfn'CSRRW» (0,0,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (0,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (7,0,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (7,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (0,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (0,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (7,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (7,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (0,0,3072) (fixture s) =
 fixture s := by rfl
example (s : riscv_state) : «dfn'CSRRS» (0,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (7,0,3072) (fixture s) =
 {fixture s with c_gpr := holUpdate 7 (holUpdate 7 ((fixture s).c_cycles 7 + ((fixture s).c_UCSR 7).cycle_delta) ((fixture s).c_gpr 7)) (fixture s).c_gpr} := by rfl
example (s : riscv_state) : «dfn'CSRRS» (7,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (0,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (0,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (7,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (7,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (0,0,3072) (fixture s) =
 fixture s := by rfl
example (s : riscv_state) : «dfn'CSRRC» (0,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (7,0,3072) (fixture s) =
 {fixture s with c_gpr := holUpdate 7 (holUpdate 7 ((fixture s).c_cycles 7 + ((fixture s).c_UCSR 7).cycle_delta) ((fixture s).c_gpr 7)) (fixture s).c_gpr} := by rfl
example (s : riscv_state) : «dfn'CSRRC» (7,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (0,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (0,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (7,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRC» (7,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (0,0,3072) (fixture s) =
 fixture s := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (0,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (7,0,3072) (fixture s) =
 {fixture s with c_gpr := holUpdate 7 (holUpdate 7 ((fixture s).c_cycles 7 + ((fixture s).c_UCSR 7).cycle_delta) ((fixture s).c_gpr 7)) (fixture s).c_gpr} := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (7,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (0,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (0,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (7,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (7,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (0,0,3072) (fixture s) =
 fixture s := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (0,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (7,0,3072) (fixture s) =
 {fixture s with c_gpr := holUpdate 7 (holUpdate 7 ((fixture s).c_cycles 7 + ((fixture s).c_UCSR 7).cycle_delta) ((fixture s).c_gpr 7)) (fixture s).c_gpr} := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (7,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (0,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (0,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (7,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (7,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (0,0,3072) (fixture s) =
 fixture s := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (0,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (7,0,3072) (fixture s) =
 {fixture s with c_gpr := holUpdate 7 (holUpdate 7 ((fixture s).c_cycles 7 + ((fixture s).c_UCSR 7).cycle_delta) ((fixture s).c_gpr 7)) (fixture s).c_gpr} := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (7,0,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (0,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (0,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (7,1,3072) (fixture s) =
 setTrap (ExceptionType.Illegal_Instr, none) (fixture s) := by rfl
example (s : riscv_state) : «dfn'CSRRCI» (7,1,832) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) =
 setTrap (ExceptionType.Illegal_Instr, none) ({fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mstatus := {((fixture s).c_MCSR id).mstatus with MPRV := 0}}}) := by rfl

private def modeFixture (s : riscv_state) (mode : BitVec 2) : riscv_state :=
 {fixture s with c_MCSR := fun id => {(fixture s).c_MCSR id with mcpuid := {((fixture s).c_MCSR id).mcpuid with ArchBase := mode}}}

example (s : riscv_state) : «dfn'CSRRW» (7,1,832) (modeFixture s 1) =
 (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 17} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 17} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRW» (7,1,832) (modeFixture s 3) =
 (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 17} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 17} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (7,1,832) (modeFixture s 1) =
 (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4403} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4403} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 17) = 4403 := by decide
  have symbolic := (show «dfn'CSRRS» (7,1,832) (modeFixture s 1) = (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 17)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 17)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRS» (7,1,832) (modeFixture s 3) =
 (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4403} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4403} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 17) = 4403 := by decide
  have symbolic := (show «dfn'CSRRS» (7,1,832) (modeFixture s 3) = (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 17)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 17)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRC» (7,1,832) (modeFixture s 1) =
 (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRC» (7,1,832) (modeFixture s 1) = (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRC» (7,1,832) (modeFixture s 3) =
 (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRC» (7,1,832) (modeFixture s 3) = (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRWI» (7,1,832) (modeFixture s 1) =
 (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 1} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 1} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRWI» (7,1,832) (modeFixture s 3) =
 (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 1} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 1} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (7,1,832) (modeFixture s 1) =
 (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4387} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4387} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 1) = 4387 := by decide
  have symbolic := (show «dfn'CSRRSI» (7,1,832) (modeFixture s 1) = (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 1)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 1)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRSI» (7,1,832) (modeFixture s 3) =
 (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4387} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4387} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 1) = 4387 := by decide
  have symbolic := (show «dfn'CSRRSI» (7,1,832) (modeFixture s 3) = (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 1)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 1)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRCI» (7,1,832) (modeFixture s 1) =
 (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRCI» (7,1,832) (modeFixture s 1) = (let t := modeFixture s 1; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'CSRRCI» (7,1,832) (modeFixture s 3) =
 (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRCI» (7,1,832) (modeFixture s 3) = (let t := modeFixture s 3; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic

example (s : riscv_state) : «dfn'CSRRW» (7,1,832) (modeFixture s 0) =
 (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 17} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 17} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRS» (7,1,832) (modeFixture s 0) =
 (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4403} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4403} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 17) = 4403 := by decide
  have symbolic := (show «dfn'CSRRS» (7,1,832) (modeFixture s 0) = (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 17)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 17)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRC» (7,1,832) (modeFixture s 0) =
 (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRC» (7,1,832) (modeFixture s 0) = (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(17 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRWI» (7,1,832) (modeFixture s 0) =
 (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 1} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 1} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by rfl
example (s : riscv_state) : «dfn'CSRRSI» (7,1,832) (modeFixture s 0) =
 (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4387} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4387} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) ||| 1) = 4387 := by decide
  have symbolic := (show «dfn'CSRRSI» (7,1,832) (modeFixture s 0) = (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) ||| 1)} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) ||| 1)} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic
example (s : riscv_state) : «dfn'CSRRCI» (7,1,832) (modeFixture s 0) =
 (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := 4386} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some 4386} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) := by
  have numeric : ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64)) = 4386 := by decide
  have symbolic := (show «dfn'CSRRCI» (7,1,832) (modeFixture s 0) = (let t := modeFixture s 0; let u := {t with c_MCSR := holUpdate 7 {t.c_MCSR 7 with mscratch := ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} t.c_MCSR, c_update := holUpdate 7 {t.c_update 7 with addr := some 832, data2 := some ((4386 : BitVec 64) &&& ~~~(1 : BitVec 64))} (holUpdate 7 {t.c_update 7 with addr := some 832} t.c_update)}; {u with c_gpr := holUpdate 7 (holUpdate 7 4386 (u.c_gpr 7)) u.c_gpr}) from by rfl)
  dsimp only at symbolic
  simpa only [numeric] using symbolic


end Flapjack.Test.L3CSRInstructionsParity
