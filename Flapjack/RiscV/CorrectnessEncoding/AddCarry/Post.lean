import Flapjack.RiscV.CorrectnessEncoding.AddCarry.Native
import Flapjack.RiscV.CorrectnessEncoding.AddCarry.Arithmetic
import Flapjack.RiscV.CorrectnessEncoding.ConstRelation
namespace Flapjack.RiscV.TargetProof.AddCarry
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
  Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
def program (r1 r2 r3 r4 : BitVec 5) : List instruction :=
  [.ArithR (.SLTU (31,0,r4)), .ArithR (.ADD (r1,r2,r3)),
   .ArithR (.SLTU (r4,r1,r3)), .ArithR (.ADD (r1,r1,31)),
   .ArithR (.SLTU (31,r1,31)), .ArithR (.OR (r4,r4,31))]
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem step_eq (op : Op) (rd rs rt : BitVec 5) (ms : riscv_state)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true) :
    constStep (instructionOf op rd rs rt) ms =
      writePost ms rd (valueOf op (GPR rs ms) (GPR rt ms)) := by
  have run := run_eq op rd rs rt ms ok
  simp [constStep, run, writePost, «write'GPR», «write'gpr», rn]
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem singleton (c : Bool) : holV2w 64 [c] = (if c then 1 else 0) := by
  cases c <;> decide
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem carry_input (c : BitVec 64) :
    holV2w 64 [BitVec.ult 0#64 c] = (if c = 0#64 then 0#64 else 1#64) := by
  rw [singleton]
  have zero : (0#64).toNat = 0 := by decide
  have iff : (0#64).ult c = true ↔ c ≠ 0#64 := by
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq, zero]
    constructor
    · intro pos eq
      simp [eq] at pos
    · intro ne
      have cn : c.toNat ≠ 0 := by
        intro eq
        apply ne
        apply BitVec.eq_of_toNat_eq
        exact eq
      omega
  by_cases eq : c = 0#64
  · subst c
    simp [BitVec.ult_eq_decide]
  · rw [if_pos (iff.mpr eq), if_neg eq]
    rfl
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
def purePost (r1 r2 r3 r4 : BitVec 5) (ms : riscv_state) : riscv_state :=
  let a := GPR r2 ms
  let b := GPR r3 ms
  let cin := if GPR r4 ms = 0#64 then 0#64 else 1#64
  let low := a+b
  let flag0 := holV2w 64 [BitVec.ult low b]
  let sum := low+cin
  let flag1 := holV2w 64 [BitVec.ult sum cin]
  writePost (writePost (writePost (writePost (writePost (writePost ms 31 cin)
    r1 low) r4 flag0) r1 sum) 31 flag1) r4 (flag0 ||| flag1)
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem pure_post (r1 r2 r3 r4 : BitVec 5) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (nz1 : r1 ≠ 0#5) (nz4 : r4 ≠ 0#5)
    (scratch1 : r1 ≠ 31#5) (scratch2 : r2 ≠ 31#5)
    (scratch3 : r3 ≠ 31#5) (scratch4 : r4 ≠ 31#5)
    (right : r1 ≠ r3) (carry : r1 ≠ r4) :
    (program r1 r2 r3 r4).foldl (fun s i => constStep i s) ms =
      purePost r1 r2 r3 r4 ms := by
  have nz31 : (31#5) ≠ 0#5 := by decide
  have add (rd rs rt : BitVec 5) (s : riscv_state)
      (nz : rd ≠ 0#5) (valid : riscvOk s = true) :
      constStep (.ArithR (.ADD (rd,rs,rt))) s =
        writePost s rd (GPR rs s + GPR rt s) := step_eq .add rd rs rt s nz valid
  have sltu (rd rs rt : BitVec 5) (s : riscv_state)
      (nz : rd ≠ 0#5) (valid : riscvOk s = true) :
      constStep (.ArithR (.SLTU (rd,rs,rt))) s =
        writePost s rd (holV2w 64 [BitVec.ult (GPR rs s) (GPR rt s)]) :=
      step_eq .sltu rd rs rt s nz valid
  have bitOr (rd rs rt : BitVec 5) (s : riscv_state)
      (nz : rd ≠ 0#5) (valid : riscvOk s = true) :
      constStep (.ArithR (.OR (rd,rs,rt))) s =
        writePost s rd (GPR rs s ||| GPR rt s) := step_eq .or rd rs rt s nz valid
  simp only [program, List.foldl_cons, List.foldl_nil]
  rw [sltu 31 0 r4 ms nz31 ok]
  rw [add r1 r2 r3 _ nz1 (writePost_ok _ _ _ ok)]
  rw [sltu r4 r1 r3 _ nz4 (writePost_ok _ _ _ (writePost_ok _ _ _ ok))]
  rw [add r1 r1 31 _ nz1
    (writePost_ok _ _ _ (writePost_ok _ _ _ (writePost_ok _ _ _ ok)))]
  rw [sltu 31 r1 31 _ nz31
    (writePost_ok _ _ _ (writePost_ok _ _ _ (writePost_ok _ _ _ (writePost_ok _ _ _ ok))))]
  rw [bitOr r4 r4 31 _ nz4
    (writePost_ok _ _ _ (writePost_ok _ _ _ (writePost_ok _ _ _
      (writePost_ok _ _ _ (writePost_ok _ _ _ ok)))))]
  simp [purePost, writePost, GPR, gpr, holUpdate, carry_input,
    nz1, nz4, scratch1, scratch4,
    Ne.symm scratch2, Ne.symm scratch3, Ne.symm scratch4, right,
    carry, Ne.symm carry]
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem post_read (r1 r2 r3 r4 i : BitVec 5) (ms : riscv_state)
    (scratch : i ≠ 31#5) (_carry : r1 ≠ r4) :
    (purePost r1 r2 r3 r4 ms).c_gpr (purePost r1 r2 r3 r4 ms).procID i =
      if i = r4 then
        holV2w 64 [BitVec.ult (GPR r2 ms + GPR r3 ms) (GPR r3 ms)] |||
          holV2w 64 [BitVec.ult
            ((GPR r2 ms + GPR r3 ms)+(if GPR r4 ms = 0#64 then 0#64 else 1#64))
            (if GPR r4 ms = 0#64 then 0#64 else 1#64)]
      else if i = r1 then
        (GPR r2 ms + GPR r3 ms)+(if GPR r4 ms = 0#64 then 0#64 else 1#64)
      else ms.c_gpr ms.procID i := by
  by_cases eq4 : i = r4
  · subst i
    simp [purePost,writePost,holUpdate]
  · by_cases eq1 : i = r1
    · subst i
      simp [purePost,writePost,holUpdate,eq4,Ne.symm eq4,Ne.symm scratch]
    · simp [purePost,writePost,holUpdate,eq4,eq1,Ne.symm eq4,
        Ne.symm eq1,Ne.symm scratch]
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem guard (r : Nat) (g : asmRegOkExact r riscvConfig = true) :
    r < 32 ∧ BitVec.ofNat 5 r ≠ 0#5 ∧ BitVec.ofNat 5 r ≠ 31#5 := by
  have facts : r < 32 ∧ r ≠ 0 ∧ r ≠ 31 := by
    simp [asmRegOkExact,riscvConfig] at g
    exact ⟨of_decide_eq_true g.1,g.2.1,g.2.2.2.2.2⟩
  refine ⟨facts.1,?_,?_⟩
  all_goals
    intro eq
    have n := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat] at n
    norm_num at n
    rw [Nat.mod_eq_of_lt facts.1] at n
  · exact facts.2.1 n
  · exact facts.2.2 n
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem reg_ne (a b : Nat) (ha : a < 32) (hb : b < 32) (h : a ≠ b) :
    BitVec.ofNat 5 a ≠ BitVec.ofNat 5 b := by
  intro eq
  have n := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at n
  norm_num at n
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at n
  exact h n
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem reg_read (r : Nat) (s : AsmState 64) (ms : riscv_state)
    (g : asmRegOkExact r riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms) :
    GPR (BitVec.ofNat 5 r) ms = readReg r s := by
  have valid : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using g
  have before := rel.2.2.2.1 r valid
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at before
  simpa [GPR,gpr,(guard r g).2.1,readReg] using before
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem program_family (r1 r2 r3 r4 : BitVec 5) :
    ∀ i ∈ program r1 r2 r3 r4, Family i := by
  intro i member
  simp only [program,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> constructor
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem source_post (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 64)
    (hs : asmStep riscvConfig s1 (.inst (.arith (.addCarry r1 r2 r3 r4))) s2) :
    s2 = updPc (s1.pc+24) (updReg r4
      (if 2^64 ≤ (readReg r2 s1).toNat+(readReg r3 s1).toNat+
        (if readReg r4 s1 = 0 then 0 else 1) then 1 else 0)
      (updReg r1 (BitVec.ofNat 64
        ((readReg r2 s1).toNat+(readReg r3 s1).toNat+
          (if readReg r4 s1 = 0 then 0 else 1))) s1)) := by
  simpa [asmUpd,instUpd,arithUpd,riscvConfig,riscvEnc_length_eq,riscvAst] using
    hs.2.2.2.2.1.symm
/-- AddCarry-local execution/source composition; no separately named HOL declaration. -/
theorem post_relation (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 64) (ms : riscv_state)
    (hs : asmStep riscvConfig s1 (.inst (.arith (.addCarry r1 r2 r3 r4))) s2)
    (rel : targetStateRel riscvTarget s1 ms) :
    targetStateRel riscvTarget s2
      ((program (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2)
        (BitVec.ofNat 5 r3) (BitVec.ofNat 5 r4)).foldl (fun s i => constStep i s) ms) := by
  have guards : asmRegOkExact r1 riscvConfig = true ∧ asmRegOkExact r2 riscvConfig = true ∧
      asmRegOkExact r3 riscvConfig = true ∧ asmRegOkExact r4 riscvConfig = true ∧
      r1 ≠ r3 ∧ r1 ≠ r4 := by
    simpa [asmOkExact,asmInstOkExact,asmArithOkExact,riscvConfig,Bool.and_eq_true,and_assoc]
      using hs.2.2.2.2.2.2
  have g1 := guard r1 guards.1
  have g2 := guard r2 guards.2.1
  have g3 := guard r3 guards.2.2.1
  have g4 := guard r4 guards.2.2.2.1
  have right := reg_ne r1 r3 g1.1 g3.1 guards.2.2.2.2.1
  have carry := reg_ne r1 r4 g1.1 g4.1 guards.2.2.2.2.2
  have post := pure_post _ _ _ _ ms rel.1 g1.2.1 g4.2.1
    g1.2.2 g2.2.2 g3.2.2 g4.2.2 right carry
  have frame := step_list_frame _ (program_family (BitVec.ofNat 5 r1)
    (BitVec.ofNat 5 r2) (BitVec.ofNat 5 r3) (BitVec.ofNat 5 r4)) ms rel.1
  let final := (program (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2)
    (BitVec.ofNat 5 r3) (BitVec.ofNat 5 r4)).foldl (fun s i => constStep i s) ms
  have leftRead := reg_read r2 s1 ms guards.2.1 rel
  have rightRead := reg_read r3 s1 ms guards.2.2.1 rel
  have carryRead := reg_read r4 s1 ms guards.2.2.2.1 rel
  rw [source_post r1 r2 r3 r4 s1 s2 hs]
  refine ⟨frame.1,?_,?_,?_,?_⟩
  · change final.c_PC final.procID = s1.pc+24
    have pc : ms.c_PC ms.procID = s1.pc := rel.2.1
    rw [frame.2.2.2,pc]
    rfl
  · intro a domain
    change final.MEM8 a = s1.mem a
    rw [frame.2.2.1]
    exact rel.2.2.1 a domain
  · intro i hi
    have ibound : i < 32 := hi.1
    have avoid := hi.2
    change [0,2,3,4,31].contains i = false at avoid
    simp at avoid
    have scratch : BitVec.ofNat 5 i ≠ 31#5 :=
      reg_ne i 31 ibound (by decide) avoid.2.2.2.2
    have before := rel.2.2.2.1 i hi
    change ms.c_gpr ms.procID (BitVec.ofNat 5 i) = s1.regs i at before
    change final.c_gpr final.procID (BitVec.ofNat 5 i) = _
    dsimp only [final]
    rw [post,post_read _ _ _ _ _ ms scratch carry,leftRead,rightRead,carryRead]
    have sumEq : (readReg r2 s1+readReg r3 s1)+
        (if readReg r4 s1 = 0#64 then 0#64 else 1#64) =
        BitVec.ofNat 64 ((readReg r2 s1).toNat+(readReg r3 s1).toNat+
          (if readReg r4 s1 = 0 then 0 else 1)) := by
      by_cases zero : readReg r4 s1 = 0#64
      · simpa [BitVec.ofNat_eq_ofNat,zero] using
          sum_value (readReg r2 s1) (readReg r3 s1) false
      · simpa [BitVec.ofNat_eq_ofNat,zero] using
          sum_value (readReg r2 s1) (readReg r3 s1) true
    have flagEq : holV2w 64 [BitVec.ult (readReg r2 s1+readReg r3 s1) (readReg r3 s1)] |||
        holV2w 64 [BitVec.ult ((readReg r2 s1+readReg r3 s1)+
          (if readReg r4 s1 = 0#64 then 0#64 else 1#64))
          (if readReg r4 s1 = 0#64 then 0#64 else 1#64)] =
        (if 2^64 ≤ (readReg r2 s1).toNat+(readReg r3 s1).toNat+
          (if readReg r4 s1 = 0 then 0 else 1) then (1 : BitVec 64) else 0) := by
      by_cases zero : readReg r4 s1 = 0#64
      · simpa [BitVec.ofNat_eq_ofNat,zero] using
          carry_value (readReg r2 s1) (readReg r3 s1) false
      · simpa [BitVec.ofNat_eq_ofNat,zero] using
          carry_value (readReg r2 s1) (readReg r3 s1) true
    rw [flagEq,sumEq,before]
    by_cases eq4 : i = r4
    · subst i
      simp [updPc,updReg]
    · by_cases eq1 : i = r1
      · subst i
        simp [updPc,updReg,eq4,reg_ne r1 r4 g1.1 g4.1 eq4]
      · simp [updPc,updReg,eq1,eq4,reg_ne i r1 ibound g1.1 eq1,
          reg_ne i r4 ibound g4.1 eq4]
  · intro i hi
    change i < 0 at hi
    omega
end Flapjack.RiscV.TargetProof.AddCarry
