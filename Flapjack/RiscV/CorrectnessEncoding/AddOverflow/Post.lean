import Flapjack.RiscV.CorrectnessEncoding.AddOverflow.Native
import Flapjack.RiscV.CorrectnessEncoding.AddOverflow.Arithmetic
import Flapjack.RiscV.CorrectnessEncoding.ConstRelation
namespace Flapjack.RiscV.TargetProof.AddOverflow
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
  Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-- Literal original six-instruction AddOverflow expansion. Untagged composition. -/
def program (r1 r2 r3 r4 : BitVec 5) : List instruction :=
  [.ArithR (.XOR (31,r2,r3)), .ArithI (.XORI (31,31,-1)),
   .ArithR (.ADD (r1,r2,r3)), .ArithR (.XOR (r4,r3,r1)),
   .ArithR (.AND (r4,31,r4)), .Shift (.SRLI (r4,r4,63))]
/-- Complete native pure step; no separately named HOL original. -/
theorem step_eq (i : instruction) (kind : Family i) (ms : riscv_state)
    (rn : destination i ≠ 0#5) (ok : riscvOk ms = true) :
    constStep i ms = writePost ms (destination i) (value i ms) := by
  have run := run_eq i kind ms ok
  simp [constStep,run,writePost,«write'GPR»,«write'gpr»,rn]
/-- The actual six successive writes, including both scratch31 writes and PC24.
This local composition is not a separately named HOL declaration. -/
def purePost (r1 r2 r3 r4 : BitVec 5) (ms : riscv_state) : riscv_state :=
  let a := GPR r2 ms
  let b := GPR r3 ms
  let bits := a ^^^ b
  let same := ~~~bits
  let sum := a+b
  let changed := b ^^^ sum
  let over := same &&& changed
  writePost (writePost (writePost (writePost (writePost (writePost ms 31 bits)
    31 same) r1 sum) r4 changed) r4 over) r4 (over >>> (63 : Nat))
/-- Pure execution with precisely the source alias exclusions. The output and
flag registers may coincide. Untagged local composition infrastructure. -/
theorem pure_post (r1 r2 r3 r4 : BitVec 5) (ms : riscv_state)
    (ok : riscvOk ms = true)
    (nz1 : r1 ≠ 0#5) (nz4 : r4 ≠ 0#5)
    (scratch1 : r1 ≠ 31#5) (scratch2 : r2 ≠ 31#5)
    (scratch3 : r3 ≠ 31#5) (scratch4 : r4 ≠ 31#5)
    (right : r1 ≠ r3) :
    (program r1 r2 r3 r4).foldl (fun s i => constStep i s) ms =
      purePost r1 r2 r3 r4 ms := by
  have nz31 : (31#5) ≠ 0#5 := by decide
  have complement (w : BitVec 64) : w ^^^ 18446744073709551615#64 = ~~~w := by
    exact BitVec.xor_allOnes
  have xor (rd rs rt : BitVec 5) (s : riscv_state)
      (nz : rd ≠ 0#5) (valid : riscvOk s = true) :
      constStep (.ArithR (.XOR (rd,rs,rt))) s =
        writePost s rd (GPR rs s ^^^ GPR rt s) :=
    step_eq _ (.xor rd rs rt) s nz valid
  have xori (rd rs : BitVec 5) (imm : BitVec 12) (s : riscv_state)
      (nz : rd ≠ 0#5) (valid : riscvOk s = true) :
      constStep (.ArithI (.XORI (rd,rs,imm))) s =
        writePost s rd (GPR rs s ^^^ imm.signExtend 64) :=
    step_eq _ (.xori rd rs imm) s nz valid
  have add (rd rs rt : BitVec 5) (s : riscv_state)
      (nz : rd ≠ 0#5) (valid : riscvOk s = true) :
      constStep (.ArithR (.ADD (rd,rs,rt))) s =
        writePost s rd (GPR rs s + GPR rt s) :=
    step_eq _ (.add rd rs rt) s nz valid
  have bitAnd (rd rs rt : BitVec 5) (s : riscv_state)
      (nz : rd ≠ 0#5) (valid : riscvOk s = true) :
      constStep (.ArithR (.AND (rd,rs,rt))) s =
        writePost s rd (GPR rs s &&& GPR rt s) :=
    step_eq _ (.and rd rs rt) s nz valid
  have srli (rd rs : BitVec 5) (imm : BitVec 6) (s : riscv_state)
      (nz : rd ≠ 0#5) (valid : riscvOk s = true) :
      constStep (.Shift (.SRLI (rd,rs,imm))) s =
        writePost s rd (GPR rs s >>> imm.toNat) :=
    step_eq _ (.srli rd rs imm) s nz valid
  simp only [program,List.foldl_cons,List.foldl_nil]
  rw [xor 31 r2 r3 ms nz31 ok]
  rw [xori 31 31 (-1) _ nz31 (writePost_ok _ _ _ ok)]
  rw [add r1 r2 r3 _ nz1 (writePost_ok _ _ _ (writePost_ok _ _ _ ok))]
  rw [xor r4 r3 r1 _ nz4
    (writePost_ok _ _ _ (writePost_ok _ _ _ (writePost_ok _ _ _ ok)))]
  rw [bitAnd r4 31 r4 _ nz4
    (writePost_ok _ _ _ (writePost_ok _ _ _ (writePost_ok _ _ _ (writePost_ok _ _ _ ok))))]
  rw [srli r4 r4 63 _ nz4
    (writePost_ok _ _ _ (writePost_ok _ _ _ (writePost_ok _ _ _
      (writePost_ok _ _ _ (writePost_ok _ _ _ ok)))))]
  simp [purePost,writePost,GPR,gpr,holUpdate,nz1,nz4,scratch1,scratch4,
    Ne.symm scratch2,Ne.symm scratch3,right,complement]
/-- Final original register observations; flag write wins when r1=r4, exactly
as in AsmSem. No separately named HOL declaration is claimed. -/
theorem post_read (r1 r2 r3 r4 i : BitVec 5) (ms : riscv_state)
    (scratch : i ≠ 31#5) :
    (purePost r1 r2 r3 r4 ms).c_gpr (purePost r1 r2 r3 r4 ms).procID i =
      if i = r4 then ((~~~(GPR r2 ms ^^^ GPR r3 ms)) &&&
        (GPR r3 ms ^^^ (GPR r2 ms+GPR r3 ms))) >>> (63 : Nat)
      else if i = r1 then GPR r2 ms+GPR r3 ms
      else ms.c_gpr ms.procID i := by
  by_cases eq4 : i = r4
  · subst i
    simp [purePost,writePost,holUpdate]
  · by_cases eq1 : i = r1
    · subst i
      simp [purePost,writePost,holUpdate,eq4,Ne.symm eq4]
    · simp [purePost,writePost,holUpdate,eq4,eq1,Ne.symm eq4,
        Ne.symm eq1,Ne.symm scratch]
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
/-- AddOverflow-local execution/source composition; no separately named HOL declaration. -/
theorem reg_ne (a b : Nat) (ha : a < 32) (hb : b < 32) (h : a ≠ b) :
    BitVec.ofNat 5 a ≠ BitVec.ofNat 5 b := by
  intro eq
  have n := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at n
  norm_num at n
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at n
  exact h n
/-- AddOverflow-local execution/source composition; no separately named HOL declaration. -/
theorem reg_read (r : Nat) (s : AsmState 64) (ms : riscv_state)
    (g : asmRegOkExact r riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms) :
    GPR (BitVec.ofNat 5 r) ms = readReg r s := by
  have valid : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using g
  have before := rel.2.2.2.1 r valid
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at before
  simpa [GPR,gpr,(guard r g).2.1,readReg] using before
/-- AddOverflow-local execution/source composition; no separately named HOL declaration. -/
theorem program_family (r1 r2 r3 r4 : BitVec 5) :
    ∀ i ∈ program r1 r2 r3 r4, Family i := by
  intro i member
  simp only [program,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> constructor
/-- Actual original AsmSem post-state, including flag-write order and PC24.
No separately named HOL declaration is claimed for this composition. -/
theorem source_post (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 64)
    (hs : asmStep riscvConfig s1 (.inst (.arith (.addOverflow r1 r2 r3 r4))) s2) :
    s2 = updPc (s1.pc+24) (updReg r4
      (if (readReg r2 s1+readReg r3 s1).toInt ≠
        (readReg r2 s1).toInt+(readReg r3 s1).toInt then 1 else 0)
      (updReg r1 (readReg r2 s1+readReg r3 s1) s1)) := by
  simpa [asmUpd,instUpd,arithUpd,riscvConfig,riscvEnc_length_eq,riscvAst] using
    hs.2.2.2.2.1.symm
/-- The pure native six-instruction list establishes the original full source
post relation, permitting destination/flag aliases. Untagged composition. -/
theorem post_relation (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 64) (ms : riscv_state)
    (hs : asmStep riscvConfig s1 (.inst (.arith (.addOverflow r1 r2 r3 r4))) s2)
    (rel : targetStateRel riscvTarget s1 ms) :
    targetStateRel riscvTarget s2
      ((program (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2)
        (BitVec.ofNat 5 r3) (BitVec.ofNat 5 r4)).foldl (fun s i => constStep i s) ms) := by
  have guards : asmRegOkExact r1 riscvConfig = true ∧ asmRegOkExact r2 riscvConfig = true ∧
      asmRegOkExact r3 riscvConfig = true ∧ asmRegOkExact r4 riscvConfig = true ∧
      r1 ≠ r3 := by
    simpa [asmOkExact,asmInstOkExact,asmArithOkExact,riscvConfig,Bool.and_eq_true,and_assoc]
      using hs.2.2.2.2.2.2
  have g1 := guard r1 guards.1
  have g2 := guard r2 guards.2.1
  have g3 := guard r3 guards.2.2.1
  have g4 := guard r4 guards.2.2.2.1
  have right := reg_ne r1 r3 g1.1 g3.1 guards.2.2.2.2
  have post := pure_post _ _ _ _ ms rel.1 g1.2.1 g4.2.1
    g1.2.2 g2.2.2 g3.2.2 g4.2.2 right
  have frame := step_list_frame _ (program_family (BitVec.ofNat 5 r1)
    (BitVec.ofNat 5 r2) (BitVec.ofNat 5 r3) (BitVec.ofNat 5 r4)) ms rel.1
  let final := (program (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2)
    (BitVec.ofNat 5 r3) (BitVec.ofNat 5 r4)).foldl (fun s i => constStep i s) ms
  have leftRead := reg_read r2 s1 ms guards.2.1 rel
  have rightRead := reg_read r3 s1 ms guards.2.2.1 rel
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
    rw [post,post_read _ _ _ _ _ ms scratch,leftRead,rightRead]
    have flag := flag_value (readReg r2 s1) (readReg r3 s1)
    simp only [BitVec.ofNat_eq_ofNat] at flag
    rw [flag,before]
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
end Flapjack.RiscV.TargetProof.AddOverflow
