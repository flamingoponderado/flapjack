import Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
import Flapjack.Compiler.Backend.StackToLab.Proofs.Prelude
import Flapjack.Compiler.Backend.Semantics.StackSem.Inst
import Flapjack.Compiler.Backend.LabSem.Inst

/-! Instruction simulation `inst_correct` of `stack_to_labProofScript.sml`
(lines 736-889): a successful StackSem primitive instruction is simulated by
the LabSem `asm_inst` transition under `state_rel`. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.InstCorrect
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open StackSemStateOps StackSemExpressions StackSemIntegerInstructions

theorem wordQuot_eq_sdiv {width : Nat} (a b : BitVec width) : wordQuot a b = a.sdiv b := by
  unfold wordQuot BitVec.sdiv
  cases a.msb <;> cases b.msb <;> simp [BitVec.udiv_eq]

section
variable {width : Nat} [NeZero width] {C F : Type}
  {s : StackSemStateFiniteExact width C F}
  {t : Flapjack.Compiler.Backend.LabSem.State width C F}

theorem regOfLookup (rel : stateRel s t) {r : Nat} {v : WordLocW width}
    (h : s.regs.lookup r = some v) : t.regs r = v := rel.1 r v h

theorem fpRegOfLookup (rel : stateRel s t) {r : Nat} {v : BitVec 64}
    (h : s.fpRegs.lookup r = some v) : t.fpRegs r = v := rel.2.1 r v h

theorem notFailed (rel : stateRel s t) : t.failed = false := by
  have := rel.2.2.2.2.2.2.2.2.2.2.2.1
  simpa using this

theorem stateRelAssertTrue (rel : stateRel s t) : stateRel s (assertState true t) := by
  simpa [Prelude.assertT] using rel

theorem wordOpBinop (bop : Flapjack.BinOp) (a b : BitVec width) :
    wordOpHOL bop [a, b] = some (match bop with
      | .add => a + b | .sub => a - b | .and => a &&& b
      | .or => a ||| b | .xor => a ^^^ b) := by
  cases bop <;> simp [wordOpHOL, wordOp]
  · change a &&& (b &&& BitVec.allOnes width) = a &&& b
    simp
  · change a ||| (b ||| 0#width) = a ||| b
    simp

theorem wordExpOp2 {bop : Flapjack.BinOp} {e1 e2 : WordLangExpHOL (BitVec width)}
    {w : BitVec width} (h : wordExp s (.op bop [e1, e2]) = some w) :
    ∃ a b, wordExp s e1 = some a ∧ wordExp s e2 = some b ∧ wordOpHOL bop [a, b] = some w := by
  rw [wordExp] at h
  cases h1 : wordExp s e1 <;> cases h2 : wordExp s e2 <;> simp_all

theorem wordExpVar {r : Nat} {w : BitVec width} (h : wordExp s (.var r) = some w) :
    s.regs.lookup r = some (.word w) := by
  rw [wordExp] at h
  split at h <;> simp_all

theorem regImmOfWordExp (rel : stateRel s t) {ri : HolRegImm width} {w : BitVec width}
    (h : wordExp s (match ri with | .reg r3 => .var r3 | .imm w => .const w) = some w) :
    regImm ri t = .word w := by
  cases ri with
  | reg r3 => simp [regImm, regOfLookup rel (wordExpVar h)]
  | imm v => simp [wordExp] at h; simp [regImm, h]

theorem instCorrectSkip {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    (h : StackSemInst.instHOL .skip s = some s2) : stateRel s2 (asmInst .skip t) := by
  simp [StackSemInst.instHOL, instInteger] at h
  subst h
  exact rel

theorem instCorrectConst {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {r : Nat} {w : BitVec width}
    (h : StackSemInst.instHOL (.const r w) s = some s2) :
    stateRel s2 (asmInst (.const r w) t) := by
  simp [StackSemInst.instHOL, instInteger, assign, wordExp] at h
  subst h
  exact setVarUpdReg rel

theorem instCorrectBinop {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {bop : Flapjack.BinOp} {r1 r2 : Nat} {ri : HolRegImm width}
    (h : StackSemInst.instHOL (.arith (.binop bop r1 r2 ri)) s = some s2) :
    stateRel s2 (asmInst (.arith (.binop bop r1 r2 ri)) t) := by
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  split_ifs at h with guard
  · rw [sameRegisterOr_iff] at guard
    obtain ⟨rfl, rfl⟩ := guard
    cases found : s.regs.lookup r2 with
    | none => simp [found] at h
    | some v =>
      simp only [found, Option.some.injEq] at h
      subst h
      have hv := regOfLookup rel found
      have step : asmInst (.arith (.binop .or r1 r2 (.reg r2))) t = updReg r1 v t := by
        cases v <;> simp [asmInst, arithUpd, regImm, hv, binopUpd]
      rw [step]
      exact setVarUpdReg rel
  · unfold assign at h
    split at h
    · simp at h
    · rename_i w hexp
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨a, b, ha, hb, hop⟩ := wordExpOp2 hexp
      have hr2 := regOfLookup rel (wordExpVar ha)
      have hri : regImm ri t = .word b := by
        split at hb
        · simp [regImm, regOfLookup rel (wordExpVar hb)]
        · simp [wordExp] at hb; simp [regImm, hb]
      rw [wordOpBinop] at hop
      cases hop
      have step : asmInst (.arith (.binop bop r1 r2 ri)) t = updReg r1 (.word (match bop with
          | .add => a + b | .sub => a - b | .and => a &&& b
          | .or => a ||| b | .xor => a ^^^ b)) t := by
        cases bop <;> simp [asmInst, arithUpd, hr2, hri, binopUpd]
      rw [step]
      exact setVarUpdReg rel

theorem instCorrectShift {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {sh : Flapjack.Shift} {r1 r2 : Nat} {ri : HolRegImm width}
    (h : StackSemInst.instHOL (.arith (.shift sh r1 r2 ri)) s = some s2) :
    stateRel s2 (asmInst (.arith (.shift sh r1 r2 ri)) t) := by
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  unfold assign at h
  split at h
  · simp at h
  · rename_i w hexp
    simp only [Option.some.injEq] at h
    subst h
    rw [wordExp] at hexp
    split at hexp
    · rename_i a b ha hb
      have hr2 := regOfLookup rel (wordExpVar ha)
      have hri : regImm ri t = .word b := by
        split at hb
        · simp [regImm, regOfLookup rel (wordExpVar hb)]
        · simp [wordExp] at hb; simp [regImm, hb]
      obtain ⟨range, value⟩ := Prelude.wordShWordShift hexp
      have step : asmInst (.arith (.shift sh r1 r2 ri)) t =
          assertState true (updReg r1 (.word w) t) := by
        simp [asmInst, arithUpd, hr2, hri, range, value]
      rw [step]
      exact stateRelAssertTrue (setVarUpdReg rel)
    · simp at hexp

theorem getVarsSome : ∀ (vs : List Nat) (xs : List (WordLocW width)),
    StackSemStateOps.getVars vs s = some xs → List.Forall₂ (fun v x => s.regs.lookup v = some x) vs xs := by
  intro vs
  induction vs with
  | nil => intro xs h; simp [StackSemStateOps.getVars] at h; subst h; exact .nil
  | cons v vs ih =>
    intro xs h
    simp only [StackSemStateOps.getVars, StackSemStateOps.getVar] at h
    split at h
    · simp at h
    · rename_i x hx
      split at h
      · simp at h
      · rename_i ys hys
        simp only [Option.some.injEq] at h
        subst h
        exact .cons hx (ih ys hys)

theorem instCorrectDiv {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {r1 r2 r3 : Nat} (h : StackSemInst.instHOL (.arith (.div r1 r2 r3)) s = some s2) :
    stateRel s2 (asmInst (.arith (.div r1 r2 r3)) t) := by
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  split at h
  · rename_i q w2 hv
    have regs := getVarsSome _ _ hv
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at regs
    split_ifs at h with nz
    simp only [Option.some.injEq] at h
    subst h
    have step : asmInst (.arith (.div r1 r2 r3)) t =
        assertState true (updReg r1 (.word (wordQuot w2 q)) t) := by
      have nz' : q ≠ 0#width := nz
      simp [asmInst, arithUpd, regOfLookup rel regs.1, regOfLookup rel regs.2, nz',
        wordQuot_eq_sdiv]
    rw [step]
    exact stateRelAssertTrue (setVarUpdReg rel)
  · simp at h

theorem instCorrectAddCarry {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {r1 r2 r3 r4 : Nat}
    (h : StackSemInst.instHOL (.arith (.addCarry r1 r2 r3 r4)) s = some s2) :
    stateRel s2 (asmInst (.arith (.addCarry r1 r2 r3 r4)) t) := by
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  split at h
  · rename_i l r c hv
    have regs := getVarsSome _ _ hv
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at regs
    simp only [Option.some.injEq] at h
    subst h
    have step : asmInst (.arith (.addCarry r1 r2 r3 r4)) t =
        updReg r4 (.word (if 2 ^ width ≤ l.toNat + r.toNat + (if c = 0 then 0 else 1)
            then 1 else 0))
          (updReg r1 (.word (BitVec.ofNat width
            (l.toNat + r.toNat + (if c = 0 then 0 else 1)))) t) := by
      simp [asmInst, arithUpd, regOfLookup rel regs.1, regOfLookup rel regs.2.1,
        regOfLookup rel regs.2.2]
    rw [step]
    exact setVarUpdReg (setVarUpdReg rel)
  · simp at h

theorem instCorrectAddOverflow {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {r1 r2 r3 r4 : Nat}
    (h : StackSemInst.instHOL (.arith (.addOverflow r1 r2 r3 r4)) s = some s2) :
    stateRel s2 (asmInst (.arith (.addOverflow r1 r2 r3 r4)) t) := by
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  split at h
  · rename_i a b hv
    have regs := getVarsSome _ _ hv
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at regs
    simp only [Option.some.injEq] at h
    subst h
    have step : asmInst (.arith (.addOverflow r1 r2 r3 r4)) t =
        updReg r4 (.word (if (a + b).toInt ≠ a.toInt + b.toInt then 1 else 0))
          (updReg r1 (.word (a + b)) t) := by
      simp [asmInst, arithUpd, regOfLookup rel regs.1, regOfLookup rel regs.2]
    rw [step]
    exact setVarUpdReg (setVarUpdReg rel)
  · simp at h

theorem instCorrectSubOverflow {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {r1 r2 r3 r4 : Nat}
    (h : StackSemInst.instHOL (.arith (.subOverflow r1 r2 r3 r4)) s = some s2) :
    stateRel s2 (asmInst (.arith (.subOverflow r1 r2 r3 r4)) t) := by
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  split at h
  · rename_i a b hv
    have regs := getVarsSome _ _ hv
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at regs
    simp only [Option.some.injEq] at h
    subst h
    have step : asmInst (.arith (.subOverflow r1 r2 r3 r4)) t =
        updReg r4 (.word (if (a - b).toInt ≠ a.toInt - b.toInt then 1 else 0))
          (updReg r1 (.word (a - b)) t) := by
      simp [asmInst, arithUpd, regOfLookup rel regs.1, regOfLookup rel regs.2]
    rw [step]
    exact setVarUpdReg (setVarUpdReg rel)
  · simp at h

theorem instCorrectLongMul {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {r1 r2 r3 r4 : Nat}
    (h : StackSemInst.instHOL (.arith (.longMul r1 r2 r3 r4)) s = some s2) :
    stateRel s2 (asmInst (.arith (.longMul r1 r2 r3 r4)) t) := by
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  split at h
  · rename_i a b hv
    have regs := getVarsSome _ _ hv
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at regs
    simp only [Option.some.injEq] at h
    subst h
    have step : asmInst (.arith (.longMul r1 r2 r3 r4)) t =
        updReg r2 (.word (BitVec.ofNat width (a.toNat * b.toNat)))
          (updReg r1 (.word (BitVec.ofNat width (a.toNat * b.toNat / 2 ^ width))) t) := by
      simp [asmInst, arithUpd, regOfLookup rel regs.1, regOfLookup rel regs.2]
    rw [step]
    exact setVarUpdReg (setVarUpdReg rel)
  · simp at h

theorem instCorrectLongDiv {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {r1 r2 r3 r4 r5 : Nat}
    (h : StackSemInst.instHOL (.arith (.longDiv r1 r2 r3 r4 r5)) s = some s2) :
    stateRel s2 (asmInst (.arith (.longDiv r1 r2 r3 r4 r5)) t) := by
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  split at h
  · rename_i a b c hv
    have regs := getVarsSome _ _ hv
    simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at regs
    split_ifs at h with bound
    simp only [Option.some.injEq] at h
    subst h
    have step : asmInst (.arith (.longDiv r1 r2 r3 r4 r5)) t =
        assertState true
          (updReg r1 (.word (BitVec.ofNat width ((a.toNat * 2 ^ width + b.toNat) / c.toNat)))
            (updReg r2 (.word (BitVec.ofNat width ((a.toNat * 2 ^ width + b.toNat) % c.toNat)))
              t)) := by
      simp [asmInst, arithUpd, regOfLookup rel regs.1, regOfLookup rel regs.2.1,
        regOfLookup rel regs.2.2, bound]
    rw [step]
    exact stateRelAssertTrue (setVarUpdReg (setVarUpdReg rel))
  · simp at h

theorem relMemory (rel : stateRel s t) : t.memory = s.memory := rel.2.2.1

theorem relMemDomain (rel : stateRel s t) : t.memDomain = s.mdomain := rel.2.2.2.1

theorem relBe (rel : stateRel s t) : t.be = s.be := rel.2.2.2.2.2.1

theorem relAligned (rel : stateRel s t) {x : BitVec width} (h : s.mdomain x = true) :
    x.toNat % (width / 8) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, align, _⟩ := rel
  exact align x h

theorem stateRelWithMemory (rel : stateRel s t) (m : BitVec width → WordLocW width) :
    stateRel { s with memory := m } { t with memory := m } := by
  obtain ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := rel
  exact ⟨h1, h2, rfl, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩

/-- The source address expression of a memory instruction is the LabSem
address of the same base register and offset. -/
theorem addrOfWordExp (rel : stateRel s t) {a : Nat} {w addr : BitVec width}
    (h : wordExp s (.op .add [.var a, .const w]) = some addr) :
    addrValue (.addr a w) t = some addr := by
  obtain ⟨x, y, hx, hy, hop⟩ := wordExpOp2 h
  simp [wordExp] at hy
  subst hy
  rw [wordOpBinop] at hop
  cases hop
  simp [addrValue, regOfLookup rel (wordExpVar hx)]

theorem instCorrectMem {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {op : HolMemop} {r : Nat} {address : HolAddr width}
    (h : StackSemInst.instHOL (.mem op r address) s = some s2) :
    stateRel s2 (asmInst (.mem op r address) t) := by
  obtain ⟨a, w⟩ := address
  simp only [StackSemInst.instHOL, instInteger, Option.join_some] at h
  cases op with
  | load =>
    simp only at h
    split at h
    · rename_i addr hexp
      split at h
      · simp at h
      · rename_i v hload
        simp only [Option.some.injEq] at h
        subst h
        unfold StackSemStateOps.memLoad at hload
        split_ifs at hload with dom
        cases hload
        have step : asmInst (.mem .load r (.addr a w)) t =
            assertState true (updReg r (s.memory addr) t) := by
          simp [asmInst, memOp, LabSem.memLoad, addrOfWordExp rel hexp, relMemory rel,
            relMemDomain rel, dom, relAligned rel dom]
        rw [step]
        exact stateRelAssertTrue (setVarUpdReg rel)
    · simp at h
  | store =>
    simp only at h
    split at h
    · rename_i addr v hexp hv
      split at h
      · rename_i s1 hstore
        simp only [Option.some.injEq] at h
        subst h
        have dom : s.mdomain addr = true := by
          unfold StackSemStateOps.memStore at hstore
          split_ifs at hstore with d
          exact d
        have hr : t.regs r = v := regOfLookup rel hv
        have step : asmInst (.mem .store r (.addr a w)) t =
            assertState true (updMem addr v t) := by
          simp [asmInst, memOp, LabSem.memStore, addrOfWordExp rel hexp, relMemDomain rel, dom,
            relAligned rel dom, hr]
        rw [step]
        exact stateRelAssertTrue (memStoreUpdMem ⟨rel, hstore⟩)
      · simp at h
    · simp at h
  | load8 =>
    simp only at h
    split at h
    · rename_i addr hexp
      split at h
      · simp at h
      · rename_i v hload
        simp only [Option.some.injEq] at h
        subst h
        have step : asmInst (.mem .load8 r (.addr a w)) t =
            updReg r (.word (v.setWidth width)) t := by
          simp [asmInst, memOp, LabSem.memLoadByte, addrOfWordExp rel hexp, relMemory rel,
            relMemDomain rel, relBe rel, hload]
        rw [step]
        exact setVarUpdReg rel
    · simp at h
  | load32 =>
    simp only at h
    split at h
    · rename_i addr hexp
      split at h
      · simp at h
      · rename_i v hload
        simp only [Option.some.injEq] at h
        subst h
        have step : asmInst (.mem .load32 r (.addr a w)) t =
            updReg r (.word (v.setWidth width)) t := by
          simp [asmInst, memOp, LabSem.memLoad32, addrOfWordExp rel hexp, relMemory rel,
            relMemDomain rel, relBe rel, hload]
        rw [step]
        exact setVarUpdReg rel
    · simp at h
  | store8 =>
    simp only at h
    split at h
    · rename_i addr v hexp hv
      split at h
      · rename_i m hstore
        simp only [Option.some.injEq] at h
        subst h
        have step : asmInst (.mem .store8 r (.addr a w)) t = { t with memory := m } := by
          simp [asmInst, memOp, LabSem.memStoreByte, addrOfWordExp rel hexp, relMemory rel,
            relMemDomain rel, relBe rel, regOfLookup rel hv, hstore]
        rw [step]
        exact stateRelWithMemory rel m
      · simp at h
    · simp at h
  | store32 =>
    simp only at h
    split at h
    · rename_i addr v hexp hv
      split at h
      · rename_i m hstore
        simp only [Option.some.injEq] at h
        subst h
        have step : asmInst (.mem .store32 r (.addr a w)) t = { t with memory := m } := by
          simp [asmInst, memOp, LabSem.memStore32, addrOfWordExp rel hexp, relMemory rel,
            relMemDomain rel, relBe rel, regOfLookup rel hv, hstore]
        rw [step]
        exact stateRelWithMemory rel m
      · simp at h
    · simp at h
  | load16 => simp at h
  | store16 => simp at h

omit [NeZero width] in
theorem extractHigh (v : BitVec 64) :
    (v.extractLsb' 32 32).setWidth width = holWordExtract 63 32 v width := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract, BitVec.extractLsb']

omit [NeZero width] in
theorem extractLow (v : BitVec 64) :
    (v.extractLsb' 0 32).setWidth width = holWordExtract 31 0 v width := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract, BitVec.extractLsb']

open StackSemFpRegisterInstructions in
theorem instCorrectFp {s2 : StackSemStateFiniteExact width C F} (rel : stateRel s t)
    {op : HolFp} (h : StackSemInst.instHOL (.fp op) s = some s2) :
    stateRel s2 (asmInst (.fp op) t) := by
  have rd : ∀ {d : Nat} {f : BitVec 64}, getFpVar d s = some f → readFpReg d t = f :=
    fun hf => fpRegOfLookup rel hf
  cases op
  all_goals simp only [StackSemInst.instHOL, StackSemFpInstructions.instFp, instFpRegister,
    Option.join_some] at h
  case fpMov d1 d2 =>
    split at h
    · rename_i f hf; cases h
      have step : asmInst (.fp (.fpMov d1 d2)) t = updFpReg d1 f t := by
        simp [asmInst, fpUpd, rd hf]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpAbs d1 d2 =>
    split at h
    · rename_i f hf; cases h
      have step : asmInst (.fp (.fpAbs d1 d2)) t = updFpReg d1 (holFp64Abs f) t := by
        simp [asmInst, fpUpd, rd hf]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpNeg d1 d2 =>
    split at h
    · rename_i f hf; cases h
      have step : asmInst (.fp (.fpNeg d1 d2)) t = updFpReg d1 (holFp64Negate f) t := by
        simp [asmInst, fpUpd, rd hf]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpSqrt d1 d2 =>
    unfold instFpSqrt at h
    split at h
    · rename_i f hf; cases h
      have step : asmInst (.fp (.fpSqrt d1 d2)) t =
          updFpReg d1 (holFp64SqrtReal .roundTiesToEven f) t := by
        simp [asmInst, fpUpd, rd hf, holFp64Sqrt_agreement]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpLess r d1 d2 =>
    split at h
    · rename_i f1 f2 h1 h2; cases h
      have step : asmInst (.fp (.fpLess r d1 d2)) t = updReg r (.word
          (if holFp64LessThan f1 f2 then BitVec.ofNat width 1 else BitVec.ofNat width 0)) t := by
        simp [asmInst, fpUpd, rd h1, rd h2]
      rw [step]; exact setVarUpdReg rel
    · simp at h
  case fpLessEqual r d1 d2 =>
    split at h
    · rename_i f1 f2 h1 h2; cases h
      have step : asmInst (.fp (.fpLessEqual r d1 d2)) t = updReg r (.word
          (if holFp64LessEqual f1 f2 then BitVec.ofNat width 1 else BitVec.ofNat width 0)) t := by
        simp [asmInst, fpUpd, rd h1, rd h2]
      rw [step]; exact setVarUpdReg rel
    · simp at h
  case fpEqual r d1 d2 =>
    split at h
    · rename_i f1 f2 h1 h2; cases h
      have step : asmInst (.fp (.fpEqual r d1 d2)) t = updReg r (.word
          (if holFp64Equal f1 f2 then BitVec.ofNat width 1 else BitVec.ofNat width 0)) t := by
        simp [asmInst, fpUpd, rd h1, rd h2]
      rw [step]; exact setVarUpdReg rel
    · simp at h
  case fpAdd d1 d2 d3 =>
    split at h
    · rename_i f1 f2 h1 h2; cases h
      have step : asmInst (.fp (.fpAdd d1 d2 d3)) t =
          updFpReg d1 (holFp64Add .roundTiesToEven f1 f2) t := by
        simp [asmInst, fpUpd, rd h1, rd h2]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpSub d1 d2 d3 =>
    split at h
    · rename_i f1 f2 h1 h2; cases h
      have step : asmInst (.fp (.fpSub d1 d2 d3)) t =
          updFpReg d1 (holFp64Sub .roundTiesToEven f1 f2) t := by
        simp [asmInst, fpUpd, rd h1, rd h2]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpMul d1 d2 d3 =>
    split at h
    · rename_i f1 f2 h1 h2; cases h
      have step : asmInst (.fp (.fpMul d1 d2 d3)) t =
          updFpReg d1 (holFp64Mul .roundTiesToEven f1 f2) t := by
        simp [asmInst, fpUpd, rd h1, rd h2]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpDiv d1 d2 d3 =>
    split at h
    · rename_i f1 f2 h1 h2; cases h
      have step : asmInst (.fp (.fpDiv d1 d2 d3)) t =
          updFpReg d1 (holFp64Div .roundTiesToEven f1 f2) t := by
        simp [asmInst, fpUpd, rd h1, rd h2]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpFma d1 d2 d3 =>
    split at h
    · rename_i f1 f2 f3 h1 h2 h3; cases h
      have step : asmInst (.fp (.fpFma d1 d2 d3)) t =
          updFpReg d1 (holFp64MulAdd .roundTiesToEven f2 f3 f1) t := by
        simp [asmInst, fpUpd, rd h1, rd h2, rd h3, fpSemFpfma]
      rw [step]; exact setFpVarUpdFpReg rel
    · simp at h
  case fpMovToReg r1 r2 d =>
    split at h
    · simp at h
    · rename_i f hf
      split_ifs at h with w64
      · cases h
        have step : asmInst (.fp (.fpMovToReg r1 r2 d)) t =
            updReg r1 (.word (f.setWidth width)) t := by
          simp [asmInst, fpUpd, rd hf, w64]
        rw [step]; exact setVarUpdReg rel
      · cases h
        have step : asmInst (.fp (.fpMovToReg r1 r2 d)) t =
            updReg r2 (.word ((f.extractLsb' 32 32).setWidth width))
              (updReg r1 (.word ((f.extractLsb' 0 32).setWidth width)) t) := by
          simp [asmInst, fpUpd, rd hf, w64, extractHigh, extractLow]
        rw [step]; exact setVarUpdReg (setVarUpdReg rel)
  case fpMovFromReg d r1 r2 =>
    split_ifs at h with w64
    · split at h
      · rename_i v hv; cases h
        have step : asmInst (.fp (.fpMovFromReg d r1 r2)) t =
            updFpReg d (v.setWidth 64) t := by
          simp [asmInst, fpUpd, w64, regOfLookup rel hv]
        rw [step]; exact setFpVarUpdFpReg rel
      · simp at h
    · split at h
      · rename_i lo hi hlo hhi; cases h
        have step : asmInst (.fp (.fpMovFromReg d r1 r2)) t =
            updFpReg d ((hi ++ lo).setWidth 64) t := by
          simp [asmInst, fpUpd, w64, regOfLookup rel hlo, regOfLookup rel hhi]
        rw [step]; exact setFpVarUpdFpReg rel
      · simp at h
  case fpToInt d1 d2 =>
    unfold instFpToInt at h
    split at h
    · simp at h
    · rename_i f hf
      split at h
      · simp at h
      · rename_i i hi
        by_cases fits : (BitVec.ofInt 32 i).toInt = i
        swap
        · rw [if_neg fits] at h; simp at h
        rw [if_pos fits] at h
        by_cases w64 : width = 64
        · rw [if_pos w64] at h
          cases h
          have step : asmInst (.fp (.fpToInt d1 d2)) t =
              updFpReg d1 ((BitVec.ofInt 32 i).setWidth 64) (assertState true t) := by
            simp [asmInst, fpUpd, rd hf, hi, fits, w64]
          rw [step, Prelude.assertT]; exact setFpVarUpdFpReg rel
        · rw [if_neg w64] at h
          split at h
          · simp at h
          · rename_i g hg
            by_cases odd : d1 % 2 = 1
            · simp only [odd, if_true, Option.some.injEq] at h
              subst h
              have step : asmInst (.fp (.fpToInt d1 d2)) t =
                  updFpReg (d1 / 2) (holBitFieldInsert 63 32 (BitVec.ofInt 32 i) g)
                    (assertState true t) := by
                simp [asmInst, fpUpd, rd hf, hi, fits, w64, rd hg, odd]
              rw [step, Prelude.assertT]; exact setFpVarUpdFpReg rel
            · simp only [odd, if_false, Option.some.injEq] at h
              subst h
              have step : asmInst (.fp (.fpToInt d1 d2)) t =
                  updFpReg (d1 / 2) (holBitFieldInsert 31 0 (BitVec.ofInt 32 i) g)
                    (assertState true t) := by
                simp [asmInst, fpUpd, rd hf, hi, fits, w64, rd hg, odd]
              rw [step, Prelude.assertT]; exact setFpVarUpdFpReg rel
  case fpFromInt d1 d2 =>
    unfold instFpFromInt at h
    by_cases w64 : width = 64
    · rw [if_pos w64] at h
      split at h
      · rename_i f hf; cases h
        have step : asmInst (.fp (.fpFromInt d1 d2)) t = updFpReg d1
            (holIntToFp64 .roundTiesToEven (holWordExtract 31 0 f 32).toInt) t := by
          simp [asmInst, fpUpd, rd hf, w64]
        rw [step]; exact setFpVarUpdFpReg rel
      · simp at h
    · rw [if_neg w64] at h
      split at h
      · rename_i f hf; cases h
        have step : asmInst (.fp (.fpFromInt d1 d2)) t = updFpReg d1
            (holIntToFp64 .roundTiesToEven (if d2 % 2 = 1 then holWordExtract 63 32 f width
              else holWordExtract 31 0 f width).toInt) t := by
          simp only [asmInst, fpUpd, if_neg w64]
          rw [rd hf]
        rw [step]; exact setFpVarUpdFpReg rel
      · simp at h

end

/-- Same-module re-export of the canonical StackSem state roundtrip;
infrastructure for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original instruction simulation: every successful StackSem
primitive instruction (all integer, memory and sixteen FP opcodes) is
simulated by LabSem `asm_inst` under `state_rel`. FP results inherit the
reviewed real-number renderings (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "inst_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem instCorrect {width : Nat} [NeZero width] {C F : Type}
    {i : HolInst width} {s1 s2 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} :
    StackSemInst.instHOL i s1 = some s2 ∧ stateRel s1 t1 → stateRel s2 (asmInst i t1) := by
  rintro ⟨h, rel⟩
  cases i with
  | skip => exact instCorrectSkip rel h
  | const r w => exact instCorrectConst rel h
  | arith op =>
    cases op with
    | binop => exact instCorrectBinop rel h
    | shift => exact instCorrectShift rel h
    | div => exact instCorrectDiv rel h
    | longMul => exact instCorrectLongMul rel h
    | longDiv => exact instCorrectLongDiv rel h
    | addCarry => exact instCorrectAddCarry rel h
    | addOverflow => exact instCorrectAddOverflow rel h
    | subOverflow => exact instCorrectSubOverflow rel h
  | mem op r a => exact instCorrectMem rel h
  | fp op => exact instCorrectFp rel h

end Flapjack.Compiler.Backend.StackToLab.Proofs.InstCorrect
