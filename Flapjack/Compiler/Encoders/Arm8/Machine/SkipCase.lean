import Flapjack.Compiler.Encoders.Arm8.Machine.Simulate
import Flapjack.Compiler.Encoders.Arm8.Machine.DecodeProof

/-!
# The closed ARMv8 `skip` case of `encoder_correct`

This is the ARM8 analogue of the `start`/`straightCase'` machinery in
`Flapjack/Mips32/TargetProof/Step.lean` and of `case_skip` in
`Flapjack/Mips32/TargetProof/Arith.lean`, reduced to what the `skip` case
needs.  A `skip` lowers to the single instruction `[.noOp]`
(`arm8Ast_skip`) and therefore encodes to `encodeBytes .noOp`, four bytes
(`arm8Enc_skip`, `arm8Enc_skip_length`).  `arm8Next_noOp` then shows that one
`arm8Next` step from a state holding those bytes only advances the PC, so the
`skip` case is a one-step `encoderCase` run with `n = 0`.

`Arm8Start` collects the facts every ARM8 case reads off `asmStep` and the
initial `targetStateRel`, and `arm8Start` extracts them.  Unlike the MIPS
`Start`, the encoded-byte fact is stated over the target memory `ms.mem`
(mirroring MIPS's `CodeIn ms.mem ...`): the source bytes are moved across
with `bytesInMemory_changeMem`, using the domain membership
`bytesInMemoryHOL_domain` and the initial memory relation.  The closed ARM8
machine has no `nextPc`/`trapped` fields, so `NextSafe` is stated without the
MIPS stop condition (see `Machine/Simulate.lean`).
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Byte facts -/

/-- Adding one to the base before adding the `j`-th byte offset is the same as
adding the `(j + 1)`-th byte offset. -/
theorem arm8AddOneOffset (a : BitVec 64) (j : Nat) :
    (a + 1) + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (j + 1) := by
  bv_omega

/-- The `j`-th byte of a byte list in memory lies in the domain, for every
`j` below the length (recursive form, all arguments explicit). -/
theorem bytesInMemoryHOL_domainAux :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64) (m : BitVec 64 → BitVec 8)
      (d : BitVec 64 → Prop), bytesInMemoryHOL a bs m d →
      ∀ j, j < bs.length → d (a + BitVec.ofNat 64 j)
  | [], _, _, _, _, j, hj => by simp at hj
  | _ :: rest, a, m, d, h, j, hj => by
      obtain ⟨-, hd, ht⟩ := h
      cases j with
      | zero => simpa using hd
      | succ j =>
          have hj' : j < rest.length := by simpa using hj
          have hrec := bytesInMemoryHOL_domainAux rest (a + 1) m d ht j hj'
          rw [arm8AddOneOffset] at hrec
          exact hrec

/-- The `j`-th byte of a byte list in memory lies in the domain, for every
`j` below the length. -/
theorem bytesInMemoryHOL_domain {a : BitVec 64} {bs : List (BitVec 8)}
    {m : BitVec 64 → BitVec 8} {d : BitVec 64 → Prop}
    (h : bytesInMemoryHOL a bs m d) :
    ∀ j, j < bs.length → d (a + BitVec.ofNat 64 j) :=
  bytesInMemoryHOL_domainAux bs a m d h

/-- `arm8_ast` of `skip` is the single instruction `noOp`. -/
theorem arm8Ast_skip : arm8Ast (.inst .skip) = [.noOp] := rfl

/-- `arm8_enc` of `skip` is the four encoded bytes of `noOp`. -/
theorem arm8Enc_skip : arm8Enc (.inst .skip) = encodeBytes .noOp := rfl

/-- The `skip` encoding is four bytes long. -/
theorem arm8Enc_skip_length : (arm8Enc (.inst .skip)).length = 4 := by
  rw [arm8Enc_skip]
  simp only [encodeBytes]
  split <;> simp [wordBytes]

/-- The `noOp` byte encoding is four bytes long. -/
theorem encodeBytes_noOp_length : (encodeBytes .noOp).length = 4 := by
  rw [← arm8Enc_skip]
  exact arm8Enc_skip_length

/-! ## The start facts -/

/-- The facts every ARM8 case reads off `asm_step` and the initial target
relation.  `bytes` is stated over the target memory, as in the MIPS `Start`.
The `fpRegs` conjunct of `targetStateRel` is vacuous (`arm8Config.fpRegCount
= 0`) and is not recorded.  A case also gets `s2.memDomain = s1.memDomain`
for free, since `asmUpd` only changes the PC (see the case proof, where it is
discharged by `rfl` after unfolding the update). -/
structure Arm8Start (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : Arm8State) : Prop where
  bytes : bytesInMemoryHOL ms.pc (arm8Enc i) ms.mem s1.memDomain
  pc : ms.pc = s1.pc
  mem : ∀ a, s1.memDomain a → ms.mem a = s1.mem a
  reg : ∀ r, r < arm8Target.config.regCount ∧ arm8Target.config.avoidRegs.contains r = false →
    ms.regs r = s1.regs r
  stateOk : arm8StateOk ms = true
  aligned : holAligned 2 ms.pc = true
  msFailed : ms.failed = false
  lr : s1.lr = 30
  be : s1.be = false
  align : s1.align = 2
  upd : asmUpd i (s1.pc + BitVec.ofNat 64 (arm8Enc i).length) s1 = s2
  ok : ¬ s2.failed
  asmOk : asmOkExact i arm8Config = true

/-- Extract the start facts from one `asm_step` and the initial target
relation. -/
theorem arm8Start (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 i s2 ∧ targetStateRel arm8Target s1 ms) :
    Arm8Start i s1 s2 ms := by
  obtain ⟨⟨hb, hlr, hbe, hal, hupd, hfail, hok⟩, hst⟩ := h
  obtain ⟨hok', hpc, hmem, hreg, -⟩ := hst
  change ms.pc = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.mem a = s1.mem a at hmem
  change ∀ r, r < arm8Target.config.regCount ∧ arm8Target.config.avoidRegs.contains r = false →
    ms.regs r = s1.regs r at hreg
  change arm8StateOk ms = true at hok'
  change bytesInMemoryHOL s1.pc (arm8Enc i) s1.mem s1.memDomain at hb
  have hok'' : holAligned 2 ms.pc = true ∧ ms.failed = false := by
    simpa only [arm8StateOk, Bool.and_eq_true, Bool.not_eq_true'] using hok'
  have hdom := bytesInMemoryHOL_domain hb
  have hbytes : bytesInMemoryHOL ms.pc (arm8Enc i) ms.mem s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _
      ⟨hb, fun n hn => (hmem _ (hdom n hn)).symm⟩
  exact {
    bytes := hbytes
    pc := hpc
    mem := hmem
    reg := hreg
    stateOk := hok'
    aligned := hok''.1
    msFailed := hok''.2
    lr := by simpa [arm8Config] using hlr
    be := by simpa [arm8Config] using hbe
    align := by simpa [arm8Config] using hal
    upd := by simpa [arm8Config] using hupd
    ok := hfail
    asmOk := hok
  }

/-! ## The `skip` case -/

/-- The `skip` constructor of `encoder_correct arm8Target`: one `arm8Next`
step from a state whose bytes are the `noOp` encoding only advances the PC. -/
theorem case_skip (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst .skip) s2 ∧ targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst .skip) s1 s2 ms := by
  have st := arm8Start (.inst .skip) s1 s2 ms h
  have hupd : asmUpd (.inst .skip) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, arm8Enc_skip_length]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd]
    rfl
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← hupd]
    intro a
    rfl
  have hs2dom : ∀ a, s2.memDomain a ↔ s1.memDomain a := by
    rw [← hupd]
    intro a
    exact Iff.rfl
  have hs2regs : ∀ r, s2.regs r = s1.regs r := by
    rw [← hupd]
    intro r
    rfl
  have hdom : s2.memDomain = s1.memDomain := by
    rw [← hupd]
    rfl
  have hbm : bytesInMemoryHOL ms.pc (encodeBytes .noOp) ms.mem s1.memDomain := by
    rw [← arm8Enc_skip]
    exact st.bytes
  have hdom4 := bytesInMemoryHOL_domain hbm
  have hfetch : FetchSafe s1.memDomain ms := by
    intro x hx
    simp only [arm8FetchBytes, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa using hdom4 0 (by rw [encodeBytes_noOp_length]; omega)
    · simpa using hdom4 1 (by rw [encodeBytes_noOp_length]; omega)
    · simpa using hdom4 2 (by rw [encodeBytes_noOp_length]; omega)
    · simpa using hdom4 3 (by rw [encodeBytes_noOp_length]; omega)
  have hdec : decodeInsn32 (fetchWord ms) = some .noOp := by
    have hw := fetchWord_encodeBytes ms .noOp ((encodeInsn .noOp).getD 0) s1.memDomain
      (by unfold encodeInsn; rfl) hbm
    rw [hw]
    exact decode_encode_noOp
  have hstepSafe : StepSafe s1.memDomain ms := by
    refine ⟨hfetch, ?_⟩
    intro i hi x hx
    rw [hdec] at hi
    cases hi
    simp [arm8Touched] at hx
  have hnextSafe : NextSafe s1.memDomain ms := by
    refine ⟨hstepSafe, ?_⟩
    intro _ hn
    rw [arm8Next_noOp ms s1.memDomain hbm] at hn
    exact absurd rfl hn
  have hsafe : ∀ k ≤ 0, NextSafe s1.memDomain (arm8Next^[k] ms) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hnextSafe
  have hcode : allPcs (arm8Target.config.encode (.inst .skip)).length s1.pc 0 ⊆
      s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, arm8Enc_skip]
    intro x hx
    rw [allPcs_eq] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hj4 : j < (encodeBytes .noOp).length := by simpa using hj
    change s1.memDomain (s1.pc + BitVec.ofNat 64 (j * 2 ^ 0))
    have h := hdom4 j hj4
    rw [st.pc] at h
    simpa using h
  have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
    show targetStateRel arm8Target s2 (arm8Next ms)
    rw [arm8Next_noOp ms s1.memDomain hbm]
    have h4 : holAligned 2 (4 : BitVec 64) = true := by
      rw [holAligned_iff]; decide
    have hal : holAligned 2 (ms.pc + (4 : BitVec 64)) = true := by
      rw [(alignedAddSub 2 ms.pc 4 h4).1, st.aligned]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [arm8Target_stateOk, arm8StateOk, hal, st.msFailed, Bool.not_false,
        Bool.and_self]
    · show ms.pc + (4 : BitVec 64) = s2.pc
      rw [st.pc, hs2pc]
      bv_omega
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      exact st.mem a ((hs2dom a).1 ha)
    · intro i hi
      show ms.regs i = s2.regs i
      rw [hs2regs i]
      exact st.reg i hi
    · intro i hi
      simp only [arm8Target_config, arm8Config] at hi
      omega
  exact encoderCase (.inst .skip) s1 s2 ms 0 hdom hcode hsafe
    (by intro k hk _; omega) hq

end Flapjack.Compiler.Encoders.Arm8
