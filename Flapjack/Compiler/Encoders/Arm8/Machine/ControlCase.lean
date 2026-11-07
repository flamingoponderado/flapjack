import Flapjack.Compiler.Encoders.Arm8.Machine.SkipCase
import Flapjack.Compiler.Encoders.Arm8.Machine.DecodeProofControl
import Flapjack.Compiler.Encoders.Arm8.Machine.DecodeProofSimple2

/-!
# The ARMv8 control-flow cases of `encoder_correct`

This is the ARM8 analogue of `case_jump`, `case_call`, `case_jumpReg` and
`case_loc` in `Flapjack/Mips32/TargetProof/Control.lean`.  A `jump`/`call`
lowers to a single `branchImmediate`, a `jumpReg` to a single `branchRegister`
and a `loc` to one `address` or, when the offset does not fit in twenty signed
bits, to a five-instruction address/`moveWide` sequence (`arm8Ast`).

The closed ARM8 machine has no delay slot, so the interference-free run of one
of these instructions is a single `arm8Next` step that moves the PC away from
`s.pc + 4`.  The delay-slot conjunct of `NextSafe` (`Machine/Simulate.lean`) then
demands the step-safety of the branch *target*, which `asm_step` does not
provide: the target of a `jump` need not be inside the source memory domain.
`encoderCase` is therefore unusable for control flow, and this file proves the
`CaseGoal` through `encoderCaseStep`, the same reduction as `encoderCase` with
`StepSafe` in place of `NextSafe`.  `StepSafe` is all `arm8Next_agree` (and
hence everything `encoderCase`'s argument needs) consumes, so no proof step is
lost; `case_skip` in `Machine/SkipCase.lean` still goes through `encoderCase`.

The encoder side conditions (`fitsSigned 28` for a branch, `fitsSigned 20` for a
short `loc`, and the four-byte alignment) are read off the `asmOkExact` fact of
`Arm8Start` through `fitsSigned_of_range`, which turns the `toInt` bounds of the
configuration's offset window into `fitsSigned`; `arm8Ast`/`arm8Enc` then
determine the emitted instructions and their bytes.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Length of the emitted bytes -/

/-- Every emitted instruction encodes to exactly four bytes: `encodeBytes` is
either the four little-endian bytes of the word or the four zero bytes of
`BadCode`. -/
theorem encodeBytes_length (i : Insn) : (encodeBytes i).length = 4 := by
  unfold encodeBytes
  split <;> simp [wordBytes]

/-- `arm8_enc` of a single-instruction lowering is four bytes. -/
theorem arm8Enc_length_single (i : Insn) : ((List.flatMap encodeBytes [i])).length = 4 := by
  simp [encodeBytes_length]

/-! ## Signed ranges

The configuration's offset windows are stated as signed `toInt` bounds, while the
encoder's guards are the `fitsSigned` tests on the low bits of the offset.
`fitsSigned_of_range` is the conversion the cases need. -/

/-- The low `bits` bits of `2 ^ 64 - d`, for a positive `d` below `2 ^ bits`
(generalization of `nat_mod_pow_sub_21` to every width). -/
theorem natModPowSub (bits d : Nat) (hbits : bits ≤ 64) (hd : 0 < d)
    (hdb : d ≤ 2 ^ bits) : (2 ^ 64 - d) % 2 ^ bits = 2 ^ bits - d := by
  have hsplit : 2 ^ 64 - d = (2 ^ 64 - 2 ^ bits) + (2 ^ bits - d) := by
    have h1 : 2 ^ bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hbits
    omega
  have hdvd : (2 ^ bits : Nat) ∣ 2 ^ 64 - 2 ^ bits := by
    have hprod : 2 ^ bits * (2 ^ (64 - bits) - 1) = 2 ^ 64 - 2 ^ bits := by
      rw [Nat.mul_sub, Nat.mul_one]
      congr 1
      rw [← pow_add]
      congr 1
      omega
    exact ⟨_, hprod.symm⟩
  rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- A sixty-four-bit word inside the signed `bits`-bit range is the sign
extension of its own low `bits` bits, i.e. `fitsSigned bits`.  This is the
`toInt`-bounds form of `fitsSigned` used by the offset windows. -/
theorem fitsSigned_of_range (bits : Nat) (v : BitVec 64) (hb : 1 ≤ bits) (hbits : bits ≤ 64)
    (hlo : -(2 : Int) ^ (bits - 1) ≤ v.toInt)
    (hhi : v.toInt ≤ (2 : Int) ^ (bits - 1) - 1) : fitsSigned bits v = true := by
  have hx : v.toNat < 2 ^ 64 := v.isLt
  have hp2 : (2 : Nat) ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hpc : (((2 : Nat) ^ (bits - 1) : Nat) : Int) = (2 : Int) ^ (bits - 1) := by simp
  have hcond : v.toInt = if 2 * v.toNat < 2 ^ 64 then (v.toNat : Int)
      else (v.toNat : Int) - (2 : Int) ^ 64 := by
    rw [BitVec.toInt_eq_toNat_cond]
    norm_num
  unfold fitsSigned sextValue
  rw [decide_eq_true_eq]
  by_cases hcase : 2 * v.toNat < 2 ^ 64
  · have htoInt : v.toInt = (v.toNat : Int) := by rw [hcond, ite_eq_left hcase]
    have hlt : v.toNat < 2 ^ (bits - 1) := by
      have h : (v.toNat : Int) ≤ (2 : Int) ^ (bits - 1) - 1 := by rw [← htoInt]; exact hhi
      omega
    have hmod : v.toNat % 2 ^ bits = v.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hmod, ite_eq_left (by omega), htoInt]
  · have htoInt : v.toInt = (v.toNat : Int) - (2 : Int) ^ 64 := by rw [hcond, ite_eq_right hcase]
    have hdpos : 0 < 2 ^ 64 - v.toNat := by omega
    have hxeq : v.toNat = 2 ^ 64 - (2 ^ 64 - v.toNat) :=
      (Nat.sub_sub_self (by omega : v.toNat ≤ 2 ^ 64)).symm
    have hdle : 2 ^ 64 - v.toNat ≤ 2 ^ (bits - 1) := by
      have hc : ((2 ^ 64 - v.toNat : Nat) : Int) = -v.toInt := by
        rw [Nat.cast_sub (by omega : v.toNat ≤ 2 ^ 64), htoInt]
        norm_num
      omega
    have hmod : v.toNat % 2 ^ bits = 2 ^ bits - (2 ^ 64 - v.toNat) := by
      conv_lhs => rw [hxeq]
      exact natModPowSub bits (2 ^ 64 - v.toNat) hbits hdpos (by omega)
    have hneg : ¬ 2 ^ bits - (2 ^ 64 - v.toNat) < 2 ^ (bits - 1) := by omega
    have hcD : ((2 ^ 64 - v.toNat : Nat) : Int) = (2 : Int) ^ 64 - (v.toNat : Int) := by
      rw [Nat.cast_sub (by omega : v.toNat ≤ 2 ^ 64)]
      norm_num
    have hcB : ((2 ^ bits - (2 ^ 64 - v.toNat) : Nat) : Int)
        = (2 : Int) ^ bits - ((2 ^ 64 - v.toNat : Nat) : Int) := by
      rw [Nat.cast_sub (by omega : 2 ^ 64 - v.toNat ≤ 2 ^ bits)]
      norm_num
    rw [hmod, ite_eq_right hneg, htoInt, hcB, hcD]
    norm_num

/-! ## The encoder side conditions -/

/-- `decide` of an arbitrary decision procedure of `p` that returns `true` gives
`p`.  The configuration's offset bounds are decided by the projection instances
of `Int.decLe`, so the canonical `decide_eq_true_eq` does not apply. -/
theorem ofDecideTrue {p : Prop} (inst : Decidable p) (h : @decide p inst = true) : p := by
  cases inst with
  | isTrue hp => exact hp
  | isFalse _ => exact Bool.noConfusion h

/-- The `jump`/`call` offset window of `arm8Config` gives the encoder's
twenty-eight-bit branch guard and the four-byte alignment. -/
theorem jumpOk_of_asm (a : W) (h : asmJumpOffsetOkExact arm8Config a = true) :
    fitsSigned 28 a = true ∧ a.toNat % 4 = 0 := by
  simp only [asmJumpOffsetOkExact, asmOffsetOkExact, arm8Config, Bool.and_eq_true] at h
  obtain ⟨⟨hlo, hhi⟩, hal⟩ := h
  have hlo := ofDecideTrue _ hlo
  have hhi := ofDecideTrue _ hhi
  have hmod : a.toNat % 4 = 0 := by simpa [asmAligned] using hal
  refine ⟨fitsSigned_of_range 28 a (by decide) (by decide) ?_ ?_, hmod⟩
  · have hl : ((-134217728 : BitVec 64)).toInt = -134217728 := by decide
    rw [hl] at hlo
    have h2 : -(2 : Int) ^ (28 - 1) = -134217728 := by norm_num
    rw [h2]
    omega
  · have hl : ((134217727 : BitVec 64)).toInt = 134217727 := by decide
    rw [hl] at hhi
    have h2 : (2 : Int) ^ (28 - 1) - 1 = 134217727 := by norm_num
    rw [h2]
    omega

/-- A register accepted by `arm8Config` is a real register, and in particular
neither the zero register nor the encoder's temporary. -/
theorem regOk_of_asm {r : Nat} (h : asmRegOkExact r arm8Config = true) :
    r < arm8Config.regCount ∧ arm8Config.avoidRegs.contains r = false ∧ r ≠ 31 := by
  simp only [asmRegOkExact, arm8Config, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨ofDecideTrue _ h1, ?_, ?_⟩
  · cases hc : List.contains [18, 26, 31] r with
    | false => exact hc
    | true =>
      rw [hc] at h2
      exact Bool.noConfusion h2
  · rintro rfl
    simp at h2

/-! ## A `NextSafe`-free `encoderCase`

The closed ARM8 machine has no delay slot: a control-transfer step moves the PC
away from `s.pc + 4`, and the delay-slot conjunct of `NextSafe`
(`Machine/Simulate.lean`) then demands `StepSafe` of the branch *target*, which
`asm_step` does not provide (the target of a `jump` need not lie in the source
memory domain).  `arm8Next_agree`, and with it everything the `encoderCase`
argument uses, needs only `StepSafe`, so the chain lemmas and `encoderCase`
below are the same proof over `StepSafe`; the resulting `CaseGoal` statement is
unchanged. -/

/-- One `arm8Next` step preserves agreement on `d` when the step stays inside
`d`.  This is `next_agree'` with the vacuous delay-slot conjunct dropped. -/
theorem next_agree_step {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (hs : StepSafe d t) : Arm8Agree d (arm8Next s) (arm8Next t) :=
  (arm8Next_agree h.symm hs).symm

/-- `asserts_of_run` with `StepSafe` along the run instead of `NextSafe`. -/
theorem asserts_of_run_step {d : BitVec 64 → Prop} {P Q : Arm8State → Prop}
    (hP : ∀ s t, Arm8Agree d s t → P t → P s) (hQ : ∀ s t, Arm8Agree d s t → Q t → Q s)
    (f : Nat → Arm8State → Arm8State) (hf : ∀ k x, Arm8Agree d (f k x) (arm8Next x)) :
    ∀ (m : Nat) (u t : Arm8State), Arm8Agree d u t →
      (∀ k ≤ m, StepSafe d (arm8Next^[k] t)) →
      (∀ k, 1 ≤ k → k ≤ m → P (arm8Next^[k] t)) → Q (arm8Next^[m + 1] t) →
      asserts m f u P Q := by
  intro m
  induction m with
  | zero =>
    intro u t hut hsafe _ hq
    exact hQ _ _ ((hf 0 u).trans (next_agree_step hut (hsafe 0 (Nat.le_refl 0)))) hq
  | succ m ih =>
    intro u t hut hsafe hp hq
    have h1 : Arm8Agree d (f (m + 1) u) (arm8Next t) :=
      (hf (m + 1) u).trans (next_agree_step hut (hsafe 0 (Nat.zero_le _)))
    refine ⟨hP _ _ h1 (hp 1 (Nat.le_refl 1) (by omega)), ?_⟩
    apply ih _ _ h1
    · intro k hk
      have := hsafe (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    · intro k hk1 hk2
      have := hp (k + 1) (by omega) (by omega)
      rwa [Function.iterate_succ_apply] at this
    · rwa [← Function.iterate_succ_apply]

/-- `asserts2_of_run` with `StepSafe` along the run instead of `NextSafe`. -/
theorem asserts2_of_run_step {d : BitVec 64 → Prop}
    (fi : Nat → Arm8State → Arm8State) (hfi : ∀ k x, Arm8Agree d (fi k x) x) :
    ∀ (m : Nat) (u t : Arm8State), Arm8Agree d u t →
      (∀ k < m, StepSafe d (arm8Next^[k] t)) →
      asserts2 m fi arm8Next u
        (fun ms1 ms2 => ∀ x, ¬ d x → ms1.mem x = ms2.mem x) := by
  intro m
  induction m with
  | zero => intros; trivial
  | succ m ih =>
    intro u t hut hsafe
    have hs0 := hsafe 0 (Nat.zero_lt_succ _)
    refine ⟨fun x hx => (arm8Next_frame u (StepSafe.of_agree hut hs0) x hx).symm, ?_⟩
    exact ih _ (arm8Next t) ((hfi (m + 1) _).trans (next_agree_step hut hs0))
      (fun k hk => by
        have := hsafe (k + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this)

/-- One constructor of `encoder_correct arm8Target` from its interference-free
run of `n + 1` steps, with `StepSafe` (not `NextSafe`) along the run. -/
theorem encoderCaseStep (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : Arm8State) (n : Nat)
    (hdom : s2.memDomain = s1.memDomain)
    (hcode : allPcs (arm8Target.config.encode i).length s1.pc 0 ⊆ s1.memDomain)
    (hsafe : ∀ k ≤ n, StepSafe s1.memDomain (arm8Next^[k] ms))
    (hp : ∀ k, 1 ≤ k → k ≤ n →
      arm8StateOk (arm8Next^[k] ms) = true ∧
      (∀ pc, pc ∈ allPcs (arm8Target.config.encode i).length s1.pc 0 →
        (arm8Next^[k] ms).mem pc = ms.mem pc) ∧
      (arm8Next^[k] ms).pc ∈
        allPcs (arm8Target.config.encode i).length s1.pc arm8Target.config.codeAlignment)
    (hq : targetStateRel arm8Target s2 (arm8Next^[n + 1] ms)) :
    CaseGoal i s1 s2 ms := by
  refine ⟨n, fun env henv => ?_⟩
  have hagree : ∀ k x, Arm8Agree s1.memDomain (env k x) x :=
    fun k x => (arm8Proj_eq_iff _ _ _).1 (henv k x)
  constructor
  · apply asserts_of_run_step (d := s1.memDomain) _ _ _ _ n ms ms (Arm8Agree.refl _ _) hsafe hp
    · exact hq
    · rintro s t hst ⟨h1, h2, h3⟩
      refine ⟨?_, fun pc hpc => ?_, ?_⟩
      · change arm8StateOk s = true
        rw [arm8StateOk_congr hst]; exact h1
      · change s.mem pc = ms.mem pc
        rw [hst.mem pc (hcode hpc)]; exact h2 pc hpc
      · change s.pc ∈ _
        rw [hst.pc]; exact h3
    · intro s t hst ht
      exact targetStateRel_congr (hdom ▸ hst) ht
    · intro k x
      exact hagree _ _
  · exact asserts2_of_run_step (d := s1.memDomain) _ (fun k x => hagree _ _) (n + 1) ms ms
      (Arm8Agree.refl _ _) (fun k hk => hsafe k (by omega))

/-! ## The emitted bytes and executed instructions of the control-flow forms -/

/-- `arm8_enc` of a `jump` is the four bytes of its branch. -/
theorem arm8Enc_jump (a : W) : arm8Enc (.jump a) = encodeBytes (.branchImmediate a false) := by
  simp [arm8Enc, arm8Ast]

/-- `arm8_enc` of a `call` is the four bytes of its linking branch. -/
theorem arm8Enc_call (a : W) : arm8Enc (.call a) = encodeBytes (.branchImmediate a true) := by
  simp [arm8Enc, arm8Ast]

/-- `arm8_enc` of a `jumpReg` is the four bytes of its register branch. -/
theorem arm8Enc_jumpReg (r : Nat) : arm8Enc (.jumpReg r) = encodeBytes (.branchRegister r .jmp) := by
  simp [arm8Enc, arm8Ast]

/-- A state with an aligned PC that has not failed satisfies `arm8StateOk`. -/
theorem arm8StateOk_set (s : Arm8State) (hal : holAligned 2 s.pc = true)
    (hf : s.failed = false) : arm8StateOk s = true := by
  simp only [arm8StateOk, hal, hf, Bool.not_false, Bool.and_self]

/-- A `Bool` that is not `true` is `false`. -/
theorem boolOfNotTrue {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

/-- The left operand of a `false` disjunction is `false`. -/
theorem boolOfOrFalse {a b : Bool} (h : (a || b) = false) : a = false := by
  cases a with
  | false => rfl
  | true =>
    rw [Bool.true_or] at h
    exact Bool.noConfusion h

/-- A negated `false` boolean is `true`. -/
theorem boolOfNotFalse {a : Bool} (h : (!a) = false) : a = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => rfl

/-- A multiple of four is a `holAligned 2` word. -/
theorem aligned_of_mod (a : W) (h : a.toNat % 4 = 0) : holAligned 2 a = true := by
  rw [holAligned_iff]
  simpa using h

/-- A non-linking branch leaves the state alone apart from its PC. -/
theorem execInsn_branchImmediate_jmp (s : Arm8State) (imm : W) :
    execInsn s (.branchImmediate imm false) = { s with pc := s.pc - 4 + imm } := rfl

/-- A linking branch writes the return address and moves the PC. -/
theorem execInsn_branchImmediate_call (s : Arm8State) (imm : W) :
    execInsn s (.branchImmediate imm true) =
      { writeReg s 30 s.pc with pc := s.pc - 4 + imm } := rfl

/-- A register jump to a non-link register only moves the PC. -/
theorem execInsn_branchRegister_jmp (s : Arm8State) (rn : Nat) :
    execInsn s (.branchRegister rn .jmp) = { s with pc := readReg s rn } := rfl

/-- The PC of a linking branch. -/
theorem execInsn_branchImmediate_call_pc (s : Arm8State) (imm : W) :
    (execInsn s (.branchImmediate imm true)).pc = s.pc - 4 + imm := rfl

/-- A linking branch writes the return address into register 30. -/
theorem execInsn_branchImmediate_call_regs (s : Arm8State) (imm : W) (i : Nat) :
    (execInsn s (.branchImmediate imm true)).regs i = (if i = 30 then s.pc else s.regs i) := by
  simp only [execInsn_branchImmediate_call, writeReg, ite_eq_right (by decide : (30 : Nat) ≠ 31)]

/-- A PC-relative address is written into its destination register. -/
theorem execInsn_addressFalse (s : Arm8State) (imm : W) (rd : Nat) :
    execInsn s (.address false imm rd) = writeReg s rd (s.pc - 4 + imm) := rfl

/-! ## The `jump` case -/

/-- The `jump` constructor of `encoder_correct arm8Target`: one `arm8Next` step
that executes the encoded branch and lands on `s1.pc + a`. -/
theorem case_jump (a : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.jump a) s2 ∧ targetStateRel arm8Target s1 ms) :
    CaseGoal (.jump a) s1 s2 ms := by
  have st := arm8Start (.jump a) s1 s2 ms h
  obtain ⟨hfits, hmod⟩ := jumpOk_of_asm a st.asmOk
  have hlen : (arm8Enc (.jump a)).length = 4 := by
    rw [arm8Enc_jump]; exact encodeBytes_length _
  have hupd : asmUpd (.jump a) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + a := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ i, s2.regs i = s1.regs i := by
    rw [← hupd]; intro i; rfl
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbytes : bytesInMemoryHOL ms.pc (encodeBytes (.branchImmediate a false)) ms.mem
      s1.memDomain := by
    rw [← arm8Enc_jump]; exact st.bytes
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 } (.branchImmediate a false) :=
    arm8Next_branchImmediate ms s1.memDomain a false hfits hmod hbytes
  have hdom4 := bytesInMemoryHOL_domain hbytes
  have hlen4 : (encodeBytes (.branchImmediate a false)).length = 4 := encodeBytes_length _
  have hfetch : FetchSafe s1.memDomain ms := by
    intro x hx
    simp only [arm8FetchBytes, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa using hdom4 0 (by rw [hlen4]; omega)
    · simpa using hdom4 1 (by rw [hlen4]; omega)
    · simpa using hdom4 2 (by rw [hlen4]; omega)
    · simpa using hdom4 3 (by rw [hlen4]; omega)
  have hfetchword : fetchWord ms =
      ((fields [(1, bit false), (5, 5), (26, (a >>> 2).toNat % 2 ^ 26)]).setWidth 64).setWidth 32 :=
    fetchWord_encodeBytes ms (.branchImmediate a false) _ s1.memDomain
      (encodeInsn_branchImmediate a false hfits hmod) hbytes
  have hdec : decodeInsn32 (fetchWord ms) = some (.branchImmediate a false) := by
    rw [hfetchword]
    show decodeInsn ((fields [(1, bit false), (5, 5),
      (26, (a >>> 2).toNat % 2 ^ 26)]).setWidth 64) = some (.branchImmediate a false)
    exact decode_encode_branchImmediate a false hfits hmod
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨hfetch, ?_⟩
    intro i hi x hx
    rw [hdec] at hi
    cases hi
    simp [arm8Touched] at hx
  have hal : holAligned 2 (ms.pc + a) = true := by
    rw [(alignedAddSub 2 ms.pc a (aligned_of_mod a hmod)).1, st.aligned]
  have hpc4 : (ms.pc + 4 : BitVec 64) - 4 + a = ms.pc + a := by bv_omega
  have hq1 : targetStateRel arm8Target s2 (arm8Next ms) := by
    rw [hnext, execInsn_branchImmediate_jmp, hpc4]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [arm8Target_stateOk]
      exact arm8StateOk_set _ hal st.msFailed
    · show ms.pc + a = s2.pc
      rw [st.pc, hs2pc]
    · intro x hx
      show ms.mem x = s2.mem x
      rw [hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro i hi
      show ms.regs i = s2.regs i
      rw [hs2regs i]
      exact st.reg i hi
    · intro i hi
      simp only [arm8Target_config, arm8Config] at hi
      omega
  have hcode : allPcs (arm8Target.config.encode (.jump a)).length s1.pc 0 ⊆ s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
    have hi : arm8Next^[0 + 1] ms = arm8Next ms := by
      rw [Nat.zero_add, Function.iterate_one]
    rw [hi]
    exact hq1
  refine encoderCaseStep (.jump a) s1 s2 ms 0 hdom hcode ?_ ?_ hq
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hsafe0
  · intro k h1 h2
    omega

/-! ## The `call` case -/

/-- The `call` constructor of `encoder_correct arm8Target`: one `arm8Next` step
that links `pc + 4` into the link register and branches to `s1.pc + a`. -/
theorem case_call (a : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.call a) s2 ∧ targetStateRel arm8Target s1 ms) :
    CaseGoal (.call a) s1 s2 ms := by
  have st := arm8Start (.call a) s1 s2 ms h
  have hok := st.asmOk
  simp only [asmOkExact, arm8Config, Bool.and_eq_true] at hok
  obtain ⟨hfits, hmod⟩ := jumpOk_of_asm a hok.2
  have hlen : (arm8Enc (.call a)).length = 4 := by
    rw [arm8Enc_call]; exact encodeBytes_length _
  have hupd : asmUpd (.call a) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.pc + a := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ i, s2.regs i = (if i = 30 then s1.pc + 4 else s1.regs i) := by
    intro i
    rw [← hupd]
    simp only [asmUpd, jumpToOffset, updPc, updReg, st.lr]
    rfl
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbytes : bytesInMemoryHOL ms.pc (encodeBytes (.branchImmediate a true)) ms.mem
      s1.memDomain := by
    rw [← arm8Enc_call]; exact st.bytes
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 } (.branchImmediate a true) :=
    arm8Next_branchImmediate ms s1.memDomain a true hfits hmod hbytes
  have hdom4 := bytesInMemoryHOL_domain hbytes
  have hlen4 : (encodeBytes (.branchImmediate a true)).length = 4 := encodeBytes_length _
  have hfetch : FetchSafe s1.memDomain ms := by
    intro x hx
    simp only [arm8FetchBytes, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa using hdom4 0 (by rw [hlen4]; omega)
    · simpa using hdom4 1 (by rw [hlen4]; omega)
    · simpa using hdom4 2 (by rw [hlen4]; omega)
    · simpa using hdom4 3 (by rw [hlen4]; omega)
  have hfetchword : fetchWord ms =
      ((fields [(1, bit true), (5, 5), (26, (a >>> 2).toNat % 2 ^ 26)]).setWidth 64).setWidth 32 :=
    fetchWord_encodeBytes ms (.branchImmediate a true) _ s1.memDomain
      (encodeInsn_branchImmediate a true hfits hmod) hbytes
  have hdec : decodeInsn32 (fetchWord ms) = some (.branchImmediate a true) := by
    rw [hfetchword]
    show decodeInsn ((fields [(1, bit true), (5, 5),
      (26, (a >>> 2).toNat % 2 ^ 26)]).setWidth 64) = some (.branchImmediate a true)
    exact decode_encode_branchImmediate a true hfits hmod
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨hfetch, ?_⟩
    intro i hi x hx
    rw [hdec] at hi
    cases hi
    simp [arm8Touched] at hx
  have hal : holAligned 2 (ms.pc + a) = true := by
    rw [(alignedAddSub 2 ms.pc a (aligned_of_mod a hmod)).1, st.aligned]
  have hpc4 : (ms.pc + 4 : BitVec 64) - 4 + a = ms.pc + a := by bv_omega
  have hq1 : targetStateRel arm8Target s2 (arm8Next ms) := by
    rw [hnext, execInsn_branchImmediate_call, writeReg,
      hpc4, ite_eq_right (by decide : (30 : Nat) ≠ 31)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [arm8Target_stateOk]
      exact arm8StateOk_set _ hal st.msFailed
    · show ms.pc + a = s2.pc
      rw [st.pc, hs2pc]
    · intro x hx
      show ms.mem x = s2.mem x
      rw [hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro i hi
      by_cases h30 : i = 30
      · subst h30
        show ms.pc + 4 = s2.regs 30
        rw [hs2regs 30, ite_eq_left rfl, st.pc]
      · show (if i = 30 then ms.pc + 4 else ms.regs i) = s2.regs i
        rw [ite_eq_right h30, hs2regs i, ite_eq_right h30]
        exact st.reg i hi
    · intro i hi
      simp only [arm8Target_config, arm8Config] at hi
      omega
  have hcode : allPcs (arm8Target.config.encode (.call a)).length s1.pc 0 ⊆ s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
    have hi : arm8Next^[0 + 1] ms = arm8Next ms := by
      rw [Nat.zero_add, Function.iterate_one]
    rw [hi]
    exact hq1
  refine encoderCaseStep (.call a) s1 s2 ms 0 hdom hcode ?_ ?_ hq
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hsafe0
  · intro k h1 h2
    omega

/-! ## The `jumpReg` case -/

/-- One `arm8Next` step of a register jump reads only the register file. -/
theorem execInsn_branchRegister_jmp_pc (s : Arm8State) (rn : Nat) :
    (execInsn s (.branchRegister rn .jmp)).pc = readReg s rn := rfl

/-- The `jumpReg` constructor of `encoder_correct arm8Target`: one `arm8Next`
step that branches to the target register. -/
theorem case_jumpReg (r : Nat) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.jumpReg r) s2 ∧ targetStateRel arm8Target s1 ms) :
    CaseGoal (.jumpReg r) s1 s2 ms := by
  have st := arm8Start (.jumpReg r) s1 s2 ms h
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asm st.asmOk
  have hlen : (arm8Enc (.jumpReg r)).length = 4 := by
    rw [arm8Enc_jumpReg]; exact encodeBytes_length _
  have hupd : asmUpd (.jumpReg r) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← st.upd, hlen]
  have hs2pc : s2.pc = s1.regs r := by
    rw [← hupd]; rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd]; intro x; rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]; rfl
  have hs2regs : ∀ i, s2.regs i = s1.regs i := by
    rw [← hupd]; intro i; rfl
  have halr : holAligned 2 (s1.regs r) = true := by
    have hok : ¬((!(holAligned 2 (s1.regs r)) || s1.failed) = true) := by
      have hok := st.ok
      rw [← hupd] at hok
      simpa only [asmUpd, updPc, assertState, st.align, AsmSem.readReg] using hok
    exact boolOfNotFalse (boolOfOrFalse (boolOfNotTrue hok))
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbytes : bytesInMemoryHOL ms.pc (encodeBytes (.branchRegister r .jmp)) ms.mem
      s1.memDomain := by
    rw [← arm8Enc_jumpReg]; exact st.bytes
  have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 } (.branchRegister r .jmp) :=
    arm8Next_branchRegister ms s1.memDomain .jmp r hlt hbytes
  have hdom4 := bytesInMemoryHOL_domain hbytes
  have hlen4 : (encodeBytes (.branchRegister r .jmp)).length = 4 := encodeBytes_length _
  have hfetch : FetchSafe s1.memDomain ms := by
    intro x hx
    simp only [arm8FetchBytes, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa using hdom4 0 (by rw [hlen4]; omega)
    · simpa using hdom4 1 (by rw [hlen4]; omega)
    · simpa using hdom4 2 (by rw [hlen4]; omega)
    · simpa using hdom4 3 (by rw [hlen4]; omega)
  have hfetchword : fetchWord ms =
      ((fields [(9, 428), (2, branchKindBits .jmp), (11, 1984), (5, r),
        (5, 0)]).setWidth 64).setWidth 32 :=
    fetchWord_encodeBytes ms (.branchRegister r .jmp) _ s1.memDomain
      (encodeInsn_branchRegister .jmp r) hbytes
  have hdec : decodeInsn32 (fetchWord ms) = some (.branchRegister r .jmp) := by
    rw [hfetchword]
    show decodeInsn ((fields [(9, 428), (2, branchKindBits .jmp), (11, 1984), (5, r),
      (5, 0)]).setWidth 64) = some (.branchRegister r .jmp)
    exact decode_encode_branchRegister .jmp r hlt
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨hfetch, ?_⟩
    intro i hi x hx
    rw [hdec] at hi
    cases hi
    simp [arm8Touched] at hx
  have hregr : ms.regs r = s1.regs r := st.reg r ⟨hlt, hav⟩
  have hread : readReg { ms with pc := ms.pc + 4 } r = s1.regs r := by
    simp only [readReg, ite_eq_right hne31]
    exact hregr
  have hq1 : targetStateRel arm8Target s2 (arm8Next ms) := by
    rw [hnext, execInsn_branchRegister_jmp]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [arm8Target_stateOk]
      refine arm8StateOk_set _ ?_ st.msFailed
      rw [hread, halr]
    · show readReg { ms with pc := ms.pc + 4 } r = s2.pc
      rw [hread, hs2pc]
    · intro x hx
      show ms.mem x = s2.mem x
      rw [hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro i hi
      show ms.regs i = s2.regs i
      rw [hs2regs i]
      exact st.reg i hi
    · intro i hi
      simp only [arm8Target_config, arm8Config] at hi
      omega
  have hcode : allPcs (arm8Target.config.encode (.jumpReg r)).length s1.pc 0 ⊆
      s1.memDomain := by
    rw [arm8Target_config, arm8Config_encode, ← st.pc]
    exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
  have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
    have hi : arm8Next^[0 + 1] ms = arm8Next ms := by
      rw [Nat.zero_add, Function.iterate_one]
    rw [hi]
    exact hq1
  refine encoderCaseStep (.jumpReg r) s1 s2 ms 0 hdom hcode ?_ ?_ hq
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hsafe0
  · intro k h1 h2
    omega


/-! ## The `loc` constructor -/


/-! ## The `moveWide` chain of the long `loc` form -/

/-- Bit `i` of the 16-bit mask `0xFFFF`. -/
theorem testBit_65535 (i : Nat) : Nat.testBit 65535 i = decide (i < 16) := by
  have h : (65535 : Nat) = 2 ^ 16 - 1 := by norm_num
  rw [h, Nat.testBit_two_pow_sub_one]

/-- Insert the 16-bit chunk `hw` of `l` into the `hw`-th 16-bit field of `x`. -/
def locTemp (x l : BitVec 64) (hw : Nat) : BitVec 64 :=
  (x &&& ~~~((BitVec.ofNat 64 0xFFFF) <<< (hw * 16))) |||
    (((l >>> (hw * 16)) &&& (BitVec.ofNat 64 0xFFFF)) <<< (hw * 16))

/-- The four-chunk insertion reproduces `l`. -/
theorem locTemp_chain (x l : BitVec 64) :
    locTemp (locTemp (locTemp (locTemp x l 0) l 1) l 2) l 3 = l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [locTemp, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, BitVec.getLsbD_ushiftRight, testBit_65535]
  interval_cases i <;> simp

/-- The `moveWide` immediate `imm16 <<< shift` with only the low 16 bits set. -/
theorem ofNat_mod_65536 (x : BitVec 64) :
    BitVec.ofNat 64 (x.toNat % 65536) = x &&& (BitVec.ofNat 64 0xFFFF) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : (65535 : Nat) % 2 ^ 64 = 2 ^ 16 - 1 := by
    rw [show (65535 : Nat) = 2 ^ 16 - 1 by norm_num]
    exact Nat.mod_eq_of_lt (by norm_num)
  rw [h1, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (show x.toNat % 65536 < 2 ^ 64 from
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))]

/-- A `moveWide .k` step writes one 16-bit chunk of `l` into `x`. -/
theorem moveWideK_eq_locTemp (x l : BitVec 64) (hw : Nat) :
    ((x &&& ~~~((BitVec.ofNat 64 0xFFFF) <<< (hw * 16))) |||
      (BitVec.ofNat 64 ((l >>> (hw * 16)).toNat % 65536) <<< (hw * 16))) = locTemp x l hw := by
  simp only [locTemp]
  rw [ofNat_mod_65536 (l >>> (hw * 16))]

/-- Executing a `moveWide .k`. -/
theorem execInsn_moveWideK (s : Arm8State) (hw imm16 rd : Nat) :
    execInsn s (.moveWide .k hw imm16 rd) =
      writeReg s rd ((readReg s rd &&& ~~~((BitVec.ofNat 64 0xFFFF) <<< (hw * 16))) |||
        (BitVec.ofNat 64 imm16 <<< (hw * 16))) := rfl

/-- Executing the untaken, flag-preserving `addSubShiftedRegister`. -/
theorem execInsn_addSubShiftedRegister_lsl0 (s : Arm8State) (rm rn rd : Nat) :
    execInsn s (.addSubShiftedRegister false false .lsl rm 0 rn rd) =
      writeReg s rd (readReg s rn + readReg s rm) := by
  simp only [execInsn, shiftValue, Nat.zero_mod, BitVec.shiftLeft_zero]
  rfl

/-- A `moveWide .k` immediate write, in the shape `execInsn` uses. -/
def wstep (x : BitVec 64) (hw imm16 : Nat) : BitVec 64 :=
  (x &&& ~~~((BitVec.ofNat 64 0xFFFF) <<< (hw * 16))) ||| (BitVec.ofNat 64 imm16 <<< (hw * 16))

/-- `wstep` at the chunk of the lowering reproduces `locTemp`. -/
theorem wstep_eq_locTemp (x l : BitVec 64) (hw imm16 : Nat)
    (h : imm16 = (l >>> (hw * 16)).toNat % 65536) : wstep x hw imm16 = locTemp x l hw := by
  subst h
  exact moveWideK_eq_locTemp x l hw

/-- The first `wstep` of the lowering, in the shape the lowering emits. -/
theorem wstep_zero (x l : BitVec 64) : wstep x 0 (l.toNat % 65536) = locTemp x l 0 := by
  simp only [wstep, locTemp, Nat.zero_mul, BitVec.ushiftRight_zero, ofNat_mod_65536]

/-- The empty byte list sits anywhere. -/
theorem bytesInMemoryHOL_nil (pc : BitVec 64) (m : BitVec 64 → BitVec 8)
    (dm : BitVec 64 → Prop) : bytesInMemoryHOL pc [] m dm = True := rfl

/-- Splitting one four-byte instruction off a `bytesInMemoryHOL` fact. -/
theorem bytesInMemory_cons (i : Insn) (rest : List Insn) (pc : BitVec 64)
    (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop) :
    bytesInMemoryHOL pc ((i :: rest).flatMap encodeBytes) m dm ↔
      bytesInMemoryHOL pc (encodeBytes i) m dm ∧
        bytesInMemoryHOL (pc + 4) (rest.flatMap encodeBytes) m dm := by
  rw [List.flatMap_cons, bytesInMemory_append, encodeBytes_length]
  rfl

/-- The last four-byte instruction of a byte region. -/
theorem bytesInMemory_one (i : Insn) (pc : BitVec 64)
    (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop) :
    bytesInMemoryHOL pc ([i].flatMap encodeBytes) m dm ↔
      bytesInMemoryHOL pc (encodeBytes i) m dm := by
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Peeling six four-byte instructions off a `bytesInMemoryHOL` fact. -/
theorem bytesInMemory_six (pc : BitVec 64) (i1 i2 i3 i4 i5 i6 : Insn)
    (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop) :
    bytesInMemoryHOL pc ([i1, i2, i3, i4, i5, i6].flatMap encodeBytes) m dm ↔
      bytesInMemoryHOL pc (encodeBytes i1) m dm ∧
      bytesInMemoryHOL (pc + 4) (encodeBytes i2) m dm ∧
      bytesInMemoryHOL (pc + 4 + 4) (encodeBytes i3) m dm ∧
      bytesInMemoryHOL (pc + 4 + 4 + 4) (encodeBytes i4) m dm ∧
      bytesInMemoryHOL (pc + 4 + 4 + 4 + 4) (encodeBytes i5) m dm ∧
      bytesInMemoryHOL (pc + 4 + 4 + 4 + 4 + 4) (encodeBytes i6) m dm := by
  rw [bytesInMemory_cons, bytesInMemory_cons, bytesInMemory_cons, bytesInMemory_cons,
    bytesInMemory_cons, bytesInMemory_one]

/-- The `i`-th of six consecutive words is a valid aligned code address. -/
theorem mem_allPcs_six (p : BitVec 64) (i : Nat) (hi : i < 6) :
    p + BitVec.ofNat 64 (i * 4) ∈ allPcs 24 p 2 := by
  rw [allPcs_eq]
  refine ⟨i, ?_, rfl⟩
  have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
  omega

/-- A state whose four PC bytes are in `d` and whose decoded instruction touches
no memory is step-safe. -/
theorem stepSafe_of_encode (s : Arm8State) (d : BitVec 64 → Prop) (i : Insn) (w : W)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes i) s.mem d)
    (henc : encodeInsn i = some w)
    (hdec : decodeInsn32 (w.setWidth 32) = some i)
    (htouch : arm8Touched s i = []) : StepSafe d s := by
  have hdom := bytesInMemoryHOL_domain hbytes
  have hlen := encodeBytes_length i
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [arm8FetchBytes, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa using hdom 0 (by rw [hlen]; omega)
    · simpa using hdom 1 (by rw [hlen]; omega)
    · simpa using hdom 2 (by rw [hlen]; omega)
    · simpa using hdom 3 (by rw [hlen]; omega)
  · intro j hj x hx
    rw [fetchWord_encodeBytes s i w d henc hbytes, hdec] at hj
    cases hj
    rw [htouch] at hx
    simp at hx

/-- The six-instruction `loc` lowering. -/
theorem arm8Enc_loc_long (r : Nat) (l : BitVec 64) (h : fitsSigned 20 l = false) :
    arm8Enc (.loc r l) = [.address false 0 r,
      .moveWide .k 0 (l.toNat % 65536) temp,
      .moveWide .k 1 ((l >>> 16).toNat % 65536) temp,
      .moveWide .k 2 ((l >>> 32).toNat % 65536) temp,
      .moveWide .k 3 ((l >>> 48).toNat % 65536) temp,
      .addSubShiftedRegister false false .lsl temp 0 r r].flatMap encodeBytes := by
  simp [arm8Enc, arm8Ast, h]

/-- The one-instruction `loc` lowering. -/
theorem arm8Enc_loc_short (r : Nat) (l : BitVec 64) (h : fitsSigned 20 l = true) :
    arm8Enc (.loc r l) = encodeBytes (.address false l r) := by
  simp [arm8Enc, arm8Ast, h]

/-- The `loc` constructor of `encoder_correct arm8Target`. -/
theorem case_loc (r : Nat) (l : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.loc r l) s2 ∧ targetStateRel arm8Target s1 ms) :
    CaseGoal (.loc r l) s1 s2 ms := by
  have st := arm8Start (.loc r l) s1 s2 ms h
  have hok := st.asmOk
  simp only [asmOkExact, Bool.and_eq_true] at hok
  obtain ⟨hlt, hav, hne31⟩ := regOk_of_asm hok.1
  by_cases hfits : fitsSigned 20 l = true
  · have hlen : (arm8Enc (.loc r l)).length = 4 := by
      rw [arm8Enc_loc_short r l hfits]; exact encodeBytes_length _
    have hupd : asmUpd (.loc r l) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
      rw [← st.upd, hlen]
    have hs2pc : s2.pc = s1.pc + 4 := by
      rw [← hupd]; rfl
    have hs2mem : ∀ x, s2.mem x = s1.mem x := by
      rw [← hupd]; intro x; rfl
    have hs2dom : s2.memDomain = s1.memDomain := by
      rw [← hupd]; rfl
    have hs2regs : ∀ i, s2.regs i = (if i = r then s1.pc + l else s1.regs i) := by
      intro i
      rw [← hupd]
      simp only [asmUpd, updPc, updReg]
    have hdom : s2.memDomain = s1.memDomain := hs2dom
    have hbytes : bytesInMemoryHOL ms.pc (encodeBytes (.address false l r)) ms.mem
        s1.memDomain := by
      rw [← arm8Enc_loc_short r l hfits]; exact st.bytes
    have hnext : arm8Next ms = execInsn { ms with pc := ms.pc + 4 } (.address false l r) :=
      arm8Next_addressFalse ms s1.memDomain l r (fitsSigned20_imp_21 l hfits) hlt hbytes
    have hdom4 := bytesInMemoryHOL_domain hbytes
    have hlen4 : (encodeBytes (.address false l r)).length = 4 := encodeBytes_length _
    have hfetch : FetchSafe s1.memDomain ms := by
      intro x hx
      simp only [arm8FetchBytes, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simpa using hdom4 0 (by rw [hlen4]; omega)
      · simpa using hdom4 1 (by rw [hlen4]; omega)
      · simpa using hdom4 2 (by rw [hlen4]; omega)
      · simpa using hdom4 3 (by rw [hlen4]; omega)
    have hfetchword : fetchWord ms =
        ((fields [(1, 0), (2, l.toNat % 4), (5, 16), (19, (l >>> 2).toNat % 2 ^ 19),
          (5, r)]).setWidth 64).setWidth 32 :=
      fetchWord_encodeBytes ms (.address false l r) _ s1.memDomain
        (encodeInsn_addressFalse l r (fitsSigned20_imp_21 l hfits)) hbytes
    have hdec : decodeInsn32 (fetchWord ms) = some (.address false l r) := by
      rw [hfetchword]
      show decodeInsn ((fields [(1, 0), (2, l.toNat % 4), (5, 16),
        (19, (l >>> 2).toNat % 2 ^ 19), (5, r)]).setWidth 64) = some (.address false l r)
      exact decode_encode_addressFalse l r (fitsSigned20_imp_21 l hfits) hlt
    have hsafe0 : StepSafe s1.memDomain ms := by
      refine ⟨hfetch, ?_⟩
      intro i hi x hx
      rw [hdec] at hi
      cases hi
      simp [arm8Touched] at hx
    have hal4 : holAligned 2 (4 : BitVec 64) = true := aligned_of_mod 4 (by decide)
    have hal : holAligned 2 (ms.pc + 4) = true := by
      rw [(alignedAddSub 2 ms.pc 4 hal4).1, st.aligned]
    have hval : (ms.pc + 4 : BitVec 64) - 4 + l = ms.pc + l := by bv_omega
    have hq1 : targetStateRel arm8Target s2 (arm8Next ms) := by
      rw [hnext, execInsn_addressFalse, writeReg, ite_eq_right hne31, hval]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [arm8Target_stateOk]
        exact arm8StateOk_set _ hal st.msFailed
      · show ms.pc + 4 = s2.pc
        rw [st.pc, hs2pc]
      · intro x hx
        show ms.mem x = s2.mem x
        rw [hs2mem x]
        exact st.mem x (hs2dom ▸ hx)
      · intro i hi
        by_cases hir : i = r
        · subst i
          show (if r = r then ms.pc + l else ms.regs r) = s2.regs r
          rw [ite_eq_left rfl, hs2regs r, ite_eq_left rfl]
          exact congrArg (· + l) st.pc
        · show (if i = r then ms.pc + l else ms.regs i) = s2.regs i
          rw [ite_eq_right hir, hs2regs i, ite_eq_right hir]
          exact st.reg i hi
      · intro i hi
        simp only [arm8Target_config, arm8Config] at hi
        omega
    have hcode : allPcs (arm8Target.config.encode (.loc r l)).length s1.pc 0 ⊆
        s1.memDomain := by
      rw [arm8Target_config, arm8Config_encode, ← st.pc]
      exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
    have hq : targetStateRel arm8Target s2 (arm8Next^[0 + 1] ms) := by
      have hi : arm8Next^[0 + 1] ms = arm8Next ms := by
        rw [Nat.zero_add, Function.iterate_one]
      rw [hi]
      exact hq1
    refine encoderCaseStep (.loc r l) s1 s2 ms 0 hdom hcode ?_ ?_ hq
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      simpa using hsafe0
    · intro k h1 h2
      omega
  · -- long form: `address` clears the destination, four `moveWide`s build the
    -- offset in `temp`, and the final `addSubShiftedRegister` adds the PC.
    have hfitf : fitsSigned 20 l = false := by
      cases hh : fitsSigned 20 l with
      | false => rfl
      | true => exact absurd hh hfits
    have hb := st.bytes
    rw [arm8Enc_loc_long r l hfitf] at hb
    obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ :=
      (bytesInMemory_six ms.pc (.address false 0 r)
        (.moveWide .k 0 (l.toNat % 65536) temp)
        (.moveWide .k 1 ((l >>> 16).toNat % 65536) temp)
        (.moveWide .k 2 ((l >>> 32).toNat % 65536) temp)
        (.moveWide .k 3 ((l >>> 48).toNat % 65536) temp)
        (.addSubShiftedRegister false false .lsl temp 0 r r) ms.mem s1.memDomain).1 hb
    have hne26 : r ≠ temp := by
      intro hre
      rw [hre] at hav
      exact Bool.noConfusion hav
    have h2631 : temp ≠ 31 := by decide
    have htr : ¬(temp = r) := fun h => hne26 h.symm
    let t1 : Arm8State :=
      { ms with regs := (fun j => if j = r then ms.pc else ms.regs j), pc := ms.pc + 4 }
    let t2 : Arm8State :=
      { t1 with regs := (fun j => if j = temp then wstep (t1.regs temp) 0 (l.toNat % 65536)
          else t1.regs j), pc := t1.pc + 4 }
    let t3 : Arm8State :=
      { t2 with regs := (fun j => if j = temp then wstep (t2.regs temp) 1 ((l >>> 16).toNat % 65536)
          else t2.regs j), pc := t2.pc + 4 }
    let t4 : Arm8State :=
      { t3 with regs := (fun j => if j = temp then wstep (t3.regs temp) 2 ((l >>> 32).toNat % 65536)
          else t3.regs j), pc := t3.pc + 4 }
    let t5 : Arm8State :=
      { t4 with regs := (fun j => if j = temp then wstep (t4.regs temp) 3 ((l >>> 48).toNat % 65536)
          else t4.regs j), pc := t4.pc + 4 }
    let t6 : Arm8State :=
      { t5 with regs := (fun j => if j = r then t5.regs r + t5.regs temp else t5.regs j), pc := t5.pc + 4 }
    have hstep1 : arm8Next ms = t1 := by
      rw [arm8Next_addressFalse ms s1.memDomain 0 r (by decide) hlt hb1]
      have h0 : (ms.pc + 4 : BitVec 64) - 4 + 0 = ms.pc := by bv_omega
      simp only [execInsn_addressFalse, writeReg, ite_eq_right hne31, h0, t1]
    have hstep2 : arm8Next t1 = t2 := by
      rw [arm8Next_moveWide t1 s1.memDomain .k 0 (l.toNat % 65536) temp (by decide)
        (Nat.mod_lt _ (by decide)) (show temp < 32 by decide) hb2, execInsn_moveWideK]
      have hreg : readReg { t1 with pc := t1.pc + 4 } temp = t1.regs temp := by
        simp only [readReg, ite_eq_right h2631]
      simp only [hreg, writeReg, ite_eq_right h2631, wstep, t2]
    have hstep3 : arm8Next t2 = t3 := by
      rw [arm8Next_moveWide t2 s1.memDomain .k 1 ((l >>> 16).toNat % 65536) temp
        (by decide) (Nat.mod_lt _ (by decide)) (show temp < 32 by decide) hb3,
        execInsn_moveWideK]
      have hreg : readReg { t2 with pc := t2.pc + 4 } temp = t2.regs temp := by
        simp only [readReg, ite_eq_right h2631]
      simp only [hreg, writeReg, ite_eq_right h2631, wstep, t3]
    have hstep4 : arm8Next t3 = t4 := by
      rw [arm8Next_moveWide t3 s1.memDomain .k 2 ((l >>> 32).toNat % 65536) temp
        (by decide) (Nat.mod_lt _ (by decide)) (show temp < 32 by decide) hb4,
        execInsn_moveWideK]
      have hreg : readReg { t3 with pc := t3.pc + 4 } temp = t3.regs temp := by
        simp only [readReg, ite_eq_right h2631]
      simp only [hreg, writeReg, ite_eq_right h2631, wstep, t4]
    have hstep5 : arm8Next t4 = t5 := by
      rw [arm8Next_moveWide t4 s1.memDomain .k 3 ((l >>> 48).toNat % 65536) temp
        (by decide) (Nat.mod_lt _ (by decide)) (show temp < 32 by decide) hb5,
        execInsn_moveWideK]
      have hreg : readReg { t4 with pc := t4.pc + 4 } temp = t4.regs temp := by
        simp only [readReg, ite_eq_right h2631]
      simp only [hreg, writeReg, ite_eq_right h2631, wstep, t5]
    have hstep6 : arm8Next t5 = t6 := by
      rw [arm8Next_addSubShiftedRegister t5 s1.memDomain false false .lsl temp 0 r r
        (show temp < 32 by decide) (by decide) hlt hlt hb6,
        execInsn_addSubShiftedRegister_lsl0]
      have hreg1 : readReg { t5 with pc := t5.pc + 4 } r = t5.regs r := by
        simp only [readReg, ite_eq_right hne31]
      have hreg2 : readReg { t5 with pc := t5.pc + 4 } temp = t5.regs temp := by
        simp only [readReg, ite_eq_right h2631]
      simp only [hreg1, hreg2, writeReg, ite_eq_right hne31, t6]
    have hit1 : arm8Next^[1] ms = t1 := by
      rw [Function.iterate_one]; exact hstep1
    have hit2 : arm8Next^[2] ms = t2 := by
      rw [show (2 : Nat) = Nat.succ 1 by rfl, Function.iterate_succ_apply',
        Function.iterate_one, hstep1, hstep2]
    have hit3 : arm8Next^[3] ms = t3 := by
      rw [show (3 : Nat) = Nat.succ 2 by rfl, Function.iterate_succ_apply', hit2, hstep3]
    have hit4 : arm8Next^[4] ms = t4 := by
      rw [show (4 : Nat) = Nat.succ 3 by rfl, Function.iterate_succ_apply', hit3, hstep4]
    have hit5 : arm8Next^[5] ms = t5 := by
      rw [show (5 : Nat) = Nat.succ 4 by rfl, Function.iterate_succ_apply', hit4, hstep5]
    have hit6 : arm8Next^[6] ms = t6 := by
      rw [show (6 : Nat) = Nat.succ 5 by rfl, Function.iterate_succ_apply', hit5, hstep6]
    have hstepSafe1 : StepSafe s1.memDomain ms :=
      stepSafe_of_encode ms s1.memDomain (.address false 0 r)
        ((encodeInsn (.address false 0 r)).getD 0) hb1 rfl
        (decode_encode_addressFalse 0 r (fitsSigned20_imp_21 0 (by decide)) hlt) (by rfl)
    have hstepSafe2 : StepSafe s1.memDomain t1 :=
      stepSafe_of_encode t1 s1.memDomain (.moveWide .k 0 (l.toNat % 65536) temp)
        ((encodeInsn (.moveWide .k 0 (l.toNat % 65536) temp)).getD 0) hb2 rfl
        (decode_encode_moveWideInsn .k 0 (l.toNat % 65536) temp (by decide)
          (Nat.mod_lt _ (by decide)) (show temp < 32 by decide)) (by rfl)
    have hstepSafe3 : StepSafe s1.memDomain t2 :=
      stepSafe_of_encode t2 s1.memDomain (.moveWide .k 1 ((l >>> 16).toNat % 65536) temp)
        ((encodeInsn (.moveWide .k 1 ((l >>> 16).toNat % 65536) temp)).getD 0) hb3 rfl
        (decode_encode_moveWideInsn .k 1 ((l >>> 16).toNat % 65536) temp (by decide)
          (Nat.mod_lt _ (by decide)) (show temp < 32 by decide)) (by rfl)
    have hstepSafe4 : StepSafe s1.memDomain t3 :=
      stepSafe_of_encode t3 s1.memDomain (.moveWide .k 2 ((l >>> 32).toNat % 65536) temp)
        ((encodeInsn (.moveWide .k 2 ((l >>> 32).toNat % 65536) temp)).getD 0) hb4 rfl
        (decode_encode_moveWideInsn .k 2 ((l >>> 32).toNat % 65536) temp (by decide)
          (Nat.mod_lt _ (by decide)) (show temp < 32 by decide)) (by rfl)
    have hstepSafe5 : StepSafe s1.memDomain t4 :=
      stepSafe_of_encode t4 s1.memDomain (.moveWide .k 3 ((l >>> 48).toNat % 65536) temp)
        ((encodeInsn (.moveWide .k 3 ((l >>> 48).toNat % 65536) temp)).getD 0) hb5 rfl
        (decode_encode_moveWideInsn .k 3 ((l >>> 48).toNat % 65536) temp (by decide)
          (Nat.mod_lt _ (by decide)) (show temp < 32 by decide)) (by rfl)
    have hstepSafe6 : StepSafe s1.memDomain t5 :=
      stepSafe_of_encode t5 s1.memDomain
        (.addSubShiftedRegister false false .lsl temp 0 r r)
        ((encodeInsn (.addSubShiftedRegister false false .lsl temp 0 r r)).getD 0) hb6 rfl
        (decode_encode_addSubShiftedRegisterInsn false false .lsl temp 0 r r
          (show temp < 32 by decide) (by decide) hlt hlt) (by rfl)
    have halw : holAligned 2 (4 : BitVec 64) = true := aligned_of_mod 4 (by decide)
    have hpc1 : t1.pc = ms.pc + 4 := rfl
    have hpc2 : t2.pc = ms.pc + BitVec.ofNat 64 (2 * 4) := by
      rw [show t2.pc = t1.pc + 4 from rfl, hpc1, BitVec.add_assoc]
      rfl
    have hpc3 : t3.pc = ms.pc + BitVec.ofNat 64 (3 * 4) := by
      rw [show t3.pc = t2.pc + 4 from rfl, hpc2, BitVec.add_assoc]
      rfl
    have hpc4 : t4.pc = ms.pc + BitVec.ofNat 64 (4 * 4) := by
      rw [show t4.pc = t3.pc + 4 from rfl, hpc3, BitVec.add_assoc]
      rfl
    have hpc5 : t5.pc = ms.pc + BitVec.ofNat 64 (5 * 4) := by
      rw [show t5.pc = t4.pc + 4 from rfl, hpc4, BitVec.add_assoc]
      rfl
    have hpc6 : t6.pc = ms.pc + BitVec.ofNat 64 (6 * 4) := by
      rw [show t6.pc = t5.pc + 4 from rfl, hpc5, BitVec.add_assoc]
      rfl
    have hal1 : holAligned 2 t1.pc = true := by
      rw [show t1.pc = ms.pc + 4 from rfl, (alignedAddSub 2 ms.pc 4 halw).1, st.aligned]
    have hal2 : holAligned 2 t2.pc = true := by
      rw [show t2.pc = t1.pc + 4 from rfl, (alignedAddSub 2 t1.pc 4 halw).1, hal1]
    have hal3 : holAligned 2 t3.pc = true := by
      rw [show t3.pc = t2.pc + 4 from rfl, (alignedAddSub 2 t2.pc 4 halw).1, hal2]
    have hal4 : holAligned 2 t4.pc = true := by
      rw [show t4.pc = t3.pc + 4 from rfl, (alignedAddSub 2 t3.pc 4 halw).1, hal3]
    have hal5 : holAligned 2 t5.pc = true := by
      rw [show t5.pc = t4.pc + 4 from rfl, (alignedAddSub 2 t4.pc 4 halw).1, hal4]
    have hal6 : holAligned 2 t6.pc = true := by
      rw [show t6.pc = t5.pc + 4 from rfl, (alignedAddSub 2 t5.pc 4 halw).1, hal5]
    have hm1 : ∀ j, t1.mem j = ms.mem j := fun _ => rfl
    have hm2 : ∀ j, t2.mem j = ms.mem j := fun _ => rfl
    have hm3 : ∀ j, t3.mem j = ms.mem j := fun _ => rfl
    have hm4 : ∀ j, t4.mem j = ms.mem j := fun _ => rfl
    have hm5 : ∀ j, t5.mem j = ms.mem j := fun _ => rfl
    have hm6 : ∀ j, t6.mem j = ms.mem j := fun _ => rfl
    have hf1 : t1.failed = ms.failed := rfl
    have hf2 : t2.failed = ms.failed := rfl
    have hf3 : t3.failed = ms.failed := rfl
    have hf4 : t4.failed = ms.failed := rfl
    have hf5 : t5.failed = ms.failed := rfl
    have hf6 : t6.failed = ms.failed := rfl
    have hreg1 : t1.regs r = ms.pc := by simp only [t1, ite_true]
    have hreg2 : t2.regs r = t1.regs r := by simp only [t2, ite_eq_right hne26]
    have hreg3 : t3.regs r = t2.regs r := by simp only [t3, ite_eq_right hne26]
    have hreg4 : t4.regs r = t3.regs r := by simp only [t4, ite_eq_right hne26]
    have hreg5 : t5.regs r = t4.regs r := by simp only [t5, ite_eq_right hne26]
    have hq1 : t1.regs temp = ms.regs temp := by simp only [t1, ite_eq_right htr]
    have hq2 : t2.regs temp = wstep (t1.regs temp) 0 (l.toNat % 65536) := by
      simp only [t2, ite_true]
    have hq3 : t3.regs temp = wstep (t2.regs temp) 1 ((l >>> 16).toNat % 65536) := by
      simp only [t3, ite_true]
    have hq4 : t4.regs temp = wstep (t3.regs temp) 2 ((l >>> 32).toNat % 65536) := by
      simp only [t4, ite_true]
    have hq5 : t5.regs temp = wstep (t4.regs temp) 3 ((l >>> 48).toNat % 65536) := by
      simp only [t5, ite_true]
    have hq6 : t6.regs r = t5.regs r + t5.regs temp := by simp only [t6, ite_true]
    have hrep : ∀ j, j ≠ r → t6.regs j = t5.regs j := by intro j hj; simp only [t6, ite_eq_right hj]
    have ht5 : t5.regs temp = l := by
      rw [hq5, hq4, hq3, hq2, hq1, wstep_zero, wstep_eq_locTemp _ l 1 _ (by rfl),
        wstep_eq_locTemp _ l 2 _ (by rfl), wstep_eq_locTemp _ l 3 _ (by rfl)]
      exact locTemp_chain _ l
    have ht5r : t5.regs r = ms.pc := by rw [hreg5, hreg4, hreg3, hreg2, hreg1]
    have hlen : (arm8Enc (.loc r l)).length = 24 := by
      rw [arm8Enc_loc_long r l hfitf]
      simp [encodeBytes_length]
    have hupd : asmUpd (.loc r l) (s1.pc + BitVec.ofNat 64 24) s1 = s2 := by
      rw [← st.upd, hlen]
    have hs2pc : s2.pc = s1.pc + 24 := by
      rw [← hupd]; rfl
    have hs2mem : ∀ x, s2.mem x = s1.mem x := by
      rw [← hupd]; intro x; rfl
    have hs2dom : s2.memDomain = s1.memDomain := by
      rw [← hupd]; rfl
    have hs2regs : ∀ i, s2.regs i = (if i = r then s1.pc + l else s1.regs i) := by
      intro i
      rw [← hupd]
      simp only [asmUpd, updPc, updReg]
    have hcode : allPcs (arm8Target.config.encode (.loc r l)).length s1.pc 0 ⊆
        s1.memDomain := by
      rw [arm8Target_config, arm8Config_encode, ← st.pc]
      exact bytesInMemory_allPcs _ _ _ _ 0 st.bytes
    have hx1 : ∀ j, j ≠ r → t1.regs j = ms.regs j := by
      intro j hj; simp only [t1, ite_eq_right hj]
    have hx2 : ∀ j, j ≠ temp → t2.regs j = t1.regs j := by
      intro j hj; simp only [t2, ite_eq_right hj]
    have hx3 : ∀ j, j ≠ temp → t3.regs j = t2.regs j := by
      intro j hj; simp only [t3, ite_eq_right hj]
    have hx4 : ∀ j, j ≠ temp → t4.regs j = t3.regs j := by
      intro j hj; simp only [t4, ite_eq_right hj]
    have hx5 : ∀ j, j ≠ temp → t5.regs j = t4.regs j := by
      intro j hj; simp only [t5, ite_eq_right hj]
    have hne26i : ∀ i, arm8Config.avoidRegs.contains i = false → i ≠ temp := by
      intro i hi h
      subst h
      have hc : arm8Config.avoidRegs.contains temp = true := by decide
      rw [hc] at hi
      exact Bool.noConfusion hi
    have hqregs : t6.regs r = ms.pc + l := by rw [hq6, ht5r, ht5]
    have hqfinal : targetStateRel arm8Target s2 (arm8Next^[6] ms) := by
      rw [hit6]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [arm8Target_stateOk]
        exact arm8StateOk_set _ hal6 st.msFailed
      · show t6.pc = s2.pc
        rw [hpc6, st.pc, hs2pc]
        bv_omega
      · intro x hx
        show t6.mem x = s2.mem x
        rw [hm6 x, hs2mem x]
        exact st.mem x (hs2dom ▸ hx)
      · intro i hi
        have har := hi.2
        by_cases hir : i = r
        · subst i
          show t6.regs r = s2.regs r
          rw [hqregs, hs2regs r, ite_eq_left rfl]
          exact congrArg (· + l) st.pc
        · have hit' : i ≠ temp := hne26i i har
          show t6.regs i = s2.regs i
          rw [hrep i hir, hx5 i hit', hx4 i hit', hx3 i hit', hx2 i hit', hx1 i hir,
            hs2regs i, ite_eq_right hir]
          exact st.reg i hi
      · intro i hi
        simp only [arm8Target_config, arm8Config] at hi
        omega
    have hq : targetStateRel arm8Target s2 (arm8Next^[5 + 1] ms) := hqfinal
    refine encoderCaseStep (.loc r l) s1 s2 ms 5 hs2dom hcode ?_ ?_ hq
    · intro k hk
      interval_cases k
      · simpa using hstepSafe1
      · rw [hit1]; exact hstepSafe2
      · rw [hit2]; exact hstepSafe3
      · rw [hit3]; exact hstepSafe4
      · rw [hit4]; exact hstepSafe5
      · rw [hit5]; exact hstepSafe6
    · intro k h1 h2
      interval_cases k
      · rw [hit1]
        refine ⟨?_, ?_, ?_⟩
        · exact arm8StateOk_set _ hal1 st.msFailed
        · intro pc hpc
          exact hm1 pc
        · rw [hpc1, st.pc, arm8Target_config, arm8Config_encode, hlen]
          exact mem_allPcs_six s1.pc 1 (by norm_num)
      · rw [hit2]
        refine ⟨?_, ?_, ?_⟩
        · exact arm8StateOk_set _ hal2 st.msFailed
        · intro pc hpc
          exact hm2 pc
        · rw [hpc2, st.pc, arm8Target_config, arm8Config_encode, hlen]
          exact mem_allPcs_six s1.pc 2 (by norm_num)
      · rw [hit3]
        refine ⟨?_, ?_, ?_⟩
        · exact arm8StateOk_set _ hal3 st.msFailed
        · intro pc hpc
          exact hm3 pc
        · rw [hpc3, st.pc, arm8Target_config, arm8Config_encode, hlen]
          exact mem_allPcs_six s1.pc 3 (by norm_num)
      · rw [hit4]
        refine ⟨?_, ?_, ?_⟩
        · exact arm8StateOk_set _ hal4 st.msFailed
        · intro pc hpc
          exact hm4 pc
        · rw [hpc4, st.pc, arm8Target_config, arm8Config_encode, hlen]
          exact mem_allPcs_six s1.pc 4 (by norm_num)
      · rw [hit5]
        refine ⟨?_, ?_, ?_⟩
        · exact arm8StateOk_set _ hal5 st.msFailed
        · intro pc hpc
          exact hm5 pc
        · rw [hpc5, st.pc, arm8Target_config, arm8Config_encode, hlen]
          exact mem_allPcs_six s1.pc 5 (by norm_num)

end Flapjack.Compiler.Encoders.Arm8
