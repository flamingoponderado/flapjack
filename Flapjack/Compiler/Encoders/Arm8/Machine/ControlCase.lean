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
  · have htoInt : v.toInt = (v.toNat : Int) := by rw [hcond, if_pos hcase]
    have hlt : v.toNat < 2 ^ (bits - 1) := by
      have h : (v.toNat : Int) ≤ (2 : Int) ^ (bits - 1) - 1 := by rw [← htoInt]; exact hhi
      omega
    have hmod : v.toNat % 2 ^ bits = v.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hmod, if_pos (by omega), htoInt]
  · have htoInt : v.toInt = (v.toNat : Int) - (2 : Int) ^ 64 := by rw [hcond, if_neg hcase]
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
    rw [hmod, if_neg hneg, htoInt, hcB, hcD]
    norm_num

/-! ## The encoder side conditions -/

/-- `decide` of an arbitrary decision procedure of `p` that returns `true` gives
`p`.  The configuration's offset bounds are decided by the projection instances
of `Int.decLe`, so the canonical `decide_eq_true_eq` does not apply. -/
theorem ofDecideTrue {p : Prop} (inst : Decidable p) (h : @decide p inst = true) : p := by
  cases inst with
  | isTrue hp => exact hp
  | isFalse _ => exact Bool.noConfusion h

/-- The `loc` offset window of `arm8Config` gives the four-byte alignment of the
offset.  It does *not* give `fitsSigned 20`: a `loc` offset outside the
twenty-bit range lowers to the five-instruction form of `arm8_ast`, which the
`loc` case splits on. -/
theorem locAligned_of_asm (l : W) (h : asmLocOffsetOkExact arm8Config l = true) :
    l.toNat % 4 = 0 := by
  simp only [asmLocOffsetOkExact, asmOffsetOkExact, arm8Config, Bool.and_eq_true] at h
  simpa [asmAligned] using h.2

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
  simp only [execInsn_branchImmediate_call, writeReg, if_neg (by decide : (30 : Nat) ≠ 31)]

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
      hpc4, if_neg (by decide : (30 : Nat) ≠ 31)]
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
        rw [hs2regs 30, if_pos rfl, st.pc]
      · show (if i = 30 then ms.pc + 4 else ms.regs i) = s2.regs i
        rw [if_neg h30, hs2regs i, if_neg h30]
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
    simp only [readReg, if_neg hne31]
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

end Flapjack.Compiler.Encoders.Arm8
