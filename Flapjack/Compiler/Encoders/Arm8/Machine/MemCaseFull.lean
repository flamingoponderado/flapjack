/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.MemCase

/-!
# The remaining ARM8 memory instruction cases of `encoder_correct`

`Machine/MemCase.lean` proves the byte-sized forms (`case_load8`,
`case_store8`) and the generic composition lemmas `case_memLoadOne`,
`case_memStoreOne`, `case_memLoadTwo` and `case_memStoreTwo`.  This file
completes the memory group of `encoder_correct arm8Target` with the word-,
half-word- and word-half-sized forms (`load`, `load16`, `load32` and the three
stores), i.e. the `loadStoreAst` sizes `3`, `1` and `2`.

The lowering of `loadStoreAst` at size `s` has these shapes:

* `fitsSigned 9 off` and `off.msb = true`: one signed load/store (the lowering
  clears the unsigned bit);
* `fitsSigned 9 off` and `off.msb = false`: one load/store with the unsigned
  bit set.  When the offset is its own scaled form the encoder emits the
  twelve-bit unsigned form, and `encodeBytes_loadStoreImmediate_flag` covers
  the other (still singly-instruction) offsets, whose encoding falls back to
  the signed form;
* `¬fitsSigned 9 off` and `off` its own scaled form: one unsigned load/store
  (the scaled form reaches offsets up to `4095 * 2 ^ s`);
* `¬fitsSigned 9 off` and `off.msb = true`: `off` is below `-256`, so the
  lowering puts `-off - 0x100` in the temporary register `26` and then
  loads/stores at offset `-0x100`;
* `¬fitsSigned 9 off`, `off.msb = false` and `off` not its own scaled form:
  `off` is above `255`, so the lowering adds `off - 0xFF` to the base and then
  loads/stores at offset `0xFF`.

The offset window of `asm_ok` (`[-4351, 4350]`, `memOffset_of_asm`) keeps both
immediates of the two-instruction forms in `[0, 4095]`; the temporary register
is in `arm8Config.avoidRegs`.

The 16- and 32-bit forms set the `regsizeWord` field of the emitted
`loadStoreImmediate`; it is invisible to the executed transition and does not
change the emitted word of these (non-signed) loads and stores, so
`loadStoreAst_regsize` rewrites it away before the generic composition lemmas
apply.

As in the other `Machine/*Case.lean` files, this is a case split of the single
HOL theorem `arm8_encoder_correct`
(`cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml`), whose
`Inst`/`Mem` branch has no per-case declaration of its own; the module is
Flapjack infrastructure and carries no `@[hol]` tags.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Auxiliary facts -/

/-- A `Bool` that is not `true` is `false`. -/
theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

/-- A scaled offset is non-negative, for every size the lowering uses. -/
theorem scaledOff_toInt_nonneg (size : Nat) (hsize : size < 4) (off : W) :
    0 ≤ (scaledOff size off).toInt := by
  have hm : (off >>> size).toNat % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  have hp : 2 ^ size ≤ 8 := by
    have hs : size ≤ 3 := by omega
    calc 2 ^ size ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hs
      _ = 8 := by norm_num
  have hnat : (scaledOff size off).toNat ≤ 32760 := by
    rw [scaledOff, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : (off >>> size).toNat % 4096 < 2 ^ 64),
      Nat.shiftLeft_eq]
    calc ((off >>> size).toNat % 4096) * 2 ^ size % 2 ^ 64
        ≤ ((off >>> size).toNat % 4096) * 2 ^ size := Nat.mod_le _ _
      _ ≤ 4095 * 8 := Nat.mul_le_mul (by omega) hp
      _ ≤ 32760 := by norm_num
  have hmsb : (scaledOff size off).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    omega
  rw [BitVec.toInt_eq_toNat_of_msb hmsb]
  exact Int.natCast_nonneg _

/-- The addition immediate of the two-instruction form for a positive offset
above `255`. -/
theorem smallImmediate_add {off : W} (hlo : (256 : Int) ≤ off.toInt)
    (hhi : off.toInt ≤ 4350) : (off - 0xFF).toNat < 4096 := by
  have hy : ((0xFF : W)).toInt = 255 := by decide
  have hbt : (off - 0xFF).toInt = off.toInt - 255 := by
    rw [BitVec.toInt_sub, hy]
    rw [Int.bmod_eq_of_le (m := 2 ^ 64)] <;> norm_num <;> omega
  have hpos : 0 ≤ (off - 0xFF).toInt := by omega
  have hub : (off - 0xFF).toInt ≤ 4095 := by omega
  have hmsb : (off - 0xFF).msb = false := by
    cases hh : (off - 0xFF).msb with
    | false => rfl
    | true => have := BitVec.toInt_neg_of_msb_true hh; omega
  have htoNat : (off - 0xFF).toNat = ((off - 0xFF).toInt).toNat :=
    (BitVec.toNat_toInt_of_msb _ hmsb).symm
  rw [htoNat]
  have hcast : (((off - 0xFF).toInt).toNat : Int) = (off - 0xFF).toInt :=
    Int.toNat_of_nonneg hpos
  omega

/-- The subtraction immediate of the two-instruction form for a negative offset
below `-256`. -/
theorem smallImmediate_sub {off : W} (hlo : (-4351 : Int) ≤ off.toInt)
    (hhi : off.toInt ≤ -257) : (-off - 0x100).toNat < 4096 := by
  have hneg : (-off).toInt = -off.toInt := by
    rw [BitVec.toInt_neg]
    rw [Int.bmod_eq_of_le (m := 2 ^ 64)] <;> norm_num <;> omega
  have hy : ((0x100 : W)).toInt = 256 := by decide
  have hbt : (-off - 0x100).toInt = (-off).toInt - 256 := by
    rw [BitVec.toInt_sub, hy]
    rw [Int.bmod_eq_of_le (m := 2 ^ 64)] <;> norm_num <;> omega
  have hpos : 0 ≤ (-off - 0x100).toInt := by omega
  have hub : (-off - 0x100).toInt ≤ 4095 := by omega
  have hmsb : (-off - 0x100).msb = false := by
    cases hh : (-off - 0x100).msb with
    | false => rfl
    | true => have := BitVec.toInt_neg_of_msb_true hh; omega
  have htoNat : (-off - 0x100).toNat = ((-off - 0x100).toInt).toNat :=
    (BitVec.toNat_toInt_of_msb _ hmsb).symm
  rw [htoNat]
  have hcast : (((-off - 0x100).toInt).toNat : Int) = (-off - 0x100).toInt :=
    Int.toNat_of_nonneg hpos
  omega

/-! ## The shapes of `loadStoreAst` -/

/-- `loadStoreAst` takes its one-instruction branch on a signed-nine-bit offset
with a negative sign, and clears the unsigned-offset bit. -/
theorem loadStoreAst_single_msbTrue (size : Nat) (rg : Bool) (memop : MemOp)
    (dest base : Nat) (off : W) (hfits : fitsSigned 9 off = true) (hmsb : off.msb = true) :
    loadStoreAst size rg memop dest base off =
      [.loadStoreImmediate size rg memop false false off base dest] := by
  unfold loadStoreAst
  rw [hfits, hmsb]
  simp

/-- `loadStoreAst` takes its one-instruction branch on an offset that is its own
scaled form with a non-negative sign, and sets the unsigned-offset bit. -/
theorem loadStoreAst_single_scaled (size : Nat) (rg : Bool) (memop : MemOp)
    (dest base : Nat) (off : W) (hmsb : off.msb = false) (hshape : off = scaledOff size off) :
    loadStoreAst size rg memop dest base off =
      [.loadStoreImmediate size rg memop false true off base dest] := by
  have hd : decide (off ≠ scaledOff size off) = false := by
    rw [decide_eq_false_iff_not]
    exact fun h => h hshape
  simp only [loadStoreAst, scaledOff] at hd ⊢
  rw [hmsb, hd]
  simp

/-- `loadStoreAst` takes its one-instruction branch on a signed-nine-bit offset
with a non-negative sign, and sets the unsigned-offset bit.  (The encoding falls
back to the signed form unless the offset is its own scaled form; the emitted
bytes are the same either way.) -/
theorem loadStoreAst_single_msbFalse (size : Nat) (rg : Bool) (memop : MemOp)
    (dest base : Nat) (off : W) (hfits : fitsSigned 9 off = true) (hmsb : off.msb = false) :
    loadStoreAst size rg memop dest base off =
      [.loadStoreImmediate size rg memop false true off base dest] := by
  unfold loadStoreAst
  rw [hfits, hmsb]
  simp

/-- `loadStoreAst` lowers an offset that is below `-256` by a subtraction of its
excess into the temporary register. -/
theorem loadStoreAst_two_msbTrue (size : Nat) (rg : Bool) (memop : MemOp)
    (dest base : Nat) (off : W) (hfits : fitsSigned 9 off = false) (hmsb : off.msb = true) :
    loadStoreAst size rg memop dest base off =
      [.addSubImmediate true false (-off - 0x100) base temp,
        .loadStoreImmediate size rg memop false false (-0x100) temp dest] := by
  unfold loadStoreAst
  rw [hfits, hmsb]
  simp

/-- `loadStoreAst` lowers an offset that is above `255` by an addition of its
excess over `255` into the temporary register. -/
theorem loadStoreAst_two_msbFalse (size : Nat) (rg : Bool) (memop : MemOp)
    (dest base : Nat) (off : W) (hfits : fitsSigned 9 off = false) (hmsb : off.msb = false)
    (hne : off ≠ scaledOff size off) :
    loadStoreAst size rg memop dest base off =
      [.addSubImmediate false false (off - 0xFF) base temp,
        .loadStoreImmediate size rg memop false true (0xFF : W) temp dest] := by
  have hd : decide (off ≠ scaledOff size off) = true := decide_eq_true hne
  simp only [loadStoreAst, scaledOff] at hd ⊢
  rw [hfits, hmsb, hd]
  simp

/-- The `regsizeWord` field of the emitted `loadStoreImmediate`s does not change
the emitted bytes of the lowering. -/
theorem loadStoreAst_regsize (size : Nat) (memop : MemOp) (dest base : Nat) (off : W) :
    (loadStoreAst size true memop dest base off).flatMap encodeBytes =
      (loadStoreAst size false memop dest base off).flatMap encodeBytes := by
  simp only [loadStoreAst]
  split <;> simp [encodeBytes_loadStoreImmediate_regsize]

/-! ## The start facts of a memory case -/

/-- The domain facts a lowering of a load needs, from the emitted length: the
source state's bytes at the effective address are in its memory domain. -/
theorem memLoadDomain_len (op : HolMemop) (r base : Nat) (off : W) (s1 s2 : AsmState 64)
    (ms : Arm8State) (size n : Nat)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ size))
    (hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = n)
    (st : Arm8Start (.inst (.mem op r (.addr base off))) s1 s2 ms) :
    ∀ k, k < 2 ^ size → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have hupd : asmUpd (.inst (.mem op r (.addr base off)))
      (s1.pc + BitVec.ofNat 64 n) s1 = s2 := by
    rw [← st.upd, hlen]
  exact memLoadDomain op r base off s1 s2 size (s1.pc + BitVec.ofNat 64 n) hspec hupd st.be st.ok


/-! ## The `loadStoreAst` lowering of a load -/

/-- A load lowered by `loadStoreAst` at one of the sizes it uses, over any of the
`mem_op` forms whose memory count is `2 ^ size`. -/
theorem case_memLoadSpine (op : HolMemop) (r base : Nat) (off : W) (s1 s2 : AsmState 64)
    (ms : Arm8State) (size : Nat) (hsize : size < 4)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ size))
    (hast0 : arm8Enc (.inst (.mem op r (.addr base off))) =
      (loadStoreAst size false .load r base off).flatMap encodeBytes)
    (hlo : (-4351 : Int) ≤ off.toInt) (hhi : off.toInt ≤ 4350)
    (hne255 : (0xFF : W) ≠ scaledOff size (0xFF : W))
    (hne100 : (-0x100 : W) ≠ scaledOff size (-0x100 : W))
    (h : asmStep arm8Config s1 (.inst (.mem op r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem op r (.addr base off))) s1 s2 ms := by
  have st := arm8Start _ s1 s2 ms h
  -- the effective address is negative, so it is not its own scaled form
  have hneg_ne : ∀ _hmsb : off.msb = true, off ≠ scaledOff size off := by
    intro hmsb hc
    have h1 := scaledOff_toInt_nonneg size hsize off
    rw [← hc] at h1
    have h2 := BitVec.toInt_neg_of_msb_true hmsb
    omega
  by_cases hfits : fitsSigned 9 off = true
  · by_cases hmsb : off.msb = true
    · -- one signed load
      have hne := hneg_ne hmsb
      have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
          encodeBytes (.loadStoreImmediate size false .load false
            (decide (off = scaledOff size off)) off base r) := by
        rw [hast0, loadStoreAst_single_msbTrue size false .load r base off hfits hmsb,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          decide_eq_false_iff_not.mpr hne]
      have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 4 := by
        rw [hast]; exact encodeBytes_length _
      exact case_memLoadOne op r base off s1 s2 ms size hspec hsize (Or.inr hfits) hast
        (memLoadDomain_len op r base off s1 s2 ms size 4 hspec hlen st) h
    · have hmsbf : off.msb = false := bool_eq_false_of_ne_true hmsb
      by_cases hshape : off = scaledOff size off
      · -- one unsigned load
        have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
            encodeBytes (.loadStoreImmediate size false .load false
              (decide (off = scaledOff size off)) off base r) := by
          rw [hast0, loadStoreAst_single_scaled size false .load r base off hmsbf hshape,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, decide_eq_true hshape]
        have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 4 := by
          rw [hast]; exact encodeBytes_length _
        exact case_memLoadOne op r base off s1 s2 ms size hspec hsize (Or.inl hshape) hast
          (memLoadDomain_len op r base off s1 s2 ms size 4 hspec hlen st) h
      · -- one load whose encoded form is the signed one
        have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
            encodeBytes (.loadStoreImmediate size false .load false
              (decide (off = scaledOff size off)) off base r) := by
          rw [hast0, loadStoreAst_single_msbFalse size false .load r base off hfits hmsbf,
            List.flatMap_cons, List.flatMap_nil, List.append_nil,
            encodeBytes_loadStoreImmediate_flag size .load true off base r hfits hshape,
            decide_eq_false_iff_not.mpr hshape]
        have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 4 := by
          rw [hast]; exact encodeBytes_length _
        exact case_memLoadOne op r base off s1 s2 ms size hspec hsize (Or.inr hfits) hast
          (memLoadDomain_len op r base off s1 s2 ms size 4 hspec hlen st) h
  · have hfitsf : fitsSigned 9 off = false := bool_eq_false_of_ne_true hfits
    by_cases hmsb : off.msb = true
    · -- two instructions, subtraction of the excess below `-256`
      have hne := hneg_ne hmsb
      have h257 : off.toInt ≤ -257 := by
        rcases not_fitsSigned9 hfitsf with hc | hc
        · omega
        · have h3 := BitVec.toInt_neg_of_msb_true hmsb
          omega
      have himm : (-off - 0x100).toNat < 4096 := smallImmediate_sub hlo h257
      have hfitsc : fitsSigned 9 (-0x100 : W) = true :=
        fitsSigned9_of_range (by decide) (by decide)
      have haddr : ∀ x : W,
          (if false then x + (-off - 0x100) else x - (-off - 0x100)) + (-0x100) = x + off := by
        intro x
        rw [if_neg (by decide : ¬((false : Bool) = true))]
        bv_omega
      have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
          ([.addSubImmediate true false (-off - 0x100) base temp,
            .loadStoreImmediate size false .load false false (-0x100) temp r].flatMap
              encodeBytes) := by
        rw [hast0, loadStoreAst_two_msbTrue size false .load r base off hfitsf hmsb]
      have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 8 := by
        rw [hast]; simp [List.flatMap_cons, encodeBytes_length]
      exact case_memLoadTwo op r base off s1 s2 ms size false (-off - 0x100) (-0x100) hspec
        hsize himm hfitsc hne100 haddr hast
        (memLoadDomain_len op r base off s1 s2 ms size 8 hspec hlen st) h
    · have hmsbf : off.msb = false := bool_eq_false_of_ne_true hmsb
      by_cases hshape : off = scaledOff size off
      · -- one unsigned load, outside the signed nine-bit window
        have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
            encodeBytes (.loadStoreImmediate size false .load false
              (decide (off = scaledOff size off)) off base r) := by
          rw [hast0, loadStoreAst_single_scaled size false .load r base off hmsbf hshape,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, decide_eq_true hshape]
        have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 4 := by
          rw [hast]; exact encodeBytes_length _
        exact case_memLoadOne op r base off s1 s2 ms size hspec hsize (Or.inl hshape) hast
          (memLoadDomain_len op r base off s1 s2 ms size 4 hspec hlen st) h
      · -- two instructions, addition of the excess above `255`
        have h256 : (256 : Int) ≤ off.toInt := by
          rcases not_fitsSigned9 hfitsf with hc | hc
          · have h3 := BitVec.toInt_nonneg_of_msb_false hmsbf
            omega
          · omega
        have himm : (off - 0xFF).toNat < 4096 := smallImmediate_add h256 hhi
        have hfitsc : fitsSigned 9 (0xFF : W) = true :=
          fitsSigned9_of_range (by decide) (by decide)
        have haddr : ∀ x : W,
            (if true then x + (off - 0xFF) else x - (off - 0xFF)) + (0xFF : W) = x + off := by
          intro x
          rw [if_pos rfl]
          bv_omega
        have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
            ([.addSubImmediate false false (off - 0xFF) base temp,
              .loadStoreImmediate size false .load false true (0xFF : W) temp r].flatMap
                encodeBytes) := by
          rw [hast0, loadStoreAst_two_msbFalse size false .load r base off hfitsf hmsbf hshape]
        have hlen : (arm8Enc (.inst (.mem op r (.addr base off)))).length = 8 := by
          rw [hast]; simp [List.flatMap_cons, encodeBytes_length]
        exact case_memLoadTwo op r base off s1 s2 ms size true (off - 0xFF) (0xFF : W) hspec
          hsize himm hfitsc hne255 haddr hast
          (memLoadDomain_len op r base off s1 s2 ms size 8 hspec hlen st) h

/-! ## The `loadStoreAst` lowering of a store -/

/-- A store lowered by `loadStoreAst` at one of the sizes it uses, over any of
the `mem_op` forms whose memory count is `2 ^ size`. -/
theorem case_memStoreSpine (op : HolMemop) (r base : Nat) (off : W) (s1 s2 : AsmState 64)
    (ms : Arm8State) (size : Nat) (hsize : size < 4)
    (hspec : memOp (width := 64) op = memStore (width := 64) (2 ^ size))
    (hast0 : arm8Enc (.inst (.mem op r (.addr base off))) =
      (loadStoreAst size false .store r base off).flatMap encodeBytes)
    (hlo : (-4351 : Int) ≤ off.toInt) (hhi : off.toInt ≤ 4350)
    (hne255 : (0xFF : W) ≠ scaledOff size (0xFF : W))
    (hne100 : (-0x100 : W) ≠ scaledOff size (-0x100 : W))
    (h : asmStep arm8Config s1 (.inst (.mem op r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem op r (.addr base off))) s1 s2 ms := by
  have hneg_ne : ∀ _hmsb : off.msb = true, off ≠ scaledOff size off := by
    intro hmsb hc
    have h1 := scaledOff_toInt_nonneg size hsize off
    rw [← hc] at h1
    have h2 := BitVec.toInt_neg_of_msb_true hmsb
    omega
  by_cases hfits : fitsSigned 9 off = true
  · by_cases hmsb : off.msb = true
    · have hne := hneg_ne hmsb
      have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
          encodeBytes (.loadStoreImmediate size false .store false
            (decide (off = scaledOff size off)) off base r) := by
        rw [hast0, loadStoreAst_single_msbTrue size false .store r base off hfits hmsb,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          decide_eq_false_iff_not.mpr hne]
      exact case_memStoreOne op r base off s1 s2 ms size hspec hsize (Or.inr hfits) hast h
    · have hmsbf : off.msb = false := bool_eq_false_of_ne_true hmsb
      by_cases hshape : off = scaledOff size off
      · have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
            encodeBytes (.loadStoreImmediate size false .store false
              (decide (off = scaledOff size off)) off base r) := by
          rw [hast0, loadStoreAst_single_scaled size false .store r base off hmsbf hshape,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, decide_eq_true hshape]
        exact case_memStoreOne op r base off s1 s2 ms size hspec hsize (Or.inl hshape) hast h
      · have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
            encodeBytes (.loadStoreImmediate size false .store false
              (decide (off = scaledOff size off)) off base r) := by
          rw [hast0, loadStoreAst_single_msbFalse size false .store r base off hfits hmsbf,
            List.flatMap_cons, List.flatMap_nil, List.append_nil,
            encodeBytes_loadStoreImmediate_flag size .store true off base r hfits hshape,
            decide_eq_false_iff_not.mpr hshape]
        exact case_memStoreOne op r base off s1 s2 ms size hspec hsize (Or.inr hfits) hast h
  · have hfitsf : fitsSigned 9 off = false := bool_eq_false_of_ne_true hfits
    by_cases hmsb : off.msb = true
    · have hne := hneg_ne hmsb
      have h257 : off.toInt ≤ -257 := by
        rcases not_fitsSigned9 hfitsf with hc | hc
        · omega
        · have h3 := BitVec.toInt_neg_of_msb_true hmsb
          omega
      have himm : (-off - 0x100).toNat < 4096 := smallImmediate_sub hlo h257
      have hfitsc : fitsSigned 9 (-0x100 : W) = true :=
        fitsSigned9_of_range (by decide) (by decide)
      have haddr : ∀ x : W,
          (if false then x + (-off - 0x100) else x - (-off - 0x100)) + (-0x100) = x + off := by
        intro x
        rw [if_neg (by decide : ¬((false : Bool) = true))]
        bv_omega
      have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
          ([.addSubImmediate true false (-off - 0x100) base temp,
            .loadStoreImmediate size false .store false false (-0x100) temp r].flatMap
              encodeBytes) := by
        rw [hast0, loadStoreAst_two_msbTrue size false .store r base off hfitsf hmsb]
      exact case_memStoreTwo op r base off s1 s2 ms size false (-off - 0x100) (-0x100) hspec
        hsize himm hfitsc hne100 haddr hast h
    · have hmsbf : off.msb = false := bool_eq_false_of_ne_true hmsb
      by_cases hshape : off = scaledOff size off
      · have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
            encodeBytes (.loadStoreImmediate size false .store false
              (decide (off = scaledOff size off)) off base r) := by
          rw [hast0, loadStoreAst_single_scaled size false .store r base off hmsbf hshape,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, decide_eq_true hshape]
        exact case_memStoreOne op r base off s1 s2 ms size hspec hsize (Or.inl hshape) hast h
      · have h256 : (256 : Int) ≤ off.toInt := by
          rcases not_fitsSigned9 hfitsf with hc | hc
          · have h3 := BitVec.toInt_nonneg_of_msb_false hmsbf
            omega
          · omega
        have himm : (off - 0xFF).toNat < 4096 := smallImmediate_add h256 hhi
        have hfitsc : fitsSigned 9 (0xFF : W) = true :=
          fitsSigned9_of_range (by decide) (by decide)
        have haddr : ∀ x : W,
            (if true then x + (off - 0xFF) else x - (off - 0xFF)) + (0xFF : W) = x + off := by
          intro x
          rw [if_pos rfl]
          bv_omega
        have hast : arm8Enc (.inst (.mem op r (.addr base off))) =
            ([.addSubImmediate false false (off - 0xFF) base temp,
              .loadStoreImmediate size false .store false true (0xFF : W) temp r].flatMap
                encodeBytes) := by
          rw [hast0, loadStoreAst_two_msbFalse size false .store r base off hfitsf hmsbf hshape]
        exact case_memStoreTwo op r base off s1 s2 ms size true (off - 0xFF) (0xFF : W) hspec
          hsize himm hfitsc hne255 haddr hast h

/-! ## The six memory cases -/

/-- A word-sized load. -/
theorem case_load (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.mem .load r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem .load r (.addr base off))) s1 s2 ms := by
  have hast0 : arm8Enc (.inst (.mem .load r (.addr base off))) =
      (loadStoreAst 3 false .load r base off).flatMap encodeBytes := by
    simp [arm8Enc, arm8Ast, arm8Inst]
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .load r base off (by decide) (by decide) st.asmOk
  exact case_memLoadSpine .load r base off s1 s2 ms 3 (by decide) rfl hast0 hlo hhi
    (by decide) (by decide) h

/-- A word-sized store. -/
theorem case_store (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.mem .store r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem .store r (.addr base off))) s1 s2 ms := by
  have hast0 : arm8Enc (.inst (.mem .store r (.addr base off))) =
      (loadStoreAst 3 false .store r base off).flatMap encodeBytes := by
    simp [arm8Enc, arm8Ast, arm8Inst]
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .store r base off (by decide) (by decide) st.asmOk
  exact case_memStoreSpine .store r base off s1 s2 ms 3 (by decide) rfl hast0 hlo hhi
    (by decide) (by decide) h

/-- A half-word-sized load. -/
theorem case_load16 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.mem .load16 r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem .load16 r (.addr base off))) s1 s2 ms := by
  have hast0 : arm8Enc (.inst (.mem .load16 r (.addr base off))) =
      (loadStoreAst 1 false .load r base off).flatMap encodeBytes := by
    simp only [arm8Enc, arm8Ast, arm8Inst]
    exact loadStoreAst_regsize 1 .load r base off
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .load16 r base off (by decide) (by decide) st.asmOk
  exact case_memLoadSpine .load16 r base off s1 s2 ms 1 (by decide) rfl hast0 hlo hhi
    (by decide) (by decide) h

/-- A half-word-sized store. -/
theorem case_store16 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.mem .store16 r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem .store16 r (.addr base off))) s1 s2 ms := by
  have hast0 : arm8Enc (.inst (.mem .store16 r (.addr base off))) =
      (loadStoreAst 1 false .store r base off).flatMap encodeBytes := by
    simp only [arm8Enc, arm8Ast, arm8Inst]
    exact loadStoreAst_regsize 1 .store r base off
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .store16 r base off (by decide) (by decide) st.asmOk
  exact case_memStoreSpine .store16 r base off s1 s2 ms 1 (by decide) rfl hast0 hlo hhi
    (by decide) (by decide) h

/-- A word-half-sized load. -/
theorem case_load32 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.mem .load32 r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem .load32 r (.addr base off))) s1 s2 ms := by
  have hast0 : arm8Enc (.inst (.mem .load32 r (.addr base off))) =
      (loadStoreAst 2 false .load r base off).flatMap encodeBytes := by
    simp only [arm8Enc, arm8Ast, arm8Inst]
    exact loadStoreAst_regsize 2 .load r base off
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .load32 r base off (by decide) (by decide) st.asmOk
  exact case_memLoadSpine .load32 r base off s1 s2 ms 2 (by decide) rfl hast0 hlo hhi
    (by decide) (by decide) h

/-- A word-half-sized store. -/
theorem case_store32 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : Arm8State)
    (h : asmStep arm8Config s1 (.inst (.mem .store32 r (.addr base off))) s2 ∧
      targetStateRel arm8Target s1 ms) :
    CaseGoal (.inst (.mem .store32 r (.addr base off))) s1 s2 ms := by
  have hast0 : arm8Enc (.inst (.mem .store32 r (.addr base off))) =
      (loadStoreAst 2 false .store r base off).flatMap encodeBytes := by
    simp only [arm8Enc, arm8Ast, arm8Inst]
    exact loadStoreAst_regsize 2 .store r base off
  have st := arm8Start _ s1 s2 ms h
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .store32 r base off (by decide) (by decide) st.asmOk
  exact case_memStoreSpine .store32 r base off s1 s2 ms 2 (by decide) rfl hast0 hlo hhi
    (by decide) (by decide) h

end Flapjack.Compiler.Encoders.Arm8
