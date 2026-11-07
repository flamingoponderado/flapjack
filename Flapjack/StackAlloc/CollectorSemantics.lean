import Flapjack.StackAlloc.FrameMachine
import Flapjack.StackAlloc.BitmapSemantics

/-!
# Bounded collector machine semantics

This module begins the machine-level collector simulation layer.  The
`memcpy` loop is the smallest non-trivial collector loop: its body updates
the source, destination, and count registers and writes one word of memory.
The theorem below relates the executable bounded frame evaluator to the
corresponding iterated machine-state transition for every word count.

The evaluator simulation theorem will use this transition API together with
the explicit machine-word count bound.  Keeping the transition layer
separate makes the later proof compositional and avoids unfolding the whole
collector state at every loop iteration.
-/

namespace Flapjack.RiscV

def stackFrameMemcpyMemory [NeZero width]
    (config : StackGcConfig) : Nat → Word width → Word width →
      (Word width → Word width) → Word width → Word width
  | 0, _, _, memory, address => memory address
  | words + 1, source, destination, memory, address =>
      stackFrameMemcpyMemory config words
        (source + BitVec.ofNat width config.bytesInWord)
        (destination + BitVec.ofNat width config.bytesInWord)
        (fun current => if current = destination then memory source else memory current) address

theorem stackFrameMemcpyMemory_unchanged [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (source destination : Word width) (memory : Word width → Word width)
    (address : Word width)
    (haddress : ∀ index, index < words →
      address ≠ destination + BitVec.ofNat width
        (index * config.bytesInWord)) :
    stackFrameMemcpyMemory config words source destination memory address =
      memory address := by
  induction words generalizing source destination memory with
  | zero => rfl
  | succ words ih =>
      have hdestination : address ≠ destination := by
        intro heq
        apply haddress 0 (by omega)
        simpa using heq
      have hrest : ∀ index, index < words →
          address ≠ (destination + BitVec.ofNat width config.bytesInWord) +
            BitVec.ofNat width (index * config.bytesInWord) := by
        intro index hindex heq
        apply haddress (index + 1) (by omega)
        simpa [Nat.succ_mul, BitVec.ofNat_add, BitVec.add_assoc,
          BitVec.add_comm] using heq
      have hmemory := ih
        (source + BitVec.ofNat width config.bytesInWord)
        (destination + BitVec.ofNat width config.bytesInWord)
        (fun current => if current = destination then memory source
          else memory current) hrest
      simp [stackFrameMemcpyMemory, hmemory, hdestination]

theorem bitVec_ofNat_succ_sub_one [NeZero width] (words : Nat) :
    BitVec.ofNat width (words + 1) - BitVec.ofNat width 1 =
      BitVec.ofNat width words := by
  rw [BitVec.ofNat_sub_ofNat_of_le]
  · rfl
  · exact Nat.one_lt_two_pow (NeZero.ne width)
  · omega

theorem stackFrameMemcpyMemory_update_toNat [NeZero width]
    (source destination : Word width) (memory : Nat → Nat) :
    (fun current : Word width =>
        if current = destination then BitVec.ofNat width (memory source.toNat)
        else BitVec.ofNat width (memory current.toNat)) =
      (fun current : Word width =>
        BitVec.ofNat width
          (if current.toNat = destination.toNat then memory source.toNat
           else memory current.toNat)) := by
  funext current
  by_cases hcurrent : current = destination
  · simp [hcurrent]
  · have hcurrent' : current.toNat ≠ destination.toNat := by
      intro heq
      apply hcurrent
      exact BitVec.eq_of_toNat_eq heq
    simp [hcurrent, hcurrent']

theorem stackFrameMemcpyMemory_toNat [NeZero width]
    (config : StackGcConfig) (words : Nat)
    (source destination : Word width) (memory : Nat → Nat)
    (hmemory : ∀ address, memory address < 2 ^ width)
    (hsource : ∀ index, index ≤ words →
      source.toNat + index * config.bytesInWord < 2 ^ width)
    (hdestination : ∀ index, index ≤ words →
      destination.toNat + index * config.bytesInWord < 2 ^ width)
    (address : Word width) :
    (stackFrameMemcpyMemory config words source destination
      (fun current => BitVec.ofNat width (memory current.toNat)) address).toNat =
      (stackGcNatMemcpy config words source.toNat destination.toNat memory
        (fun _ => true)).memory address.toNat := by
  induction words generalizing source destination memory address with
  | zero =>
      simp [stackFrameMemcpyMemory, stackGcNatMemcpy,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hmemory _)]
  | succ words ih =>
      have hbytes : config.bytesInWord < 2 ^ width := by
        have h := hsource 1 (by omega)
        omega
      have hsource_add :
          (source + BitVec.ofNat width config.bytesInWord).toNat =
            source.toNat + config.bytesInWord := by
        have hsum : source.toNat + config.bytesInWord < 2 ^ width := by
          simpa using hsource 1 (by omega)
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hbytes]
        exact Nat.mod_eq_of_lt hsum
      have hdestination_add :
          (destination + BitVec.ofNat width config.bytesInWord).toNat =
            destination.toNat + config.bytesInWord := by
        have hsum : destination.toNat + config.bytesInWord < 2 ^ width := by
          simpa using hdestination 1 (by omega)
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hbytes]
        exact Nat.mod_eq_of_lt hsum
      let memory' : Nat → Nat := fun current =>
        if current = destination.toNat then memory source.toNat else memory current
      have hmemory' : ∀ current, memory' current < 2 ^ width := by
        intro current
        simp only [memory']
        split
        · exact hmemory _
        · exact hmemory _
      have hsource' : ∀ index, index ≤ words →
          (source + BitVec.ofNat width config.bytesInWord).toNat +
              index * config.bytesInWord < 2 ^ width := by
        intro index hindex
        rw [hsource_add]
        have h := hsource (index + 1) (by omega)
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      have hdestination' : ∀ index, index ≤ words →
          (destination + BitVec.ofNat width config.bytesInWord).toNat +
              index * config.bytesInWord < 2 ^ width := by
        intro index hindex
        rw [hdestination_add]
        have h := hdestination (index + 1) (by omega)
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      have hmemoryWord :
          (fun current : Word width =>
            if current = destination then
              BitVec.ofNat width (memory source.toNat)
            else BitVec.ofNat width (memory current.toNat)) =
            (fun current => BitVec.ofNat width (memory' current.toNat)) := by
        simpa [memory'] using
          stackFrameMemcpyMemory_update_toNat source destination memory
      rw [show stackFrameMemcpyMemory config (words + 1) source destination
          (fun current => BitVec.ofNat width (memory current.toNat)) address =
          stackFrameMemcpyMemory config words
            (source + BitVec.ofNat width config.bytesInWord)
            (destination + BitVec.ofNat width config.bytesInWord)
            (fun current => if current = destination then
              BitVec.ofNat width (memory source.toNat)
            else BitVec.ofNat width (memory current.toNat)) address by rfl]
      rw [hmemoryWord]
      rw [ih (source + BitVec.ofNat width config.bytesInWord)
        (destination + BitVec.ofNat width config.bytesInWord) memory'
        hmemory' hsource' hdestination' address]
      simp [stackGcNatMemcpy, memory', hsource_add, hdestination_add]

private theorem natLandFour_eq_zero_iff_testBit_two_false (value : Nat) :
    value &&& 4 = 0 ↔ value.testBit 2 = false := by
  constructor
  · intro hzero
    cases hbit : value.testBit 2 with
    | false => simp []
    | true =>
        have hmask : (4 : Nat).testBit 2 = true := by decide
        have hand : (value &&& 4).testBit 2 = true := by
          rw [Nat.testBit_and, hbit, hmask]
          decide
        simp [hzero] at hand
  · intro hbit
    have hall : ∀ index, (value &&& 4).testBit index = false := by
      intro index
      rw [Nat.testBit_and]
      by_cases hindex : index = 2
      · simp [hindex, hbit]
      · have hmask : (4 : Nat).testBit index = false := by
          have hpow : (4 : Nat) = 2 ^ 2 := by decide
          simpa [hpow] using
            (Nat.testBit_two_pow_of_ne (Ne.symm hindex))
        simp [hmask]
    by_cases hzero : value &&& 4 = 0
    · exact hzero
    · obtain ⟨index, hindex⟩ := Nat.exists_testBit_of_ne_zero hzero
      have hfalse := hall index
      simp [hindex] at hfalse

theorem stackGcNatHeaderHasCode_iff_testBit_two (header : Nat) :
    stackGcNatHeaderHasCode header = true ↔ header.testBit 2 = true := by
  unfold stackGcNatHeaderHasCode
  simp only [decide_eq_true_eq]
  rw [Nat.mod_two_eq_one_iff_testBit_zero]
  rw [show (4 : Nat) = 2 ^ 2 by decide]
  rw [Nat.testBit_div_two_pow]

theorem stackGcMachineHeaderCondition_matches_nat [NeZero width]
    (header : Word width) (hwidth : 3 ≤ width) :
    (header &&& BitVec.ofNat width 4 == 0) = true ↔
      stackGcNatHeaderHasCode header.toNat ≠ true := by
  have hmask : (BitVec.ofNat width 4).toNat = 4 := by
    simp [BitVec.toNat_ofNat]
    have hpow : 2 ^ 3 ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by decide) hwidth
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (by decide) hpow)
  have htest :
      (header &&& BitVec.ofNat width 4 == 0) = true ↔
        header.toNat.testBit 2 = false := by
    constructor
    · intro h
      have hzero : header &&& BitVec.ofNat width 4 = 0 := by
        simpa using h
      have hzero' := congrArg BitVec.toNat hzero
      apply (natLandFour_eq_zero_iff_testBit_two_false header.toNat).mp
      simpa [BitVec.toNat_and, hmask] using hzero'
    · intro h
      have hzero' :=
        (natLandFour_eq_zero_iff_testBit_two_false header.toNat).mpr h
      have hzero : header &&& BitVec.ofNat width 4 = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.toNat_and, hmask] using hzero'
      simp [hzero]
  have hcode := stackGcNatHeaderHasCode_iff_testBit_two header.toNat
  have hcodeData :
      stackGcNatHeaderHasCode header.toNat ≠ true ↔
        header.toNat.testBit 2 = false := by
    have hneq := not_congr hcode
    simpa only [Bool.eq_false_iff] using hneq
  exact htest.trans hcodeData.symm

/-! One machine transition for the header/code branch of `word_gc_move_loop`.
The data branch delegates to the already established MoveList transition API;
this branch only advances the scan pointer and is therefore a useful first
composable step for the full loop simulation. -/

def stackGcNatBitmapTableAt : List Nat → Nat → Option Nat
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: values, index + 1 => stackGcNatBitmapTableAt values index

def stackGcMachineBitmapTableMatchesNat [NeZero width] :
    List (Word width) → List Nat → Prop
  | [], [] => True
  | bitmap :: bitmaps, value :: values =>
      bitmap.toNat = value ∧
        stackGcMachineBitmapTableMatchesNat bitmaps values
  | _, _ => False

theorem stackGcMachineBitmapTableMatchesNat_lookup [NeZero width]
    (bitmaps : List (Word width)) (values : List Nat)
    (hrelation : stackGcMachineBitmapTableMatchesNat bitmaps values)
    (index : Nat) :
    (stackFrameBitmapAt bitmaps index).map BitVec.toNat =
      stackGcNatBitmapTableAt values index := by
  induction bitmaps generalizing values index with
  | nil =>
      cases values with
      | nil =>
          cases index <;> rfl
      | cons value values =>
          simp [stackGcMachineBitmapTableMatchesNat] at hrelation
  | cons bitmap bitmaps ih =>
      cases values with
      | nil =>
          simp [stackGcMachineBitmapTableMatchesNat] at hrelation
      | cons value values =>
          cases index with
          | zero =>
              simp [stackFrameBitmapAt, stackGcNatBitmapTableAt,
                hrelation.1]
          | succ index =>
              have htail :
                  stackGcMachineBitmapTableMatchesNat bitmaps values :=
                hrelation.2
              simpa [stackFrameBitmapAt, stackGcNatBitmapTableAt] using
                ih values htail index

end Flapjack.RiscV
