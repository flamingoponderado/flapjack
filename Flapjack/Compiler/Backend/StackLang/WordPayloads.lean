import Flapjack.Stack

/-!
# Production StackProg word-payload boundary

Flapjack-only carrier infrastructure: this is not a HOL datatype or theorem
port. Only fields whose production type is the shared word parameter are
converted. Register indices, labels, counts, String names and the Nat-only
`const`/`arith`/`shift` macros are retained, not silently reduced modulo the
machine width. Those macros still need a separate reviewed projection before
the executed StackNames route can use the canonical program codec.

The two directions distinguish an exact width-typed image roundtrip from a
Nat roundtrip that needs an explicit bound on every word-valued payload.
Neither law establishes executable transition equivalence or full compiler
routing. In particular this module does not approve shMem store aliases,
FFI/Install length renaming or arbitrary String-to-mlstring inputs.
-/
namespace Flapjack.Compiler.Backend.StackLang.WordPayloads
open Flapjack

def mapRegImm (f : α → β) : WordRegImm α → WordRegImm β
  | .imm value => .imm (f value)
  | .reg register => .reg register

def regImmValues : WordRegImm α → List α
  | .imm value => [value]
  | .reg _ => []

def mapArith (f : α → β) : WordArith α → WordArith β
  | .longMul a b c d => .longMul a b c d
  | .longDiv a b c d e => .longDiv a b c d e
  | .addCarry a b c d e => .addCarry a b c d e
  | .cakeAddCarry a b c d => .cakeAddCarry a b c d
  | .addOverflow a b c d => .addOverflow a b c d
  | .subOverflow a b c d => .subOverflow a b c d
  | .div a b c => .div a b c
  | .binOp op a b right => .binOp op a b (mapRegImm f right)
  | .shift op a b right => .shift op a b (mapRegImm f right)

def arithValues : WordArith α → List α
  | .binOp _ _ _ right | .shift _ _ _ right => regImmValues right
  | _ => []

def mapInst (f : α → β) : WordInst α → WordInst β
  | .const r value => .const r (f value)
  | .arith op => .arith (mapArith f op)
  | .mem op r address => .mem op r address
  | .memOffset op r address offset => .memOffset op r address (f offset)

def instValues : WordInst α → List α
  | .const _ value | .memOffset _ _ _ value => [value]
  | .arith op => arithValues op
  | .mem _ _ _ => []

def mapProg (f : α → β) : StackProg α → StackProg β
  | .skip  => .skip 
  | .const r value => .const r value
  | .shMem op r address => .shMem op r address
  | .get r store => .get r store
  | .set store r => .set store r
  | .arith op r s t => .arith op r s t
  | .shift op r s t => .shift op r s t
  | .opCurrHeap op r s => .opCurrHeap op r s
  | .jumpLower r s label => .jumpLower r s label
  | .alloc n => .alloc n
  | .storeConsts r s stub => .storeConsts r s stub
  | .codeBufferWrite r s => .codeBufferWrite r s
  | .dataBufferWrite r s => .dataBufferWrite r s
  | .raise r => .raise r
  | .return r => .return r
  | .break l => .break l
  | .continue l => .continue l
  | .ffi f r1 r2 r3 r4 r5 => .ffi f r1 r2 r3 r4 r5
  | .tick  => .tick 
  | .locValue r l e => .locValue r l e
  | .install r1 r2 r3 r4 r5 => .install r1 r2 r3 r4 r5
  | .rawCall l => .rawCall l
  | .stackAlloc n => .stackAlloc n
  | .stackFree n => .stackFree n
  | .stackStore r offset => .stackStore r offset
  | .stackStoreAny r s => .stackStoreAny r s
  | .stackLoad r offset => .stackLoad r offset
  | .stackLoadAny r s => .stackLoadAny r s
  | .stackGetSize r => .stackGetSize r
  | .stackSetSize r => .stackSetSize r
  | .bitmapLoad r s => .bitmapLoad r s
  | .halt r => .halt r
  | .inst instruction => .inst (mapInst f instruction)
  | .shMemOffset op r address offset => .shMemOffset op r address (f offset)
  | .seq first second => .seq (mapProg f first) (mapProg f second)
  | .ite op r right first second =>
      .ite op r (mapRegImm f right) (mapProg f first) (mapProg f second)
  | .loop body => .loop (mapProg f body)
  | .call returns target handler =>
      .call
        (match returns with
         | none => none
         | some (p, link, l1, l2) => some (mapProg f p, link, l1, l2))
        target
        (match handler with
         | none => none
         | some (p, l1, l2) => some (mapProg f p, l1, l2))

/-- Enumerate exactly the shared word-valued fields; macro Nats are excluded. -/
def values : StackProg α → List α
  | .inst instruction => instValues instruction
  | .shMemOffset _ _ _ offset => [offset]
  | .seq first second => values first ++ values second
  | .ite _ _ right first second => regImmValues right ++ values first ++ values second
  | .loop body => values body
  | .call returns _ handler =>
      (match returns with
       | none => []
       | some (p, _, _, _) => values p) ++
      (match handler with
       | none => []
       | some (p, _, _) => values p)
  | _ => []

theorem mapRegImm_inverseOn (f : α → β) (g : β → α) (operand : WordRegImm α)
    (h : ∀ x ∈ regImmValues operand, g (f x) = x) :
    mapRegImm g (mapRegImm f operand) = operand := by
  cases operand <;> simp_all [mapRegImm, regImmValues]

theorem mapArith_inverseOn (f : α → β) (g : β → α) (operation : WordArith α)
    (h : ∀ x ∈ arithValues operation, g (f x) = x) :
    mapArith g (mapArith f operation) = operation := by
  cases operation <;> simp_all [mapArith, arithValues, mapRegImm_inverseOn]

theorem mapInst_inverseOn (f : α → β) (g : β → α) (instruction : WordInst α)
    (h : ∀ x ∈ instValues instruction, g (f x) = x) :
    mapInst g (mapInst f instruction) = instruction := by
  cases instruction <;> simp_all [mapInst, instValues, mapArith_inverseOn]

/-- Invert only with pointwise evidence for the actual word payloads. -/
theorem mapProg_inverseOn (f : α → β) (g : β → α) (program : StackProg α)
    (h : ∀ x ∈ values program, g (f x) = x) :
    mapProg g (mapProg f program) = program := by
  cases program with
  | inst instruction =>
      simp [mapProg, mapInst_inverseOn f g instruction h]
  | shMemOffset op r address offset =>
      have ho := h offset (by simp [values])
      simp [mapProg, ho]
  | seq first second =>
      have hf : ∀ x ∈ values first, g (f x) = x :=
        fun x hx => h x (by simp [values, hx])
      have hs : ∀ x ∈ values second, g (f x) = x :=
        fun x hx => h x (by simp [values, hx])
      simp [mapProg, mapProg_inverseOn f g first hf, mapProg_inverseOn f g second hs]
  | ite op r right first second =>
      have hr : ∀ x ∈ regImmValues right, g (f x) = x :=
        fun x hx => h x (by simp [values, hx])
      have hf : ∀ x ∈ values first, g (f x) = x :=
        fun x hx => h x (by simp [values, hx])
      have hs : ∀ x ∈ values second, g (f x) = x :=
        fun x hx => h x (by simp [values, hx])
      simp [mapProg, mapRegImm_inverseOn f g right hr,
        mapProg_inverseOn f g first hf, mapProg_inverseOn f g second hs]
  | loop body =>
      simp [mapProg, mapProg_inverseOn f g body h]
  | call returns target handler =>
      rcases hr : returns with _ | ⟨p, link, l1, l2⟩ <;>
        rcases hh : handler with _ | ⟨q, l3, l4⟩
      · simp [mapProg]
      · have hq : ∀ x ∈ values q, g (f x) = x :=
          fun x hx => h x (by simp [values, hr, hh, hx])
        simp [mapProg, mapProg_inverseOn f g q hq]
      · have hp : ∀ x ∈ values p, g (f x) = x :=
          fun x hx => h x (by simp [values, hr, hh, hx])
        simp [mapProg, mapProg_inverseOn f g p hp]
      · have hp : ∀ x ∈ values p, g (f x) = x :=
          fun x hx => h x (by simp [values, hr, hh, hx])
        have hq : ∀ x ∈ values q, g (f x) = x :=
          fun x hx => h x (by simp [values, hr, hh, hx])
        simp [mapProg, mapProg_inverseOn f g p hp, mapProg_inverseOn f g q hq]
  | _ => rfl
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hr]
    try rw [hh]
    simp <;> omega

theorem regImmValues_mapRegImm (f : α → β) (operand : WordRegImm α) :
    regImmValues (mapRegImm f operand) = (regImmValues operand).map f := by
  cases operand <;> rfl

theorem arithValues_mapArith (f : α → β) (operation : WordArith α) :
    arithValues (mapArith f operation) = (arithValues operation).map f := by
  cases operation <;> simp [mapArith, arithValues, regImmValues_mapRegImm]

theorem instValues_mapInst (f : α → β) (instruction : WordInst α) :
    instValues (mapInst f instruction) = (instValues instruction).map f := by
  cases instruction <;> simp [mapInst, instValues, arithValues_mapArith]

/-- No shared word payload is omitted by the traversal or numeric invariant. -/
theorem values_mapProg (f : α → β) (program : StackProg α) :
    values (mapProg f program) = (values program).map f := by
  cases program with
  | inst instruction => simp [mapProg, values, instValues_mapInst]
  | seq first second =>
      simp [mapProg, values, values_mapProg f first, values_mapProg f second]
  | ite op r right first second =>
      simp [mapProg, values, regImmValues_mapRegImm,
        values_mapProg f first, values_mapProg f second]
  | loop body => simp [mapProg, values, values_mapProg f body]
  | call returns target handler =>
      rcases hr : returns with _ | ⟨p, link, l1, l2⟩ <;>
        rcases hh : handler with _ | ⟨q, l3, l4⟩
      · simp [mapProg, values]
      · simp [mapProg, values, values_mapProg f q]
      · simp [mapProg, values, values_mapProg f p]
      · simp [mapProg, values, values_mapProg f p, values_mapProg f q]
  | _ => rfl
termination_by sizeOf program
decreasing_by all_goals simp_wf <;> simp_all <;> omega

/-- Lift word-valued Nat fields exactly as the executed Lab operand boundary
reduces words; all other Nat fields and production macros remain unchanged. -/
def natToWords (width : Nat) : StackProg Nat → StackProg (BitVec width) :=
  mapProg (BitVec.ofNat width)

def wordsToNat : StackProg (BitVec width) → StackProg Nat := mapProg BitVec.toNat

/-- Exact width-typed source image; no bound premise is needed. -/
theorem natToWords_wordsToNat (program : StackProg (BitVec width)) :
    natToWords width (wordsToNat program) = program :=
  mapProg_inverseOn BitVec.toNat (BitVec.ofNat width) program
    (fun x _ => by simp)

/-- Actual numeric obligations on every shared word payload, not an assumed
codec equality or target run. Nat-only macro fields are not covered. -/
def Bounded (width : Nat) (program : StackProg Nat) : Prop :=
  ∀ value ∈ values program, value < 2 ^ width

theorem wordsToNat_natToWords (program : StackProg Nat) (h : Bounded width program) :
    wordsToNat (natToWords width program) = program := by
  apply mapProg_inverseOn
  intro x hx
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h x hx)]

/-- The width-typed source supplies every numeric bound after toNat projection. -/
theorem bounded_wordsToNat (program : StackProg (BitVec width)) :
    Bounded width (wordsToNat program) := by
  intro value hv
  rw [wordsToNat, values_mapProg] at hv
  rcases List.mem_map.mp hv with ⟨word, _, rfl⟩
  exact word.isLt

end Flapjack.Compiler.Backend.StackLang.WordPayloads
