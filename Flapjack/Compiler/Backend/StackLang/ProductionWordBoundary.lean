import Flapjack.Compiler.Backend.StackLang.ProductionCodec

/-!
Flapjack-specific structural word-payload boundary, with no HOL declaration.
The executed Nat route currently converts payloads after flattening; the native
input codec needs words before flattening. This map changes only alpha-valued
payloads. Nat registers, labels, stack offsets, counts, macro constants and
String names are preserved. In particular, it does not expand macros or prove
that independent flatteners commute with this map.
-/
namespace Flapjack.Compiler.Backend.StackLang
open Flapjack
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

def mapRegImmPayloads (map : α → β) : WordRegImm α → WordRegImm β
  | .reg register => .reg register
  | .imm word => .imm (map word)

def mapArithPayloads (map : α → β) : WordArith α → WordArith β
  | .longMul a b c d => .longMul a b c d
  | .longDiv a b c d e => .longDiv a b c d e
  | .addCarry a b c d e => .addCarry a b c d e
  | .cakeAddCarry a b c d => .cakeAddCarry a b c d
  | .div a b c => .div a b c
  | .binOp op a b right => .binOp op a b (mapRegImmPayloads map right)
  | .shift op a b right => .shift op a b (mapRegImmPayloads map right)

def mapInstPayloads (map : α → β) : WordInst α → WordInst β
  | .const register word => .const register (map word)
  | .arith operation => .arith (mapArithPayloads map operation)
  | .mem op a b => .mem op a b
  | .memOffset op a b offset => .memOffset op a b (map offset)

def mapWordPayloads (map : α → β) : StackProg α → StackProg β
  | .skip => .skip
  | .const destination value => .const destination value
  | .inst instruction => .inst (mapInstPayloads map instruction)
  | .shMem operator source address => .shMem operator source address
  | .shMemOffset operator source address offset =>
      .shMemOffset operator source address (map offset)
  | .get destination store => .get destination store
  | .set store source => .set store source
  | .arith operator destination left right =>
      .arith operator destination left right
  | .shift operator destination left right =>
      .shift operator destination left right
  | .opCurrHeap operator destination source =>
      .opCurrHeap operator destination source
  | .call none target none => .call none target none
  | .call none target (some (program, exceptionLabel, handlerLabel)) =>
      .call none target
        (some (mapWordPayloads map program, exceptionLabel, handlerLabel))
  | .call (some (program, link, returnLabel, entryLabel)) target none =>
      .call (some (mapWordPayloads map program, link, returnLabel, entryLabel))
        target none
  | .call (some (program, link, returnLabel, entryLabel)) target
      (some (handlerProgram, exceptionLabel, handlerLabel)) =>
      .call (some (mapWordPayloads map program, link, returnLabel, entryLabel))
        target
        (some (mapWordPayloads map handlerProgram, exceptionLabel, handlerLabel))
  | .seq first second => .seq (mapWordPayloads map first) (mapWordPayloads map second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition (mapRegImmPayloads map right)
        (mapWordPayloads map thenBranch) (mapWordPayloads map elseBranch)
  | .loop body => .loop (mapWordPayloads map body)
  | .jumpLower register target label => .jumpLower register target label
  | .alloc words => .alloc words
  | .storeConsts source bitmap stub => .storeConsts source bitmap stub
  | .codeBufferWrite address value => .codeBufferWrite address value
  | .dataBufferWrite address value => .dataBufferWrite address value
  | .raise exception => .raise exception
  | .return value => .return value
  | .break label => .break label
  | .continue label => .continue label
  | .ffi function configuration configurationLength array arrayLength returnAddress =>
      .ffi function configuration configurationLength array arrayLength
        returnAddress
  | .tick => .tick
  | .locValue destination label entry => .locValue destination label entry
  | .install codeBuffer codeLength dataBuffer dataLength returnAddress =>
      .install codeBuffer codeLength dataBuffer dataLength
        returnAddress
  | .rawCall target => .rawCall target
  | .stackAlloc words => .stackAlloc words
  | .stackFree words => .stackFree words
  | .stackStore register offset => .stackStore register offset
  | .stackStoreAny register offsetRegister => .stackStoreAny register offsetRegister
  | .stackLoad register offset => .stackLoad register offset
  | .stackLoadAny register offsetRegister => .stackLoadAny register offsetRegister
  | .stackGetSize register => .stackGetSize register
  | .stackSetSize register => .stackSetSize register
  | .bitmapLoad destination address => .bitmapLoad destination address
  | .halt register => .halt register
termination_by program => stackMapDepth program
decreasing_by
  all_goals simp [stackMapDepth] <;> omega

/-- Complete payload functor law; no HOL original or semantic claim. -/
theorem mapRegImmPayloads_comp (f : α → β) (g : β → γ) (x : WordRegImm α) :
    mapRegImmPayloads g (mapRegImmPayloads f x) = mapRegImmPayloads (g ∘ f) x := by
  cases x <;> rfl

theorem mapArithPayloads_comp (f : α → β) (g : β → γ) (x : WordArith α) :
    mapArithPayloads g (mapArithPayloads f x) = mapArithPayloads (g ∘ f) x := by
  cases x <;> simp [mapArithPayloads, mapRegImmPayloads_comp]

theorem mapInstPayloads_comp (f : α → β) (g : β → γ) (x : WordInst α) :
    mapInstPayloads g (mapInstPayloads f x) = mapInstPayloads (g ∘ f) x := by
  cases x <;> simp [mapInstPayloads, mapArithPayloads_comp]

/-- Every recursive production constructor, including both call bodies. -/
theorem mapWordPayloads_comp (f : α → β) (g : β → γ) (program : StackProg α) :
    mapWordPayloads g (mapWordPayloads f program) = mapWordPayloads (g ∘ f) program := by
  cases program with
  | call returns target handler =>
    rcases hr : returns with _ | ⟨p, link, l1, l2⟩ <;>
      rcases hh : handler with _ | ⟨q, l3, l4⟩
    · simp only [mapWordPayloads]
    · simp only [mapWordPayloads, mapWordPayloads_comp f g q]
    · simp only [mapWordPayloads, mapWordPayloads_comp f g p]
    · simp only [mapWordPayloads, mapWordPayloads_comp f g p, mapWordPayloads_comp f g q]
  | seq first second => simp only [mapWordPayloads,
      mapWordPayloads_comp f g first, mapWordPayloads_comp f g second]
  | ite op r right first second =>
    simp only [mapWordPayloads, mapRegImmPayloads_comp,
      mapWordPayloads_comp f g first, mapWordPayloads_comp f g second]
  | loop body => simp only [mapWordPayloads, mapWordPayloads_comp f g body]
  | _ => simp only [mapWordPayloads, mapInstPayloads_comp, Function.comp_apply]
termination_by sizeOf program
decreasing_by all_goals subst_vars; decreasing_trivial

theorem mapRegImmPayloads_id (x : WordRegImm α) : mapRegImmPayloads id x = x := by
  cases x <;> rfl

theorem mapArithPayloads_id (x : WordArith α) : mapArithPayloads id x = x := by
  cases x <;> simp [mapArithPayloads, mapRegImmPayloads_id]

theorem mapInstPayloads_id (x : WordInst α) : mapInstPayloads id x = x := by
  cases x <;> simp [mapInstPayloads, mapArithPayloads_id]

/-- An arbitrary program is recovered, rather than just successful codec images. -/
theorem mapWordPayloads_id (program : StackProg α) : mapWordPayloads id program = program := by
  cases program with
  | call returns target handler =>
    rcases hr : returns with _ | ⟨p, link, l1, l2⟩ <;>
      rcases hh : handler with _ | ⟨q, l3, l4⟩
    · simp only [mapWordPayloads]
    · simp only [mapWordPayloads, mapWordPayloads_id q]
    · simp only [mapWordPayloads, mapWordPayloads_id p]
    · simp only [mapWordPayloads, mapWordPayloads_id p, mapWordPayloads_id q]
  | seq first second => simp only [mapWordPayloads,
      mapWordPayloads_id first, mapWordPayloads_id second]
  | ite op r right first second =>
    simp only [mapWordPayloads, mapRegImmPayloads_id,
      mapWordPayloads_id first, mapWordPayloads_id second]
  | loop body => simp only [mapWordPayloads, mapWordPayloads_id body]
  | _ => simp only [mapWordPayloads, mapInstPayloads_id, id_eq]
termination_by sizeOf program
decreasing_by all_goals subst_vars; decreasing_trivial

/-- Width conversion only. Macro constants and names retain their original carriers. -/
def natToWord {width : Nat} (program : StackProg Nat) : StackProg (BitVec width) :=
  mapWordPayloads (BitVec.ofNat width) program

/-- Exact normalization of alpha-valued Nat payloads; structural Nat fields
are unaffected, including the separate production-only Const macro. -/
theorem natToWord_toNat {width : Nat} (program : StackProg Nat) :
    mapWordPayloads BitVec.toNat (natToWord (width := width) program) =
      mapWordPayloads (fun n => n % 2 ^ width) program := by
  rw [natToWord, mapWordPayloads_comp]
  rfl

/-- Every typed production program embeds into the Nat payload carrier and
recovers. The unrestricted Nat reverse direction instead normalizes words. -/
theorem natToWord_of_toNat {width : Nat} (program : StackProg (BitVec width)) :
    natToWord (mapWordPayloads BitVec.toNat program) = program := by
  rw [natToWord, mapWordPayloads_comp]
  have inverse : (BitVec.ofNat width ∘ BitVec.toNat) = id := by
    funext value
    simp
  rw [inverse, mapWordPayloads_id]

/-- Check every FFI name, including both bodies of every nested call.
Flapjack-only boundary guard: native names are byte lists, not Unicode strings. -/
def byteNames (program : StackProg α) : Bool :=
  match program with
  | .ffi name _ _ _ _ _ => name.toList.all (fun c => decide (c.toNat < 256))
  | .seq p q | .ite _ _ _ p q => byteNames p && byteNames q
  | .loop p => byteNames p
  | .call ret _ handler =>
    (match ret with | none => true | some (p, _, _, _) => byteNames p) &&
    (match handler with | none => true | some (q, _, _) => byteNames q)
  | _ => true
termination_by sizeOf program
decreasing_by all_goals decreasing_trivial

/-- Partial native input boundary. Rejects non-byte names before the existing
codec can truncate them. Macro expansion and section conventions remain
separate obligations; this is not a semantic-equivalence theorem. -/
def natToHolProg {width : Nat} [NeZero width] (program : StackProg Nat) :
    Option (HolProg width) :=
  if byteNames program then productionToHolProg (natToWord program) else none

/-- A successful conversion requires the complete recursive name guard. -/
theorem natToHolProg_byteNames {width : Nat} [NeZero width]
    (program : StackProg Nat) (native : HolProg width)
    (accepted : natToHolProg program = some native) : byteNames program = true := by
  unfold natToHolProg at accepted
  split at accepted
  · assumption
  · contradiction

end Flapjack.Compiler.Backend.StackLang
