import Flapjack.Compiler.Backend.MlStringBridge
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Stack

/-!
# Production StackProg structural codec

Flapjack-only infrastructure: neither conversion has a HOL declaration.
`StackProg` is a different production datatype, not a tagged HOL port.
This codec handles its literal shared StackLang constructors at `BitVec width`.
It reuses the existing instruction codec, including its rejection of the
five-register `addCarry` and normalization of `memOffset ... 0` to `mem`.
The canonical-to-production-to-canonical law below is therefore an accepted
canonical-image law, not an unconditional production inverse.

Production-only `const`, `arith`, and `shift` macros are rejected; expanding
those macros needs its own projection proof. A zero-offset `shMem` encodes as
an address with offset zero and decodes to `shMemOffset ... 0`. Temp stores
encode only below 32. Register, label, count and stack offset Nats remain Nats;
word-valued payloads remain BitVecs. StackStore and StackLang stackStore/load
argument orders are reversed explicitly. FFI Strings are preserved by these
codecs; the separate MlString bridge supplies the byte-ranged exact image.

The executed Lab route uses `StackProg Nat`, not this width-typed image.
Its `BitVec.ofNat` boundary, macro expansion, FFI input byte range, and actual
use of `progCompHOL` remain open under the production StackNames route bead.
No transition equivalence, full-route replacement or performance exception
is claimed here. In particular, the existing production shMem store alias
adjustment and FFI/Install length renaming differences are not approved by
this carrier codec.
-/

namespace Flapjack.Compiler.Backend.StackLang
open Flapjack StackCarrier

def storeToProduction : StoreName → StackStore
  | .nextFree => .nextFree
  | .endOfHeap => .endOfHeap
  | .triggerGC => .triggerGC
  | .heapLength => .heapLength
  | .progStart => .progStart
  | .bitmapBase => .bitmapBase
  | .currHeap => .currHeap
  | .otherHeap => .otherHeap
  | .allocSize => .allocSize
  | .globals => .globals
  | .globReal => .globReal
  | .handler => .handler
  | .genStart => .genStart
  | .codeBuffer => .codeBuffer
  | .codeBufferEnd => .codeBufferEnd
  | .bitmapBuffer => .bitmapBuffer
  | .bitmapBufferEnd => .bitmapBufferEnd
  | .temp value => .temp value.toNat

def storeFromProduction : StackStore → Option StoreName
  | .nextFree => some .nextFree
  | .endOfHeap => some .endOfHeap
  | .triggerGC => some .triggerGC
  | .heapLength => some .heapLength
  | .progStart => some .progStart
  | .bitmapBase => some .bitmapBase
  | .currHeap => some .currHeap
  | .otherHeap => some .otherHeap
  | .allocSize => some .allocSize
  | .globals => some .globals
  | .globReal => some .globReal
  | .handler => some .handler
  | .genStart => some .genStart
  | .codeBuffer => some .codeBuffer
  | .codeBufferEnd => some .codeBufferEnd
  | .bitmapBuffer => some .bitmapBuffer
  | .bitmapBufferEnd => some .bitmapBufferEnd
  | .temp value => if value < 32 then some (.temp (BitVec.ofNat 5 value)) else none

theorem storeFromProduction_toProduction (store : StoreName) :
    storeFromProduction (storeToProduction store) = some store := by
  cases store <;> simp [storeFromProduction, storeToProduction]
  exact BitVec.isLt _

def progToProduction {width : Nat} : ProgW (BitVec width) → Option (StackProg (BitVec width))
  | .skip  => some (.skip )
  | .get r store => some (.get r (storeToProduction store))
  | .set store r => some (.set (storeToProduction store) r)
  | .opCurrHeap op r s => some (.opCurrHeap op r s)
  | .jumpLower r s label => some (.jumpLower r s label)
  | .alloc n => some (.alloc n)
  | .storeConsts r s stub => some (.storeConsts r s stub)
  | .raise r => some (.raise r)
  | .ret r => some (.return r)
  | .break l => some (.break l)
  | .continue l => some (.continue l)
  | .ffi f r1 r2 r3 r4 r5 => some (.ffi f r1 r2 r3 r4 r5)
  | .tick  => some (.tick )
  | .locValue r l e => some (.locValue r l e)
  | .install r1 r2 r3 r4 r5 => some (.install r1 r2 r3 r4 r5)
  | .codeBufferWrite r s => some (.codeBufferWrite r s)
  | .dataBufferWrite r s => some (.dataBufferWrite r s)
  | .rawCall l => some (.rawCall l)
  | .stackAlloc n => some (.stackAlloc n)
  | .stackFree n => some (.stackFree n)
  | .stackStore offset r => some (.stackStore r offset)
  | .stackStoreAny r s => some (.stackStoreAny r s)
  | .stackLoad offset r => some (.stackLoad r offset)
  | .stackLoadAny r s => some (.stackLoadAny r s)
  | .stackGetSize r => some (.stackGetSize r)
  | .stackSetSize r => some (.stackSetSize r)
  | .bitmapLoad r s => some (.bitmapLoad r s)
  | .halt r => some (.halt r)
  | .inst i => (wordLangInstFromHOL i).map .inst
  | .shMemOp op r (.addr address offset) => some (.shMemOffset op r address offset)
  | .seq first second => do
      let first ← progToProduction first
      let second ← progToProduction second
      pure (.seq first second)
  | .ite op r right first second => do
      let first ← progToProduction first
      let second ← progToProduction second
      pure (.ite op r right first second)
  | .loop body => (progToProduction body).map .loop
  | .call returns target handler => do
      let returns ← match returns with
        | none => pure none
        | some (p, link, l1, l2) => do
            let p ← progToProduction p
            pure (some (p, link, l1, l2))
      let handler ← match handler with
        | none => pure none
        | some (p, l1, l2) => do
            let p ← progToProduction p
            pure (some (p, l1, l2))
      pure (.call returns
        (match target with | .inl l => .label l | .inr r => .register r) handler)

def progFromProduction {width : Nat} : StackProg (BitVec width) → Option (ProgW (BitVec width))
  | .skip  => some (.skip )
  | .get r store => (storeFromProduction store).map (.get r)
  | .set store r => (storeFromProduction store).map (fun store => .set store r)
  | .opCurrHeap op r s => some (.opCurrHeap op r s)
  | .jumpLower r s label => some (.jumpLower r s label)
  | .alloc n => some (.alloc n)
  | .storeConsts r s stub => some (.storeConsts r s stub)
  | .raise r => some (.raise r)
  | .return r => some (.ret r)
  | .break l => some (.break l)
  | .continue l => some (.continue l)
  | .ffi f r1 r2 r3 r4 r5 => some (.ffi f r1 r2 r3 r4 r5)
  | .tick  => some (.tick )
  | .locValue r l e => some (.locValue r l e)
  | .install r1 r2 r3 r4 r5 => some (.install r1 r2 r3 r4 r5)
  | .codeBufferWrite r s => some (.codeBufferWrite r s)
  | .dataBufferWrite r s => some (.dataBufferWrite r s)
  | .rawCall l => some (.rawCall l)
  | .stackAlloc n => some (.stackAlloc n)
  | .stackFree n => some (.stackFree n)
  | .stackStore r offset => some (.stackStore offset r)
  | .stackStoreAny r s => some (.stackStoreAny r s)
  | .stackLoad r offset => some (.stackLoad offset r)
  | .stackLoadAny r s => some (.stackLoadAny r s)
  | .stackGetSize r => some (.stackGetSize r)
  | .stackSetSize r => some (.stackSetSize r)
  | .bitmapLoad r s => some (.bitmapLoad r s)
  | .halt r => some (.halt r)
  | .const _ _ | .arith _ _ _ _ | .shift _ _ _ _ => none
  | .inst i => (wordLangInstToHOL i).map .inst
  | .shMem op r address => some (.shMemOp op r (.addr address 0))
  | .shMemOffset op r address offset => some (.shMemOp op r (.addr address offset))
  | .seq first second => do
      let first ← progFromProduction first
      let second ← progFromProduction second
      pure (.seq first second)
  | .ite op r right first second => do
      let first ← progFromProduction first
      let second ← progFromProduction second
      pure (.ite op r right first second)
  | .loop body => (progFromProduction body).map .loop
  | .call returns target handler => do
      let returns ← match returns with
        | none => pure none
        | some (p, link, l1, l2) => do
            let p ← progFromProduction p
            pure (some (p, link, l1, l2))
      let handler ← match handler with
        | none => pure none
        | some (p, l1, l2) => do
            let p ← progFromProduction p
            pure (some (p, l1, l2))
      pure (.call returns
        (match target with | .label l => .inl l | .register r => .inr r) handler)

/-- Accepted canonical programs survive their production projection exactly.
This is a carrier law, not an evaluator simulation or a production inverse. -/
theorem progFromProduction_of_toProduction {width : Nat}
    (program : ProgW (BitVec width)) (production : StackProg (BitVec width))
    (h : progToProduction program = some production) :
    progFromProduction production = some program := by
  cases program with
  | inst instruction =>
      simp only [progToProduction, Option.map_eq_some_iff] at h
      rcases h with ⟨i, hi, rfl⟩
      simp [progFromProduction, wordLangInstToHOL_of_fromHOL instruction i hi]
  | shMemOp op r address =>
      cases address
      simp only [progToProduction, Option.some.injEq] at h
      subst production
      rfl
  | seq first second =>
      simp [progToProduction, Option.bind_eq_some_iff] at h
      rcases h with ⟨a, ha, b, hb, rfl⟩
      simp [progFromProduction, progFromProduction_of_toProduction first a ha,
        progFromProduction_of_toProduction second b hb]
  | ite op r right first second =>
      simp [progToProduction, Option.bind_eq_some_iff] at h
      rcases h with ⟨a, ha, b, hb, rfl⟩
      simp [progFromProduction, progFromProduction_of_toProduction first a ha,
        progFromProduction_of_toProduction second b hb]
  | loop body =>
      simp only [progToProduction, Option.map_eq_some_iff] at h
      rcases h with ⟨b, hb, rfl⟩
      simp [progFromProduction, progFromProduction_of_toProduction body b hb]
  | call returns target handler =>
      rcases hr : returns with _ | ⟨p, link, l1, l2⟩ <;>
        rcases hh : handler with _ | ⟨q, l3, l4⟩
      · cases target <;> simp [progToProduction, hr, hh] at h <;>
          subst production <;> rfl
      · simp [progToProduction, hr, hh, Option.bind_eq_some_iff] at h
        rcases h with ⟨c, hc, rfl⟩
        cases target <;>
          simp [progFromProduction, progFromProduction_of_toProduction q c hc]
      · simp [progToProduction, hr, hh, Option.bind_eq_some_iff] at h
        rcases h with ⟨b, hb, rfl⟩
        cases target <;>
          simp [progFromProduction, progFromProduction_of_toProduction p b hb]
      · simp [progToProduction, hr, hh, Option.bind_eq_some_iff] at h
        rcases h with ⟨b, hb, c, hc, rfl⟩
        cases target <;>
          simp [progFromProduction, progFromProduction_of_toProduction p b hb,
            progFromProduction_of_toProduction q c hc]

  | _ =>
      simp only [progToProduction, Option.some.injEq] at h
      subst production
      simp [progFromProduction, storeFromProduction_toProduction]
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hr]
    try rw [hh]
    simp <;> omega

/-- Exact shared-word/MlString image projected into the separate production AST.
Instruction rejection is inherited from the reviewed Word carrier decoder. -/
def holProgToProduction {width : Nat} [NeZero width] (program : HolProg width) :
    Option (StackProg (BitVec width)) :=
  progToProduction (holProgToProgW program)

/-- Partial structural encoding; arbitrary production String inputs are not
claimed to survive a roundtrip through HOL mlstring. -/
def productionToHolProg {width : Nat} [NeZero width]
    (program : StackProg (BitVec width)) : Option (HolProg width) :=
  (progFromProduction program).map progWToHolProg

/-- Every accepted exact canonical program preserves its entire constructor
payload, including FFI bytes and nested continuations. This is an accepted
image inverse, not an assumption or claim of successful target evaluation. -/
theorem productionToHolProg_of_holProgToProduction {width : Nat} [NeZero width]
    (program : HolProg width) (production : StackProg (BitVec width))
    (h : holProgToProduction program = some production) :
    productionToHolProg production = some program := by
  unfold holProgToProduction at h
  simp [productionToHolProg,
    progFromProduction_of_toProduction (holProgToProgW program) production h,
    progWToHolProg_holProgToProgW]

end Flapjack.Compiler.Backend.StackLang
