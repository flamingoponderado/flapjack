import Flapjack.Pancake.LoopToWord.WordExpCarrierCodec
import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.WordLang

/-!
# Exact WordLang-to-production Word program carrier projection

The executed backend consumes `WordProg`; the reviewed HOL-shaped `compHOL`
returns `WordLangProgHOL`. This module projects the common RISC-V subset at a
fixed machine width. It rejects HOL constructors absent from the production
carrier (`Inst Skip` and FP instructions) rather
than silently erasing them. Spt cutsets are enumerated with `fromNumSetHOL`.
FFI names project with `MlString.toStringOfBytes`; the reverse `ofString`
round-trip is total on this projected String. An arbitrary production String
round-trips through `ofString` only when its characters are byte-ranged, so
production-String-to-HOL use still needs that boundary premise. The
fixed-width production route uses this projection only after the source
encoder's FFI byte-range guard succeeds.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Flapjack-only carrier adapter (there is no HOL declaration for conversion
between these two Lean datatype instances). Decode a HOL wordLang arithmetic
instruction into the production RISC-V carrier, retaining all eight native
arithmetic constructors and their positional registers. -/
def wordLangArithFromHOL {width : Nat} :
    WordLangArith (BitVec width) → Option (WordArith (BitVec width))
  | .binop operator destination source right =>
      some (.binOp operator destination source right)
  | .shift operator destination source right =>
      some (.shift operator destination source right)
  | .div destination dividend divisor => some (.div destination dividend divisor)
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      some (.longMul destinationLeft destinationRight sourceLeft sourceRight)
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      some (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient)
  /- HOL asm's `AddCarry r1 r2 r3 r4` consumes r2/r3 as addends and r4 as
     carry-in/output (asmSemScript.sml:95-100). `loop_to_word$comp` constructs
     it as `AddCarry scratch_res left right scratch_ci` (loop_to_wordScript.sml:74-77),
     so this projection must preserve positions 2-4. The old pattern treated
     position 2 as carry and silently emitted `(r3, r4, r2)` as the production
     addend/addend/carry tuple, causing arithmetic corpus drift. -/
  | .addCarry destination sourceLeft sourceRight carry =>
      some (.cakeAddCarry destination sourceLeft sourceRight carry)
  | .addOverflow d l r flag => some (.addOverflow d l r flag)
  | .subOverflow d l r flag => some (.subOverflow d l r flag)

/-- Flapjack-only carrier adapter (there is no HOL declaration for conversion
between these two Lean datatype instances). Decode a HOL wordLang instruction.
An exact `Inst Skip` and FP instruction have no production RISC-V `WordInst`
counterpart and are rejected. -/
def wordLangInstFromHOL {width : Nat} :
    WordLangInst (BitVec width) → Option (WordInst (BitVec width))
  | .skip => none
  | .const destination value => some (.const destination value)
  | .arith operation => (wordLangArithFromHOL operation).map .arith
  | .mem operator destination (.addr address offset) =>
      if offset = 0 then some (.mem operator destination address)
      else some (.memOffset operator destination address offset)
  | .fp _ => none

/-- Flapjack-only carrier adapter (there is no HOL declaration converting the
exact Spt carrier to this production list pair). It delegates each component
to HOL-shaped `fromNumSetHOL`, retaining its observable enumeration order. -/
def wordCutsetsFromHOL (sets : WordLangCutsetsHOL) :
    List Nat × List Nat :=
  (Flapjack.LoopToWord.fromNumSetHOL sets.1,
    Flapjack.LoopToWord.fromNumSetHOL sets.2)

/-- Flapjack-only partial carrier adapter (there is no HOL declaration for
conversion into this separate executable Lean carrier) from exact HOL
`wordLang$prog` into executed `WordProg` at one word width. Every outer program
constructor is explicit; failure propagates only from an exact instruction
with no RISC-V counterpart or a recursively nested instruction. Spt cutsets
become canonical key lists, and FFI `mlstring` names become byte-decoded Lean
`String`s. -/
def wordLangProgFromHOL {width : Nat} :
    WordLangProgHOL (BitVec width) → Option (WordProg (BitVec width))
  | .skip => some .skip
  | .move priority moves => some (.move priority moves)
  | .inst instruction => (wordLangInstFromHOL instruction).map .inst
  | .assign name value => some (.assign name (wordExpFromHOL value))
  | .get destination store => some (.get destination (wordStoreFromHOL store))
  | .set store value => some (.set (wordStoreFromHOL store) (wordExpFromHOL value))
  | .store address value => some (.store (wordExpFromHOL address) value)
  | .mustTerminate body => (wordLangProgFromHOL body).map .mustTerminate
  | .call returns target arguments handler => do
      let returns ← match returns with
        | none => pure none
        | some (values, sets, returnBody, firstLabel, secondLabel) => do
            let returnBody ← wordLangProgFromHOL returnBody
            pure (some (values, wordCutsetsFromHOL sets, returnBody,
              firstLabel, secondLabel))
      let handler ← match handler with
        | none => pure none
        | some (exception, handlerBody, firstLabel, secondLabel) => do
            let handlerBody ← wordLangProgFromHOL handlerBody
            pure (some (exception, handlerBody, firstLabel, secondLabel))
      pure (.call returns target arguments handler)
  | .seq first second => do
      let first ← wordLangProgFromHOL first
      let second ← wordLangProgFromHOL second
      pure (.seq first second)
  | .ite operator condition right thenBranch elseBranch => do
      let thenBranch ← wordLangProgFromHOL thenBranch
      let elseBranch ← wordLangProgFromHOL elseBranch
      pure (.ite operator condition right thenBranch elseBranch)
  | .loop liveIn body liveOut => do
      let body ← wordLangProgFromHOL body
      pure (.loop (Flapjack.LoopToWord.fromNumSetHOL liveIn) body
        (Flapjack.LoopToWord.fromNumSetHOL liveOut))
  | .alloc destination sets => some (.alloc destination (wordCutsetsFromHOL sets))
  | .storeConsts source bitmap codeLength dataLength constants =>
      some (.storeConsts source bitmap codeLength dataLength constants)
  | .raise exception => some (.raise exception)
  | .return label values => some (.return label values)
  | .break label => some (.break label)
  | .continue label => some (.continue label)
  | .tick => some .tick
  | .opCurrHeap operator destination source =>
      some (.opCurrHeap operator destination source)
  | .locValue destination source => some (.locValue destination source)
  | .install codeBuffer codeLength dataBuffer dataLength sets =>
      some (.install codeBuffer codeLength dataBuffer dataLength
        (wordCutsetsFromHOL sets))
  | .codeBufferWrite address value => some (.codeBufferWrite address value)
  | .dataBufferWrite address value => some (.dataBufferWrite address value)
  | .ffi function configuration configurationLength array arrayLength sets =>
      some (.ffi (toStringOfBytes function) configuration configurationLength
        array arrayLength (wordCutsetsFromHOL sets))
  | .shareInst operator name address =>
      some (.shareInst operator name (wordExpFromHOL address))
end Flapjack
