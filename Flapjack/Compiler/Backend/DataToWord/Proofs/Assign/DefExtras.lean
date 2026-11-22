module

public import Flapjack.Compiler.Backend.DataToWord.Stubs
public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq

@[expose] public section

/-! The auxiliary definition equations `assign_def_extras` of the data-to-word
assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- HOL `assign_def_extras` (`data_to_word_assignProofScript.sml:63-72`) is the
`LIST_CONJ` of 28 theorems, in this order: `LoadWord64_def`, `WriteWord64_def`,
`BignumHalt_def`, `LoadBignum_def`, `AnyArith_code_def`, `Add_code_def`,
`Sub_code_def`, `Mul_code_def`, `Div_code_def`, `Mod_code_def`,
`Compare1_code_def`, `Compare_code_def`, `Equal1_code_def`, `Equal_code_def`,
`LongDiv1_code_def`, `LongDiv_code_def`, `ShiftVar_def`,
`generated_bignum_stubs_eq`, `DivCode_def`, `AddNumSize_def`, `AnyHeader_def`,
`WriteWord64_on_32_def`, `WriteWord32_on_32_def`, `AllocVar_def`,
`SilentFFI_def`, `WordOp64_on_32_def`, `WordShift64_on_32_def` and
`Make_ptr_bits_code_def`. The Lean statement has one conjunct per theorem in the
same order, right-nested as `LIST_CONJ` builds it.

* Each definition conjunct quantifies HOL's binders, with HOL's names and in
  HOL's order, and states the definitional equation (`eq_def`) of the tagged
  Lean port of that definition at those arguments.
* Conjunct 18 is the statement of the reviewed port
  `WordBignum.generatedBignumStubs_eq`. HOL's free variable `n` occurs only in
  that conjunct and is universally quantified there.
* The capture's only type variable is the word dimension `α`, shared by every
  conjunct; Lean shares the single positive `width`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_def_extras"
  (words_as_type_indexed_bitvec)]
theorem assignDefExtras {width : Nat} [NeZero width] :
    (∀ (c : Config) (i j : Nat), type_of% (@loadWord64.eq_def width _ c i j)) ∧
    (∀ (c : Config) (header : BitVec width) (dest i : Nat),
      type_of% (@writeWord64.eq_def width _ c header dest i)) ∧
    (∀ r : Nat, type_of% (@bignumHalt.eq_def width _ r)) ∧
    (∀ (c : Config) (header word1 k : Nat),
      type_of% (@loadBignum.eq_def width _ c header word1 k)) ∧
    (∀ c : Config, type_of% (@anyArithCode.eq_def width _ c)) ∧
    type_of% (@addCode.eq_def width _) ∧
    type_of% (@subCode.eq_def width _) ∧
    type_of% (@mulCode.eq_def width _) ∧
    type_of% (@DataToWord.divCode.eq_def width _) ∧
    type_of% (@modCode.eq_def width _) ∧
    type_of% (@compare1Code.eq_def width _) ∧
    (∀ c : Config, type_of% (@compareCode.eq_def width _ c)) ∧
    type_of% (@equal1Code.eq_def width _) ∧
    (∀ c : Config, type_of% (@equalCode.eq_def width _ c)) ∧
    (∀ c : Config, type_of% (@longDiv1Code.eq_def width _ c)) ∧
    (∀ c : Config, type_of% (@longDivCode.eq_def width _ c)) ∧
    (∀ (sh : Shift) (v n : Nat), type_of% (@shiftVar.eq_def width _ sh v n)) ∧
    (∀ n : Nat, type_of% (@WordBignum.generatedBignumStubs_eq width _ n)) ∧
    (∀ (l1 l2 n1 n2 n3 n4 n5 : Nat),
      type_of% (@WordBignum.divCode.eq_def width _ l1 l2 n1 n2 n3 n4 n5)) ∧
    (∀ (c : Config) (src : Nat), type_of% (@addNumSize.eq_def width _ c src)) ∧
    (∀ (c : Config) (r : Nat) (a : Bool) (t1 t2 t3 : BitVec 5),
      type_of% (@anyHeader.eq_def width _ c r a t1 t2 t3)) ∧
    (∀ (c : Config) (header : BitVec width) (dest i1 i2 : Nat),
      type_of% (@writeWord64On32.eq_def width _ c header dest i1 i2)) ∧
    (∀ (c : Config) (header : BitVec width) (dest i1 : Nat),
      type_of% (@writeWord32On32.eq_def width _ c header dest i1)) ∧
    (∀ (c : Config) (limit : Nat) (names : NumSet),
      type_of% (@allocVar.eq_def width _ c limit names)) ∧
    (∀ (c : Config) (n : Nat) (names : WordLangCutsetsHOL),
      type_of% (@silentFfi.eq_def width _ c n names)) ∧
    (∀ opw : BackendCommon.Opw, type_of% (@wordOp64On32.eq_def width _ opw)) ∧
    (∀ (sh : Shift) (n : Nat), type_of% (@wordShift64On32.eq_def width _ sh n)) ∧
    (∀ (c : Config) (tag len dest : Nat),
      type_of% (@makePtrBitsCode.eq_def width _ c tag len dest)) :=
  ⟨fun c i j => loadWord64.eq_def c i j,
   fun c header dest i => writeWord64.eq_def c header dest i,
   fun r => bignumHalt.eq_def r,
   fun c header word1 k => loadBignum.eq_def c header word1 k,
   fun c => anyArithCode.eq_def c,
   addCode.eq_def, subCode.eq_def, mulCode.eq_def, DataToWord.divCode.eq_def,
   modCode.eq_def, compare1Code.eq_def,
   fun c => compareCode.eq_def c,
   equal1Code.eq_def,
   fun c => equalCode.eq_def c,
   fun c => longDiv1Code.eq_def c,
   fun c => longDivCode.eq_def c,
   fun sh v n => shiftVar.eq_def sh v n,
   fun n => WordBignum.generatedBignumStubs_eq n,
   fun l1 l2 n1 n2 n3 n4 n5 => WordBignum.divCode.eq_def l1 l2 n1 n2 n3 n4 n5,
   fun c src => addNumSize.eq_def c src,
   fun c r a t1 t2 t3 => anyHeader.eq_def c r a t1 t2 t3,
   fun c header dest i1 i2 => writeWord64On32.eq_def c header dest i1 i2,
   fun c header dest i1 => writeWord32On32.eq_def c header dest i1,
   fun c limit names => allocVar.eq_def c limit names,
   fun c n names => silentFfi.eq_def c n names,
   fun opw => wordOp64On32.eq_def opw,
   fun sh n => wordShift64On32.eq_def sh n,
   fun c tag len dest => makePtrBitsCode.eq_def c tag len dest⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
