import Flapjack.Compiler.Backend.WordBignum.CompileExp
import Flapjack.Compiler.Backend.WordBignum.Mini

/-! Word-code construction helpers for the generic bignum generator. The
executed compiler still uses the captured 64-bit generated stubs. -/
namespace Flapjack.Compiler.Backend.WordBignum

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "TempIn1_def"]
def tempIn1 : WordStoreHOL := .temp 31

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "TempIn2_def"]
def tempIn2 : WordStoreHOL := .temp 30

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "TempOut_def"]
def tempOut : WordStoreHOL := .temp 29

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "SeqTemp_def"
  (words_as_type_indexed_bitvec)]
def seqTemp {width : Nat} [NeZero width] (i r : Nat) (p : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  .seq (.assign i (.lookup (.temp (BitVec.ofNat 5 r)))) p

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "SeqTempImm_def"
  (words_as_type_indexed_bitvec)]
def seqTempImm {width : Nat} [NeZero width] (i : Nat) (arg : WordRegImm (BitVec width))
    (p : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match arg with
  | .reg r => seqTemp i r p
  | .imm w => .seq (.assign i (.const w)) p

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "SeqTempImmNot_def"
  (words_as_type_indexed_bitvec)]
def seqTempImmNot {width : Nat} [NeZero width] (i : Nat) (arg : WordRegImm (BitVec width))
    (p : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match arg with
  | .reg r => seqTemp i r (.seq (.assign i (.op .xor [.var i, .const (~~~(0 : BitVec width))])) p)
  | .imm w => .seq (.assign i (.const (~~~w))) p

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "SeqIndex_def"
  (words_as_type_indexed_bitvec)]
def seqIndex {width : Nat} [NeZero width] (i r : Nat) (arr : Address)
    (p : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  let base := match arr with
    | .out => tempOut
    | .in2 => tempIn2
    | .in1 => tempIn1
  .seq (.assign i (.op .add [.lookup base,
    .shift .lsl (.lookup (.temp (BitVec.ofNat 5 r)))
      (.const (BitVec.ofNat width (wordShiftAmount width)))])) p

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "div_location_def"]
def divLocation : Nat := 23

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "DivCode_def"
  (words_as_type_indexed_bitvec)]
def divCode {width : Nat} [NeZero width] (l1 l2 n1 n2 n3 n4 n5 : Nat) :
    WordLangProgHOL (BitVec width) :=
  .mustTerminate (.seq (.call (some ([n1], (.ls (), .ln), .skip, l1, l2))
    (some divLocation) [n3, n4, n5] none) (.assign n2 (.lookup (.temp 28))))

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "LoadRegs_def"
  (words_as_type_indexed_bitvec)]
def loadRegs {width : Nat} [NeZero width] : List Nat → WordLangProgHOL (BitVec width) →
    WordLangProgHOL (BitVec width)
  | [], p => p
  | n :: ns, p => .seq (.get (n + 2) (.temp (BitVec.ofNat 5 n))) (loadRegs ns p)

@[hol "cakeml/compiler/backend/word_bignumScript.sml" "SaveRegs_def"
  (words_as_type_indexed_bitvec)]
def saveRegs {width : Nat} [NeZero width] : List Nat → WordLangProgHOL (BitVec width)
  | [] => .skip
  | n :: ns => .seq (.set (.temp (BitVec.ofNat 5 n)) (.var (n + 2))) (saveRegs ns)

end Flapjack.Compiler.Backend.WordBignum
