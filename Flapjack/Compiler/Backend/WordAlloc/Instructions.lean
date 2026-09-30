import Flapjack.Pancake.WordLang

namespace Flapjack.WordAlloc

/-- Exact HOL immediate colouring: register operands are renamed and word
immediates remain unchanged. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "apply_colour_imm_def"
  (words_as_type_indexed_bitvec)]
def applyColourImm {width : Nat} [NeZero width] (f : Nat → Nat) :
    WordRegImm (BitVec width) → WordRegImm (BitVec width)
  | .reg n => .reg (f n)
  | .imm w => .imm w

/-- Shared generic immediate recursion for exact and executed colouring.
Flapjack implementation infrastructure; the tagged port keeps its word type. -/
def applyColourImmCore {α : Type u} (f : Nat → Nat) : WordRegImm α → WordRegImm α
  | .reg n => .reg (f n)
  | .imm w => .imm w

/-- Shared exact constructor recursion for instruction colouring.
Flapjack implementation infrastructure used by the executed carrier route. -/
def applyColourInstCore {α : Type u} (f : Nat → Nat) :
    WordLangInst α → WordLangInst α
  | .skip => .skip
  | .const r w => .const (f r) w
  | .arith (.binop op r1 r2 ri) => .arith (.binop op (f r1) (f r2) (applyColourImmCore f ri))
  | .arith (.shift sh r1 r2 ri) => .arith (.shift sh (f r1) (f r2) (applyColourImmCore f ri))
  | .arith (.div r1 r2 r3) => .arith (.div (f r1) (f r2) (f r3))
  | .arith (.addCarry r1 r2 r3 r4) => .arith (.addCarry (f r1) (f r2) (f r3) (f r4))
  | .arith (.addOverflow r1 r2 r3 r4) => .arith (.addOverflow (f r1) (f r2) (f r3) (f r4))
  | .arith (.subOverflow r1 r2 r3 r4) => .arith (.subOverflow (f r1) (f r2) (f r3) (f r4))
  | .arith (.longMul r1 r2 r3 r4) => .arith (.longMul (f r1) (f r2) (f r3) (f r4))
  | .arith (.longDiv r1 r2 r3 r4 r5) => .arith (.longDiv (f r1) (f r2) (f r3) (f r4) (f r5))
  | .mem .load r (.addr a w) => .mem .load (f r) (.addr (f a) w)
  | .mem .store r (.addr a w) => .mem .store (f r) (.addr (f a) w)
  | .mem .load32 r (.addr a w) => .mem .load32 (f r) (.addr (f a) w)
  | .mem .store32 r (.addr a w) => .mem .store32 (f r) (.addr (f a) w)
  | .mem .load8 r (.addr a w) => .mem .load8 (f r) (.addr (f a) w)
  | .mem .store8 r (.addr a w) => .mem .store8 (f r) (.addr (f a) w)
  | .fp (.fpLess r f1 f2) => .fp (.fpLess (f r) f1 f2)
  | .fp (.fpLessEqual r f1 f2) => .fp (.fpLessEqual (f r) f1 f2)
  | .fp (.fpEqual r f1 f2) => .fp (.fpEqual (f r) f1 f2)
  | .fp (.fpMovToReg r1 r2 d) => .fp (.fpMovToReg (f r1) (f r2) d)
  | .fp (.fpMovFromReg d r1 r2) => .fp (.fpMovFromReg d (f r1) (f r2))
  | instruction => instruction


/-- Exact HOL instruction colouring. The literal six memory clauses omit
Load16/Store16, which retain the whole instruction through HOL's catchall.
FP comparison/move integer registers alone are renamed; float registers are
unchanged. The executed instruction route uses this same generic recursion. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "apply_colour_inst_def"
  (words_as_type_indexed_bitvec)]
def applyColourInst {width : Nat} [NeZero width] (f : Nat → Nat) :
    WordLangInst (BitVec width) → WordLangInst (BitVec width) :=
  applyColourInstCore f

end Flapjack.WordAlloc
