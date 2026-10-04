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
  | instruction => instruction


/-- Integer instruction colouring. The six memory clauses omit Load16/Store16,
which retain the whole instruction through the original catchall. The executed
instruction route uses this same generic recursion. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def applyColourInst {width : Nat} [NeZero width] (f : Nat → Nat) :
    WordLangInst (BitVec width) → WordLangInst (BitVec width) :=
  applyColourInstCore f

/-- Shared instruction-liveness recursion. This Flapjack implementation
infrastructure accepts an explicit numeric word width; the HOL port below
binds that dimension through its positive-width word carrier. -/
def getLiveInstCore {α : Type u} (_width : Nat) : WordLangInst α → NumSet → NumSet
  | .skip, live => live
  | .const r _, live => sptDelete r live
  | .arith (.binop _ r1 r2 (.reg r3)), live
  | .arith (.shift _ r1 r2 (.reg r3)), live =>
      sptInsert r2 () (sptInsert r3 () (sptDelete r1 live))
  | .arith (.binop _ r1 r2 (.imm _)), live
  | .arith (.shift _ r1 r2 (.imm _)), live => sptInsert r2 () (sptDelete r1 live)
  | .arith (.div r1 r2 r3), live => sptInsert r3 () (sptInsert r2 () (sptDelete r1 live))
  | .arith (.addCarry r1 r2 r3 r4), live =>
      sptInsert r4 () (sptInsert r3 () (sptInsert r2 () (sptDelete r1 live)))
  | .arith (.addOverflow r1 r2 r3 r4), live
  | .arith (.subOverflow r1 r2 r3 r4), live =>
      sptInsert r3 () (sptInsert r2 () (sptDelete r4 (sptDelete r1 live)))
  | .arith (.longMul r1 r2 r3 r4), live =>
      sptInsert r4 () (sptInsert r3 () (sptDelete r2 (sptDelete r1 live)))
  | .arith (.longDiv r1 r2 r3 r4 r5), live =>
      sptInsert r5 () (sptInsert r4 () (sptInsert r3 () (sptDelete r2 (sptDelete r1 live))))
  | .mem .load r (.addr a _), live
  | .mem .load32 r (.addr a _), live
  | .mem .load8 r (.addr a _), live => sptInsert a () (sptDelete r live)
  | .mem .store r (.addr a _), live
  | .mem .store32 r (.addr a _), live
  | .mem .store8 r (.addr a _), live => sptInsert a () (sptInsert r () live)
  | _, live => live

/-- Integer instruction liveness, retaining the original insertion/deletion
order. Load16/Store16 use the original catchall. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getLiveInst {width : Nat} [NeZero width] :
    WordLangInst (BitVec width) → NumSet → NumSet :=
  getLiveInstCore width

/-- Shared removal decision with an explicit numeric word dimension.
Flapjack implementation infrastructure; the tagged wrapper retains HOL's
positive-width word carrier. -/
def removeDeadInstCore {α : Type u} (_width : Nat) : WordLangInst α → NumSet → Bool
  | .skip, _ => true
  | .const r _, live => (sptLookup r live).isNone
  | .arith (.binop _ r _ _), live
  | .arith (.shift _ r _ _), live
  | .arith (.div r _ _), live => (sptLookup r live).isNone
  | .arith (.addCarry r1 _ _ r4), live
  | .arith (.addOverflow r1 _ _ r4), live
  | .arith (.subOverflow r1 _ _ r4), live =>
      (sptLookup r1 live).isNone && (sptLookup r4 live).isNone
  | .arith (.longMul r1 r2 _ _), live
  | .arith (.longDiv r1 r2 _ _ _), live =>
      (sptLookup r1 live).isNone && (sptLookup r2 live).isNone
  | .mem .load r _, live
  | .mem .load32 r _, live
  | .mem .load8 r _, live => (sptLookup r live).isNone
  | _, _ => false

/-- Exact HOL dead-instruction decision. Stores, 16-bit loads and all
unlisted operations are retained by the literal catchall clause. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def removeDeadInst {width : Nat} [NeZero width] :
    WordLangInst (BitVec width) → NumSet → Bool :=
  removeDeadInstCore width

end Flapjack.WordAlloc
