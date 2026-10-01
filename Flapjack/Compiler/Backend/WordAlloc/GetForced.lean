import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg

namespace Flapjack.WordAlloc

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `get_forced_def` (`word_allocScript.sml:1466-1513`): the
architecture-forced interference edges, accumulated in front of `acc`.

`Inst` adds `(r1,r3)`/`(r1,r4)` for `AddCarry` and `(r1,r3)` for
`AddOverflow`/`SubOverflow` on MIPS or RISC-V. `LongMul` adds `(r1,r2)` on
ARMv7 and otherwise `(r1,r3)`/`(r1,r4)` on ARMv8, RISC-V or Ag32. Each pair is
omitted when its two registers are equal. `FPMovToReg r1 r2 d` and
`FPMovFromReg d r1 r2` add `(r1,r2)` when `dimindex (:'a) = 32` (`width = 32`)
and `r1 ≠ r2`. `MustTerminate` and `Loop` recurse on the body. `Seq` and `If`
fold right to left. A returning `Call` folds the handler program (if any) after
the return handler. Every other program, including `Call NONE`, returns `acc`.

The sole carrier translation is HOL's type-indexed `'a word` and
`'a asm_config` to `BitVec width` and `AsmConfigExact width`, with HOL's
positive dimension discharged by `[NeZero width]`. This proof-side port does
not replace the executed RISC-V `get_forced` traversal yet. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_forced_def"
  (words_as_type_indexed_bitvec)]
def getForced {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    WordLangProgHOL (BitVec width) → List (Nat × Nat) → List (Nat × Nat)
  | .inst i, acc =>
      match i with
      | .arith (.addCarry r1 _ r3 r4) =>
          if c.isa = .mips ∨ c.isa = .riscv then
            (if r1 = r3 then [] else [(r1, r3)]) ++
            (if r1 = r4 then [] else [(r1, r4)]) ++ acc
          else acc
      | .arith (.addOverflow r1 _ r3 _) =>
          if c.isa = .mips ∨ c.isa = .riscv then
            (if r1 = r3 then [] else [(r1, r3)]) ++ acc
          else acc
      | .arith (.subOverflow r1 _ r3 _) =>
          if c.isa = .mips ∨ c.isa = .riscv then
            (if r1 = r3 then [] else [(r1, r3)]) ++ acc
          else acc
      | .arith (.longMul r1 r2 r3 r4) =>
          if c.isa = .armv7 then
            (if r1 = r2 then [] else [(r1, r2)]) ++ acc
          else if c.isa = .armv8 ∨ c.isa = .riscv ∨ c.isa = .ag32 then
            (if r1 = r3 then [] else [(r1, r3)]) ++
            (if r1 = r4 then [] else [(r1, r4)]) ++ acc
          else acc
      | .fp (.fpMovToReg r1 r2 _) =>
          (if width = 32 ∧ r1 ≠ r2 then [(r1, r2)] else []) ++ acc
      | .fp (.fpMovFromReg _ r1 r2) =>
          (if width = 32 ∧ r1 ≠ r2 then [(r1, r2)] else []) ++ acc
      | _ => acc
  | .mustTerminate s1, acc => getForced c s1 acc
  | .seq s1 s2, acc => getForced c s1 (getForced c s2 acc)
  | .ite _ _ _ e2 e3, acc => getForced c e2 (getForced c e3 acc)
  | .call (some (_, _, retHandler, _, _)) _ _ h, acc =>
      match h with
      | none => getForced c retHandler acc
      | some (_, prog, _, _) => getForced c prog (getForced c retHandler acc)
  | .loop _ body _, acc => getForced c body acc
  | _, acc => acc
termination_by program _ => sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.WordAlloc
