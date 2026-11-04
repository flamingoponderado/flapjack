import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Fragment

/-! Source-shaped equations for the established data-to-word fragment. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A partial, source-shaped reconstruction of HOL `comp` on the currently
verified data-language fragment. It returns `none` for all other programs and
is not tagged as the complete HOL definition. -/
def fragmentCompile64 (conf : Config) (secn label : Nat) : DataLang.Prog → Option (WordLangProgHOL (BitVec 64) × Nat)
  | .skip => some (.skip, label)
  | .tick => some (.tick, label)
  | .move dest src => some (.move 0 [(adjustVar dest, adjustVar src)], label)
  | .return names => some (.return 0 (names.map adjustVar), label)
  | .raise name => some (.raise (adjustVar name), label)
  | .seq first second => do
      let (first', next) ← fragmentCompile64 conf secn label first
      let (second', last) ← fragmentCompile64 conf secn next second
      pure (.seq first' second', last)
  | .ifThenElse name yes no => do
      let (yes', next) ← fragmentCompile64 conf secn label yes
      let (no', last) ← fragmentCompile64 conf secn next no
      pure (.ite .equal (adjustVar name) (.imm 18) yes' no', last)
  | .assign dest (.intOp (.const i)) [] none => some (.assign (adjustVar dest) (.const (smallnum i)), label)
  | .assign dest (.intOp (.lessConstSmall n)) [src] none =>
      some (.ite .less (adjustVar src) (.imm (BitVec.ofNat 64 (4 * n)))
        (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2)), label)
  | .assign dest (.blockOp .boolNot) [src] none =>
      some (.assign (adjustVar dest) (.op .xor [.var (adjustVar src), .const 16]), label)
  | .assign dest (.blockOp (.boolTest _)) [left, right] none =>
      some (.ite .equal (adjustVar left) (.reg (adjustVar right))
        (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2)), label)
  | .assign dest (.blockOp (.elemAt index)) [src] none =>
      some (.assign (adjustVar dest) (.load (.op .add [realAddr conf (adjustVar src),
        .const (BitVec.ofNat 64 8 + BitVec.ofNat 64 8 * BitVec.ofNat 64 index)])), label)
  | .assign dest (.blockOp .lengthBlock) [src] none =>
      some (.ite .test (adjustVar src) (.imm 1) (.assign (adjustVar dest) (.const 0))
        (.assign (adjustVar dest) (shiftN .lsl (shiftN .lsr (.load (realAddr conf (adjustVar src))) (64 - conf.lenSize)) 2)), label)
  | .assign dest (.blockOp (.lenEq 0)) [src] none =>
      some (.ite .test (adjustVar src) (.imm 1)
        (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2)), label)
  | .assign dest (.blockOp (.tagLenEq tag 0)) [src] none =>
      if tag < 2 ^ 64 / 16 then
        some (.ite .equal (adjustVar src) (.imm (BitVec.ofNat 64 (16 * tag + 2)))
          (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2)), label)
      else some (.assign (adjustVar dest) (.const 2), label)
  | .assign dest (.blockOp (.tagEq tag)) [src] none =>
      if tag < 2 ^ 64 / 16 then
        some (wordListSeq [
          .assign 1 (.var (adjustVar src)),
          .ite .test (adjustVar src) (.imm 1) .skip
            (.assign 1 (.op .and [.load (realAddr conf (adjustVar src)), .const (tagMask conf ||| 2)])),
          .ite .equal 1 (.imm (BitVec.ofNat 64 (16 * tag + 2)))
            (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))], label)
      else some (.assign (adjustVar dest) (.const 2), label)
  | .assign dest (.blockOp (.cons tag)) [] none =>
      if tag < 2 ^ 64 / 16 then some (.assign (adjustVar dest) (.const (BitVec.ofNat 64 (16 * tag + 2))), label)
      else some (giveUp, label)
  | .assign dest (.label codeLabel) [] none => some (.locValue (adjustVar dest) codeLabel, label)
  | .assign dest (.globOp .globalsPtr) [] none => some (.assign (adjustVar dest) (.lookup .globals), label)
  | _ => none

/-- On the verified fragment, the independent source-shaped traversal returns
exactly the program and label emitted by the actual 64-bit compiler. -/
theorem fragmentCompile64_agrees (conf : Config) (secn : Nat) (program : DataLang.Prog)
    (fragment : VerifiedFragment program) : ∀ label,
    fragmentCompile64 conf secn label program = some (compileControl64 conf secn label program) := by
  induction fragment with
  | skip | tick | move | ret | raise | label | globalsPtr =>
    intro label
    simp [fragmentCompile64, compileControl64, compileControl?]
  | intConst dest i =>
    intro label
    simp [fragmentCompile64, compileControl64, compileControl?, smallnum_eq_inlined]
  | boolNot | boolTest | lessConst | blockEmpty | blockLength | element =>
    intro label
    simp only [fragmentCompile64, compileControl64, compileControl?, Option.getD_some]
    all_goals rfl
  | blockTagEmpty dest src tag =>
    intro label
    by_cases bound : tag < 2 ^ 64 / 16
    · simp only [fragmentCompile64, bound, ↓reduceIte, compileControl64, compileControl?, Option.getD_some]
      rfl
    · have bound' : ¬ tag < 1152921504606846976 := by simpa using bound
      simp [fragmentCompile64, bound', compileControl64, compileControl?]
  | blockTag dest src tag =>
    intro label
    by_cases bound : tag < 2 ^ 64 / 16
    · simp only [fragmentCompile64, bound, ↓reduceIte, compileControl64, compileControl?, Option.getD_some]
      rfl
    · have bound' : ¬ tag < 1152921504606846976 := by simpa using bound
      simp [fragmentCompile64, bound', compileControl64, compileControl?]
  | emptyCons dest tag bound =>
    intro label
    simp only [fragmentCompile64, bound, ↓reduceIte, compileControl64, compileControl?, Option.getD_some]
    change _ = some (if tag < 2 ^ 64 / 16 then
      (.assign (adjustVar dest) (.const (BitVec.ofNat 64 (16 * tag + 2))), label) else (giveUp, label))
    have bound' : tag < 1152921504606846976 := by simpa using bound
    simp [bound']
  | @seq first second hfirst hsecond ihFirst ihSecond =>
    intro label
    simp only [fragmentCompile64, ihFirst, ihSecond, bind, Option.bind, compileControl64_seq]
    rfl
  | @ite name yes no hy hn ihYes ihNo =>
    intro label
    simp only [fragmentCompile64, ihYes, ihNo, bind, Option.bind, compileControl64_if]
    rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
