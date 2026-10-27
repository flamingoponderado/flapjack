import Flapjack.Compiler.Backend.DataToWord.Locations
import Flapjack.Pancake.WordLang

/-! A partial selection of data-to-word runtime stubs. -/
namespace Flapjack.Compiler.Backend.DataToWord

private def listSeq {α : Type} : List (WordLangProgHOL α) → WordLangProgHOL α
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (listSeq (y :: xs))

/-- Flapjack's partial stub lookup. It supplies only the listed stubs and
returns `none` for all others; the complete HOL `stubs` list, including
bignum code, remains unported. -/
def compileStub? {width : Nat} (location : Nat) : Option (Nat × WordLangProgHOL (BitVec width)) :=
  if location = memCopyLocation then
    some (5, .ite .test 2 (.reg 2) (.return 0 [8]) (listSeq [
      .assign 1 (.load (.var 4)),
      .assign 2 (.op .sub [.var 2, .const 4]),
      .assign 4 (.op .add [.var 4, .const (BitVec.ofNat width (width / 8))]),
      .store (.var 6) 1,
      .assign 6 (.op .add [.var 6, .const (BitVec.ofNat width (width / 8))]),
      .call none (some memCopyLocation) [0, 2, 4, 6, 8] none]))
  else if location = stringCmpLoopLocation then
    some (6, .ite .equal 6 (.imm (BitVec.ofNat width (width / 8))) (.return 0 [8, 10])
      (listSeq [
        .inst (.mem .load8 1 (.addr 2 0)),
        .inst (.mem .load8 3 (.addr 4 0)),
        .ite .notEqual 1 (.reg 3) (.return 0 [1, 3]) .skip,
        .assign 2 (.op .add [.var 2, .const 1]),
        .assign 4 (.op .add [.var 4, .const 1]),
        .assign 6 (.op .sub [.var 6, .const 1]),
        .call none (some stringCmpLoopLocation) [0, 2, 4, 6, 8, 10] none]))
  else if location = replicateLocation then
    some (5, .ite .equal 6 (.imm 0) (.return 0 [8]) (listSeq [
      .assign 2 (.op .add [.var 2, .const (BitVec.ofNat width (width / 8))]),
      .store (.var 2) 4,
      .assign 6 (.op .sub [.var 6, .const 4]),
      .call none (some replicateLocation) [0, 2, 4, 6, 8] none]))
  else if location = addLocation ∨ location = subLocation ∨ location = mulLocation ∨
      location = divLocation ∨ location = modLocation then
    let operation := if location = addLocation then 0 else if location = subLocation then 1
      else if location = mulLocation then 4 else if location = divLocation then 5 else 6
    some (3, .seq (.assign 6 (.const (BitVec.ofNat width (4 * operation))))
      (.call none (some anyArithLocation) [0, 2, 4, 6] none))
  else if location = unusedLocation then some (6, .skip)
  else if location = byteCopyNewLocation then some (4, .skip)
  else if location = dummyLocation then some (0, .skip)
  else none

end Flapjack.Compiler.Backend.DataToWord
