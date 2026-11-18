module

public import Flapjack.Compiler.Backend.DataToWord.Control

@[expose] public section

/-! The constructor-extension assignment expansion. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- Expanding the assignment dispatcher yields the original constructor-extension
    code for every argument list and configuration. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_ConsExtend_expand"
  (words_as_type_indexed_bitvec)]
theorem assignConsExtend_expand {width : Nat} [NeZero width] (conf : Config) (secn l dest tag : Nat)
    (args : List Nat) (names : Option NumSet) :
    (compileAssign conf secn l dest (.blockOp (.consExtend tag)) args names :
      WordLangProgHOL (BitVec width) × Nat) =
    match args with
      | old :: start :: len :: total :: rest =>
          match encodeHeader (width := width) conf (4 * tag) 0 with
          | none => (giveUp, l)
          | some header =>
              let names := names.getD .ln
              let bytes := (wordSemBytesInWord : BitVec width)
              let limit := min (2 ^ conf.lenSize) (2 ^ width / 16)
              let total := adjustVar total
              (wordListSeq [
                .ite .test total (.imm 1) .skip giveUp,
                .assign 1 (.var total), allocVar conf limit (sptListInsert args names),
                .assign 1 (.lookup .nextFree),
                .assign 5 (.op .or [shiftN .lsl (.var total) (width - conf.lenSize - 2), .const header]),
                .assign 7 (shiftN .lsr (.var total) 2), .assign 9 (.const (BitVec.ofNat width tag)),
                storeEach 1 (5 :: rest.map adjustVar) 0, makePtrBitsCode conf 9 7 3,
                .set .nextFree (.op .add [.var 1, .const bytes, shiftN .lsl (.var 7) (wordShiftAmount width)]),
                .assign 15 (.var (adjustVar len)),
                .assign 13 (.op .add [.var 1, .const (bytes * BitVec.ofNat width (rest.length + 1))]),
                .assign 11 (.op .add [realAddr conf (adjustVar old), .const bytes,
                  shiftVar .lsl (adjustVar start) (wordShiftAmount width - 2)]),
                .ite .test 15 (.reg 15) (.assign (adjustVar dest) (.var 3))
                  (.mustTerminate (.call (some ([adjustVar dest], adjustSets names, .skip, secn, l))
                    (some memCopyLocation) [15, 11, 13, 3] none))], l + 1)
      | _ => (.skip, l) := by
  rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
