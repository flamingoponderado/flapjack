import Flapjack.Compiler.Backend.PresLang.Word
import Flapjack.Compiler.Backend.DataToWord.Stubs
import Flapjack.Compiler.Backend.RiscVConfig.Executable

/-! Prefix of `_FromList@7` after `data_to_word` in the pinned CakeML
explorer. The Lean side prints the actual configuration-dependent stub. -/
namespace Flapjack.Test.CakeWordDisplayParity
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def expectedPrefix : String :=
  "(func _FromList@7 (0 2 4 6)\n   (if (Equal 2 (Imm 0x0))\n" ++
  "      (seq\n         (6 := (Op Add (Var 6) (Const 0x2)))\n" ++
  "         (return 0 (6)))\n      (seq\n         (if (Test 2 (Imm 0x1)) skip\n" ++
  "            (seq\n               (1 := (Const 0xFFFFFFFFFFFFFFFF))\n" ++
  "               (alloc 1 ({0} {}))))\n         (1 := (Var 2))\n"

private def actual : Option String := do
  let (arity, body) ← DataToWord.compileConfiguredStub? (width := 64)
    RiscVConfig.riscvBackendConfigExecutable.dataConf DataToWord.fromListLocation
  let names := sptInsert DataToWord.fromListLocation (ofString "_FromList") .ln
  pure (String.join (PresLang.Word.functions names [(DataToWord.fromListLocation, arity, body)]))

#guard actual.any (fun output => output.startsWith expectedPrefix)

private def render (fuel : Nat) (p : WordLangProgHOL (BitVec 64)) : String :=
  String.join (displayStrTreeToStrings "" (displayToStrTree (PresLang.Word.program fuel .ln p)))

#guard render 0 .skip == "..."
#guard render 2 (.seq .skip .tick) == "(seq\n   ...)"
#guard render 3 (.seq .skip .tick) == "(seq\n   skip\n   ...)"
#guard render 3 (.call (some ([], (.ln, .ln), .skip, 3, 4)) none [] none) ==
  "(call (returning (() ({} {}) skip 3 4)) none () no_handler)"

end Flapjack.Test.CakeWordDisplayParity
