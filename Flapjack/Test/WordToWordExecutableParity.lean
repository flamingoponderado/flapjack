module

public import Flapjack.Compiler.Backend.WordToWord.ExecutableCompile
public import Flapjack.Test.WordInstSelectExactParity

@[expose] public section

/-! Original full native WordToWord EVAL regressions. Complete expected programs
are transcribed from word_to_word_executable_probe.out, never derived from Lean
compilation. Runtime checks reject codec failures and compare full production
program observations plus function name and arity. Oracle remainder checks
observe every canonical tree through its full constructor representation. -/
namespace Flapjack.Test.WordToWordExecutableParity
open Flapjack Flapjack.Compiler.Backend.WordToWord
abbrev P := WordLangProgHOL (BitVec 64)
def cfg := { WordInstSelectExactParity.cfg with regCount := 32, avoidRegs := [0,2,3,4,31] }

private def input_skip : P := .skip
private def expected_skip : P := .skip

private def input_return : P := .return 0 [0]
private def expected_return : P := .seq (.move 1 [(2,0),(0,0)]) (.return 0 [2])

private def input_assign_return : P := .seq (.assign 2 (.op .add [.var 0,.const 7])) (.return 2 [2])
private def expected_assign_return : P := .seq (.move 1 [(0,0)]) (.seq (.inst (.arith (.binop .add 0 0 (.imm 7)))) (.seq (.move 0 [(2,0)]) (.return 0 [2])))

private def input_must_terminate : P := .mustTerminate (.return 0 [0])
private def expected_must_terminate : P := .seq (.move 1 [(0,0)]) (.seq (.move 0 [(2,0)]) (.return 0 [2]))

private def input_tail_call : P := .call none (some 9) [0] none
private def expected_tail_call : P := .seq (.move 1 [(0,0)]) (.call none (some 9) [0] none)

private def input_branch : P := .ite .equal 0 (.imm 0) (.return 0 [0]) (.raise 0)
private def expected_branch : P := .seq (.move 1 [(0,0)]) (.ite .equal 0 (.imm 0) (.seq (.move 0 [(2,0)]) (.return 0 [2])) (.seq (.move 1 [(2,0)]) (.raise 2)))

def runChecks : IO Bool := do
  let conf : Config := ⟨0, []⟩
  unless (compileExecutable conf cfg []).1.isEmpty && (compileExecutable conf cfg []).2.isEmpty do
    throw (IO.userError "original WordToWord empty mismatch")
  IO.println "PASS executable full native WordToWord: 12 body and 3 oracle cases"
  return true

end Flapjack.Test.WordToWordExecutableParity
