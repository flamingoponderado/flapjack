import Flapjack.Compiler.Backend.StackToLab.InitializedProduction
set_option maxRecDepth 4096
namespace Flapjack.Test.InitializedProduction
open Flapjack Flapjack.Compiler.Backend.StackToLab
private def observe {width : Nat} [NeZero width] (gc jump : Bool)
    (heap pointer start : Nat) (nonempty : Bool) : Option (List (Nat × Nat)) :=
  let input : List (Nat × StackProg Nat) :=
    if nonempty then [(9, .get 4 .currHeap), (9, .tick), (0, .skip)] else []
  (Flapjack.Compiler.Backend.StackToLab.InitializedProduction.compile? (width := width) jump (0, -1) gc heap pointer start
    Flapjack.Compiler.Backend.RiscVConfig.riscvNames input).map
      (fun sections => sections.map (fun s => (s.name, s.lines.length)))

/-- Forty fresh original complete initialized section name/line-count rows. -/
private def parityGuard : Bool :=
  (observe (width := 1) false false 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 1) false false 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 1) false true 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 1) false true 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 1) true false 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 1) true false 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 1) true true 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 1) true true 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 8) false false 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 8) false false 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 8) false true 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 8) false true 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 8) true false 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 8) true false 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 8) true true 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 8) true true 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 32) false false 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 32) false false 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 32) false true 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 32) false true 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 32) true false 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 32) true false 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 32) true true 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 32) true true 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 64) false false 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 64) false false 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 64) false true 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 64) false true 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 64) true false 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 64) true false 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 64) true true 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 64) true true 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 80) false false 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 80) false false 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 80) false true 0 0 6 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 80) false true 0 0 6 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 80) true false 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 80) true false 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)]) &&
  (observe (width := 80) true true 1208925819614629174706185 23 1208925819614629174706183 false == some [(0, 189), (1, 4), (2, 4)]) &&
  (observe (width := 80) true true 1208925819614629174706185 23 1208925819614629174706183 true == some [(0, 189), (1, 4), (2, 4), (9, 2), (9, 2), (0, 1)])

#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then IO.println "PASS full native initialized production boundary matches40 original section layouts"
  else IO.println "FAIL initialized production boundary"
  pure parityGuard

-- Earlier allocation must run before the whole-list native boundary.
#guard (Flapjack.Compiler.Backend.StackToLab.InitializedProduction.compile?
    (width := 64) false (0, -1) false 0 23 6
    Flapjack.Compiler.Backend.RiscVConfig.riscvNames [(9, .alloc 1)]).isNone

-- Byte-observable FFI names retain the actual production input guard.
#guard (Flapjack.Compiler.Backend.StackToLab.InitializedProduction.nativeInputs?
    (width := 64) [(9, .ffi "Ā" 0 0 0 0 0)]).isNone

end Flapjack.Test.InitializedProduction
