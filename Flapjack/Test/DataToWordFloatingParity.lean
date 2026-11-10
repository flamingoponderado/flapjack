module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Test.DataToWordFp32Oracle
public import Flapjack.Test.DataToWordFp64Oracle
public meta import Flapjack.Test.DataToWordFp64Oracle
public meta import Flapjack.Compiler.Backend.DataToWord.Control
public meta import Flapjack.Test.DataToWordFp32Oracle

@[expose] public section

/-! Exact data-to-word floating-point lowering observations from pinned HOL. -/
namespace Flapjack.Test.DataToWordFloatingParity
open Flapjack Flapjack.Compiler.Backend

private def config : DataToWord.Config :=
  ⟨1, 2, 3, 16, false, false, true, true, false, false, .simple⟩

private def cases : List (DataToWord.Config × DataLang.Prog) := [
  (config, .assign 3 (.wordOp (.fpCmp .less)) [1, 2] none),
  (config, .assign 3 (.wordOp (.fpCmp .greaterEqual)) [1, 2] none),
  (config, .assign 3 (.wordOp (.fpBop .sub)) [1, 2] none),
  (config, .assign 3 (.wordOp (.fpUop .sqrt)) [1] none),
  (config, .assign 3 (.wordOp (.fpTop .fma)) [1, 2, 3] none),
  ({ config with hasFpOps := false }, .assign 3 (.wordOp (.fpCmp .equal)) [1, 2] none),
  ({ config with lenSize := 0 }, .assign 3 (.wordOp (.fpBop .add)) [1, 2] none),
  ({ config with hasFpTern := false }, .assign 3 (.wordOp (.fpTop .fma)) [1, 2, 3] none),
  (config, .assign 3 (.wordOp (.fpUop .neg)) [1, 2] none)]

private def compileCases {width : Nat} [NeZero width] :
    Option (List (Nat × Nat × (WordLangProgHOL (BitVec width) × Nat))) :=
  cases.zipIdx.mapM fun ((config, program), index) => do
    let result ← DataToWord.compileControl? config 4 7 program
    pure (index, 0, result)

#guard match compileCases (width := 64) with
  | some result => DataToWordFp64Oracle.matchesCaptured result
  | none => false

#guard match compileCases (width := 32) with
  | some result => DataToWordFp32Oracle.matchesCaptured result
  | none => false

-- Unsupported hardware and an unencodable result header follow HOL's GiveUp path.
#guard match DataToWord.compileControl? (width := 64) { config with hasFpOps := false } 4 7
    (.assign 3 (.wordOp (.fpCmp .equal)) [1, 2] none) with
  | some (.seq (.assign 1 (.const _)) (.alloc 1 _), 7) => true
  | _ => false
#guard match DataToWord.compileControl? (width := 64) { config with hasFpTern := false } 4 7
    (.assign 3 (.wordOp (.fpTop .fma)) [1, 2, 3] none) with
  | some (.seq (.assign 1 (.const _)) (.alloc 1 _), 7) => true
  | _ => false
#guard match DataToWord.compileControl? (width := 64) { config with lenSize := 0 } 4 7
    (.assign 3 (.wordOp (.fpBop .add)) [1, 2] none) with
  | some (.seq (.assign 1 (.const _)) (.alloc 1 _), 7) => true
  | _ => false
#guard match DataToWord.compileControl? (width := 64) config 4 7
    (.assign 3 (.wordOp (.fpUop .neg)) [1, 2] none) with
  | some (.skip, 7) => true
  | _ => false

end Flapjack.Test.DataToWordFloatingParity
