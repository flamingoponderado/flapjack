import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

/-! Installation and outer dispatcher edge cases. -/
namespace Flapjack.Test.DataSemInstall
open Flapjack
open Flapjack.Compiler.Backend
open DataSem

private def nil : Value := .block 0 BackendCommon.nilTag []

private def ready {F : Type} (s : State Unit F) : State Unit F :=
  { s with code := .ls (3, .skip), safeForSpace := true, compile := (fun _ _ => some ([], [], ())), compileOracle := (fun _ => ((), [(0, 0, .skip)])) }

/-- The source permits an installation whose label is already present. -/
example {F : Type} (s : State Unit F) :
    doInstall (R := Unit) [nil, nil, .number 0, .number 0] (ready s) =
      .val (.codePtr 0, { ready s with safeForSpace := false, code := sptUnion (ready s).code (sptFromAList [(0, 0, .skip)]), compileOracle := (fun n => (ready s).compileOracle (n + 1)) }) := by
  simp [doInstall, ready, nil, valueToBytes, valueToWords, valueToList,
    byteNumbers, wordValues, BackendCommon.nilTag]

example : sptLookup 0 (sptUnion (.ls (3, DataLang.Prog.skip))
    (sptFromAList [(0, 0, DataLang.Prog.skip)])) = some (3, DataLang.Prog.skip) := by
  simp [sptLookup, sptUnion, sptFromAList]

example {F : Type} (s : State Unit F) :
    doInstall (R := Unit) [nil, nil, .number 1, .number 0] (ready s) = .err (.abort .typeError) := by
  simp [doInstall, nil, valueToBytes, valueToWords, valueToList,
    byteNumbers, wordValues, BackendCommon.nilTag]

example {C F : Type} (s : State C F) :
    doApp (.intOp .greater) [] s = .err (.abort .typeError) := by rfl

example {C F : Type} (s : State C F) :
    doApp .install [] s = .err (.abort .typeError) := by rfl

end Flapjack.Test.DataSemInstall
