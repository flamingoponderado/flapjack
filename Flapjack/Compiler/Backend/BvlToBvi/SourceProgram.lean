import Flapjack.Compiler.Backend.BvlToBvi.SourceSing

/-! Source-shaped labeled and incremental BVL-to-BVI compilation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- Compile a labeled function into the source auxiliary tree. The singleton
conversion and let-optimizer forms are justified by the original
`compile_single_eq` and `compile_exp_eq` theorems. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_single_def"]
def compileSingleSource (n : Nat) (program : Nat × Nat × Bvl.Exp) :
    AppList (Nat × Nat × Bvi.Exp) × Nat :=
  let (name, args, body) := program
  let (converted, aux, next) := compileSingSource n body
  (smartAppend (.list [(bvlNumStubs + bvlToBviNamespaces * name, args,
    BviLet.compileSing [] 0 converted)]) aux, next)

/-- Compile labeled functions in order, retaining the original tree. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_list_def"]
def compileProgramsSource : Nat → List (Nat × Nat × Bvl.Exp) →
    AppList (Nat × Nat × Bvi.Exp) × Nat
  | n, [] => (.list [], n)
  | n, program :: programs =>
    let (code, next) := compileSingleSource n program
    let (rest, final) := compileProgramsSource next programs
    (smartAppend code rest, final)

/-- Incremental compilation returns the fresh-name counter and flattened code. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_inc_def"]
def compileIncSource (n : Nat) (programs : List (Nat × Nat × Bvl.Exp)) :
    Nat × List (Nat × Nat × Bvi.Exp) :=
  let (code, next) := compileProgramsSource n programs
  (next, appListAppend code)

end Flapjack.Compiler.Backend.BvlToBvi
