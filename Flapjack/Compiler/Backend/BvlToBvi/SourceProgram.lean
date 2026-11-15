module

public import Flapjack.Compiler.Backend.BvlToBvi.SourceSing
public import Flapjack.Compiler.Backend.BvlToBvi.Stubs

@[expose] public section

/-! Source-shaped labeled and incremental BVL-to-BVI compilation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- The original labeled-function compiler. HOL head selection is arbitrary on
empty lists, so this literal definition is noncomputable; `compileSingle_eq`
proves the executable singleton implementation gives the same result. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_single_def"]
noncomputable def compileSingleSource (n : Nat) (program : Nat × Nat × Bvl.Exp) :
    AppList (Nat × Nat × Bvi.Exp) × Nat :=
  let (name, args, body) := program
  let (converted, aux, next) := compileExpsSource n [body]
  (smartAppend (.list [(bvlNumStubs + bvlToBviNamespaces * name, args,
    BviLet.compileExp (@Flapjack.holHd Bvi.Exp ⟨.var 0⟩ converted))]) aux, next)

/-- Executable singleton form, equal to the original definition by
`compileSingle_eq`. -/
def compileSingleImpl (n : Nat) (program : Nat × Nat × Bvl.Exp) :
    AppList (Nat × Nat × Bvi.Exp) × Nat :=
  let (name, args, body) := program
  let (converted, aux, next) := compileSingSource n body
  (smartAppend (.list [(bvlNumStubs + bvlToBviNamespaces * name, args,
    BviLet.compileSing [] 0 converted)]) aux, next)

/-- HOLs singleton rewrite for the labeled-function compiler. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_single_eq"]
theorem compileSingle_eq (n name args : Nat) (body : Bvl.Exp) :
    compileSingleSource n (name, args, body) =
      let (converted, aux, next) := compileSingSource n body
      (smartAppend (.list [(bvlNumStubs + bvlToBviNamespaces * name, args,
        BviLet.compileExp converted)]) aux, next) := by
  simp [compileSingleSource, compileExpsSing.1, Flapjack.holHd]

/-- Code generation uses HOLs proved singleton rewrite, including the
proved let-optimizer rewrite. The canonical source API remains the original. -/
@[csimp] theorem compileSingleSource_eq_impl : compileSingleSource = compileSingleImpl := by
  funext n program
  rcases program with ⟨name, args, body⟩
  simpa [compileSingleImpl, BviLet.compileExp_eq] using compileSingle_eq n name args body

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

/-- Compile a whole program with the original entry point, stub order,
allocation count, and fresh-name counter. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_prog_def"]
def compileProgSource (start n : Nat) (programs : List (Nat × Nat × Bvl.Exp)) :
    Nat × List (Nat × Nat × Bvi.Exp) × Nat :=
  let count := allocGlobCount (programs.map (fun (_, _, body) => body))
  let (code, next) := compileProgramsSource n programs
  (initGlobalsLocation,
    stubs (bvlNumStubs + bvlToBviNamespaces * start) count ++ appListAppend code, next)

end Flapjack.Compiler.Backend.BvlToBvi
