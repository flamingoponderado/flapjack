import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.Pancake.PanGlobals.CompileTopExact
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.LoopToWord.CompFuncExact

/-!
Counterpart of `cakeml/pancake/pan_to_wordScript.sml`: the whole Pancake to
wordLang compiler as the composition of the reviewed exact pass definitions.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `pan_to_word$compile_prog_def` (`pan_to_wordScript.sml:10-18`):

    ```
    compile_prog arch prog =
      let prog = pan_simp$compile_prog prog;
          prog = pan_structs$compile_top prog;
          prog = pan_globals$compile_top prog «main»;
          prog = pan_to_crep$compile_prog prog;
          prog = crep_to_loop$compile_prog arch prog in
        loop_to_word$compile prog
    ```

    Each stage is the reviewed exact port of the named HOL definition. Proof-side
    definition: the executed `flapjack-compile` path is the production pipeline
    in `Flapjack/Pipeline.lean`, not this declaration. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def panToWordCompileProgHOL {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (DeclHOL width)) : List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let prog := panSimpDeclsHOL prog
  let prog := Pancake.PanStructs.CompileShapeExact.compileTopExact prog
  let prog := compileTopExactHOL prog (ofString "main")
  let prog := compileProgDeclsHOLW prog
  let prog := compileProgHOLExact arch prog
  loopToWordCompileHOL prog

end Flapjack
