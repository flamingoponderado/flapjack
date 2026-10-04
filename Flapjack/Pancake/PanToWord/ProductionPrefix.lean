import Flapjack.Pipeline
import Flapjack.Pancake.PanToWord

/-! Caller composition for the complete original source-to-Word prefix.
These equalities have no separately named HOL originals; each literal pass
is reused from its reviewed counterpart. Downstream CLI assembly is separate. -/
namespace Flapjack
open Pancake.PanLang Basis.Pure.MlString

private theorem panSimpDecls_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    (panSimpDecls declarations).map declToHOL =
      panSimpDeclsHOL (declarations.map declToHOL) := by
  have encoded := congrArg (List.map declToHOL) (panSimpDeclsRouted_eq declarations source)
  simpa only [panSimpDeclsRouted, List.map_map, Function.comp_def,
    declToHOL_declOfHOL, List.map_id_fun', id_eq] using encoded.symm

private theorem globalCompileTopCake_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    (globalCompileTopCake declarations "main").map declToHOL =
      compileTopExactHOL (declarations.map declToHOL) (ofString "main") := by
  have encoded := congrArg (List.map declToHOL)
    (compileTopExactHOL_decode declarations "main" source (by simp [NameRanged]))
  simpa only [List.map_map, Function.comp_def, declToHOL_declOfHOL,
    List.map_id_fun', id_eq] using encoded.symm

/-- Every actual frontend declaration field re-encodes to the complete original
source prefix. No successful-pass or compiler-output relation is assumed. -/
theorem frontendCakeDeclarations_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    (frontendCakeDeclarations "main" declarations).map declToHOL =
      compileTopExactHOL
        (Pancake.PanStructs.CompileShapeExact.compileTopExact
          (panSimpDeclsHOL ((panTargetMoveStartToFront "main" declarations).map declToHOL)))
        (ofString "main") := by
  have moved := panTargetMoveStartToFront_byteRanged "main" declarations source
  have simplified := panSimpDecls_byteRanged _ moved
  have structured := structCompileTop_byteRanged _ simplified
  unfold frontendCakeDeclarations
  rw [globalCompileTopCake_encode _ structured,
    structCompileTop_encode _ simplified, panSimpDecls_encode _ moved]

/-- Literal original Word program rows, directly usable by the native
WordToStack API. Preserve original names/labels and simplify Crep only inside
its reviewed whole compiler. Existing CLI assembly is tracked separately. -/
def compileFlapjackFrontendWordNative? {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    Option (List (Nat × Nat × WordLangProgHOL (BitVec width))) :=
  (compileFlapjackFrontendLoopNative? "main" declarations source).map loopToWordCompileHOL

/-- Complete original six-pass source-to-Word result on the actual shared
frontend's moved input. Byte ranges are the only input premise; every codec
and the native producer success are derived. No target execution or relabel
hypothesis is introduced. -/
theorem compileFlapjackFrontendWordNative_original {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    compileFlapjackFrontendWordNative? declarations source =
      some (panToWordCompileProgHOL .riscv
        ((panTargetMoveStartToFront "main" declarations).map declToHOL)) := by
  unfold compileFlapjackFrontendWordNative?
  rw [compileFlapjackFrontendLoopNative_original,
    frontendCakeDeclarations_encode declarations source]
  rfl

end Flapjack
