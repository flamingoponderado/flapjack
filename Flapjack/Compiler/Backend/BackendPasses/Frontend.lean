import Flapjack.Compiler.Backend.PresLang.Source
import Flapjack.Compiler.Backend.PresLang.Flat
import Flapjack.Compiler.Backend.PresLang.Clos
import Flapjack.Compiler.Backend.SourceToFlat.ToClos

/-! Capturing the initial explorer stages of `backend_passesScript.sml`.
The existing source-to-closure compiler runs the same passes, but this module
also retains their intermediate values for presentation. It is untagged: the
display representations and complete cross-language pass correspondence
remain under review, and later explorer stages are not yet captured. -/
namespace Flapjack.Compiler.Backend.BackendPasses
open Flapjack.Basis.Pure.MlString

/-- The six frontend snapshots in CakeML's `to_flat_all` and `to_clos_all`. -/
structure FrontendStages where
  original : List AstHOL.Dec
  lifted : List AstHOL.Dec
  rawFlat : List FlatLang.Exp
  reducedFlat : List FlatLang.Exp
  patternedFlat : List FlatLang.Exp
  closure : List ClosLang.Exp
  config : SourceToFlat.Config

/-- Run the original source, flat, and closure pass sequence while retaining
each intermediate result. The final output is the same value used by the
normal source-to-closure compiler. -/
def captureFrontend (config : SourceToFlat.Config) (decls : List AstHOL.Dec) : FrontendStages :=
  let lifted := SourceLet.compileDecs decls
  let (config, rawFlat) := SourceToFlat.compileProg config lifted
  let reducedFlat := FlatElim.removeFlatProgTotal rawFlat
  let patternedFlat := reducedFlat.map (FlatPattern.compileDec config.patternCfg)
  let closure := FlatToClos.compileProg patternedFlat
  ⟨decls, lifted, rawFlat, reducedFlat, patternedFlat, closure, config⟩

/-- Capturing stages does not alter the executed source-to-closure result. -/
theorem captureFrontend_result (fuel : Nat) (config : SourceToFlat.Config)
    (decls : List AstHOL.Dec) :
    SourceToFlat.compileCakeToClosFuel fuel config decls =
      some ((captureFrontend config decls).config, (captureFrontend config decls).closure) := by
  rfl

private def title (s : String) : List HolChar := (ofString ("# " ++ s ++ "\n\n")).explode

/-- Render the six captured stages in the original order as bytes. -/
def frontendReportBytes (stages : FrontendStages) : List HolChar :=
  let names := ClosToBvl.getSrcNames stages.closure .ln
  title "original source code" ++ PresLang.Source.declarationBytes stages.original ++
  title "after source_let" ++ PresLang.Source.declarationBytes stages.lifted ++
  title "after source_to_flat" ++ PresLang.Flat.expressionBytes stages.rawFlat ++
  title "after remove_flat" ++ PresLang.Flat.expressionBytes stages.reducedFlat ++
  title "after flat_pattern" ++ PresLang.Flat.expressionBytes stages.patternedFlat ++
  title "after flat_to_clos" ++ PresLang.Clos.programBytes names stages.closure []

end Flapjack.Compiler.Backend.BackendPasses
