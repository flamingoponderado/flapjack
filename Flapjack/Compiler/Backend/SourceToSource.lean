import Flapjack.Compiler.Backend.SourceLet

/-! CakeML's source-to-source pass driver. -/
namespace Flapjack.Compiler.Backend.SourceToSource

/-- Apply the original source let-lifting pass. -/
@[hol "cakeml/compiler/backend/source_to_sourceScript.sml" "compile_def"]
def compile (ds : List AstHOL.Dec) : List AstHOL.Dec := SourceLet.compileDecs ds

end Flapjack.Compiler.Backend.SourceToSource
