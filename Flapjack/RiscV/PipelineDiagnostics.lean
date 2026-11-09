module

public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobalsByteRanged
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.Pancake.PanStructs.CompileDeclsExact
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.LoopToWord
public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.Display
public import Flapjack.Parser
public import Flapjack.Parser.ParseTopDecsByteRanged
public import Flapjack.RiscV.Encoding
public import Flapjack.RiscV.LabDiagnostics
public import Flapjack.RiscV.LabToTargetRoute
public import Flapjack.RiscV.WordToStackFailure
public import Flapjack.Compiler.Backend.WordRemove.Production
public import Flapjack.Compiler.Backend.WordAlloc.ProductionLimitVar
public import Flapjack.Compiler.Backend.WordAlloc.ProductionRemoveDead
public import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAMetadata
public import Flapjack.Compiler.Backend.WordUnreach.Production
public import Flapjack.Compiler.Backend.WordCopy.Production
public import Flapjack.Compiler.Backend.LabToTarget.Diagnostics
public import Flapjack.Compiler.Backend.LabToTarget.EncodingGuard
public import Flapjack.Compiler.Backend.WordToStack.Guard

@[expose] public section

/-!
# Checked pipeline Word-to-Stack diagnostics

The historical pipeline boundary returns `Option`, which is convenient for
existing executable artifacts but loses the reason a function could not be
lowered.  This wrapper retains the function section label and the checked
Word diagnostic while leaving that API unchanged.
-/

namespace Flapjack.RiscV

structure PipelineWordLoweringError where
  sectionId : Nat
  path : List Nat
  feature : WordUnsupportedFeature
  deriving DecidableEq, Repr

end Flapjack.RiscV

namespace Flapjack.RiscV

end Flapjack.RiscV

namespace Flapjack

inductive PipelineRiscVLoweringError where
  | wordToStack (error : RiscV.PipelineWordLoweringError)
  | allocationFailure (sectionId : Nat)
  | wordToStackFailure (sectionId : Nat) (path : List Nat)
      (kind : RiscV.WordToStackFailureKind)
  | labToRiscV (error : RiscV.LabLoweringError)
  | stackToRiscV
  deriving DecidableEq, Repr

/-! Source-shaped sibling of the checked bitmap pipeline.  Pancake's
    `loop_to_word$compile_prog` has already assigned the dense Word names and
    has retained the extra entry slot in the function arity.  Re-running
    `loopToWordCompFunc` from the loop-facing pipeline loses that distinction,
    so the source runtime path must allocate this Word program directly.

    This diagnostic API also accepts arbitrary raw Word rows. A raw row outside
    `WordProgCarrierCodec.supportsCodec` may enter the historical allocator
    extension; no original HOL correspondence is claimed for that input. Actual
    source-produced rows satisfy the codec domain before allocation. The proofs
    in `WordRemove/ProductionCallerErrors` show their allocation diagnostic
    identifies a real allocator None, rather than post-allocation codec rejection.
    Raw extension errors and other lowering errors retain their executed behavior. -/

inductive SourceRiscVImageError where
  | parse (errors : List Parser.ParseError)
  | static (error : StatErr)
  | entryNotFound
  | lowering (error : PipelineRiscVLoweringError)
  | loweringInFunction (functionName : FunName) (error : PipelineRiscVLoweringError)
  | artifactFailure (failure : Flapjack.Compiler.Backend.LabToTarget.LabLoweringFailure)
  | wordStackGuard (failure : Flapjack.Compiler.Backend.WordToStack.WordStackGuardFailure)
  | labEncodingGuard (failure : Flapjack.Compiler.Backend.LabToTarget.EncodingGuardFailure)
  deriving Repr

def pipelineLoweringSectionId : PipelineRiscVLoweringError → Option Nat
  | .wordToStack error => some error.sectionId
  | .allocationFailure sectionId => some sectionId
  | .wordToStackFailure sectionId _ _ => some sectionId
  | .labToRiscV error => some error.sectionId
  | .stackToRiscV => none

/-- Human-readable name of the pipeline pass that reported a lowering error. -/
def pipelineRiscVLoweringPassName : PipelineRiscVLoweringError → String
  | .wordToStack _ => "word-to-stack"
  | .allocationFailure _ => "register allocation"
  | .wordToStackFailure _ _ _ => "word-to-stack"
  | .labToRiscV _ => "lab-to-riscv"
  | .stackToRiscV => "stack-to-riscv"

/-- User-facing description of a lowering error.

The `sectionId` inside a lowering error is the position of the failing
function in the crepe list the pass consumed, so it is a pipeline-local label
rather than a stable identity: `--hex` numbers crepe sections from 1 while the
default runtime-image mode numbers them from `stackFunctionFirstLabel`, and the
same failing function is therefore section `n` in one mode and `n + 2` in the
other.  Diagnostics name the containing function when `loweringInFunction`
resolved one and always mark the raw section id as mode-local, while leaving
the Cake-compatible internal labels unchanged. -/
def pipelineRiscVLoweringErrorDescription
    (error : PipelineRiscVLoweringError) : String :=
  match pipelineLoweringSectionId error with
  | some sectionId =>
      s!"{pipelineRiscVLoweringPassName error} failed in mode-local section {sectionId}"
  | none => s!"{pipelineRiscVLoweringPassName error} failed (section id unavailable)"

def sourceRiscVImageErrorDescription : SourceRiscVImageError → String
  | .parse errors => s!"parse error: {repr errors}"
  | .static error => s!"static check failed: {repr error}"
  | .entryNotFound => "no entry point named 'main'"
  | .lowering error => pipelineRiscVLoweringErrorDescription error
  | .loweringInFunction functionName error =>
      s!"in function '{functionName}': {pipelineRiscVLoweringErrorDescription error}"
  | .artifactFailure failure =>
      "native backend compilation failed: " ++
        Flapjack.Compiler.Backend.LabToTarget.labLoweringFailureDescription failure
  | .wordStackGuard failure =>
      "native backend compilation failed: " ++
        Flapjack.Compiler.Backend.WordToStack.wordStackGuardFailureDescription failure
  | .labEncodingGuard failure =>
      "native backend compilation failed: " ++
        Flapjack.Compiler.Backend.LabToTarget.encodingGuardFailureDescription failure

end Flapjack
