import Flapjack.Compiler.Backend.BackendProof.CompileCorrectDraft
import Flapjack.Compiler.Backend.BackendProof.FromTupleCc
import Flapjack.Compiler.Backend.BackendProof.FlatSemantics
import Flapjack.Compiler.Backend.Backend.SourcePipeline
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SyntaxOracle

set_option autoImplicit false

/-! Untagged statements of the `backendProofScript.sml` results that
`compile_correct'` uses and that are not yet ported. The draft proof of
`compile_correct'` takes them as explicit hypotheses; each one is the HOL
statement with its free variables universally quantified, and must be
replaced by the ported, tagged theorem once it lands. The data-to-word
`compile_semantics` hypothesis is `DataToWord.Proofs.AssignThmStmt`, via
`compileSemantics_of_assign` (`DataToWord/Proofs/Correct/CompileSemanticsDraft.lean`). -/
namespace Flapjack.Compiler.Backend.BackendProof.Draft

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL Flapjack.PrimTypesHOL
open Flapjack.Compiler.Backend.SourceEval.Proofs Flapjack.Compiler.Backend.BackendProps

/-- The statement of HOL `source_eval_to_flat_semantics`
(`backendProofScript.sml:3203-3217`), at word width `width` and FFI state type
`F`. -/
def SourceEvalToFlatSemanticsStmt (width : Nat) [NeZero width] (F : Type) [Nonempty F] :
    Prop :=
  ∀ (ev : Option (CompilerInstance Flapjack.Compiler.Backend.Backend.Config))
    (s0 : State F) (env : SemEnv Value) (prog : List AstHOL.Dec)
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (srcC' : SourceToFlat.Config)
    (p' : List FlatLang.Exp) (ffi : HolFfiState F),
    ¬ semanticsProg (addEvalState ev s0) env prog .fail ∧
      BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
      SourceToFlat.compileTotal Flapjack.Compiler.Backend.Backend.primSrcConfig
        (SourceToSource.compile prog) = (srcC', p') ∧
      holThe (primSemEnv ffi) = (s0, env) ∧
      optEvalConfigWf asmConf c' ev ∧
      c.stackConf.perfCalls = false ∧
      c.sourceConf = Flapjack.Compiler.Backend.Backend.primSrcConfig →
    ∃ syntaxOracle : Nat → (Nat × Nat) × List AstHOL.Dec,
      semanticsProg (addEvalState ev s0) env prog
        (FlatSem.semantics
          (FlatProps.mkFlatInstallConf (backendFromFlatTupleCc asmConf c)
            (cakeOrac asmConf c' syntaxOracle (Prod.snd ∘ configTuple1)
              (fun ps => ps.flatProg)))
          s0.ffi p')

/-- The statement of HOL `cake_orac_clos_syntax_oracle_ok`
(`backendProofScript.sml:1120-1129`), at word width `width`. HOL's
`clos_to_bvl$compile c2 clos_prog = (clos_c', clos_prog')` returns the
program together with its name map, so `closProg'` is that pair. -/
def CakeOracClosSyntaxOracleOkStmt (width : Nat) [NeZero width] : Prop :=
  ∀ (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (c2 closC' : ClosToBvl.Config)
    (closProg : List ClosLang.Exp)
    (closProg' : List (Nat × Nat × Bvl.Exp) × Spt Basis.Pure.MlString.MlString)
    (syntaxOracle : Nat → (Nat × Nat) × List AstHOL.Dec),
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧
      ClosToBvl.compileSource c2 closProg = (closC', closProg') ∧
      (∃ st, c'.closConf = { closC' with start := st }) ∧
      c2 = c.closConf ∧ closProg = (Flapjack.Compiler.Backend.Backend.toClos c prog).2 ∧
      1 ≤ c.closConf.maxApp ∧
      c.sourceConf = Flapjack.Compiler.Backend.Backend.primSrcConfig →
    ClosToBvl.syntaxOracleOkCommon c.closConf closC' closProg
      (cakeOrac asmConf c' syntaxOracle (Prod.snd ∘ configTuple1) (fun ps => ps.closProg))

end Flapjack.Compiler.Backend.BackendProof.Draft
