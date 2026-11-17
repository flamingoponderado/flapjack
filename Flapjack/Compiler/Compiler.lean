module

public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Inference.Infer
public import Flapjack.HolRef

@[expose] public section

/-!
# `compilerScript.sml`

Declarations of the top-level CakeML compiler driver used by the Pancake route.
-/

namespace Flapjack.Compiler

/-- The original CakeML compiler configuration, including its inference
environment, backend, target assembler, and input/output mode flags. -/
@[hol "cakeml/compiler/compilerScript.sml" "config"
  (words_as_type_indexed_bitvec)]
structure CompilerConfig (width : Nat) [NeZero width] where
  inferencerConfig : Inference.Infer.Env
  backendConfig : Flapjack.Compiler.Backend.Backend.Config
  asmConfig : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width
  inputIsSexp : Bool
  excludePrelude : Bool
  skipTypeInference : Bool
  onlyPrintTypes : Bool
  onlyPrintSexp : Bool

/-- HOL `pancake_backend_conf_def` (`compilerScript.sml:744-747`): the backend configuration
used to compile Pancake, which is the given one with the data configuration's `gc_kind`
set to `None`. -/
@[hol "cakeml/compiler/compilerScript.sml" "pancake_backend_conf_def"]
def pancakeBackendConf (c : Backend.Backend.Config) : Backend.Backend.Config :=
  { c with dataConf := { c.dataConf with gcKind := .none } }

end Flapjack.Compiler
