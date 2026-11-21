module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.Backend.ToTarget
public import Flapjack.Compiler.Backend.BackendProof.StackFrameSizes
public import Flapjack.Compiler.Backend.Semantics.DataSem.Semantics

@[expose] public section

/-! backendProofScript.sml 2709-2721: `is_64_bits_def` and the space-safety
predicate `is_safe_for_space`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `backendProof$is_64_bits_def` (`backendProofScript.sml:2709-2711`):
`is_64_bits (:'a) ⇔ dimindex (:'a) = 64`. HOL's word dimension is used only
numerically, as the named positive width; the Bool result is decided. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "is_64_bits_def"
  (word_dimension_as_width := width)]
def is64Bits (width : Nat) [NeZero width] : Bool := decide (width = 64)

/-- Exact HOL `backendProof$is_safe_for_space_def` (`backendProofScript.sml:2713-2721`):
the data program of `to_data` is safe for space under the computed limits and
the stack frame sizes of the `to_word` program, and the GC kind is not `None`.
`fromAList` is `sptFromAList`, `InitGlobals_location` is the reviewed
`BvlToBvi.initGlobalsLocation`. The semantics inherit SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "is_safe_for_space_def"
  (words_as_type_indexed_bitvec)]
def isSafeForSpace {width : Nat} [NeZero width] {F : Type} (ffi : HolFfiState F)
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (stackHeapLimit : Nat × Nat) : Prop :=
  let dataProg := (Flapjack.Compiler.Backend.Backend.toData c prog).2.1
  let wordProg := (BackendDefs.toWord asmConf c prog).2.1
  DataSem.dataLangSafeForSpace ffi (sptFromAList dataProg)
      (DataSem.computeLimits c.dataConf.lenSize (is64Bits width) c.dataConf.hasFpOps
        c.dataConf.hasFpTern stackHeapLimit)
      (computeStackFrameSizes asmConf wordProg) BvlToBvi.initGlobalsLocation ∧
    c.dataConf.gcKind ≠ .none

end Flapjack.Compiler.Backend.BackendProof
