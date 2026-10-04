import Flapjack.Compiler.Backend.WordCse.ProductionProgram
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAOutputCodec
import Flapjack.Compiler.Backend.WordAlloc.ProductionRemoveDeadDecoderImage

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Complete actual allocator CSE boundary after its native SSA producer and
first native dead-program cleanup. Successful metadata decoding is the real
producer API condition, not a target execution assumption. The entire CSE
input image, original wrapper result and output decoder success are derived;
no input roundtrip, output relation or callback is supplied. This is untagged
Flapjack production infrastructure, with no separate HOL theorem original.
It justifies the optimized implementation on this source image, not the
broader rejected instruction extensions or whole compiler semantics. -/
theorem nativeAllocatorCse_sourceImage {width : Nat} [NeZero width]
    (count : Nat) (native : WordLangProgHOL (BitVec width))
    (produced : WordSsaState × List Nat × WordProg (BitVec width))
    (producer : wordFullSsaCcTransNativeWithStateFromHOL count native = some produced) :
    ∃ beforeDead : WordLangProgHOL (BitVec width),
      wordLangProgToHOL produced.2.2 = some beforeDead ∧
      wordLangProgFromHOL (Flapjack.WordAlloc.removeDeadProg beforeDead) =
        some (wordRemoveDeadProgramViaHOL produced.2.2) ∧
      wordLangProgFromHOL
          (wordCommonSubexpElim (Flapjack.WordAlloc.removeDeadProg beforeDead)) =
        some (wordCseProp (wordRemoveDeadProgramViaHOL produced.2.2)) := by
  have accepted := wordFullSsaCcTransNativeWithStateFromHOL_outputCodec
    count native produced producer
  obtain ⟨beforeDead, encoded⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨actual, decoded, routed⟩ :=
    Flapjack.WordAlloc.wordRemoveDeadProgramViaHOL_sourceNative produced.2.2 beforeDead encoded
  have inputImage : wordLangProgFromHOL (Flapjack.WordAlloc.removeDeadProg beforeDead) =
      some (wordRemoveDeadProgramViaHOL produced.2.2) := by
    simpa only [routed] using decoded
  exact ⟨beforeDead, encoded, inputImage,
    wordCommonSubexpElim_production_transport _ _ inputImage⟩

end Flapjack.Compiler.Backend.WordCse
