import Flapjack.Compiler.Backend.MlStringBridge
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Stack
import Flapjack.Compiler.Backend.WordToStack.NativeCompile

/-! Native `compNative` body output in the actual production decoder image.
Flapjack codec infrastructure (no HOL original): the production StackLang
decoder rejects only instruction payloads without a production counterpart, so
the whole body lies in its image when every emitted instruction does. The
source-side domain is the one actual callers already hold: the native input
decodes through `wordLangProgFromHOL` and the decoded program satisfies the
runtime `allocatorMemorySupported` guard. No output codec, desired body or
target run is assumed. -/
namespace Flapjack.ProductionBodyImage
open Compiler.Backend
open Compiler.Backend.WordToStack.Native Compiler.Backend.StackLang
open Compiler.Encoders.Asm RiscV

/-- Decode a concrete StackLang leaf or instruction-only fragment. -/
macro "output_image_leaf" : tactic => `(tactic|
  simp [OutputImage, holProgToProduction, holProgToProgW, Prog.map, progToProduction,
    HolInst.toWordLangInst, HolArith.toWordLangArith, HolRegImm.toWordRegImm,
    HolAddr.toWordLangAddr, wordLangInstFromHOL, wordLangArithFromHOL, listSeq] <;>
  (repeat' split) <;> simp)

end Flapjack.ProductionBodyImage
