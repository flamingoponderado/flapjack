import Flapjack.Compiler.Backend.WordUnreach.ProductionDecoderDomain
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

/-! Actual partial encoder/native cleanup/decoder boundaries. These kernel
checks distinguish encoding rejection from proven native output acceptance,
including both Call bodies and representation normalization. No HOL declaration
states a property of this Flapjack carrier conversion. -/
namespace Flapjack.Test.WordUnreachEncoderBoundary
open Flapjack Compiler.Backend.WordUnreach

end Flapjack.Test.WordUnreachEncoderBoundary
