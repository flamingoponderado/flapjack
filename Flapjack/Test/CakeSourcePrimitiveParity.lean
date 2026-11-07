import Flapjack.SemanticPrimitivesHOL.Primitives

/-! Source type and word-shift observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourcePrimitiveParity
open Flapjack.SemanticPrimitivesHOL

#guard checkType .boolT (boolValue true)
#guard !checkType .boolT (.litv (.intLit 1))
#guard checkType (.wordT .w8) (.litv (.word8 3))
#guard !checkType (.wordT .w64) (.litv (.word8 3))
#guard shift8Lookup .lsl 129 8 = 0
#guard shift8Lookup .lsr 129 9 = 0
#guard shift8Lookup .asr 129 9 = 255
#guard shift8Lookup .ror 129 9 = 192
#guard shift64Lookup .asr 9223372036854775808 65 = 18446744073709551615
#guard shift64Lookup .ror 9223372036854775808 65 = 4611686018427387904

end Flapjack.Test.CakeSourcePrimitiveParity
