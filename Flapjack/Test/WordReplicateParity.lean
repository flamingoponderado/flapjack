import Flapjack.Misc.Words.Replicate

set_option maxRecDepth 10000

namespace Flapjack.Test
example : (Flapjack.holWordReplicate 1 0 (1 : BitVec 1)).toNat = 0 := by decide
example : (Flapjack.holWordReplicate 1 5 (1 : BitVec 1)).toNat = 1 := by decide
example : (Flapjack.holWordReplicate 7 1 (5 : BitVec 3)).toNat = 5 := by decide
example : (Flapjack.holWordReplicate 7 2 (5 : BitVec 3)).toNat = 45 := by decide
example : (Flapjack.holWordReplicate 7 3 (5 : BitVec 3)).toNat = 109 := by decide
example : (Flapjack.holWordReplicate 8 3 (5 : BitVec 3)).toNat = 109 := by decide
example : (Flapjack.holWordReplicate 16 2 (165 : BitVec 8)).toNat = 42405 := by decide
example : (Flapjack.holWordReplicate 64 8 (165 : BitVec 8)).toNat = 11936128518282651045 := by decide
example : (Flapjack.holWordReplicate 80 10 (165 : BitVec 8)).toNat = 782246118574171818927525 := by decide
example : (Flapjack.holWordReplicate 80 2 (65535 : BitVec 16)).toNat = 4294967295 := by decide
example : (Flapjack.holWordReplicate 8 2 (4660 : BitVec 16)).toNat = 52 := by decide
example : (Flapjack.holWordReplicate 16 0 (7 : BitVec 3)).toNat = 0 := by decide
example : (Flapjack.holWordReplicate 16 1 (7 : BitVec 3)).toNat = 7 := by decide
example : (Flapjack.holWordReplicate 16 20 (5 : BitVec 3)).toNat = 56173 := by decide
example : (Flapjack.holWordReplicate 8 8 (1 : BitVec 1)).toNat = 255 := by decide
example : (Flapjack.holWordReplicate 8 3 (1 : BitVec 1)).toNat = 7 := by decide

end Flapjack.Test
