import Flapjack.Pancake.Proofs.WordConvs.SmartSeqLabels
namespace Flapjack.Test.WordSimpSmartSeqParity
open Flapjack.Compiler.Backend.WordSimp
private def call : WordLangProgHOL (BitVec 8) :=
  .call (some ([], (.ln,.ln), .skip,3,4)) none [] none
-- Original HOL skip_left=Tick; skip_right=Seq Tick Skip.
example : smartSeqHOL (width := 8) .skip .tick = .tick := by rfl
example : smartSeqHOL (width := 8) .tick .skip = .seq .tick .skip := by rfl
-- Original HOL labels_skip_left=[(3,4)]; labels_call_left=[(3,4)].
example : extractLabels (smartSeqHOL .skip call) = [(3,4)] := by rfl
example : extractLabels (smartSeqHOL call .skip) = [(3,4)] := by rfl
-- Original HOL labels_both and labels_seq=[(3,4);(3,4)].
example : extractLabels (smartSeqHOL call call) = [(3,4),(3,4)] := by rfl
example : extractLabels (smartSeqHOL (.seq .skip call) call) = [(3,4),(3,4)] := by rfl
end Flapjack.Test.WordSimpSmartSeqParity
