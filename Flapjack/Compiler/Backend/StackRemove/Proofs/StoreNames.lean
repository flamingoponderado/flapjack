import Flapjack.Compiler.Backend.StackRemove.StoreAddress

namespace Flapjack.Compiler.Backend.StackRemove.StoreNames
open Flapjack.Compiler.Backend.StackLang

/-- Every original store name except CurrHeap has an actual store_list slot,
including all values of the fixed five-bit Temp payload. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "name_cases"]
theorem nameCases (name : StoreName) (notCurrHeap : name ≠ .currHeap) :
    name ∈ storeList := by
  cases name <;> simp [storeList] at notCurrHeap ⊢
  case temp value =>
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    have bound := value.isLt
    omega

end Flapjack.Compiler.Backend.StackRemove.StoreNames
