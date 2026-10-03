import Flapjack.Compiler.Backend.RegAlloc.Proofs.ColourExtraction
import Flapjack.Compiler.Backend.RegAlloc.Proofs.DoAlloc1Success
namespace Flapjack.Test.RegAllocGenericCarrierRepair
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
example {α : Type} (ls : List (α × Nat)) (s : State)
    (h : ∀ p ∈ ls, p.2 < s.node_tag.length) :
    stExMap (fun (k, v) => bind (nodeTagSub v) fun t => ret (k, extractTag t)) ls s =
      (.success (ls.map fun (k, v) => (k, extractTag (holEl v s.node_tag))), s) :=
  extractColorStExMapLem ls s h
example {α : Type} (k : Nat) (ls acc : List (α × (Nat × Nat))) (s : State)
    (h : goodRaState s) :
    ∃ ts, stExFilter (fun (m : α × (Nat × Nat)) => fullConsistencyOk k m.2.1 m.2.2) ls acc s =
      (.success ts, s) ∧ ∀ m ∈ ts, (m.2.1 < s.dim ∧ m.2.2 < s.dim) ∨ m ∈ acc :=
  stExFilterFullConsistencyOk k ls acc s h
end Flapjack.Test.RegAllocGenericCarrierRepair
