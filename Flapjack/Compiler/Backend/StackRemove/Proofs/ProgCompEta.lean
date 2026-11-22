module

public import Flapjack.Compiler.Backend.StackRemove.ProgComp

@[expose] public section
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Full original function-level equality: arbitrary section-name carrier,
all compiler parameters and native programs retained. No hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "prog_comp_eta"
  (words_as_type_indexed_bitvec)]
theorem progCompEta {width : Nat} [NeZero width] {Name : Type} :
    (progComp : Bool → (BitVec width × BitVec width) → Nat →
      (Name × HolProg width) → (Name × HolProg width)) =
    fun jump bounds pointer entry => (entry.1, comp jump bounds pointer entry.2) := rfl

/-- HOL `FST_prog_comp` (`cakeml/compiler/backend/proofs/stack_removeProofScript.sml`):
the wrapper keeps the arbitrary section name of its input. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "FST_prog_comp"
  (words_as_type_indexed_bitvec)]
theorem fstProgComp {width : Nat} [NeZero width] {Name : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) (entry : Name × HolProg width) :
    Prod.fst (progComp jump bounds pointer entry) = Prod.fst entry := rfl

end Flapjack.Compiler.Backend.StackRemove
