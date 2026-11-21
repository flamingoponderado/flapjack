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

/-- Compiling a section keeps its name. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "FST_prog_comp"
  (words_as_type_indexed_bitvec)]
theorem fstProgComp {width : Nat} [NeZero width] {Name : Type} (jump : Bool)
    (off : BitVec width × BitVec width) (k : Nat) (pp : Name × HolProg width) :
    (progComp jump off k pp).1 = pp.1 := rfl

end Flapjack.Compiler.Backend.StackRemove
