import Flapjack.Compiler.Backend.StackRemove.Comp

/-! Literal stack_removeScript.sml:224–226 section wrapper. HOL's section-name
carrier is independent beta, retained without specializing to numeric labels.
Actual runtime routing remains dependency-linked on 36ez.3.
-/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Full original wrapper: preserve the arbitrary section name and compile
only its faithful native program. No successful-pass or safety premise. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "prog_comp_def"
  (words_as_type_indexed_bitvec)]
def progComp {width : Nat} [NeZero width] {Name : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) (entry : Name × HolProg width) :
    Name × HolProg width :=
  (entry.1, comp jump bounds pointer entry.2)

end Flapjack.Compiler.Backend.StackRemove
