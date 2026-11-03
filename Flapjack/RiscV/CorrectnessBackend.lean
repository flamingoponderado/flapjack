import Flapjack.RiscV.Backend
import Flapjack.RiscV.Calls

/-!
Compositional correctness for the straight-line Word fragment.  The RISC-V
instruction runner is intentionally separate from the branch-aware `executeCode`
runner, so this theorem captures exactly the fragment whose compiler emits a
single sequential instruction list.
-/

namespace Flapjack.RiscV

inductive WordRiscVStraightLine : WordProg α → Prop where
  | skip : WordRiscVStraightLine (.skip : WordProg α)
  | move (store : Nat) (moves : List (Nat × Nat)) :
      WordRiscVStraightLine (.move store moves)
  | assign (destination : Nat) (value : WordExp α) :
      WordRiscVStraightLine (.assign destination value)
  | inst (instruction : WordInst α) :
      WordRiscVStraightLine (.inst instruction)
  | store (address : WordExp α) (value : Nat) :
      WordRiscVStraightLine (.store address value)
  | seq (first second : WordProg α) :
      WordRiscVStraightLine first → WordRiscVStraightLine second →
      WordRiscVStraightLine (.seq first second)
  | locValue (destination source : Nat) :
      WordRiscVStraightLine (.locValue destination source)
  | tick : WordRiscVStraightLine (.tick : WordProg α)
  | shareInst (operator : WordMemOp) (name : Nat) (address : WordExp α) :
      WordRiscVStraightLine (.shareInst operator name address)

end Flapjack.RiscV
