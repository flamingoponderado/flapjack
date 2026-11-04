import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockElement
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Number

/-! Dynamic indexing of blocks and value arrays. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- For an in-range nonnegative source integer, the generated dynamic load
has the same address as the corresponding static element load. -/
theorem dynamicElementExp64 {C F : Type} (conf : Config)
    (target : WordSemStateFiniteExact 64 C F) (base index : Nat) (n : Nat)
    (indexRun : WordSemStateFiniteExact.getVar (adjustVar index) target =
      some (.word (smallnum (Int.ofNat n)))) :
    WordSemStateFiniteExact.wordExp target
      (.load (.op .add [realAddr conf (adjustVar base),
        .op .add [.const 8, .shift .lsl (.var (adjustVar index)) (.const 1)]])) =
    WordSemStateFiniteExact.wordExp target
      (.load (.op .add [realAddr conf (adjustVar base),
        .const (BitVec.ofNat 64 8 + BitVec.ofNat 64 8 * BitVec.ofNat 64 n)])) := by
  have encoding : (smallnum (Int.ofNat n) : BitVec 64) = BitVec.ofNat 64 (4 * n) := by
    simp [smallnum_eq_inlined]
  change (smallnum (n : Int) : BitVec 64) = _ at encoding
  simp [WordSemStateFiniteExact.wordExp, indexRun, wordShiftHOL, wordOpHOL, wordOp, theWords]
  rw [encoding, BitVec.ofNat_mul]
  congr 5; bv_decide

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
