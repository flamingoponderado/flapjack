import Flapjack.Pancake.PanToWord
import Flapjack.Pancake.Proofs.PanToWord.PanToCrepProgramValidity
import Flapjack.Pancake.Proofs.PanToWord.PanSimpValidity
import Flapjack.Pancake.Proofs.PanToWord.EveryInstOkLess.PanStructs
import Flapjack.Pancake.Proofs.PanToWord.EveryInstOkLess.PanGlobals
import Flapjack.Pancake.Proofs.PanToWord.EveryInstOkLess

namespace Flapjack.PanToWord
open Pancake.PanLang Compiler.Encoders.Asm

/-- Full original whole-pass instruction validity theorem (1410–1424).
All six native passes are composed under the original compile equation,
byte/addr zero-offset guards and source good_panops guard. The conclusion
concerns every instruction of the actual compiled word program; it assumes
neither target execution nor desired instruction validity. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem panToWordEveryInstOkLess {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (pan_code : List (DeclHOL width))
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (compiled : panToWordCompileProgHOL c.isa pan_code = wprog0)
    (byte_offset : asmByteOffsetOkExact c 0 = true)
    (addr_offset : asmAddrOffsetOkExact c 0 = true)
    (guard : pan_code.all goodPanopsHOL = true) :
    ∀ f ∈ wprog0,
      everyInst (fun i => instOkLessExact c (HolInst.ofWordLangInst i)) f.2.2 = true := by
  have hs := everyInstOkLess_panSimpCompileProg pan_code guard
  have ht := PanToWordEveryInstOkLessPanStructs.every_inst_ok_less_pan_structs_compile_top
    () _ hs
  have hg := PanToWordEveryInstOkLessPanGlobals.every_inst_ok_less_pan_globals_compile_top
    _ (Basis.Pure.MlString.ofString "main") ht
  have hc := PanToCrepProgramValidity.everyInstOkLess_panToCrepCompileProg
    _ ((List.all_eq_true).mp hg)
  apply LoopToWord.loopToWordEveryInstOkLess c _ wprog0
  refine ⟨compiled, byte_offset, addr_offset, ?_⟩
  apply everyInstOkLessCrepToLoopCompileProg
  exact hc

end Flapjack.PanToWord
