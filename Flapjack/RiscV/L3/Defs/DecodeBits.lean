import Flapjack.RiscV.L3.Types

/-! Complete original generated fixed-width bit tuples. Import.sml BL invokes
bitstringLib.bitify_boolify; mk_boolify orders word_bit from width-1 down to 0
in a right-associated product. Full original equations and types are captured
in l3_boolify_provenance_probe.out. No input premise is added. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "boolify8_def" 4536]
def boolify8 (w : (BitVec 8)) : (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))))) :=
  ((w.getLsbD 7), (((w.getLsbD 6), (((w.getLsbD 5), (((w.getLsbD 4), (((w.getLsbD 3), (((w.getLsbD 2), (((w.getLsbD 1), (w.getLsbD 0))))))))))))))

/-- Flapjack check of the entire tuple without input restrictions. No distinct
named HOL theorem: the corresponding original definition is above. -/
theorem boolify8_fullEquation (w : BitVec 8) :
    boolify8 w = (w.getLsbD 7, (w.getLsbD 6, (w.getLsbD 5, (w.getLsbD 4, (w.getLsbD 3, (w.getLsbD 2, (w.getLsbD 1, w.getLsbD 0))))))) := rfl

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "boolify32_def" 12179]
def boolify32 (w : (BitVec 32)) : (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))))))))))))))))))))))))))))) :=
  ((w.getLsbD 31), (((w.getLsbD 30), (((w.getLsbD 29), (((w.getLsbD 28), (((w.getLsbD 27), (((w.getLsbD 26), (((w.getLsbD 25), (((w.getLsbD 24), (((w.getLsbD 23), (((w.getLsbD 22), (((w.getLsbD 21), (((w.getLsbD 20), (((w.getLsbD 19), (((w.getLsbD 18), (((w.getLsbD 17), (((w.getLsbD 16), (((w.getLsbD 15), (((w.getLsbD 14), (((w.getLsbD 13), (((w.getLsbD 12), (((w.getLsbD 11), (((w.getLsbD 10), (((w.getLsbD 9), (((w.getLsbD 8), (((w.getLsbD 7), (((w.getLsbD 6), (((w.getLsbD 5), (((w.getLsbD 4), (((w.getLsbD 3), (((w.getLsbD 2), (((w.getLsbD 1), (w.getLsbD 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Flapjack check of the entire tuple without input restrictions. No distinct
named HOL theorem: the corresponding original definition is above. -/
theorem boolify32_fullEquation (w : BitVec 32) :
    boolify32 w = (w.getLsbD 31, (w.getLsbD 30, (w.getLsbD 29, (w.getLsbD 28, (w.getLsbD 27, (w.getLsbD 26, (w.getLsbD 25, (w.getLsbD 24, (w.getLsbD 23, (w.getLsbD 22, (w.getLsbD 21, (w.getLsbD 20, (w.getLsbD 19, (w.getLsbD 18, (w.getLsbD 17, (w.getLsbD 16, (w.getLsbD 15, (w.getLsbD 14, (w.getLsbD 13, (w.getLsbD 12, (w.getLsbD 11, (w.getLsbD 10, (w.getLsbD 9, (w.getLsbD 8, (w.getLsbD 7, (w.getLsbD 6, (w.getLsbD 5, (w.getLsbD 4, (w.getLsbD 3, (w.getLsbD 2, (w.getLsbD 1, w.getLsbD 0))))))))))))))))))))))))))))))) := rfl

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "boolify16_def" 20507]
def boolify16 (w : (BitVec 16)) : (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × Bool))))))))))))))) :=
  ((w.getLsbD 15), (((w.getLsbD 14), (((w.getLsbD 13), (((w.getLsbD 12), (((w.getLsbD 11), (((w.getLsbD 10), (((w.getLsbD 9), (((w.getLsbD 8), (((w.getLsbD 7), (((w.getLsbD 6), (((w.getLsbD 5), (((w.getLsbD 4), (((w.getLsbD 3), (((w.getLsbD 2), (((w.getLsbD 1), (w.getLsbD 0))))))))))))))))))))))))))))))

/-- Flapjack check of the entire tuple without input restrictions. No distinct
named HOL theorem: the corresponding original definition is above. -/
theorem boolify16_fullEquation (w : BitVec 16) :
    boolify16 w = (w.getLsbD 15, (w.getLsbD 14, (w.getLsbD 13, (w.getLsbD 12, (w.getLsbD 11, (w.getLsbD 10, (w.getLsbD 9, (w.getLsbD 8, (w.getLsbD 7, (w.getLsbD 6, (w.getLsbD 5, (w.getLsbD 4, (w.getLsbD 3, (w.getLsbD 2, (w.getLsbD 1, w.getLsbD 0))))))))))))))) := rfl

end Flapjack.RiscV.L3
