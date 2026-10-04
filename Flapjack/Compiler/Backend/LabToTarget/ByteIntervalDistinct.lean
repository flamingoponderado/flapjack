import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
import Flapjack.Compiler.Backend.LabToTarget.FetchSuccessor
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original fetched-byte interval distinctness. Every source guard is
retained, including the dimensional emitted-length bound; all positions and
the final inequality remain Nat. The proof uses native natural-position order,
without assuming a successful target execution or the desired separation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem posVal_asmFetchAux_distinct {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))
    (a otherPC p : Nat) :
    allEncOk c labs ffis validPos code ∧ encOk c ∧ asmFetchAux pc code = some line ∧
      a < (lineBytes line).length ∧ (progToBytes code).length < 2^width ∧ otherPC ≠ pc →
    a + posVal pc p code ≠ posVal otherPC p code := by
  rintro ⟨he,hc,hf,ha,_hsize,hne⟩
  have hpc := asmFetchAux_some_ltNumPcs pc code line hf
  have hnext := asmFetchAux_posVal_successor pc p code validPos c labs ffis line ⟨he,hf⟩
  have hinside : a + posVal pc p code < posVal (pc+1) p code := by omega
  by_cases hleft : otherPC < pc
  · have hs := posVal_mono otherPC p code pc validPos c labs ffis
      ⟨hleft,by omega,he,hc⟩
    omega
  have hright : pc+1 ≤ otherPC := by omega
  by_cases hbound : otherPC ≤ numPcs code
  · have hs : posVal (pc+1) p code ≤ posVal otherPC p code := by
      by_cases heq : pc+1 = otherPC
      · rw [heq]
        exact Nat.le_refl _
      · have ht := posVal_mono (pc+1) p code otherPC validPos c labs ffis
          ⟨by omega,hbound,he,hc⟩
        omega
    omega
  · have hs : posVal (pc+1) p code ≤ posVal (numPcs code) p code := by
      by_cases heq : pc+1 = numPcs code
      · rw [heq]
        exact Nat.le_refl _
      · have ht := posVal_mono (pc+1) p code (numPcs code) validPos c labs ffis
          ⟨by omega,Nat.le_refl _,he,hc⟩
        omega
    have hsaturate := posVal_geNumPcs otherPC p code (by omega)
    omega
end Flapjack.Compiler.Backend.LabToTarget
