import Flapjack.Compiler.Backend.LabToTarget.MmioClassification
import Flapjack.Compiler.Backend.LabToTarget.FetchSuccessor
import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Encoders.AsmSem.State
import Flapjack.Misc.BytesInMem.Imp
import Flapjack.Misc.BytesInMemory.Domain
import Flapjack.Misc.FindIndex.Membership
import Flapjack.Misc.FindIndex.SuccessfulMembership

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Misc

/-- Full original exclusion of every fetched byte from the external-call
entry-PC prefix. All nine source guard families are retained, including the
shared/halt/cache exclusions and emitted-size bound. Every EL is accessed only
under a bound derived from original hypotheses or the original search witness.
The existing optional choice and total-list defaults remain unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmFetch_notFfiEntryPcs {width : Nat} [NeZero width]
    {state projection : Type} (a : Nat)
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))
    (pos : Nat) (dm : BitVec width → Prop) (t : AsmState width)
    (ms : state) (ffiNames : List HolFfiName) (labs : Spt (Spt Nat)) (i : Nat)
    (mc : MachineConfig width state projection)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (progToBytes code).length < 2^width ∧
    mmioPcsMinIndex mc.ffiNames = some i ∧
    mc.ffiNames.length = mc.ffiEntryPcs.length ∧
    allEncOk mc.target.config labs ffiNames 0 code ∧ encOk mc.target.config ∧
    (∀ index, index < i →
      ¬ mc.progAddresses (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms) ∧
      ¬ mc.sharedAddresses (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms) ∧
      -BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms ≠ mc.haltPc ∧
      -BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms ≠ mc.ccachePc ∧
      findIndex (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms)
        mc.ffiEntryPcs 0 = some index) ∧
    bytesInMemHOL (mc.target.getPc ms) (progToBytes code) t.mem mc.progAddresses dm ∧
    asmFetchAux pos code = some line ∧ a < (lineBytes line).length →
    mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pos 0 code)
      ∉ mc.ffiEntryPcs.take i := by
  rintro ⟨_hsize, hmi, hlength, he, _hc, hffi, hm, hf, ha⟩ hmem
  let : Nonempty (BitVec width) := ⟨0⟩
  obtain ⟨j, hj, hvalue⟩ := List.mem_take_iff_getElem.mp hmem
  have hji : j < i := by omega
  have hjlen : j < mc.ffiEntryPcs.length := by omega
  obtain ⟨hnot, _hshared, _hhalt, _hcache, hs⟩ := hffi j hji
  have hfound := findIndex_isMem _ _ 0 j hs
  obtain ⟨k, hk, hklen, hkvalue⟩ := findIndex_mem _ _ 0 hfound
  have hkj : k = j := by
    simp only [Nat.zero_add] at hk
    exact Option.some.inj (hk.symm.trans hs)
  subst k
  have haddr : mc.target.getPc ms + BitVec.ofNat width a +
      BitVec.ofNat width (posVal pos 0 code) =
      -BitVec.ofNat width (ffiOffset*(j+3)) + mc.target.getPc ms := by
    exact hvalue.symm.trans ((holEl_eq_getElem j mc.ffiEntryPcs hjlen).symm.trans hkvalue)
  have hnext := asmFetchAux_posVal_successor pos 0 code 0 mc.target.config labs ffiNames line ⟨he,hf⟩
  have hbound := posVal_bound (pos+1) 0 code mc.target.config labs ffiNames 0 he
  have hb : a + posVal pos 0 code < (progToBytes code).length := by omega
  have hdomain := bytesInMemoryInDomain (mc.target.getPc ms) (progToBytes code) t.mem
    mc.progAddresses (a+posVal pos 0 code)
    ⟨bytesInMem_impliesMemory _ _ _ _ _ hm,hb⟩
  have hw : mc.target.getPc ms + BitVec.ofNat width (a+posVal pos 0 code) =
      mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pos 0 code) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [hw, haddr] at hdomain
  exact hnot hdomain

end Flapjack.Compiler.Backend.LabToTarget
