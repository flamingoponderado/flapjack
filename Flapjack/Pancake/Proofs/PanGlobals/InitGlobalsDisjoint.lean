import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsAlignment
import Flapjack.Compiler.Backend.StackRemove

namespace Flapjack.PanGlobalsInitGlobalsDisjoint

open Flapjack
open Flapjack.Compiler.Backend

/-- Exact HOL disjoint address ranges lemma (source2098-2109). Sets remain
predicates and DISJOINT means no common member. The base address may wrap;
only the combined offset has HOL's numeric bound. No extra premise is used. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "DISJOINT_addresses_lemma"
  (words_as_type_indexed_bitvec)]
theorem disjointAddressesHOL {width : Nat} [NeZero width]
    (addr1 addr2 : BitVec width) (offs offs' : Nat) :
    addr1 + panBytesInWord width * BitVec.ofNat width offs = addr2 ∧
      goodDimindex width ∧
      (panBytesInWord width).toNat * (offs + offs') < 2 ^ width →
    ∀ x, StackRemove.addresses addr1 offs x →
      ¬ StackRemove.addresses addr2 offs' x := by
  rintro ⟨rfl, hwidth, hbound⟩ x hx hy
  obtain ⟨i, hi, hxi⟩ := (StackRemove.mem_addresses offs addr1 x).mp hx
  obtain ⟨j, hj, hxj⟩ := (StackRemove.mem_addresses offs'
    (addr1 + panBytesInWord width * BitVec.ofNat width offs) x).mp hy
  have heq := hxi.symm.trans hxj
  have heqRight :
      BitVec.ofNat width i * panBytesInWord width + addr1 =
        (panBytesInWord width * BitVec.ofNat width offs +
          BitVec.ofNat width j * panBytesInWord width) + addr1 := by
    calc
      _ = addr1 + BitVec.ofNat width i * StackRemove.bytesInWord width := by
        unfold panBytesInWord StackRemove.bytesInWord; ac_rfl
      _ = _ := heq
      _ = _ := by unfold panBytesInWord StackRemove.bytesInWord; ac_rfl
  have hcancel := congrArg (fun v => v - addr1) heqRight
  have hwords : BitVec.ofNat width i * panBytesInWord width =
      panBytesInWord width * BitVec.ofNat width offs +
        BitVec.ofNat width j * panBytesInWord width := by
    simpa only [BitVec.add_sub_cancel] using hcancel
  rcases hwidth with rfl | rfl
  · have hn := congrArg BitVec.toNat hwords
    simp only [panBytesInWord, BitVec.toNat_mul,
      BitVec.toNat_add, BitVec.toNat_ofNat] at hn hbound
    omega
  · have hn := congrArg BitVec.toNat hwords
    simp only [panBytesInWord, BitVec.toNat_mul,
      BitVec.toNat_add, BitVec.toNat_ofNat] at hn hbound
    omega

end Flapjack.PanGlobalsInitGlobalsDisjoint
