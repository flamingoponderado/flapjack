import Flapjack.Compiler.Backend.LabToTarget.ShareMemDomain

namespace Flapjack.Test.LabToTargetShareMemDomainParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget

/-! Kernel replay of `scripts/hol-probes/lab_to_target_share_mem_domain_probe.out`: the reduction
of `share_mem_domain_code_rel` on code with no lines, a satisfied instance (the full domain) and
a violated one (the 64-bit singleton `{8w}`, since `byte_align 9w = 8w` through
`LOG2 8 = 3`). -/

-- smd_nil=share_mem_domain_code_rel mc p [] d ⇔ (∀a. byte_align a ∈ d ⇒ a ∈ d) ∧ mc.shared_addresses = d
example {width : Nat} [NeZero width] {β γ : Type} (mc : MachineConfig width β γ)
    (p : BitVec width) (d : BitVec width → Prop) :
    shareMemDomainCodeRel mc p [] d ↔
      (∀ a : BitVec width, d (holByteAlign a) → d a) ∧ mc.sharedAddresses = d :=
  shareMemDomainCodeRel_nil mc p d

-- smd_univ=∀mc p. mc.shared_addresses = 𝕌(:α word) ⇒ share_mem_domain_code_rel mc p [] 𝕌(:α word)
example {width : Nat} [NeZero width] {β γ : Type} (mc : MachineConfig width β γ)
    (p : BitVec width) (h : mc.sharedAddresses = fun _ => True) :
    shareMemDomainCodeRel mc p [] (fun _ => True) :=
  (shareMemDomainCodeRel_nil mc p _).mpr ⟨fun _ _ => trivial, h⟩

private theorem byteAlign9 : holByteAlign (9 : BitVec 64) = 8 := by
  show holAlign (holLOG2 (64 / 8)) _ = _
  rw [show (64 : Nat) / 8 = 8 from rfl, show holLOG2 8 = 3 from holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩]
  decide +kernel

-- smd_singleton=∀mc p. ¬share_mem_domain_code_rel mc p [] {8w}
example {β γ : Type} (mc : MachineConfig 64 β γ) (p : BitVec 64) :
    ¬ shareMemDomainCodeRel mc p [] (fun x => x = 8) := by
  intro h
  have := ((shareMemDomainCodeRel_nil mc p _).mp h).1 9 byteAlign9
  exact absurd this (by decide)

end Flapjack.Test.LabToTargetShareMemDomainParity
