import Flapjack.Pancake.WordLang
import Flapjack.Misc.FiniteMapApply

/-! Initial-store value selector of `stack_removeProofScript.sml` (2631-2634)
and its literal-word map law (2811-2815). The register map is the canonical
finite-support carrier; missing registers keep HOL's unspecified `FAPPLY`
value through `holFapply`.
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.MemVal
open Flapjack

-- This supplies only HOL type inhabitedness. Undefined FAPPLY results remain
-- the opaque holFapplyOutside; this instance does not choose a missing value.
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Broad register map: a lookup function paired with its finite support. -/
private abbrev RegisterMapBroad (width : Nat) [NeZero width] :=
  { lookup : Nat → Option (WordLocW width) //
    ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys }

private def RegisterMapBroad.toBroad {width : Nat} [NeZero width]
    (regs : HolFiniteMapExact Nat (WordLocW width)) : RegisterMapBroad width :=
  ⟨regs.lookup, regs.finiteSupport⟩

private def RegisterMapBroad.ofBroad {width : Nat} [NeZero width]
    (broad : RegisterMapBroad width) : HolFiniteMapExact Nat (WordLocW width) :=
  ⟨broad.1, broad.2⟩

/-- Canonical standalone-map witness for the `mem_val_def` register map:
the finite-support map roundtrips through its lookup and support proof. -/
theorem holFmapAsFiniteSupportParamWitness_memVal_regs {width : Nat} [NeZero width]
    (regs : HolFiniteMapExact Nat (WordLocW width)) (key : Nat) :
    (RegisterMapBroad.ofBroad (RegisterMapBroad.toBroad regs)).lookup key = regs.lookup key ∧
      (RegisterMapBroad.ofBroad (RegisterMapBroad.toBroad regs)).finiteSupport =
        regs.finiteSupport ∧
      RegisterMapBroad.ofBroad (RegisterMapBroad.toBroad regs) = regs :=
  ⟨rfl, rfl, rfl⟩

/-- Complete original selector: a literal `INL` word becomes `Word`, and an
`INR` register is read with the original `FAPPLY`, including its unspecified
value for an absent register. No register presence or zero default is used. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_val_def"
  (fmap_as_finite_support_parameters := [regs]) (words_as_type_indexed_bitvec)]
noncomputable def memVal {width : Nat} [NeZero width]
    (regs : HolFiniteMapExact Nat (WordLocW width)) : BitVec width ⊕ Nat → WordLocW width
  | .inl w => .word w
  | .inr n => holFapply regs n

/-- Canonical standalone-map witness for the `MAP_mem_val_MAP_INL` map binder. -/
theorem holFmapAsFiniteSupportParamWitness_mapMemValMapInl_f {width : Nat} [NeZero width]
    (f : HolFiniteMapExact Nat (WordLocW width)) (key : Nat) :
    (RegisterMapBroad.ofBroad (RegisterMapBroad.toBroad f)).lookup key = f.lookup key ∧
      (RegisterMapBroad.ofBroad (RegisterMapBroad.toBroad f)).finiteSupport =
        f.finiteSupport ∧
      RegisterMapBroad.ofBroad (RegisterMapBroad.toBroad f) = f :=
  ⟨rfl, rfl, rfl⟩

/-- Complete original law for literal words, for every word list and every
register map. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "MAP_mem_val_MAP_INL"
  (fmap_as_finite_support_parameters := [f]) (words_as_type_indexed_bitvec)]
theorem mapMemValMapInl {width : Nat} [NeZero width] (ws : List (BitVec width))
    (f : HolFiniteMapExact Nat (WordLocW width)) :
    (ws.map Sum.inl).map (memVal f) = ws.map WordLocW.word := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons, memVal, List.cons.injEq, true_and]; exact ih

end Flapjack.Compiler.Backend.StackRemove.Proofs.MemVal
