import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store

/-! The data-to-word memory relation and its reference-cell invariant. The
remaining higher-level invariants have not yet been reviewed as HOL ports. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Finite-map domain membership in the canonical lookup representation. -/
def mapDomain (map : HolFiniteMapExact Nat Nat) (key : Nat) : Prop :=
  ∃ value, map.lookup key = some value

/-- HOL-shaped injectivity into the selected heap locations. -/
noncomputable def mapInjInto (map : HolFiniteMapExact Nat Nat) (target : Nat → Prop) : Prop :=
  (∀ key, mapDomain map key → target (holFapply map key)) ∧
    ∀ x y, mapDomain map x ∧ mapDomain map y → holFapply map x = holFapply map y → x = y

/-- Reference-cell invariant with all original cell cases. Its source-shaped
equation with explicit tuple components is tagged separately below. -/
noncomputable def bcRefInv {width : Nat} [NeZero width] (conf : Config) (n : Nat)
    (refs : Spt (BvlSem.Ref Value))
    (context : HolFiniteMapExact Nat Nat × HolFiniteMapExact Nat Nat × ValueHeap width × Bool) : Prop :=
  let (f, tf, heap, bigEndian) := context
  match f.lookup n, sptLookup n refs with
  | some ptr, some (.valueArray values) =>
      ∃ addresses, heapLookup ptr heap = some (refBlock addresses) ∧
        List.Forall₂ (fun address value => valueInv conf value refs (address, f, tf, heap)) addresses values
  | some ptr, some (.byteArray compareByContents bytes) =>
      let count := bytes.length / (width / 8) + 1
      heapLookup ptr heap = some (bytesRep bigEndian compareByContents bytes (List.replicate count 0))
  | some ptr, some (.thunk mode value) =>
      ∃ address, heapLookup ptr heap = some (thunkBlock mode address) ∧
        (mode = .evaluated → destThunk value refs = .notThunk) ∧
        valueInv conf value refs (address, f, tf, heap)
  | some ptr, some (.mutBlock tag finalised left value right) =>
      (∀ sizes, conf.gcKind ≠ .generational sizes) ∧
      (finalised = false → ¬ ∃ stamp, mapDomain tf stamp ∧ holFapply tf stamp = ptr) ∧
      ∃ addresses, heapLookup ptr heap = some (blockRep tag addresses) ∧
        List.Forall₂ (fun address item => valueInv conf item refs (address, f, tf, heap))
          addresses (left ++ [value] ++ right)
  | _, _ => False

/-- The reference-cell invariant with its tuple components exposed, in the
source case order. The two map parameters use the canonical finite-support
carrier; the unwrapped form also exposes the shared heap word width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_ref_inv_def"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem bcRefInv_explicit {width : Nat} [NeZero width] (conf : Config) (n : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (bigEndian : Bool) :
    bcRefInv conf n refs (f, tf, heap, bigEndian) ↔
      match f.lookup n, sptLookup n refs with
      | some ptr, some (.valueArray values) =>
          ∃ addresses, heapLookup ptr heap = some (refBlock addresses) ∧
            List.Forall₂ (fun address value => valueInv conf value refs (address, f, tf, heap)) addresses values
      | some ptr, some (.byteArray compareByContents bytes) =>
          let count := bytes.length / (width / 8) + 1
          heapLookup ptr heap = some (bytesRep bigEndian compareByContents bytes (List.replicate count 0))
      | some ptr, some (.thunk mode value) =>
          ∃ address, heapLookup ptr heap = some (thunkBlock mode address) ∧
            (mode = .evaluated → destThunk value refs = .notThunk) ∧
            valueInv conf value refs (address, f, tf, heap)
      | some ptr, some (.mutBlock tag finalised left value right) =>
          (∀ sizes, conf.gcKind ≠ .generational sizes) ∧
          (finalised = false → ¬ ∃ stamp, mapDomain tf stamp ∧ holFapply tf stamp = ptr) ∧
          ∃ addresses, heapLookup ptr heap = some (blockRep tag addresses) ∧
            List.Forall₂ (fun address item => valueInv conf item refs (address, f, tf, heap))
              addresses (left ++ [value] ++ right)
      | _, _ => False := Iff.rfl

/-- Stack and reference invariant, retaining existential finite maps and the
source's reachability and timestamp conditions. Its full source correspondence
and existential finite-map carriers still require review. -/
noncomputable def bcStackRefInv {width : Nat} [NeZero width] (conf : Config) (next : Nat)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (context : List (HeapAddress (WordLocW width)) × ValueHeap width × Bool) : Prop :=
  let (roots, heap, bigEndian) := context
  ∃ f tf : HolFiniteMapExact Nat Nat,
    mapInjInto f (fun ptr => isSomeDataElement (heapLookup ptr heap)) ∧
    (∀ n, mapDomain f n → ∃ cell, sptLookup n refs = some cell) ∧
    mapInjInto tf (fun ptr => isSomeDataElement (heapLookup ptr heap)) ∧
    (∀ n, mapDomain tf n → allTimestamps refs stack n) ∧
    (∀ n, mapDomain tf n → n < next) ∧ beOk conf.be bigEndian ∧
    blocksUnique next (allValues refs stack) ∧
    List.Forall₂ (fun value address => valueInv conf value refs (address, f, tf, heap)) stack roots ∧
    ∀ n, reachableRefs stack refs n ∧ mapDomain f n → bcRefInv conf n refs (f, tf, heap, bigEndian)

/-- Abstract ML heap invariant; this is not yet a reviewed HOL port. -/
noncomputable def absMlInv {width : Nat} [NeZero width] (conf : Config)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (context : List (HeapAddress (WordLocW width)) × ValueHeap width × Bool × Nat × Nat × Nat × GenState)
    (limit next : Nat) : Prop :=
  let (roots, heap, bigEndian, a, sp, sp1, gens) := context
  rootsOk roots heap ∧ heapOk heap limit ∧ gcKindInv conf a sp sp1 gens heap ∧
    unusedSpaceInv a (sp + sp1) heap ∧ bcStackRefInv conf next stack refs (roots, heap, bigEndian)

/-- Word-level ML invariant over the preliminary abstract invariant. It is not
yet a reviewed port of the original declaration. -/
noncomputable def wordMlInv {width : Nat} [NeZero width]
    (context : ValueHeap width × Bool × Nat × Nat × Nat × GenState) (limit next : Nat)
    (conf : Config) (refs : Spt (BvlSem.Ref Value)) (stack : List (Value × WordLocW width)) : Prop :=
  let (heap, bigEndian, a, sp, sp1, gens) := context
  ∃ roots, absMlInv conf (stack.map Prod.fst) refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next ∧
    List.Forall₂ (fun address word => wordAddr conf address = word) roots (stack.map Prod.snd)

/-- Full memory-relation shape; this is not yet a reviewed HOL port or a
pass-correctness theorem. -/
noncomputable def memoryRel {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref Value)) (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Value × WordLocW width)) : Prop :=
  ∃ heap limit a sp sp1 gens,
    heapInMemoryStore heap a sp sp1 gens conf store memory domain limit ∧
    wordMlInv (heap, bigEndian, a, sp, sp1, gens) limit next conf refs vars ∧
    (limit + 3) * (width / 8) + 1 < 2 ^ width ∧ space ≤ sp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
