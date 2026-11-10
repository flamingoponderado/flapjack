module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationBool
public import Flapjack.Compiler.Backend.Semantics.ClosProps.DecodeRelations

@[expose] public section


/-! Installation-value decoding in the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations
open ClosSem ClosProps

/-- The optimizer value relation satisfies the general primitive-operation
relation interface. This is Flapjack proof infrastructure. -/
theorem valueRelSimple (c : Config) (g : Spt ValApprox) : simpleValRel (ValueRel c g) := by
  refine ⟨?_, fun x p n => valueRelBlockTarget c g x n p, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n; constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .number n
  · intro x w; constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .word64 w
  · intro x bytes; constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .byteVector bytes
  · intro x ptr flag; constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .refPtr flag ptr
  · intro body arity env args loc x h
    cases h
    simp [isClos]
  · intro index funs env args loc x h
    cases h
    simp [isClos]

/-- Related values decode to the same installation bytes. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_IMP_v_to_bytes"]
theorem valueRelImpValueToBytes (c : Config) (g : Spt ValApprox) (x y : Value)
    (related : ValueRel c g x y) : valueToBytes y = valueToBytes x :=
  (simpleValRel_valueToBytes (ValueRel c g) x y ⟨valueRelSimple c g, related⟩).symm

/-- Related values decode to the same installation words. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "v_rel_IMP_v_to_words"]
theorem valueRelImpValueToWords (c : Config) (g : Spt ValApprox) (x y : Value)
    (related : ValueRel c g x y) : valueToWords y = valueToWords x :=
  (simpleValRel_valueToWords x y (ValueRel c g) ⟨valueRelSimple c g, related⟩).symm

end Flapjack.Compiler.Backend.ClosKnown.Relations
