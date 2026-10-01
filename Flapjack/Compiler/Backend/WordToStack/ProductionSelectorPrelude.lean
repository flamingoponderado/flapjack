import Flapjack.RiscV.WordInstSelect
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack
open RiscV WordProgCarrierCodec

/-- Flapjack-only constructor support of the actual selector's sequence join.
No corresponding HOL theorem is asserted. -/
private theorem selectSeqDomain {α : Type u} (first second : WordProg α) :
    supportsCodec (wordDeadSelectSeq first second) =
      (supportsCodec first && supportsCodec second) := by
  unfold wordDeadSelectSeq
  split <;> simp_all [supportsCodec]

/-- The actual load-tail helper adds only shared memory/constant/binop
instructions. Its output support is exactly the incoming prelude's support,
for arbitrary address shapes and immediate-policy decisions. Carrier closure
only: this is not a load semantics or selector equivalence theorem. -/
theorem supportsCodec_wordInstSelectLoadTail {α : Type u} [WordInstSelectImmediate α]
    (temporary : Nat) (prelude : WordProg α) (address : WordExp α) :
    supportsCodec (wordInstSelectLoadTail temporary prelude address).1 =
      supportsCodec prelude := by
  unfold wordInstSelectLoadTail
  repeat' (split <;> simp_all [selectSeqDomain, supportsCodec])

/-- Every expression-selection prelude is accepted structurally, including
all recursive load/operation/shift branches and arbitrary natural temporaries.
Flapjack-only infrastructure; no input/output semantic relation, normal-form,
register bound, or codec-success premise is assumed. -/
theorem supportsCodec_wordInstSelectAtom {α : Type u}
    [Sub α] [Add α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α] (temporary : Nat) (expression : WordExp α) :
    supportsCodec (wordInstSelectAtom temporary expression).1 = true := by
  refine (measure sizeOf).wf.induction expression
    (C := fun e => ∀ t, supportsCodec (wordInstSelectAtom t e).1 = true) ?_ temporary
  intro expression ih temporary
  change ∀ (e : WordExp α), sizeOf e < sizeOf expression →
    ∀ t, supportsCodec (wordInstSelectAtom t e).1 = true at ih
  have recursive (e : WordExp α) (t : Nat) (prelude : WordProg α)
      (selected : WordExp α) (equation : wordInstSelectAtom t e = (prelude, selected))
      (smaller : sizeOf e < sizeOf expression) : supportsCodec prelude = true := by
    simpa only [equation, Prod.fst] using ih e smaller t
  unfold wordInstSelectAtom
  repeat' split
  all_goals simp [supportsCodec_wordInstSelectLoadTail, selectSeqDomain, supportsCodec]
  all_goals repeat' apply And.intro
  all_goals apply recursive
  all_goals first
    | assumption
    | (solve | simp_all only [sizeOf, WordExp._sizeOf_1] <;> omega)
    | (simp_all only [sizeOf, WordExp._sizeOf_1, WordExp._sizeOf_2] <;> omega)


/-- The actual address wrapper only chooses an atom prelude or preserves it
with an address expression. This is unconditional carrier support, not a
memory-offset or address evaluation equivalence theorem. -/
theorem supportsCodec_wordInstSelectAddressAtom {α : Type u}
    [Sub α] [Add α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α] (temporary : Nat) (expression : WordExp α) :
    supportsCodec (wordInstSelectAddressAtom temporary expression).1 = true := by
  have prelude (e : WordExp α) (t : Nat) (p : WordProg α) (s : WordExp α)
      (equation : wordInstSelectAtom t e = (p,s)) : supportsCodec p = true := by
    simpa only [equation, Prod.fst] using supportsCodec_wordInstSelectAtom t e
  unfold wordInstSelectAddressAtom
  repeat' split
  all_goals simp [supportsCodec_wordInstSelectAtom]
  all_goals apply prelude
  all_goals assumption

/-- Native partial codec acceptance of every actual expression-selection
prelude at every positive word width, with no desired output-codec premise.
This does not establish whole-program selection, universal HOL selector
equivalence, pre-SSA/source image closure or executed native routing. -/
theorem wordLangProgToHOL_wordInstSelectAtom_isSome {width : Nat} [NeZero width]
    (temporary : Nat) (expression : WordExp (BitVec width)) :
    (wordLangProgToHOL (wordInstSelectAtom temporary expression).1).isSome = true := by
  rw [codecDomain]
  exact supportsCodec_wordInstSelectAtom temporary expression

/-- Native codec acceptance for the actual address-selection wrapper, with
the same scope limits as the atom prelude result. -/
theorem wordLangProgToHOL_wordInstSelectAddressAtom_isSome {width : Nat} [NeZero width]
    (temporary : Nat) (expression : WordExp (BitVec width)) :
    (wordLangProgToHOL (wordInstSelectAddressAtom temporary expression).1).isSome = true := by
  rw [codecDomain]
  exact supportsCodec_wordInstSelectAddressAtom temporary expression

end Flapjack
