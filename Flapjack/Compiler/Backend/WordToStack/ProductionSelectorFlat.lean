import Flapjack.Compiler.Backend.WordToStack.ProductionFlatCodec

namespace Flapjack
open RiscV WordProgCarrierCodec

/-- Flapjack structural property of the actual selector sequence join;
no separate HOL declaration corresponds to this production API helper. -/
private theorem flatSeq {α : Type u} (first second : WordProg α) :
    productionFlat (wordDeadSelectSeq first second) =
      (productionFlat first && productionFlat second) := by
  unfold wordDeadSelectSeq
  split <;> simp_all [productionFlat]

/-- The actual load-tail appends only flat memory instructions. Flapjack-only
production infrastructure, not a HOL semantics theorem. -/
theorem productionFlat_wordInstSelectLoadTail {α : Type u} [WordInstSelectImmediate α]
    (temporary : Nat) (prelude : WordProg α) (address : WordExp α) :
    productionFlat (wordInstSelectLoadTail temporary prelude address).1 =
      productionFlat prelude := by
  unfold wordInstSelectLoadTail
  repeat' (split <;> simp_all [flatSeq, productionFlat])

set_option maxHeartbeats 800000 in
/-- Every expression prelude of the actual word-width-indexed selector is
flat, including total unsupported-expression cases. The real immediate
instance resolves every constant shift, so its abstract unsupported-policy
branch contributes no extra source condition. Flapjack-only API invariant;
no corresponding independent HOL theorem is claimed. -/
theorem productionFlat_wordInstSelectAtom {width : Nat} (temporary : Nat)
    (expression : WordExp (BitVec width)) :
    productionFlat (wordInstSelectAtom temporary expression).1 = true := by
  refine (measure sizeOf).wf.induction expression
    (C := fun e => ∀ t, productionFlat (wordInstSelectAtom t e).1 = true) ?_ temporary
  intro expression ih temporary
  change ∀ (e : WordExp (BitVec width)), sizeOf e < sizeOf expression →
    ∀ t, productionFlat (wordInstSelectAtom t e).1 = true at ih
  have recursive (e : WordExp (BitVec width)) (t : Nat) (prelude : WordProg (BitVec width))
      (selected : WordExp (BitVec width)) (equation : wordInstSelectAtom t e = (prelude, selected))
      (smaller : sizeOf e < sizeOf expression) : productionFlat prelude = true := by
    simpa only [equation, Prod.fst] using ih e smaller t
  have returned (e : WordExp (BitVec width)) (t : Nat)
      (p : WordProg (BitVec width)) (v : WordExp (BitVec width))
      (equation : wordInstSelectAtom t e = (p, v)) : v = .var t := by
    simpa only [equation, Prod.snd] using wordInstSelectAtom_selected t e
  have shiftPolicy (v : BitVec width) :
      (∃ n, WordInstSelectImmediate.shiftImmediate v = .valid n) ∨
      WordInstSelectImmediate.shiftImmediate v = .outOfRange := by
    change (∃ n, (if v.toNat < width then WordShiftImmediate.valid v.toNat
      else .outOfRange) = .valid n) ∨
      (if v.toNat < width then WordShiftImmediate.valid v.toNat else .outOfRange) = .outOfRange
    split
    · exact Or.inl ⟨v.toNat, rfl⟩
    · exact Or.inr rfl
  have impossibleShift (e : WordExp (BitVec width)) (t : Nat)
      (p : WordProg (BitVec width)) (selected : WordExp (BitVec width))
      (v : BitVec width) (equation : wordInstSelectAtom t e = (p, selected))
      (badOut : WordInstSelectImmediate.shiftImmediate v = .outOfRange → False)
      (badValid : ∀ l n, selected = .var l →
        WordInstSelectImmediate.shiftImmediate v = .valid n → False) : False := by
    have shape := returned e t p selected equation
    rcases shiftPolicy v with ⟨n, hn⟩ | hout
    · exact badValid t n shape hn
    · exact badOut hout
  unfold wordInstSelectAtom
  repeat' split
  all_goals simp [productionFlat_wordInstSelectLoadTail, flatSeq, productionFlat]
  all_goals try simp_all only [Prod.mk.injEq]
  all_goals subst_vars
  all_goals repeat' apply And.intro
  all_goals first
    | (apply recursive; assumption; simp_all only [sizeOf, WordExp._sizeOf_1] <;> omega)
    | (apply impossibleShift; assumption; assumption; assumption)

/-- The actual expression selector produces a codec-accepted native flat
program, with no conversion-success or output-flat premise. This composes
production API invariants rather than claiming a separate HOL theorem. -/
theorem wordInstSelectAtom_nativeFlat {width : Nat} [NeZero width]
    (temporary : Nat) (expression : WordExp (BitVec width)) :
    ∃ native, wordLangProgToHOL (wordInstSelectAtom temporary expression).1 = some native ∧
      flatExpConventions native = true := by
  have accepted := wordLangProgToHOL_wordInstSelectAtom_isSome temporary expression
  cases encoded : wordLangProgToHOL (wordInstSelectAtom temporary expression).1 with
  | none => simp only [encoded, Option.isSome_none, Bool.false_eq_true] at accepted
  | some native =>
      refine ⟨native, rfl, ?_⟩
      rw [productionFlat_codec _ native encoded]
      exact productionFlat_wordInstSelectAtom temporary expression

end Flapjack
