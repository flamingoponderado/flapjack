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
    | (apply recursive; assumption; (simp_all only [sizeOf, WordExp._sizeOf_1]; omega))
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

/-- The actual address selector preserves a flat atom prelude in every offset
case. This is Flapjack-only production API infrastructure. -/
theorem productionFlat_wordInstSelectAddressAtom {width : Nat} (temporary : Nat)
    (expression : WordExp (BitVec width)) :
    productionFlat (wordInstSelectAddressAtom temporary expression).1 = true := by
  have prelude (e : WordExp (BitVec width)) (t : Nat)
      (p : WordProg (BitVec width)) (s : WordExp (BitVec width))
      (equation : wordInstSelectAtom t e = (p, s)) : productionFlat p = true := by
    simpa only [equation, Prod.fst] using productionFlat_wordInstSelectAtom t e
  unfold wordInstSelectAddressAtom
  repeat' split
  all_goals simp [productionFlat_wordInstSelectAtom]
  all_goals apply prelude
  all_goals assumption

/-- The actual Store boundary appends a flat memory instruction in every
original offset case. Flapjack API infrastructure, with no separate HOL tag. -/
theorem productionFlat_wordInstSelectStoreCake {width : Nat} (temporary : Nat)
    (address : WordExp (BitVec width)) (value : Nat) :
    productionFlat (wordInstSelectStoreCake temporary address value) = true := by
  unfold wordInstSelectStoreCake
  dsimp only
  split <;> (try split) <;>
    simp [flatSeq, productionFlat, productionFlat_wordInstSelectAtom]

/-- Flapjack-only sequence output-equation transport for the actual selector. -/
private theorem flatSelectedSeq {α : Type u} (first second result : WordProg α)
    (equation : wordDeadSelectSeq first second = result)
    (left : productionFlat first = true) (right : productionFlat second = true) :
    productionFlat result = true := by
  rw [← equation, flatSeq, left, right]
  rfl

set_option maxHeartbeats 800000 in
/-- Complete flatness of the actual whole-program instruction selector,
including both optional Call continuations. No source-flat, expression-arity,
codec-success or target-execution premise is assumed. Flapjack-only production
API invariant; the separate original native selector theorem is not replaced. -/
theorem productionFlat_wordInstSelectProgram {width : Nat} (temporary : Nat)
    (program : WordProg (BitVec width)) :
    productionFlat (wordInstSelectProgram temporary program) = true := by
  fun_induction wordApplyColour (fun name => name) program generalizing temporary
  all_goals try simp only [wordInstSelectProgram]
  all_goals try dsimp +zetaDelta only
  all_goals repeat' (split <;>
    (try dsimp +zetaDelta only) <;>
    (try simp_all only [wordInstSelectAtom_selected,
      productionFlat_wordInstSelectAtom,
      flatSeq, productionFlat, WordInstSelectImmediate.shiftImmediate,
      Bool.and_true, Bool.false_eq_true]))
  all_goals try simp_all only [productionFlat, flatSeq, productionFlat_wordInstSelectStoreCake,
    productionFlat_wordInstSelectAtom, productionFlat_wordInstSelectAddressAtom,
    wordInstSelectAtom_selected, Bool.and_true]
  all_goals repeat' split at *
  all_goals subst_vars
  all_goals try simp_all
  all_goals apply flatSelectedSeq
  all_goals first
    | assumption
    | (exact productionFlat_wordInstSelectAtom _ _)
    | (simp [productionFlat])

/-- Every actual encoded selector output satisfies the original native flat
convention. Codec rejection remains none, so no success premise is invented
for arbitrary production extensions. This is Flapjack API infrastructure. -/
theorem wordInstSelectProgram_nativeFlat_map {width : Nat} (temporary : Nat)
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordInstSelectProgram temporary program)).map flatExpConventions =
      (wordLangProgToHOL (wordInstSelectProgram temporary program)).map (fun _ => true) := by
  cases encoded : wordLangProgToHOL (wordInstSelectProgram temporary program) with
  | none => rfl
  | some native =>
      simp only [Option.map_some]
      exact congrArg some ((productionFlat_codec _ native encoded).trans
        (productionFlat_wordInstSelectProgram temporary program))

/-- The actual wrapper computes its temporary from the complete source body.
The native flat observation has no codec-success or target-flat premise.
Flapjack-only production API specialization, with no independent HOL tag. -/
theorem wordInstSelectProgramFrom_nativeFlat_map {width : Nat}
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordInstSelectProgramFrom program)).map flatExpConventions =
      (wordLangProgToHOL (wordInstSelectProgramFrom program)).map (fun _ => true) := by
  unfold wordInstSelectProgramFrom
  exact wordInstSelectProgram_nativeFlat_map _ program

end Flapjack
