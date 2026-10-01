import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

/-! Flapjack-only support for the actual partial production carrier encoder.
The structural domain is proved equal to the real encoder for every program.
These helpers describe codec acceptance, not HOL semantics or pass simulation,
and have no HOL original or HOL tags. -/

namespace Flapjack.WordProgCarrierCodec

/-- Shared structural view of the actual partial codec's domain. The theorem
below proves equality with the real encoder for every program. This is not an
alternate evaluator or a caller assumption. Flapjack-only infrastructure;
there is no HOL declaration for this production carrier predicate. -/
def supportsCodec {α : Type u} : WordProg α → Bool
  | .inst (.arith (.addCarry _ _ _ _ _)) => false
  | .seq first second | .ite _ _ _ first second => supportsCodec first && supportsCodec second
  | .loop _ body _ | .mustTerminate body => supportsCodec body
  | .call returns _ _ handler =>
      (match returns with
       | none => true
       | some (_, _, body, _, _) => supportsCodec body) &&
      (match handler with
       | none => true
       | some (_, body, _, _) => supportsCodec body)
  | _ => true
termination_by program => sizeOf program

/-- Flapjack-only Option-domain packaging, with no separate HOL original. -/
theorem optionPairDomain {α β γ : Type} (first : Option α)
    (second : Option β) (make : α → β → γ) :
    (first.bind fun a => second.bind fun b => some (make a b)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

/-- Flapjack-only single-payload Option-domain packaging. -/
theorem optionMapDomain {α β : Type} (value : Option α) (make : α → β) :
    (value.bind fun a => some (make a)).isSome = value.isSome := by
  cases value <;> rfl

/-- Instruction-domain equality on every production constructor. Ordinary
16-bit memory is codec-accepted; only the distinct five-register arithmetic
primitive is rejected here. Flapjack-only codec infrastructure. -/
theorem instructionDomain {width : Nat} (instruction : WordInst (BitVec width)) :
    (wordLangInstToHOL instruction).isSome = supportsCodec (.inst instruction) := by
  cases instruction with
  | const destination value => simp [wordLangInstToHOL, supportsCodec]
  | arith operation => cases operation <;> simp [wordLangInstToHOL, wordLangArithToHOL, supportsCodec]
  | mem operation destination address => simp [wordLangInstToHOL, supportsCodec]
  | memOffset operation destination address offset => simp [wordLangInstToHOL, supportsCodec]

/-- Full proved equality with the actual encoder, including both optional
Call continuations. This is Flapjack-only carrier correspondence. -/
theorem codecDomain {width : Nat} (program : WordProg (BitVec width)) :
    (wordLangProgToHOL program).isSome = supportsCodec program := by
  -- The total colouring recursion supplies complete constructor induction,
  -- including both Call bodies; the colour values play no role here.
  fun_induction wordApplyColour (fun name => name) program <;>
    simp_all [wordLangProgToHOL, supportsCodec, instructionDomain,
      optionPairDomain, optionMapDomain]

end Flapjack.WordProgCarrierCodec
