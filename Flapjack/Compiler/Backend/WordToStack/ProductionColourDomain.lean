import Flapjack.RiscV.Allocator
import Flapjack.RiscV.AllocatorMemoryInvariant
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

namespace Flapjack

/-- The actual instruction colouring retains the existing memory guard,
including the unchanged 16-bit catchall forms. Flapjack-only infrastructure;
there is no corresponding guard in HOL. -/
private theorem instructionMemoryGuard {α : Type u} (colour : Nat → Nat)
    (instruction : WordInst α) :
    RiscV.allocatorMemorySupported (.inst (wordApplyColourInst colour instruction)) =
      RiscV.allocatorMemorySupported (.inst instruction) := by
  cases instruction
  all_goals try cases ‹WordMemOp›
  all_goals
    dsimp only [wordApplyColourInst, WordAlloc.applyColourInstExecutable,
      WordAlloc.applyColourInstCore] <;>
    simp only [RiscV.allocatorMemorySupported]

/-- Instruction colouring retains precisely the partial codec's domain.
The distinct five-register AddCarry stays rejected. This correspondence
between Flapjack carriers has no HOL original. -/
private theorem instructionCodecDomain {width : Nat} (colour : Nat → Nat)
    (instruction : WordInst (BitVec width)) :
    (wordLangInstToHOL (wordApplyColourInst colour instruction)).isSome =
      (wordLangInstToHOL instruction).isSome := by
  cases instruction with
  | const destination value => rfl
  | arith operation => cases operation <;> rfl
  | mem operation destination address => cases operation <;> rfl
  | memOffset operation destination address offset => cases operation <;> rfl

/-- Complete recursive preservation of the existing production memory guard.
No supported-input premise, injectivity, register bound or successful pass is
assumed. Both Call continuations are traversed even for a nonreturning Call.
Flapjack-only guard infrastructure, not a HOL theorem port. -/
theorem allocatorMemorySupported_wordApplyColour {α : Type u}
    (colour : Nat → Nat) (program : WordProg α) :
    RiscV.allocatorMemorySupported (wordApplyColour colour program) =
      RiscV.allocatorMemorySupported program := by
  fun_induction wordApplyColour colour program <;>
    simp_all only [RiscV.allocatorMemorySupported,
      instructionMemoryGuard]

/-- Flapjack-only Option product-domain packaging; constructing the payload
does not introduce a further failure point. -/
private theorem optionPairDomain {α β γ : Type} (first : Option α)
    (second : Option β) (make : α → β → γ) :
    (first.bind fun a => second.bind fun b => some (make a b)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

/-- Flapjack-only domain packaging for one successful payload constructor. -/
private theorem optionMapDomain {α β : Type} (value : Option α) (make : α → β) :
    (value.bind fun a => some (make a)).isSome = value.isSome := by
  cases value <;> rfl

/-- The actual whole-program colouring preserves precisely the existing
partial WordLang codec domain, including both Call continuations and every
recursive constructor. Arbitrary colliding/unbounded colours are allowed;
no successful codec or source-image premise is assumed. This is Flapjack
carrier infrastructure. It does not prove the initial source-to-SSA image,
the full maximum correspondence or the executed native compiler route. -/
theorem wordLangProgToHOL_wordApplyColour_isSome {width : Nat}
    (colour : Nat → Nat) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordApplyColour colour program)).isSome =
      (wordLangProgToHOL program).isSome := by
  fun_induction wordApplyColour colour program <;>
    simp_all [wordLangProgToHOL, instructionCodecDomain,
      optionPairDomain, optionMapDomain]

end Flapjack
