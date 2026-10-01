import Flapjack.Compiler.Backend.WordToStack.ProductionSelectorPrelude

namespace Flapjack
open RiscV WordProgCarrierCodec

private theorem selectSeqDomain {α : Type u} (first second : WordProg α) :
    supportsCodec (wordDeadSelectSeq first second) =
      (supportsCodec first && supportsCodec second) := by
  unfold wordDeadSelectSeq
  split <;> simp_all [supportsCodec]

private theorem selectedSeqDomain {α : Type u} (first second result : WordProg α)
    (equation : wordDeadSelectSeq first second = result)
    (left : supportsCodec first = true) (right : supportsCodec second = true) :
    supportsCodec result = true := by
  rw [← equation, selectSeqDomain, left, right]
  rfl

/-- Flapjack-only structural domain equality for the actual executed whole
instruction selector. It covers arbitrary programs, temporaries, immediate
policies and both optional Call bodies, and preserves codec rejection too.
This is carrier closure, not a HOL selector-semantics or native-routing port. -/
theorem supportsCodec_wordInstSelectProgram {α : Type u}
    [Sub α] [Add α] [AndOp α] [OrOp α] [HXor α α α]
    [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α] [WordInstSelectConstants α]
    (temporary : Nat) (program : WordProg α) :
    supportsCodec (wordInstSelectProgram temporary program) = supportsCodec program := by
  have atom (e : WordExp α) (t : Nat) (p : WordProg α) (s : WordExp α)
      (equation : wordInstSelectAtom t e = (p,s)) : supportsCodec p = true := by
    simpa only [equation, Prod.fst] using supportsCodec_wordInstSelectAtom t e
  have address (e : WordExp α) (t : Nat) (p : WordProg α) (s : WordExp α)
      (equation : wordInstSelectAddressAtom t e = (p,s)) : supportsCodec p = true := by
    simpa only [equation, Prod.fst] using supportsCodec_wordInstSelectAddressAtom t e
  fun_induction wordInstSelectProgram temporary program
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat' split
  all_goals repeat' split at *
  all_goals subst_vars
  all_goals simp_all [supportsCodec, selectSeqDomain]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply atom; assumption)
    | (apply address; assumption)
    | (apply selectedSeqDomain; assumption; (apply atom; assumption); simp [supportsCodec])

/-- Exact acceptance/rejection equality for the real native partial codec
before and after actual whole-program selection at every positive word width.
Flapjack-only carrier closure; no desired output-codec premise is supplied. -/
theorem wordLangProgToHOL_wordInstSelectProgram_isSome {width : Nat} [NeZero width]
    (temporary : Nat) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordInstSelectProgram temporary program)).isSome =
      (wordLangProgToHOL program).isSome := by
  rw [codecDomain, codecDomain, supportsCodec_wordInstSelectProgram]

/-- The actual production wrapper computes its own temporary from source
variables. Unbounded natural register names and the maximum computation add
no new caller assumption to codec-domain preservation. -/
theorem wordLangProgToHOL_wordInstSelectProgramFrom_isSome {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordInstSelectProgramFrom program)).isSome =
      (wordLangProgToHOL program).isSome := by
  unfold wordInstSelectProgramFrom
  exact wordLangProgToHOL_wordInstSelectProgram_isSome _ program

end Flapjack
