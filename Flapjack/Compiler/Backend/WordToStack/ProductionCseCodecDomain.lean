import Flapjack.RiscV.WordCse
import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

namespace Flapjack
open RiscV

/-- Private structural view of the actual partial codec's domain. The theorem
below proves equality with the real encoder for every program. This is not an
alternate evaluator or a caller assumption. Flapjack-only infrastructure;
there is no HOL declaration for this production carrier predicate. -/
private def supportsCodec {α : Type u} : WordProg α → Bool
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
private theorem optionPairDomain {α β γ : Type} (first : Option α)
    (second : Option β) (make : α → β → γ) :
    (first.bind fun a => second.bind fun b => some (make a b)).isSome =
      (first.isSome && second.isSome) := by
  cases first <;> cases second <;> rfl

/-- Flapjack-only single-payload Option-domain packaging. -/
private theorem optionMapDomain {α β : Type} (value : Option α) (make : α → β) :
    (value.bind fun a => some (make a)).isSome = value.isSome := by
  cases value <;> rfl

/-- Instruction-domain equality on every production constructor. Ordinary
16-bit memory is codec-accepted; only the distinct five-register arithmetic
primitive is rejected here. Flapjack-only codec infrastructure. -/
private theorem instructionDomain {width : Nat} (instruction : WordInst (BitVec width)) :
    (wordLangInstToHOL instruction).isSome = supportsCodec (.inst instruction) := by
  cases instruction with
  | const destination value => simp [wordLangInstToHOL, supportsCodec]
  | arith operation => cases operation <;> simp [wordLangInstToHOL, wordLangArithToHOL, supportsCodec]
  | mem operation destination address => simp [wordLangInstToHOL, supportsCodec]
  | memOffset operation destination address offset => simp [wordLangInstToHOL, supportsCodec]

/-- Full proved equality with the actual encoder, including both optional
Call continuations. This is Flapjack-only carrier correspondence. -/
private theorem codecDomain {width : Nat} (program : WordProg (BitVec width)) :
    (wordLangProgToHOL program).isSome = supportsCodec program := by
  -- The total colouring recursion supplies complete constructor induction,
  -- including both Call bodies; the colour values play no role here.
  fun_induction wordApplyColour (fun name => name) program <;>
    simp_all [wordLangProgToHOL, supportsCodec, instructionDomain,
      optionPairDomain, optionMapDomain]

/-- Flapjack-only fact substitution preserves accepted program constructors. -/
private theorem factDomain {width : Nat} (data : WordCseKnowledge)
    (table : WordCseFactMap) (register : Nat) (key : List Nat)
    (instruction : WordProg (BitVec width))
    (insert : WordCseKnowledge → Nat → WordCseKnowledge)
    (accepted : supportsCodec instruction = true) :
    supportsCodec (wordCseAddToFact data table register key instruction insert).1 = true := by
  unfold wordCseAddToFact
  split <;> split <;> simp_all [supportsCodec]

/-- Flapjack-only constant fact recording emits the original accepted constant. -/
private theorem constantDomain {width : Nat} (data : WordCseKnowledge)
    (register : Nat) (value : BitVec width) :
    supportsCodec (wordCseAddToDataConst data register value).1 = true := by
  unfold wordCseAddToDataConst
  dsimp only
  split <;> simp [supportsCodec]

/-- Full actual instruction CSE codec domain, without well-formed knowledge
assumptions. The unsupported five-register primitive is never recorded. -/
private theorem cseInstructionDomain {width : Nat} (data : WordCseKnowledge)
    (instruction : WordInst (BitVec width)) :
    supportsCodec (wordCseInst data instruction).1 = supportsCodec (.inst instruction) := by
  cases instruction with
  | arith operation =>
    cases operation <;>
      simp [wordCseInst, wordCseCanonicalArith, wordCseCanMemArith,
        wordCseAddToData, supportsCodec]
    all_goals repeat' (split <;> simp_all [supportsCodec, factDomain])
  | const register value =>
    simp [wordCseInst, supportsCodec]
    split <;> simp_all [supportsCodec, constantDomain]
  | mem operator register address =>
    simp only [wordCseInst]
    repeat' (split <;> simp_all [supportsCodec, wordCseAddToLoad, factDomain])
  | memOffset operator register address offset =>
    simp only [wordCseInst]
    repeat' (split <;> simp_all [supportsCodec, wordCseAddToLoad, factDomain])

/-- Full production CSE recursion, with arbitrary knowledge and both Call
continuations. Flapjack-only carrier closure, not a HOL theorem port. -/
private theorem cseDomain {width : Nat} (data : WordCseKnowledge)
    (program : WordProg (BitVec width)) :
    supportsCodec (wordCseProg data program).1 = supportsCodec program := by
  fun_induction wordApplyColour (fun name => name) program generalizing data <;>
    simp_all [wordCseProg, supportsCodec, cseInstructionDomain,
      factDomain]
  case case3 =>
    unfold wordCseProg
    split <;> simp_all [supportsCodec, wordCseAddToLoad]
    repeat' (split <;> simp_all [supportsCodec, factDomain])
  case case5 =>
    rename_i destination store
    cases (wordCseInvalidate data destination).getsMem[wordCseStoreCode store]? <;>
      simp_all
    all_goals split <;> simp_all [supportsCodec]
  case case7 =>
    cases ‹WordExp (BitVec width)› <;> simp_all
    all_goals repeat' (split <;> simp_all [supportsCodec])
  all_goals repeat' (split <;> simp_all [supportsCodec, factDomain])

/-- Complete native codec-domain equality through the actual executed CSE
recursion for arbitrary knowledge. No desired output, valid-knowledge, codec
success or successful-pass premise is assumed. Flapjack-only infrastructure;
there is no HOL original theorem about the production partial codec. -/
theorem wordLangProgToHOL_wordCseProg_isSome {width : Nat}
    (data : WordCseKnowledge) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordCseProg data program).1).isSome =
      (wordLangProgToHOL program).isSome := by
  rw [codecDomain, codecDomain]
  exact cseDomain data program

/-- The actual production CSE wrapper preserves exactly the codec domain.
Other optimization passes and native frame/route remain separate obligations.
Flapjack-only carrier infrastructure, not a HOL port. -/
theorem wordLangProgToHOL_wordCseProp_isSome {width : Nat}
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordCseProp program)).isSome =
      (wordLangProgToHOL program).isSome :=
  wordLangProgToHOL_wordCseProg_isSome wordCseEmpty program

end Flapjack
