import Flapjack.RiscV.WordSimp
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack
open RiscV WordProgCarrierCodec

private theorem smartSeqDomain {α : Type u} (first second : WordProg α) :
    supportsCodec (wordSimpSmartSeq first second) =
      (supportsCodec first && supportsCodec second) := by
  unfold wordSimpSmartSeq
  split <;> simp_all [supportsCodec]

private theorem foldDomain {α : Type u} (pieces : List (WordProg α))
    (first : WordProg α) (initial : supportsCodec first = true)
    (accepted : ∀ p ∈ pieces, supportsCodec p = true) :
    supportsCodec (pieces.foldl wordSimpSmartSeq first) = true := by
  induction pieces generalizing first with
  | nil => exact initial
  | cons p ps ih =>
    apply ih
    · simp [smartSeqDomain, initial, accepted p (by simp)]
    · intro p hp; exact accepted p (by simp [hp])

private theorem leftSeqDomain {α : Type u} (pieces : List (WordProg α))
    (accepted : ∀ p ∈ pieces, supportsCodec p = true) :
    supportsCodec (wordSimpLeftSeq pieces) = true := by
  cases pieces with
  | nil => simp [wordSimpLeftSeq, supportsCodec]
  | cons p ps =>
    exact foldDomain ps p (accepted p (by simp)) (by
      intro q hq; exact accepted q (by simp [hq]))

private theorem leftItemsDomain {α : Type u} (pieces : List (WordProg α))
    (accepted : ∀ p ∈ pieces, supportsCodec p = true) :
    ∀ p ∈ wordSimpLeftSeqItems pieces, supportsCodec p = true := by
  fun_induction wordSimpLeftSeqItems pieces <;>
    simp_all [supportsCodec]

private theorem assocItemsDomain {α : Type u} (fuel : Nat) (program : WordProg α)
    (accepted : supportsCodec program = true) :
    ∀ p ∈ wordSimpSeqAssocItemsFuel fuel program, supportsCodec p = true := by
  induction fuel generalizing program with
  | zero => simpa [wordSimpSeqAssocItemsFuel] using accepted
  | succ fuel ih =>
    have left (p : WordProg α) (h : supportsCodec p = true) :
        supportsCodec (wordSimpLeftSeq (wordSimpSeqAssocItemsFuel fuel p)) = true :=
      leftSeqDomain _ (ih p h)
    cases program <;> simp_all [wordSimpSeqAssocItemsFuel, supportsCodec]
    case seq first second =>
      apply leftItemsDomain
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih first accepted.1 p hp
      · exact ih second accepted.2 p hp
    case call returns target arguments handler =>
      rcases returns with (_ | ⟨names, cutsets, body, label, entry⟩) <;>
        rcases handler with (_ | ⟨exception, handlerBody, handlerLabel, handlerEntry⟩) <;>
        simp_all [supportsCodec]

private theorem assocDomain {α : Type u} (program : WordProg α)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordSimpSeqAssoc program) = true :=
  leftSeqDomain _ (assocItemsDomain _ program accepted)

private theorem dropDomain {α : Type} (constants : NatInfoMap α) (names : List Nat) :
    supportsCodec (wordSimpDropConsts constants names) = true := by
  induction names with
  | nil => simp [wordSimpDropConsts, supportsCodec]
  | cons name names ih =>
    simp only [wordSimpDropConsts]
    split <;> simp_all [supportsCodec, smartSeqDomain]

/-- Flapjack-only carrier closure of the actual constant-propagation recursion,
with an arbitrary initial knowledge map, including both optional Call bodies.
The only premise is source codec acceptance, not a desired output relation.
Constant branch elimination can remove rejected code, so this is an implication
rather than acceptance/rejection equality. No HOL semantic equivalence is claimed. -/
theorem supportsCodec_wordConstFpLoop {α : Type}
    [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 1] [OfNat α 0] [DecidableEq α]
    [PanCmp α] [WordSimpShift α]
    (program : WordProg α) (constants : NatInfoMap α)
    (accepted : supportsCodec program = true) :
    supportsCodec (wordConstFpLoop program constants).1 = true := by
  fun_induction wordConstFpLoop program constants
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [supportsCodec, smartSeqDomain, dropDomain]

/-- The actual production constant pass first reassociates the program and then
starts its recursion with empty knowledge. Both real stages preserve acceptance;
this is untagged carrier infrastructure, not a port of HOL's pass semantics. -/
theorem supportsCodec_wordConstFp {α : Type}
    [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 1] [OfNat α 0] [DecidableEq α]
    [PanCmp α] [WordSimpShift α]
    (program : WordProg α) (accepted : supportsCodec program = true) :
    supportsCodec (wordConstFp program) = true :=
  supportsCodec_wordConstFpLoop _ [] (assocDomain program accepted)

/-- Actual native partial-codec acceptance of the production constant pass,
derived from input acceptance at any positive width. No output premise or
semantic simulation is assumed; there is no corresponding HOL codec theorem. -/
theorem wordLangProgToHOL_wordConstFp_isSome {width : Nat} [NeZero width]
    (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordConstFp program)).isSome = true := by
  rw [codecDomain] at accepted ⊢
  exact supportsCodec_wordConstFp program accepted

end Flapjack
