import Flapjack.Compiler.Backend.WordToStackRegFormat

/-! Native move lowering for the literal Word-to-Stack compiler.
All source scheduler and formatting operations are retained; this does not
establish move evaluation correctness or change the executed compiler route.
-/
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang
open WordToStackRegFormat (formatVar)

/-- Literal native wMoveSingle on the shared positive word-width carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wMoveSingle_def"
  (words_as_type_indexed_bitvec)]
def wMoveSingleNative {width : Nat} [NeZero width] (xy : Sum Nat Nat × Sum Nat Nat)
    (kf : Nat × Nat × Nat) : HolProg width :=
  match xy with
  | (.inl r1, .inl r2) => .inst (.arith (.binop .or r1 r2 (.reg r2)))
  | (.inl r1, .inr r2) => .stackLoad r1 (kf.2.1 - 1 - (r2 - kf.1))
  | (.inr r1, .inl r2) => .stackStore r2 (kf.2.1 - 1 - (r1 - kf.1))
  | (.inr r1, .inr r2) =>
    .seq (.stackLoad kf.1 (kf.2.1 - 1 - (r2 - kf.1)))
      (.stackStore kf.1 (kf.2.1 - 1 - (r1 - kf.1)))

/-- Literal native wMoveAux on the shared positive word-width carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wMoveAux_def"
  (words_as_type_indexed_bitvec)]
def wMoveAuxNative {width : Nat} [NeZero width] : List (Sum Nat Nat × Sum Nat Nat) → Nat × Nat × Nat → HolProg width
  | [], _ => .skip
  | [xy], kf => wMoveSingleNative xy kf
  | xy :: xys, kf => .seq (wMoveSingleNative xy kf) (wMoveAuxNative xys kf)

/-- Literal native wMove on the shared positive word-width carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wMove_def"
  (words_as_type_indexed_bitvec)]
def wMoveNative {width : Nat} [NeZero width] (moves : List (Nat × Nat))
    (kf : Nat × Nat × Nat) : HolProg width :=
  let scheduled := Flapjack.Compiler.Backend.Parmove.parmove
    (moves.map (fun move => (move.1 / 2, move.2 / 2)))
  wMoveAuxNative (scheduled.map (fun move => (formatVar kf.1 move.1, formatVar kf.1 move.2))) kf

/-- Flapjack-only payload transport for every formatted source/destination pair. -/
theorem map_wMoveSingleNative {width : Nat} [NeZero width]
    (xy : Sum Nat Nat × Sum Nat Nat) (kf : Nat × Nat × Nat) :
    Prog.map HolInst.toWordLangInst id HolRegImm.toWordRegImm id id
      HolAddr.toWordLangAddr id (wMoveSingleNative (width := width) xy kf) =
      WordToStackRegFormat.wMoveSingle (α := BitVec width) xy kf := by
  rcases xy with ⟨x, y⟩
  cases x <;> cases y <;> simp [wMoveSingleNative, WordToStackRegFormat.wMoveSingle,
    StackLang.Prog.map, HolInst.toWordLangInst, HolArith.toWordLangArith,
    HolRegImm.toWordRegImm]

/-- Flapjack-only payload transport preserves literal empty/singleton sequencing. -/
theorem map_wMoveAuxNative {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    Prog.map HolInst.toWordLangInst id HolRegImm.toWordRegImm id id
      HolAddr.toWordLangAddr id (wMoveAuxNative (width := width) moves kf) =
      WordToStackRegFormat.wMoveAux (α := BitVec width) moves kf := by
  induction moves with
  | nil => simp [wMoveAuxNative, WordToStackRegFormat.wMoveAux, StackLang.Prog.map]
  | cons xy rest ih =>
    cases rest with
    | nil => exact map_wMoveSingleNative xy kf
    | cons next tail =>
      simp only [wMoveAuxNative, WordToStackRegFormat.wMoveAux, Prog.map,
        map_wMoveSingleNative, ih]

/-- Flapjack-only all-input relation to the accepted exact generic helper.
No scheduler-success, result, bound or target-evaluation premise is assumed. -/
theorem map_wMoveNative {width : Nat} [NeZero width]
    (moves : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    Prog.map HolInst.toWordLangInst id HolRegImm.toWordRegImm id id
      HolAddr.toWordLangAddr id (wMoveNative (width := width) moves kf) =
      WordToStackRegFormat.wMove (width := width) moves kf := by
  exact map_wMoveAuxNative _ kf

end Flapjack.Compiler.Backend.WordToStack.Native
