import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "prog_to_bytes_APPEND"
  (words_as_type_indexed_bitvec)]
theorem progToBytes_append {width : Nat} [NeZero width] (c1 c2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    progToBytes (c1 ++ c2) = progToBytes c1 ++ progToBytes c2 := by
  simp [progToBytesMap, List.map_append, List.flatten_append]

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_line_byte_length"
  (words_as_type_indexed_bitvec)]
theorem lineOk_lineByteLength {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffi : List HolFfiName)
    (n : Nat) (l : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineOk c labs ffi n l → (lineBytes l).length = LabProps.lineLength l := by
  cases l with
  | label l1 l2 length =>
      intro h
      simp only [lineOk] at h
      simp [lineBytes, LabProps.lineLength, h.2]
  | asm instruction bytes length => intro _; rfl
  | labAsm instruction word bytes length => intro _; rfl

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_ok_MAP_line_byte_length"
  (words_as_type_indexed_bitvec)]
theorem linesOk_mapLineByteLength {width : Nat} [NeZero width]
    (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffi : List HolFfiName) (n : Nat) :
    linesOk c labs ffi n ls →
    (ls.map lineBytes).map List.length = ls.map LabProps.lineLength := by
  intro h
  induction ls generalizing n with
  | nil => rfl
  | cons l ls ih =>
      change lineOk c labs ffi n l ∧
        linesOk c labs ffi (n + LabProps.lineLength l) ls at h
      simp only [List.map_cons]
      rw [lineOk_lineByteLength c labs ffi n l h.1, ih _ h.2]

/-- Full original local even-output theorem. Its universally quantified `n : β`
is absent from every hypothesis and the conclusion, as the fresh original full
type capture confirms; this vacuous binder is omitted, with no width or position
specialization. The original start-position and full validity guards remain. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_prog_to_bytes_EVEN"
  (words_as_type_indexed_bitvec)]
theorem allEncOk_progToBytes_even {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffi : List HolFfiName) (pos : Nat) :
    pos % 2 = 0 ∧ allEncOk c labs ffi pos code → (progToBytes code).length % 2 = 0 := by
  intro h
  induction code generalizing pos with
  | nil => simp [progToBytes]
  | cons sec code ih =>
      rcases sec with ⟨k, ls⟩
      have hs := (allEncOk_cons c labs ffi ls pos k code).mp h.2
      have ht := ih (pos + (ls.map LabProps.lineLength).sum) ⟨hs.2.1, hs.1⟩
      have hl : ((ls.map lineBytes).flatten).length = (ls.map LabProps.lineLength).sum := by
        rw [List.length_flatten, linesOk_mapLineByteLength ls c labs ffi pos hs.2.2]
      rw [progToBytesMap]
      simp only [List.map_cons, List.flatten_cons]
      rw [List.length_append, hl, ← progToBytesMap code]
      have he := hs.2.1
      omega

end Flapjack.Compiler.Backend.LabToTarget
