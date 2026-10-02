import Flapjack.Compiler.Backend.LabToTarget.NopInvariant
import Flapjack.Compiler.Backend.LabToTarget.AddNopProps
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack proof infrastructure: increment the witness from the original
encWithNop_iff. There is no separately named HOL declaration for this factoring. -/
private theorem encWithNop_appendSkip {width : Nat} [NeZero width] {Value : Type}
    (enc : HolAsm width → List Value) (x : HolAsm width) (bytes : List Value)
    (h : encWithNop enc x bytes) : encWithNop enc x (bytes ++ enc (.inst .skip)) := by
  rcases (encWithNop_iff enc x bytes).mp h with ⟨count,hbytes⟩
  apply (encWithNop_iff enc x _).mpr
  refine ⟨count+1, ?_⟩
  have hr : List.replicate (count+1) (enc (.inst .skip)) =
      List.replicate count (enc (.inst .skip)) ++ [enc (.inst .skip)] := by
    simpa using (List.replicate_append_replicate (n := count) (m := 1)
      (a := enc (.inst .skip))).symm
  simp [hbytes,hr,List.flatten_append,List.append_assoc]

/-- Flapjack constructor proof factoring for the original NOP insertion clause;
no separately named HOL declaration is being ported by this helper. -/
private theorem labAsm_appendSkip {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat)
    (a : AsmWithLab HolCmp (HolRegImm width) MlString) (w : BitVec width)
    (bytes : List (BitVec 8)) (len : Nat) (hnop : (enc (.inst .skip)).length = 1)
    (h : lineEncWithNop enc labs ffis pos (.labAsm a w bytes len)) :
    lineEncWithNop enc labs ffis pos
      (.labAsm a w (bytes ++ enc (.inst .skip)) (len+1)) := by
  cases a <;> simp only [lineEncWithNop] at h ⊢
  all_goals first
    | exact ⟨encWithNop_appendSkip enc _ bytes h.1, by simp [List.length_append,h.2,hnop]⟩
    | simp [List.length_append,h,hnop]

/-- Full original reverse-accumulator preservation, retaining the one-byte NOP
guard and every native line constructor. Word dimension is the sole representation
translation; no extra label or length-correctness premise is assumed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_add_nop"
  (words_as_type_indexed_bitvec)]
theorem linesEncWithNop_addNop {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat)
    (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (enc (.inst .skip)).length = 1 ∧ linesEncWithNop enc labs ffis pos ls.reverse →
    linesEncWithNop enc labs ffis pos (addNop (enc (.inst .skip)) ls).reverse := by
  induction ls with
  | nil => simp [addNop,linesEncWithNop]
  | cons line rest ih =>
    rintro ⟨hnop,hvalid⟩
    rw [List.reverse_cons,linesEncWithNop_append] at hvalid
    rcases hvalid with ⟨hpre,hpost⟩
    cases line with
    | label k1 k2 len =>
      have hz : len = 0 := hpost.1
      have hr := ih ⟨hnop,hpre⟩
      simp only [addNop,List.reverse_cons,linesEncWithNop_append]
      exact ⟨hr, by simp [linesEncWithNop,lineEncWithNop,hz]⟩
    | asm a bytes len =>
      have he : encWithNop enc (cbwToAsmExact a) bytes := hpost.1.1
      have hlen : bytes.length = len := hpost.1.2
      simp only [addNop,List.reverse_cons,linesEncWithNop_append]
      refine ⟨hpre, ?_⟩
      exact ⟨⟨encWithNop_appendSkip enc _ bytes he,
        by simp [List.length_append,hlen,hnop]⟩, trivial⟩
    | labAsm a w bytes len =>
      simp only [addNop,List.reverse_cons,linesEncWithNop_append]
      exact ⟨hpre, labAsm_appendSkip enc labs ffis _ a w bytes len hnop hpost.1, trivial⟩
end Flapjack.Compiler.Backend.LabToTarget
