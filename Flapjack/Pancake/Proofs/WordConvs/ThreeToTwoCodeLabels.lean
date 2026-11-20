module

public import Flapjack.Pancake.Proofs.WordConvs.ThreeToTwo
public import Flapjack.Pancake.WordConvs.CodeLabels

@[expose] public section

/-!
Code-label preservation for the native optional three-to-two register pass.
Kept in a sibling module so that the `Set`-based statement does not enter
`CompileSingle`'s or `CompileConventions.Labels`'s environment.
-/

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordInst

/-- Original label equality for the whole optional three-to-two pass: enabling
the pass leaves the code-label set unchanged. HOL's free flag `b` is the
leading binder and `ps` is universal. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_three_to_two_reg_prog" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_threeToTwoRegProg {width : Nat} [NeZero width]
    (b : Bool) (ps : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (threeToTwoRegProg b ps) = getCodeLabelsHOL ps := by
  cases b with
  | false => simp [threeToTwoRegProg]
  | true =>
    simp only [threeToTwoRegProg, if_true]
    induction ps using
        (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
    | h ps ih =>
      cases ps <;> try simp_all +zetaDelta [threeToTwoReg, getCodeLabelsHOL]
      case inst instruction =>
        cases instruction <;> try simp_all +zetaDelta [threeToTwoReg, getCodeLabelsHOL]
        case arith operation =>
          cases operation <;> simp_all +zetaDelta [threeToTwoReg, getCodeLabelsHOL]
      case seq p1 p2 =>
        have h1 : WellFoundedRelation.rel p1
            (.seq p1 p2 : WordLangProgHOL (BitVec width)) := by
          change sizeOf p1 < sizeOf (.seq p1 p2 : WordLangProgHOL (BitVec width))
          simp
          omega
        have h2 : WellFoundedRelation.rel p2
            (.seq p1 p2 : WordLangProgHOL (BitVec width)) := by
          change sizeOf p2 < sizeOf (.seq p1 p2 : WordLangProgHOL (BitVec width))
          simp
          omega
        rw [ih p1 h1, ih p2 h2]
      case mustTerminate p1 =>
        have h1 : WellFoundedRelation.rel p1
            (.mustTerminate p1 : WordLangProgHOL (BitVec width)) := by
          change sizeOf p1 < sizeOf (.mustTerminate p1 : WordLangProgHOL (BitVec width))
          simp
        rw [ih p1 h1]
      case ite cmp r1 ri c1 c2 =>
        have h1 : WellFoundedRelation.rel c1
            (.ite cmp r1 ri c1 c2 : WordLangProgHOL (BitVec width)) := by
          change sizeOf c1 < sizeOf (.ite cmp r1 ri c1 c2 : WordLangProgHOL (BitVec width))
          simp
          omega
        have h2 : WellFoundedRelation.rel c2
            (.ite cmp r1 ri c1 c2 : WordLangProgHOL (BitVec width)) := by
          change sizeOf c2 < sizeOf (.ite cmp r1 ri c1 c2 : WordLangProgHOL (BitVec width))
          simp
          omega
        rw [ih c1 h1, ih c2 h2]
      case loop names body exitNames =>
        have hbody : WellFoundedRelation.rel body
            (.loop names body exitNames : WordLangProgHOL (BitVec width)) := by
          change sizeOf body < sizeOf
            (.loop names body exitNames : WordLangProgHOL (BitVec width))
          simp
          omega
        rw [ih body hbody]
      case call ret dest args handler =>
        cases ret with
        | none =>
          cases handler with
          | none => simp [threeToTwoReg, getCodeLabelsHOL]
          | some h =>
            obtain ⟨n, body, l1, l2⟩ := h
            have hbody : WellFoundedRelation.rel body
                (.call none dest args (some (n, body, l1, l2)) :
                  WordLangProgHOL (BitVec width)) := by
              change sizeOf body < sizeOf
                (.call none dest args (some (n, body, l1, l2)) :
                  WordLangProgHOL (BitVec width))
              simp
              omega
            simp only [threeToTwoReg, getCodeLabelsHOL]
            rw [ih body hbody]
        | some r =>
          obtain ⟨n, names, rh, l1, l2⟩ := r
          cases handler with
          | none =>
            have hbody : WellFoundedRelation.rel rh
                (.call (some (n, names, rh, l1, l2)) dest args none :
                  WordLangProgHOL (BitVec width)) := by
              change sizeOf rh < sizeOf
                (.call (some (n, names, rh, l1, l2)) dest args none :
                  WordLangProgHOL (BitVec width))
              simp
              omega
            simp only [threeToTwoReg, getCodeLabelsHOL]
            rw [ih rh hbody]
          | some h =>
            obtain ⟨m, hb, hl1, hl2⟩ := h
            have hret : WellFoundedRelation.rel rh
                (.call (some (n, names, rh, l1, l2)) dest args (some (m, hb, hl1, hl2)) :
                  WordLangProgHOL (BitVec width)) := by
              change sizeOf rh < sizeOf
                (.call (some (n, names, rh, l1, l2)) dest args (some (m, hb, hl1, hl2)) :
                  WordLangProgHOL (BitVec width))
              simp
              omega
            have hhandler : WellFoundedRelation.rel hb
                (.call (some (n, names, rh, l1, l2)) dest args (some (m, hb, hl1, hl2)) :
                  WordLangProgHOL (BitVec width)) := by
              change sizeOf hb < sizeOf
                (.call (some (n, names, rh, l1, l2)) dest args (some (m, hb, hl1, hl2)) :
                  WordLangProgHOL (BitVec width))
              simp
              omega
            simp only [threeToTwoReg, getCodeLabelsHOL]
            rw [ih rh hret, ih hb hhandler]

end Flapjack.WordConvs
