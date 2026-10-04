import Flapjack.Compiler.Backend.LabToTarget.ComputedLabelDomain
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Encoding
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelSets
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelUpdates

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Original outer label-map domain result. No section uniqueness or accumulator
freshness guard is needed: insertion preserves the union of outer keys.
The paired label-domain result in ComputedLabelDomain is a distinct theorem. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem computeLabelsAlt_domain {width : Nat} [NeZero width] (pos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (labs : Spt (Spt Nat)) :
    sptDomain (computeLabelsAlt pos code labs) =
      Prod.fst '' getCodeLabels code ∪ sptDomain labs := by
  induction code generalizing pos labs with
  | nil =>
    ext n
    change sptDomain labs n ↔ ((∃ p, (∃ sec ∈ ([] : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))), p ∈ secGetCodeLabels sec) ∧ p.1 = n) ∨ sptDomain labs n)
    simp
  | cons sec rest ih =>
    generalize he : sectionLabels pos sec.lines [] = entry
    rcases entry with ⟨newPos, secLabs⟩
    simp only [computeLabelsAlt, he]
    rw [ih, sptDomainInsert, getCodeLabels_cons, Set.image_union]
    have hs : Prod.fst '' secGetCodeLabels sec = {sec.sectionId} := by
      ext n
      simp only [Set.mem_image, secGetCodeLabels, Set.mem_union,
        Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rcases hp with rfl | ⟨k, _, rfl⟩ <;> rfl
      · intro hn
        subst n
        exact ⟨(sec.sectionId, 0), Or.inl rfl, rfl⟩
    rw [hs]
    ext n
    change (n ∈ Prod.fst '' getCodeLabels rest ∨ n = sec.sectionId ∨ sptDomain labs n) ↔
      ((n = sec.sectionId ∨ n ∈ Prod.fst '' getCodeLabels rest) ∨ sptDomain labs n)
    tauto


/-- Full original loop domain conclusion, assuming only the observed successful
loop result. No clock bound, unique section ids, or successful target run. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem removeLabelsLoop_domain {width : Nat} [NeZero width]
    (clock : Nat) (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (code output : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (labs : Spt (Spt Nat))
    (he : removeLabelsLoop clock c pos acc ffis code = some (output, labs)) :
    sptDomain labs = Prod.fst '' getCodeLabels code ∪ sptDomain acc := by
  induction clock using Nat.strong_induction_on generalizing code output labs with
  | h clock ih =>
    generalize hf : encSecsAgain pos (computeLabelsAlt pos code acc) ffis c.encode code = first
    rcases first with ⟨first, done⟩
    rw [removeLabelsLoop.eq_def] at he
    dsimp only at he
    rw [hf] at he
    cases done with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at he
      split at he
      · contradiction
      · have hs := encSecsAgain_implies_similar pos _ ffis c.encode code first false hf
        have hr := ih (clock - 1) (by omega) first output labs he
        rw [← codeSimilar_codeLabels code first hs] at hr
        exact hr
    | true =>
      simp only [↓reduceIte] at he
      generalize hl : encSecsAgain pos (computeLabelsAlt pos (updLabLen pos first) acc)
        ffis c.encode (updLabLen pos first) = last at he
      rcases last with ⟨last, done⟩
      split at he
      · have heq := Option.some.inj he
        have hlabs : labs = computeLabelsAlt pos (updLabLen pos first) acc :=
          (congrArg Prod.snd heq).symm
        rw [hlabs, computeLabelsAlt_domain]
        have hs := encSecsAgain_implies_similar pos _ ffis c.encode code first true hf
        have hu := codeSimilar_sym (updLabLen pos first) first
          ((codeSimilar_updLabLen first pos first).mpr (codeSimilar_refl first))
        rw [← codeSimilar_codeLabels first (updLabLen pos first) hu,
          ← codeSimilar_codeLabels code first hs]
      · contradiction


/-- Original remove_labels domain conclusion for the observed complete result.
The initial encoding preserves the entire original code-label set. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem removeLabels_domain {width : Nat} [NeZero width]
    (clock : Nat) (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (code output : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (labs : Spt (Spt Nat))
    (he : removeLabels clock c pos acc ffis code = some (output, labs)) :
    sptDomain labs = Prod.fst '' getCodeLabels code ∪ sptDomain acc := by
  have hr := removeLabelsLoop_domain clock c pos acc ffis
    (encSecList c.encode code) output labs he
  have hs := (codeSimilar_encSecList code code c.encode).mpr (codeSimilar_refl code)
  rw [codeSimilar_codeLabels (encSecList c.encode code) code hs] at hr
  exact hr

end Flapjack.Compiler.Backend.LabToTarget
