import Flapjack.Compiler.Backend.LabToTarget.Alignment
import Flapjack.Compiler.Backend.LabToTarget.CodeLabelPositionPadding
import Flapjack.Compiler.Backend.LabToTarget.CodeNopEncoding
import Flapjack.Compiler.Backend.LabToTarget.CodeOffsetPadding
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Encoding
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelSets
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.LabelUpdates
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding
import Flapjack.Compiler.Backend.LabToTarget.ComputedLabelDomain
import Flapjack.Compiler.Backend.LabToTarget.ComputedLabelPositions
import Flapjack.Compiler.Backend.LabToTarget.ComputedLabelPreservation
import Flapjack.Compiler.Backend.LabToTarget.EncodingInvariant
import Flapjack.Compiler.Backend.LabToTarget.EndingLabels
import Flapjack.Compiler.Backend.LabToTarget.LabelAnnotations
import Flapjack.Compiler.Backend.LabToTarget.LabelExistenceDomain
import Flapjack.Compiler.Backend.LabToTarget.LabelExistenceEncoding
import Flapjack.Compiler.Backend.LabToTarget.LabelLookup
import Flapjack.Compiler.Backend.LabToTarget.LabelLookupEvenness
import Flapjack.Compiler.Backend.LabToTarget.LabelPositionEncoding
import Flapjack.Compiler.Backend.LabToTarget.LabelPositionUpdates
import Flapjack.Compiler.Backend.LabToTarget.LabelValidity
import Flapjack.Compiler.Backend.LabToTarget.Navigation
import Flapjack.Compiler.Backend.LabToTarget.NopInvariant
import Flapjack.Compiler.Backend.LabToTarget.OddInstructionAlignment
import Flapjack.Compiler.Backend.LabToTarget.OffsetEstablishment
import Flapjack.Compiler.Backend.LabToTarget.PaddingLabels
import Flapjack.Compiler.Backend.LabToTarget.PositionalEncoding
import Flapjack.Compiler.Backend.LabToTarget.PreconditionPreservation
import Flapjack.Compiler.Backend.LabToTarget.PrefixPreservation
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Compiler.Backend.LabToTarget.StrongEvenLabels
import Flapjack.Compiler.Backend.LabToTarget.UpdateZero
import Flapjack.Compiler.Backend.LabToTarget.ValidityEstablishment
import Flapjack.Compiler.Backend.LabToTarget.ZeroLabelExistence
import Flapjack.Compiler.Backend.LabToTarget.ZeroPositionEvenLabels
import Flapjack.Compiler.Backend.LabToTarget.ZeroPreservation
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack proof packaging of the eleven non-execution guards. No independently
named HOL declaration; the final port expands these fields in its statement. -/
private structure LoopGuards {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (code : List (Section (LabLineHOL width))) : Prop where
  ends : ∀ sec ∈ code, secEndsWithLabelNative sec
  valid : ∀ sec ∈ code, secLabelsOk sec
  ids : (code.map Section.sectionId).Nodup
  labels : ∀ sec ∈ code, (extractLabels sec.lines).Nodup
  disjoint : Disjoint (sptDomain acc) {n | n ∈ code.map Section.sectionId}
  subset : restrictNonzero (getLabels code) ⊆ getCodeLabels code ∪ labsDomain acc
  pre : allEncOkPreHOL c code
  encd : allEncd0 c.encode code
  encoder : encOk c
  even : pos % 2 = 0
  accEven : ∀ sid lid, match labLookup sid lid acc with
    | none => True
    | some value => value % 2 = 0

/-- Flapjack proof packaging of the original eight conclusions, with no new
premises or omitted clauses. It has no independently named HOL declaration. -/
private def LoopResult {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (code output : List (Section (LabLineHOL width)))
    (labs : Spt (Spt Nat)) : Prop :=
  allEncOkPreHOL c output ∧ (∀ sec ∈ output, secLabelsOk sec) ∧
  allEncOk c labs ffis pos output ∧ codeSimilar code output ∧
  (hasOddInst output → c.codeAlignment = 0) ∧
  (∀ sid lid value, labLookup sid lid labs = some value → value % 2 = 0) ∧
  (∀ sid lid value, labLookup sid lid acc = some value → labLookup sid lid labs = some value) ∧
  (∀ sid lid pc, locToPc sid lid code = some pc →
    labLookup sid lid labs = some (posVal pc pos output))

/-- Flapjack induction infrastructure: transport the original guard package
through the actual arbitrary-flag repeated encoder result. No desired output
validity or returned label-map property is assumed. -/
private theorem LoopGuards.encode {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (pos : Nat) (acc labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (code result : List (Section (LabLineHOL width)))
    (flag : Bool) (h : LoopGuards c pos acc code)
    (he : encSecsAgain pos labs ffis c.encode code = (result,flag)) :
    LoopGuards c pos acc result := by
  have hs := encSecsAgain_implies_similar pos labs ffis c.encode code result flag he
  have hi := codeSimilar_sectionNumbers code result hs
  have hl := codeSimilar_extractedLabels code result hs
  have hsub := codeSimilar_labels code result hs
  have hcode := codeSimilar_codeLabels code result hs
  refine ⟨encSecsAgain_endsWithLabel pos labs ffis c.encode code result flag ⟨he,h.ends⟩,
    encSecsAgain_secLabelsOk pos labs ffis c.encode code result flag ⟨he,h.valid⟩,
    hi ▸ h.ids, ?_, ?_, ?_,
    encSecsAgain_pre pos labs ffis c.encode code result flag c ⟨he,h.pre⟩,
    encSecsAgain_encd0 pos labs ffis c.encode code result flag ⟨he,h.encd⟩,
    h.encoder,h.even,h.accEven⟩
  · have hAll : ∀ labels ∈ code.map (fun sec => extractLabels sec.lines),labels.Nodup := by
      simpa only [List.forall_mem_map] using h.labels
    rw [hl] at hAll
    simpa only [List.forall_mem_map] using hAll
  · simpa only [hi] using h.disjoint
  · simpa only [hsub,hcode] using h.subset

/-- Flapjack proof infrastructure for the successful original loop branch.
The additional equalities/Boolean facts select the actual source branch; no
post-state correctness property or simulation callback is assumed. -/
private theorem successfulPass {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (code first last : List (Section (LabLineHOL width)))
    (h : LoopGuards c pos acc code)
    (hfirst : encSecsAgain pos (computeLabelsAlt pos code acc) ffis c.encode code = (first,true))
    (hlast : encSecsAgain pos (computeLabelsAlt pos (updLabLen pos first) acc)
      ffis c.encode (updLabLen pos first) = (last,true))
    (hlight : allEncOkLight c (padCode (c.encode (.inst .skip)) last) = true)
    (hzero : zeroLabsAccExist (computeLabelsAlt pos (updLabLen pos first) acc)
      (padCode (c.encode (.inst .skip)) last) = true) :
    LoopResult c pos acc ffis code (padCode (c.encode (.inst .skip)) last)
      (computeLabelsAlt pos (updLabLen pos first) acc) := by
  let updated := updLabLen pos first
  let labs := computeLabelsAlt pos updated acc
  let nop := c.encode (.inst .skip)
  let output := padCode nop last
  have hf := h.encode c pos acc (computeLabelsAlt pos code acc) ffis code first true hfirst
  have huSim : codeSimilar first updated :=
    codeSimilar_sym updated first ((codeSimilar_updLabLen first pos first).mpr (codeSimilar_refl first))
  have hfSim := encSecsAgain_implies_similar pos _ ffis c.encode code first true hfirst
  have hlSim := encSecsAgain_implies_similar pos labs ffis c.encode updated last true hlast
  have hCodeUpd := codeSimilar_trans code first updated ⟨hfSim,huSim⟩
  have hCodeLast := codeSimilar_trans code updated last ⟨hCodeUpd,hlSim⟩
  have hSim := codeSimilar_padCode code last nop hCodeLast
  have huEnds := updLabLen_endsWithLabel pos first hf.ends
  have huValid := updLabLen_secLabelsOk pos first hf.valid
  have huPre := updLabLen_pre c pos first hf.pre
  have huEncd := updLabLen_encd0 pos first c.encode hf.encd
  have huOne := updLabLen_labelOne pos first
  have huPrefix := updLabLen_labelPrefixZero pos first ⟨h.even,hf.ends⟩
  have hlEnds := encSecsAgain_endsWithLabel pos labs ffis c.encode updated last true ⟨hlast,huEnds⟩
  have hlValid := encSecsAgain_secLabelsOk pos labs ffis c.encode updated last true ⟨hlast,huValid⟩
  have hlPre := encSecsAgain_pre pos labs ffis c.encode updated last true c ⟨hlast,huPre⟩
  have hlOne := encSecsAgain_labelOne pos labs ffis c.encode updated last true ⟨hlast,huOne⟩
  have hlPrefix := encSecsAgain_labelPrefixZero pos labs ffis c.encode updated last true ⟨hlast,huPrefix⟩
  have hlEncd := encSecsAgain_encd pos labs ffis c.encode updated last ⟨hlast,huOne,huEncd⟩
  have hlLength := allEncd_lengthLeq c.encode labs ffis pos last hlEncd
  have hlPos := encSecsAgain_posOk pos labs ffis c.encode updated last ⟨hlast,updLabLen_posOk pos first⟩
  have hspecial : nop.length ≠ 1 →
      (∀ sec ∈ last,secAligned nop.length sec) ∧ (∀ sec ∈ last,secLabelZero sec) := by
    intro hn
    have hAlign : c.codeAlignment ≠ 0 := by
      intro hz
      have hh := h.encoder.1
      simp [hz] at hh
      exact hn hh.symm
    have huZero := updLabLen_encd0LabelZero c c.encode pos first
      ⟨h.encoder,rfl,hAlign,hf.encd,h.even,hf.ends⟩
    have huAligned := allEncd0_aligned c c.encode updated ⟨h.encoder,rfl,huEncd,huZero⟩
    have halign : ∀ a,(c.encode a).length % nop.length = 0 := by
      intro a
      simpa only [nop,←h.encoder.1] using (h.encoder.2.1 a).1
    exact ⟨encSecsAgain_aligned nop.length pos labs ffis c.encode updated last true
      ⟨halign,hlast,huAligned⟩,
      encSecsAgain_labelZero pos labs ffis c.encode updated last true ⟨hlast,huZero⟩⟩
  have hnop : 0 < nop.length := by
    have hn := (h.encoder.2.1 (.inst .skip)).2
    exact Nat.pos_of_ne_zero hn
  have hNop := allEncWithNop_padCode c.encode labs ffis nop last pos
    ⟨hnop,rfl,hspecial,hlOne,hlLength,hlPrefix,hlEncd⟩
  have hOutZero := allEncWithNop_labelZero c.encode labs ffis pos output hNop
  have hOutEnds := padCode_endsWithLabel nop last hlEnds
  have hOutPre := padCode_pre nop last c hlPre
  have hOutValid := padCode_secLabelsOk nop last hlValid
  have hOutPos := allLabLenPosOk_padCode nop last pos
    ⟨hlPos,fun hn => (hspecial hn).2,hlOne,hlPrefix⟩
  have hEven := evenLabels_ends_imp_strong pos output
    ⟨labelZero_posOk_evenLabels pos output ⟨hOutZero,hOutPos⟩,hOutEnds,hOutZero⟩
  have hOffset := offsetOk_padCode nop labs ffis pos last
    ⟨fun hn => (hspecial hn).2,hlOne,hlPrefix,hlPos,
      encSecsAgain_offsetOk pos labs ffis c.encode updated last true hlast⟩
  have hIdsUpd := codeSimilar_sectionNumbers code updated hCodeUpd
  have hDomain := labsDomain_computeLabelsAlt pos updated acc
    ⟨hIdsUpd ▸ h.ids,by simpa only [hIdsUpd] using h.disjoint⟩
  have hLabelsUpd := codeSimilar_labels code updated hCodeUpd
  have hCodeLabelsUpd := codeSimilar_codeLabels code updated hCodeUpd
  have hLabelsOut := codeSimilar_labels code output hSim
  have hExist : allLabsExist labs updated := by
    apply (allLabsExist_iff_labelsSubset labs updated).mpr
    rw [hDomain]
    intro label hm
    by_cases hz : label.2 = 0
    · have hzeroSet := (zeroLabsAccExist_eq labs output).mp hzero
      have hmOut : label ∈ getLabels output := hLabelsOut ▸ (hLabelsUpd.symm ▸ hm)
      have hzLab := hzeroSet ⟨hmOut,hz⟩
      rw [hDomain] at hzLab
      exact hzLab
    · have hnz := h.subset ⟨hLabelsUpd.symm ▸ hm,hz⟩
      simpa only [hCodeLabelsUpd] using hnz
  have hLastExist := encSecsAgain_allLabsExist pos labs ffis c.encode updated last true labs ⟨hlast,hExist⟩
  have hOutExist : allLabsExist labs output := by
    apply (allLabsExist_iff_labelsSubset labs output).mpr
    have hh := (allLabsExist_iff_labelsSubset labs last).mp hLastExist
    have hs := codeSimilar_labels last output (codeSimilar_padCode last last nop (codeSimilar_refl last))
    simpa only [hs] using hh
  have hOk := allEncOk_pre_light_establishes c labs ffis pos output
    ⟨hNop,hOutPre,hlight,hEven,hOutExist,hOffset⟩
  have hComputed : computeLabelsAlt pos output acc = labs := by
    rw [padCode_computeLabels nop pos last acc
      ⟨hlOne,fun hn => (hspecial hn).2,hlPrefix,hlPos⟩]
    exact encSecsAgain_computeLabels pos labs ffis c.encode updated last acc hlast
  have hIdsOut := codeSimilar_sectionNumbers code output hSim
  have hLabelsOutList := codeSimilar_extractedLabels code output hSim
  have hDistinctOut : ∀ sec ∈ output,(extractLabels sec.lines).Nodup := by
    have hh : ∀ ls ∈ code.map (fun sec => extractLabels sec.lines),ls.Nodup := by
      simpa only [List.forall_mem_map] using h.labels
    rw [hLabelsOutList] at hh
    simpa only [List.forall_mem_map] using hh
  refine ⟨hOutPre,hOutValid,hOk,hSim,?_,?_,?_,?_⟩
  · intro ho
    exact hasOddInst_alignment c labs ffis pos output ⟨h.encoder,hOk,ho⟩
  · intro sid lid value hv
    apply allEncOk_computeLabels_lookup_even c labs ffis pos output sid lid acc value
    refine ⟨hOk,?_,?_,h.even⟩
    · simpa only [hComputed] using hv
    · intro x hx
      have hh := h.accEven sid lid
      simpa only [hx] using hh
  · intro sid lid value hv
    have hSome : sptDomain acc sid := by
      unfold labLookup at hv
      cases hh : sptLookup sid acc with
      | none => simp [hh] at hv
      | some inner => simp [sptDomain,hh]
    have hNot : sid ∉ output.map Section.sectionId := by
      rw [←hIdsOut]
      intro hm
      exact Set.disjoint_left.mp h.disjoint hSome hm
    change labLookup sid lid labs = some value
    rw [←hComputed,labLookup_computeLabelsAlt_ignore pos output acc sid lid hNot]
    exact hv
  · intro sid lid pc hp
    change labLookup sid lid labs = some (posVal pc pos output)
    rw [←hComputed]
    apply labLookup_computeLabels_position pos output acc sid lid pc c labs ffis ()
    refine ⟨hOutValid,hIdsOut ▸ h.ids,hDistinctOut,hOutZero,hOk,?_⟩
    rw [←codeSimilar_locToPc sid lid code output hSim]
    exact hp

/-- Flapjack clock-induction infrastructure. The recursion premise is the actual
source execution equality, and its result is the complete original conclusion. -/
private theorem loopChecked {width : Nat} [NeZero width]
    (clock : Nat) (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (code output : List (Section (LabLineHOL width)))
    (labs : Spt (Spt Nat)) (h : LoopGuards c pos acc code)
    (he : removeLabelsLoop clock c pos acc ffis code = some (output,labs)) :
    LoopResult c pos acc ffis code output labs := by
  induction clock using Nat.strong_induction_on generalizing code with
  | h clock ih =>
    generalize hfirst : encSecsAgain pos (computeLabelsAlt pos code acc) ffis c.encode code = entry
    rcases entry with ⟨first,flag⟩
    rw [removeLabelsLoop.eq_def] at he
    dsimp only at he
    rw [hfirst] at he
    dsimp only at he
    cases flag with
    | false =>
      by_cases hz : clock = 0
      · simp [hz] at he
      · simp only [Bool.false_eq_true,ite_false,hz] at he
        have hf := h.encode c pos acc (computeLabelsAlt pos code acc) ffis code first false hfirst
        have ht := ih (clock-1) (by omega) first hf he
        have hs := encSecsAgain_implies_similar pos _ ffis c.encode code first false hfirst
        rcases ht with ⟨hp,hvalid,henc,hsim,ho,heven,hacc,hlookup⟩
        refine ⟨hp,hvalid,henc,codeSimilar_trans code first output ⟨hs,hsim⟩,ho,heven,hacc,?_⟩
        intro sid lid pc hpc
        apply hlookup sid lid pc
        rw [←codeSimilar_locToPc sid lid code first hs]
        exact hpc
    | true =>
      generalize hlast : encSecsAgain pos (computeLabelsAlt pos (updLabLen pos first) acc)
        ffis c.encode (updLabLen pos first) = entry
      rcases entry with ⟨last,lastFlag⟩
      simp only [ite_true] at he
      rw [hlast] at he
      dsimp only at he
      cases lastFlag with
      | false => simp at he
      | true =>
        split at he
        · rename_i hbranch
          have hb : allEncOkLight c (padCode (c.encode (.inst .skip)) last) = true ∧
              zeroLabsAccExist (computeLabelsAlt pos (updLabLen pos first) acc)
                (padCode (c.encode (.inst .skip)) last) = true := by
            simpa using hbranch
          have hout := Option.some.inj he
          cases hout
          exact successfulPass c pos acc ffis code first last h hfirst hlast hb.1 hb.2
        · simp at he

/-- Full original label-removal loop theorem. All twelve guards and eight
conclusion clauses are retained over actual native recursive encoding, label
updates, padding and canonical numeric sptrees. No returned validity, lookup
result or simulation callback is assumed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "remove_labels_loop_thm" (words_as_type_indexed_bitvec)]
theorem removeLabelsLoop_correct {width : Nat} [NeZero width]
    (clock : Nat) (c : AsmConfigExact width) (pos : Nat) (acc : Spt (Spt Nat))
    (ffis : List HolFfiName)
    (code output : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (labs : Spt (Spt Nat)) :
    removeLabelsLoop clock c pos acc ffis code = some (output,labs) ∧
    (∀ sec ∈ code,secEndsWithLabelNative sec) ∧
    (∀ sec ∈ code,secLabelsOk sec) ∧ (code.map Section.sectionId).Nodup ∧
    (∀ sec ∈ code,(extractLabels sec.lines).Nodup) ∧
    Disjoint (sptDomain acc) {n | n ∈ code.map Section.sectionId} ∧
    restrictNonzero (getLabels code) ⊆ getCodeLabels code ∪ labsDomain acc ∧
    allEncOkPreHOL c code ∧ allEncd0 c.encode code ∧ encOk c ∧ pos % 2 = 0 ∧
    (∀ sid lid,match labLookup sid lid acc with
      | none => True
      | some value => value % 2 = 0) →
    allEncOkPreHOL c output ∧ (∀ sec ∈ output,secLabelsOk sec) ∧
    allEncOk c labs ffis pos output ∧ codeSimilar code output ∧
    (hasOddInst output → c.codeAlignment = 0) ∧
    (∀ sid lid value,labLookup sid lid labs = some value → value % 2 = 0) ∧
    (∀ sid lid value,labLookup sid lid acc = some value → labLookup sid lid labs = some value) ∧
    (∀ sid lid pc,locToPc sid lid code = some pc →
      labLookup sid lid labs = some (posVal pc pos output)) := by
  rintro ⟨he,hends,hvalid,hids,hlabels,hdis,hsub,hpre,hencd,hencoder,heven,hacc⟩
  exact loopChecked clock c pos acc ffis code output labs
    ⟨hends,hvalid,hids,hlabels,hdis,hsub,hpre,hencd,hencoder,heven,hacc⟩ he

end Flapjack.Compiler.Backend.LabToTarget
