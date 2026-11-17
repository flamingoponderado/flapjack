module

public import Flapjack.Compiler.Inference.Unify.ComputationalWf
public import Flapjack.HOL.Unification.UnifDef
public import Flapjack.HOL.Transfer.Fmsp.Operations
public import Flapjack.Misc.Sptree.Wf
public import Flapjack.Compiler.Inference.Unify.Occurs.Correctness

@[expose] public section

/-! Well-formedness of a fresh de Bruijn binding. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

private theorem missingOfNotDomain (s : Spt InferT) (v : Nat) (absent : ¬ sptDomain s v) :
    sptLookup v s = none := by
  cases found : sptLookup v s with
  | none => rfl
  | some t => exact (absent ((sptDomain_iff_lookup s v).mpr ⟨t, found⟩)).elim

private theorem encodedFresh (s : Spt InferT) (v : Nat) (absent : ¬ sptDomain s v) :
    v ∉ (sp2fm (sptMap encodeInferT s)).domain := by
  change ¬ (sptLookup v (sptMap encodeInferT s) ≠ none)
  simp [sptLookup_sptMap, missingOfNotDomain s v absent]

/-- A fresh sparse-tree update preserves computational well-formedness when
    its encoded value does not contain the new variable after normalization.
    This specializes the source `wfs_extend` step to the executed tree update;
    it is supporting infrastructure rather than a separate HOL declaration. -/
theorem cwfsFreshInsert (s : Spt InferT) (v : Nat) (t : InferT)
    (h : ¬ sptDomain s v ∧ cwfs s ∧
      ¬ vars (walkstar (sp2fm (sptMap encodeInferT s)) (encodeInferT t)) v) :
    cwfs (sptInsert v t s) := by
  obtain ⟨absent, ⟨hw, htree⟩, hnot⟩ := h
  have extended := wfsExtend (sp2fm (sptMap encodeInferT s)) v (encodeInferT t)
    ⟨hw, encodedFresh s v absent, hnot⟩
  constructor
  · change wfs (sp2fm (sptMap encodeInferT (sptInsert v t s)))
    rw [sptMap_sptInsert, (sp2fmThm (α := Atom) v (encodeInferT t) (sptMap encodeInferT s)).2]
    exact extended
  · exact sptWfInsert v t s htree

@[hol "cakeml/compiler/inference/unifyScript.sml" "cwfs_insert_tvar_db"]
theorem cwfsInsertTvarDb (s : Spt InferT) (v c : Nat)
    (h : ¬ sptDomain s v ∧ cwfs s) : cwfs (sptInsert v (.varDb c) s) := by
  obtain ⟨absent, hw, htree⟩ := h
  have hw0 : wfs (sp2fm (sptMap encodeInferT s)) := hw
  have hnot : ¬ vars (walkstar (sp2fm (sptMap encodeInferT s)) (.const (.dbTag c))) v := by
    rw [walkstarEq _ hw0]
    simp [walk, vars]
  apply cwfsFreshInsert s v (.varDb c)
  exact ⟨absent, ⟨hw, htree⟩, by simpa only [encodeInferT] using hnot⟩

@[hol "cakeml/compiler/inference/unifyScript.sml" "cwfs_var2_extend"]
theorem cwfsVar2Extend (s : Spt InferT) (v1 v2 : Nat)
    (h : cwfs s ∧ v1 ≠ v2 ∧ ¬ sptDomain s v1 ∧ ¬ sptDomain s v2) :
    cwfs (sptInsert v1 (.uvar v2) s) := by
  obtain ⟨⟨hw, htree⟩, hne, absent1, absent2⟩ := h
  have hw0 : wfs (sp2fm (sptMap encodeInferT s)) := hw
  have missEncoded : (sp2fm (sptMap encodeInferT s)).lookup v2 = none := by
    simp [sp2fm, sptLookup_sptMap, missingOfNotDomain s v2 absent2]
  have hnot : ¬ vars (walkstar (sp2fm (sptMap encodeInferT s)) (.var v2)) v1 := by
    classical
    simp [walkstar, hw0, normalizeVar, missEncoded, vars, hne]
  apply cwfsFreshInsert s v1 (.uvar v2)
  exact ⟨absent1, ⟨hw, htree⟩, by simpa only [encodeInferT] using hnot⟩

/-- The application-update branch of the executed unifier preserves
    well-formedness when its actual occurrence worklist returns `false`.
    This connects the worklist's returned value to the source `wfs_extend`
    argument; it is not a separate HOL declaration. -/
theorem cwfsInsertAppOfOccursFalse (s : Spt InferT) (v tc : Nat) (ts : List InferT)
    (h : ¬ sptDomain s v ∧ cwfs s ∧ occursWorkPartial s v [ts] = some false) :
    cwfs (sptInsert v (.app ts tc) s) := by
  obtain ⟨absent, hw, result⟩ := h
  obtain ⟨b, hb, hiff⟩ := occursWorkListCoclCorrect s ts v hw
  have bfalse : b = false := Option.some.inj (hb.symm.trans result)
  subst b
  have noList : ¬ coclModel s ts v := by
    intro present
    have impossible := hiff.mp present
    contradiction
  have noOcc : ¬ cocModel s (.app ts tc) v := by
    intro present
    have walked := (cocThm s (.app ts tc) v hw).mp present
    rw [cwalkThm s (.app ts tc) hw] at walked
    exact noList ((coclExists s ts v).mpr walked)
  apply cwfsFreshInsert s v (.app ts tc)
  refine ⟨absent, hw, ?_⟩
  intro varsOcc
  apply noOcc
  exact (ocEqVarsWalkstar _ _ _ hw.1).2 varsOcc

end Flapjack.Compiler.Inference.Unify
