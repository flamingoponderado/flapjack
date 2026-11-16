module

public import Flapjack.Compiler.Inference.Unify.ComputationalWf
public import Flapjack.HOL.Unification.UnifDef
public import Flapjack.HOL.Transfer.Fmsp.Operations
public import Flapjack.Misc.Sptree.Wf

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

@[hol "cakeml/compiler/inference/unifyScript.sml" "cwfs_insert_tvar_db"]
theorem cwfsInsertTvarDb (s : Spt InferT) (v c : Nat)
    (h : ¬ sptDomain s v ∧ cwfs s) : cwfs (sptInsert v (.varDb c) s) := by
  obtain ⟨absent, hw, htree⟩ := h
  have fresh := encodedFresh s v absent
  have hw0 : wfs (sp2fm (sptMap encodeInferT s)) := hw
  have hnot : ¬ vars (walkstar (sp2fm (sptMap encodeInferT s)) (.const (.dbTag c))) v := by
    rw [walkstarEq _ hw0]
    simp [walk, vars]
  have extended := wfsExtend (sp2fm (sptMap encodeInferT s)) v (.const (.dbTag c)) ⟨hw0, fresh, hnot⟩
  constructor
  · change wfs (sp2fm (sptMap encodeInferT (sptInsert v (.varDb c) s)))
    have maps : sp2fm (sptMap encodeInferT (sptInsert v (.varDb c) s)) =
      (sp2fm (sptMap encodeInferT s)).updateEq (v, .const (.dbTag c)) := by
      rw [sptMap_sptInsert]
      simpa only [encodeInferT] using
        (sp2fmThm (α := Atom) v (.const (.dbTag c)) (sptMap encodeInferT s)).2
    rw [maps]
    exact extended
  · exact sptWfInsert v (.varDb c) s htree

@[hol "cakeml/compiler/inference/unifyScript.sml" "cwfs_var2_extend"]
theorem cwfsVar2Extend (s : Spt InferT) (v1 v2 : Nat)
    (h : cwfs s ∧ v1 ≠ v2 ∧ ¬ sptDomain s v1 ∧ ¬ sptDomain s v2) :
    cwfs (sptInsert v1 (.uvar v2) s) := by
  obtain ⟨⟨hw, htree⟩, hne, absent1, absent2⟩ := h
  have fresh := encodedFresh s v1 absent1
  have hw0 : wfs (sp2fm (sptMap encodeInferT s)) := hw
  have missEncoded : (sp2fm (sptMap encodeInferT s)).lookup v2 = none := by
    simp [sp2fm, sptLookup_sptMap, missingOfNotDomain s v2 absent2]
  have hnot : ¬ vars (walkstar (sp2fm (sptMap encodeInferT s)) (.var v2)) v1 := by
    classical
    simp [walkstar, hw0, normalizeVar, missEncoded, vars, hne]
  have extended := wfsExtend (sp2fm (sptMap encodeInferT s)) v1 (.var v2) ⟨hw0, fresh, hnot⟩
  constructor
  · change wfs (sp2fm (sptMap encodeInferT (sptInsert v1 (.uvar v2) s)))
    rw [sptMap_sptInsert]
    simp only [encodeInferT]
    rw [(sp2fmThm (α := Atom) v1 (.var v2) (sptMap encodeInferT s)).2]
    exact extended
  · exact sptWfInsert v1 (.uvar v2) s htree

end Flapjack.Compiler.Inference.Unify
