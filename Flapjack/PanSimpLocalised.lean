import Flapjack.Pancake.PanSimp
import Flapjack.PanLocalised
import Flapjack.Pancake.Proofs.PanSimp

/-!
`pan_simp` only inserts `Skip`, `Seq`, and `Annot` nodes and rewrites the
`AssignCall`/`Return` shape into a destination-free tail call.  None of these
introduce global-variable reads, so the localisation invariant `localisedProg`
used by the Pancake-to-Crep boundary is preserved by the whole pass.  This is
the source-side ingredient of Cake's `mk_ctxt_code_imp_code_rel`
(`pan_to_crepProofScript.sml`), which requires the compiled code to consist of
localised programs.
-/

namespace Flapjack

theorem localisedProg_skip : localisedProg (.skip : Prog α) := by
  simp [localisedProg]

theorem localisedProg_annot (tag text : String) :
    localisedProg (.annot tag text : Prog α) := by
  simp [localisedProg]

theorem localisedProg_smartSeq (pre program : Prog α)
    (hpre : localisedProg pre) (hprogram : localisedProg program) :
    localisedProg (smartSeq pre program) := by
  unfold smartSeq
  split
  · exact hprogram
  · exact ⟨hpre, hprogram⟩

theorem localisedProg_seqCallRet (program : Prog α) (h : localisedProg program) :
    localisedProg (seqCallRet program) := by
  unfold seqCallRet
  split
  · split
    · simp only [localisedProg] at h ⊢
      exact ⟨h.1.1, ⟨trivial, trivial⟩⟩
    · exact h
  · exact h

theorem localisedProg_seqAssoc (pre program : Prog α)
    (hpre : localisedProg pre) (hprogram : localisedProg program) :
    localisedProg (seqAssoc pre program) := by
  fun_induction progSize program generalizing pre with
  | case7 _ _ returns | case8 _ _ returns _ _ _ _ =>
      rcases returns with _ | ⟨_ | _, name⟩ <;>
        grind only [seqAssoc, localisedProg_smartSeq, localisedProg]
  | _ => grind only [seqAssoc, localisedProg_smartSeq, localisedProg]

theorem localisedProg_retToTail (program : Prog α) (h : localisedProg program) :
    localisedProg (retToTail program) := by
  fun_induction progSize program with
  | case7 _ _ returns | case8 _ _ returns _ _ _ _ =>
      rcases returns with _ | ⟨_ | _, name⟩ <;>
        grind only [retToTail, localisedProg_seqCallRet, localisedProg]
  | _ => grind only [retToTail, localisedProg_seqCallRet, localisedProg]

theorem localisedProg_panSimpProg (program : Prog α) (h : localisedProg program) :
    localisedProg (panSimpProg program) := by
  unfold panSimpProg
  exact localisedProg_retToTail _ (localisedProg_seqAssoc .skip program
    localisedProg_skip h)

end Flapjack
