import Flapjack.Pancake.CrepInline.InlineRouteBridge

/-! Byte-name preservation for the executed recursive inliner. These are
Flapjack codec obligations, with no separate HOL declaration, needed to turn
encoded-output correspondence into decoded-output equality. -/

namespace Flapjack.CrepInlineRoute

private theorem crepNameRanged_decode (name : Flapjack.Basis.Pure.MlString.MlString) :
    CrepNameRanged (Flapjack.Basis.Pure.MlString.toStringOfBytes name) := by
  intro character hmem
  simp only [Flapjack.Basis.Pure.MlString.toStringOfBytes, String.toList_ofList,
    List.mem_map] at hmem
  obtain ⟨byte, _, rfl⟩ := hmem
  have hb : byte.toNat < 256 := by simpa using byte.isLt
  rw [Flapjack.Basis.Pure.MlString.ofNat_toNat_char byte]
  exact hb

private theorem crepInlineLookup_nameRanged {width : Nat}
    [BEq FunName] (entries : List (CrepInlineEntry (BitVec width)))
    (hentries : ∀ entry ∈ entries, CrepProgNameRanged entry.2.2)
    (name : FunName) (params : List Nat) (body : CrepProg (BitVec width))
    (hlookup : crepInlineLookup name entries = some (params, body)) :
    CrepProgNameRanged body := by
  induction entries with
  | nil => simp [crepInlineLookup] at hlookup
  | cons entry entries ih =>
      rcases entry with ⟨key, parameters, program⟩
      simp only [crepInlineLookup] at hlookup
      split at hlookup
      · cases hlookup
        exact hentries (key, params, body) (List.mem_cons_self)
      · exact ih (fun entry h => hentries entry (List.mem_cons_of_mem _ h)) hlookup

end Flapjack.CrepInlineRoute
