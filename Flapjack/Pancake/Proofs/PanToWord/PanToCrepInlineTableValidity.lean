import Flapjack.Pancake.Proofs.PanToWord.PanToCrepValidity
import Flapjack.Pancake.Proofs.CrepInline.ExpressionProvenance
namespace Flapjack.PanToCrepInlineTableValidity
/-- Internal key-filter lookup correspondence, all lists including duplicate keys; no separate HOL declaration. -/
private theorem filter_lookup {α β : Type} [BEq α] [LawfulBEq α]
    (p : α → Bool) (es : List (α × β)) (key : α) :
    FUPDATE_LIST (FEMPTY : FiniteMap α β) (es.filter (fun e => p e.1)).reverse key =
      if p key then FUPDATE_LIST FEMPTY es.reverse key else none := by
  induction es with
  | nil => simp [FUPDATE_LIST, FEMPTY]
  | cons entry es ih =>
    rcases entry with ⟨name, value⟩
    by_cases eq : key = name
    · subst key
      by_cases hp : p name = true <;>
        simp_all [List.reverse_cons, FUPDATE_LIST_append,
          FUPDATE_LIST_cons, FUPDATE_LIST_nil, FUPDATE]
    · have ne : name ≠ key := Ne.symm eq
      by_cases hp : p name = true <;>
        simp_all [List.reverse_cons, FUPDATE_LIST_append,
          FUPDATE_LIST_cons, FUPDATE_LIST_nil, FUPDATE, beq_iff_eq]
/-- Internal full native inlining-wrapper factoring using accepted source theorem; no separate HOL declaration. -/
private theorem inline_top_valid {width : Nat} [NeZero width]
    (names : List CrepInlineMapHOLName)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (input : ∀ entry ∈ prog, crepBinaryProgNative entry.2.2) :
    ∀ entry ∈ CrepInlineCanonical.compileInlTopHOLExact names prog,
      crepBinaryProgNative entry.2.2 := by
  rw [CrepInlineCanonical.compileInlTopHOLExact_eq_compileInlProgHOLExact]
  have sub : HolFiniteMapExact.submap
      (CrepInlineCanonical.alistToFmapHOLExact (prog.filter fun entry => names.contains entry.1))
      (alistToFmapCodeExact prog) := by
    intro key value found
    simp only [CrepInlineCanonical.alistToFmapHOLExact, alistToFmapCodeExact,
      HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.empty] at found ⊢
    have filtered := filter_lookup (fun key => names.contains key) prog key
    have found' : FUPDATE_LIST FEMPTY
        (prog.filter (fun entry => names.contains entry.1)).reverse key = some value := found
    rw [filtered] at found'
    split at found'
    · exact found'
    · contradiction
  have valid := crepInline_everyInstCrepInline prog _
    (And.intro (by
      intro entry member
      rcases entry with ⟨name, params, body⟩
      exact input (name, params, body) member) sub)
  intro entry member
  rcases entry with ⟨name, params, body⟩
  exact valid (name, params, body) member

/-- Full original table implication (`pan_to_wordProofScript.sml:1135–1152`).
The only premise is binary-Crepop validity of the actual compile_to_crep table.
The filtered inline map SUBMAP is derived from name-based filtering, without a
name-distinctness or byte-range premise. The source-shaped wrapper equality
reuses the native accepted full inlining theorem and its exact finite-map
carrier; no translated map occurs in this theorem signature. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_w_inline"
  (words_as_type_indexed_bitvec)]
theorem everyInstWInline {width : Nat} [NeZero width]
    (pan_code : List (Pancake.PanLang.DeclHOL width))
    (input : ∀ (entry : CrepInlineMapHOLName × List Nat × CrepProgHOL width),
      entry ∈ compileToCrepExactHOLW pan_code → crepBinaryProgNative entry.2.2) :
    ∀ (entry : CrepInlineMapHOLName × List Nat × CrepProgHOL width),
      entry ∈ compileProgDeclsHOLW pan_code → crepBinaryProgNative entry.2.2 := by
  unfold compileProgDeclsHOLW
  exact inline_top_valid _ _ input
end Flapjack.PanToCrepInlineTableValidity
