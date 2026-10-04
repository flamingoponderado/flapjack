import Flapjack.Pancake.Proofs.PanToWord.EveryInstOkLess.PanGlobals
import Flapjack.Pancake.PanStructs.CompileDeclsExact

/-!
# `pan_to_wordProofScript.sml` 1237-1298: `every_inst_ok_less` for `pan_structs`

The pan_structs compiler keeps every `Panop` at two arguments. Renderings as in
the pan_globals group: `every_exp P` is `everyExpHOL panopArityTwoHOL`,
`EVERY (every_exp P)` is `everyExpListHOL`, `EVERY good_panops` is
`List.all goodPanopsHOL`, and `MAP SND flds` is `flds.map Prod.snd`. The
compiler definitions are the reviewed exact pan_structs ports.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang Flapjack.Pancake.PanStructs.CompileShapeExact
open PanToWordEveryInstOkLessPanGlobals

namespace PanToWordEveryInstOkLessPanStructs

/-- `EVERY (every_exp P)` as membership (Flapjack infrastructure). -/
theorem everyExpListHOL_iff {width : Nat} [NeZero width] (P : ExpHOL width → Bool)
    (es : List (ExpHOL width)) :
    everyExpListHOL P es = true ↔ ∀ e ∈ es, everyExpHOL P e = true := by
  induction es with
  | nil => simp [everyExpListHOL]
  | cons e es ih => simp [everyExpListHOL, ih]

/-- The field-list form of `every_exp` is `EVERY (every_exp P) (MAP SND flds)`
(Flapjack infrastructure). -/
theorem everyExpFieldListHOL_eq {width : Nat} [NeZero width] (P : ExpHOL width → Bool)
    (flds : List (MlS × ExpHOL width)) :
    everyExpFieldListHOL P flds = everyExpListHOL P (flds.map Prod.snd) := by
  induction flds with
  | nil => simp [everyExpFieldListHOL, everyExpListHOL]
  | cons f flds ih => obtain ⟨n, e⟩ := f; simp [everyExpFieldListHOL, everyExpListHOL, ih]

/-- A value found by name in an association list is one of its values
(`ALOOKUP_MEM`; Flapjack infrastructure). -/
theorem findSome_snd_mem {α β : Type} [DecidableEq α] (l : List (α × β)) (k : α) (v : β)
    (h : l.findSome? (fun q => if q.1 = k then some q.2 else none) = some v) :
    v ∈ l.map Prod.snd := by
  induction l with
  | nil => simp at h
  | cons q l ih =>
      simp only [List.findSome?_cons] at h
      by_cases hq : q.1 = k
      · simp only [hq, if_true, Option.some.injEq] at h
        subst h
        simp
      · simp only [hq, if_false] at h
        exact List.mem_map.mpr (by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (ih h)
          exact ⟨x, List.mem_cons_of_mem _ hx, rfl⟩)

mutual
  theorem structsExp_every {width : Nat} [NeZero width] (ctxt : ContextExact) :
      ∀ e : ExpHOL width, everyExpHOL panopArityTwoHOL e = true →
        everyExpHOL panopArityTwoHOL (compileExpExact ctxt e) = true
    | .const _, h => by simpa [compileExpExact] using h
    | .var _ _, h => by simpa [compileExpExact] using h
    | .rstruct es, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], (structsExps_every ctxt es h.2).1⟩
    | .rfield i e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], structsExp_every ctxt e h.2⟩
    | .nstruct name fields, h => by
        simp only [everyExpHOL, Bool.and_eq_true, everyExpFieldListHOL_eq] at h
        have hc := structsFields_every ctxt fields h.2
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        refine ⟨by simp [panopArityTwoHOL], ?_⟩
        rw [everyExpListHOL_iff]
        intro v hv
        split at hv
        · simp only [List.mem_flatMap] at hv
          obtain ⟨p, -, hp⟩ := hv
          split at hp
          · simp at hp
          · rename_i value hfind
            simp only [List.mem_singleton] at hp
            subst hp
            exact (everyExpListHOL_iff _ _).mp hc v (findSome_snd_mem _ _ _ hfind)
        · simp at hv
    | .nfield f e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], structsExp_every ctxt e h.2⟩
    | .load sh e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], structsExp_every ctxt e h.2⟩
    | .load32 e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], structsExp_every ctxt e h.2⟩
    | .loadByte e, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], structsExp_every ctxt e h.2⟩
    | .op bop es, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨by simp [panopArityTwoHOL], (structsExps_every ctxt es h.2).1⟩
    | .panop op es, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        have hl := structsExps_every ctxt es h.2
        refine ⟨?_, hl.1⟩
        have h1 := h.1
        simp only [panopArityTwoHOL, decide_eq_true_eq] at h1 ⊢
        rw [hl.2, h1]
    | .cmp c e1 e2, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨⟨by simp [panopArityTwoHOL], structsExp_every ctxt e1 h.1.2⟩,
          structsExp_every ctxt e2 h.2⟩
    | .shift sh e1 e2, h => by
        simp only [everyExpHOL, Bool.and_eq_true] at h
        simp only [compileExpExact, everyExpHOL, Bool.and_eq_true]
        exact ⟨⟨by simp [panopArityTwoHOL], structsExp_every ctxt e1 h.1.2⟩,
          structsExp_every ctxt e2 h.2⟩
    | .baseAddr, h => by simpa [compileExpExact] using h
    | .topAddr, h => by simpa [compileExpExact] using h
    | .bytesInWord, h => by simpa [compileExpExact] using h
  termination_by e => sizeOf e

  theorem structsExps_every {width : Nat} [NeZero width] (ctxt : ContextExact) :
      ∀ es : List (ExpHOL width), everyExpListHOL panopArityTwoHOL es = true →
        everyExpListHOL panopArityTwoHOL (compileExpsExact ctxt es) = true ∧
          (compileExpsExact ctxt es).length = es.length
    | [], _ => by simp [compileExpsExact, everyExpListHOL]
    | e :: es, h => by
        simp only [everyExpListHOL, Bool.and_eq_true] at h
        have ih := structsExps_every ctxt es h.2
        simp only [compileExpsExact, everyExpListHOL, Bool.and_eq_true, List.length_cons]
        exact ⟨⟨structsExp_every ctxt e h.1, ih.1⟩, by rw [ih.2]⟩
  termination_by es => sizeOf es

  theorem structsFields_every {width : Nat} [NeZero width] (ctxt : ContextExact) :
      ∀ flds : List (MlS × ExpHOL width), everyExpListHOL panopArityTwoHOL (flds.map Prod.snd) = true →
        everyExpListHOL panopArityTwoHOL ((compileFieldsExact ctxt flds).map Prod.snd) = true
    | [], _ => by simp [compileFieldsExact, everyExpListHOL]
    | (n, e) :: flds, h => by
        simp only [List.map_cons, everyExpListHOL, Bool.and_eq_true] at h
        simp only [compileFieldsExact, List.map_cons, everyExpListHOL, Bool.and_eq_true]
        exact ⟨structsExp_every ctxt e h.1, structsFields_every ctxt flds h.2⟩
  termination_by flds => sizeOf flds
end

/-- Full original `every_inst_ok_less_pan_structs_compile_exp`: the three
conjuncts for `compile_exp`, `compile_exps` (with its length) and
`compile_fields` (over `MAP SND`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_structs_compile_exp"
  (words_as_type_indexed_bitvec)]
theorem every_inst_ok_less_pan_structs_compile_exp {width : Nat} [NeZero width] :
    (∀ (ctxt : ContextExact) (e : ExpHOL width),
      everyExpHOL panopArityTwoHOL e = true →
        everyExpHOL panopArityTwoHOL (compileExpExact ctxt e) = true) ∧
    (∀ (ctxt : ContextExact) (es : List (ExpHOL width)),
      everyExpListHOL panopArityTwoHOL es = true →
        everyExpListHOL panopArityTwoHOL (compileExpsExact ctxt es) = true ∧
          (compileExpsExact ctxt es).length = es.length) ∧
    (∀ (ctxt : ContextExact) (flds : List (MlS × ExpHOL width)),
      everyExpListHOL panopArityTwoHOL (flds.map Prod.snd) = true →
        everyExpListHOL panopArityTwoHOL ((compileFieldsExact ctxt flds).map Prod.snd) = true) :=
  ⟨structsExp_every, structsExps_every, structsFields_every⟩

/-- Full original `every_inst_ok_less_pan_structs_compile`:
`∀ctxt p. EVERY (every_exp P) (exps_of p) ⇒ EVERY (every_exp P) (exps_of (pan_structs$compile ctxt p))`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_structs_compile"
  (words_as_type_indexed_bitvec)]
theorem every_inst_ok_less_pan_structs_compile {width : Nat} [NeZero width] :
    ∀ (ctxt : ContextExact) (p : ProgHOL width),
      everyExpListHOL panopArityTwoHOL (expsOfHOL p) = true →
        everyExpListHOL panopArityTwoHOL (expsOfHOL (compileProgExact ctxt p)) = true := by
  intro ctxt p
  have hE : ∀ (c : ContextExact) (e : ExpHOL width), everyExpHOL panopArityTwoHOL e = true →
      everyExpHOL panopArityTwoHOL (compileExpExact c e) = true := structsExp_every
  have hL : ∀ (c : ContextExact) (es : List (ExpHOL width)),
      everyExpListHOL panopArityTwoHOL es = true →
        everyExpListHOL panopArityTwoHOL (compileExpsExact c es) = true :=
    fun c es h => (structsExps_every c es h).1
  induction ctxt, p using compileProgExact.induct
  case case18 =>
    rename_i p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    cases p <;> first
      | (simp_all [compileProgExact, expsOfHOL]; done)
      | (rename_i h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact (h _ _ _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact (h _ _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _ _ _ _ _ _ _ _; exact (h _ _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _ _ _ _ _ _ _; exact (h _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _ _ _ _ _ _; exact (h _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _ _ _ _ _; exact (h _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _ _ _ _; exact (h _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _ _ _; exact (h _ _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _ _; exact (h _ _ rfl).elim)
      | (rename_i h _ _ _ _ _ _; exact (h _ _ _ rfl).elim)
      | (rename_i h _ _ _ _ _; exact (h _ _ _ _ _ rfl).elim)
      | (rename_i h _ _ _ _; exact (h _ _ _ _ _ rfl).elim)
      | (rename_i h _ _ _; exact (h _ rfl).elim)
      | (rename_i h _ _; exact (h _ _ rfl).elim)
      | (rename_i h _; exact (h _ _ _ rfl).elim)
      | (rename_i h; exact (h _ _ _ _ rfl).elim)
  all_goals
    rw [compileProgExact.eq_def]
    try simp_all [expsOfHOL, everyExpListHOL, everyExpListHOL_append]
    try split <;> simp_all [expsOfHOL, everyExpListHOL_append]

/-- Full original `every_inst_ok_less_pan_structs_compile_decs`:
`∀ctxt pan_code. EVERY good_panops pan_code ⇒
EVERY good_panops (FST (pan_structs$compile_decs ctxt pan_code))`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_structs_compile_decs"
  (words_as_type_indexed_bitvec)]
theorem every_inst_ok_less_pan_structs_compile_decs {width : Nat} [NeZero width] :
    ∀ (ctxt : ContextExact) (pan_code : List (DeclHOL width)),
      pan_code.all goodPanopsHOL = true →
        (compileDeclsExact ctxt pan_code).1.all goodPanopsHOL = true := by
  intro ctxt pan_code
  induction pan_code generalizing ctxt with
  | nil => simp [compileDeclsExact]
  | cons d ds ih =>
      intro h
      simp only [List.all_cons, Bool.and_eq_true] at h
      cases d with
      | decl sh v e =>
          simp only [compileDeclsExact, List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih _ h.2⟩
          simp only [goodPanopsHOL] at h ⊢
          exact structsExp_every ctxt e h.1
      | function fi =>
          simp only [compileDeclsExact, List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih _ h.2⟩
          simp only [goodPanopsHOL] at h ⊢
          exact every_inst_ok_less_pan_structs_compile _ fi.body h.1
      | exnDecl eid sh =>
          simp only [compileDeclsExact, List.all_cons, Bool.and_eq_true]
          exact ⟨rfl, ih _ h.2⟩
      | name nm flds =>
          simp only [compileDeclsExact]
          exact ih _ h.2

/-- Full original `every_inst_ok_less_pan_structs_compile_top`:
`∀ctxt pan_code. EVERY good_panops pan_code ⇒
EVERY good_panops (pan_structs$compile_top pan_code)`. HOL's binder `ctxt` does
not occur in the body; it is retained at its free type. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_structs_compile_top"
  (words_as_type_indexed_bitvec)]
theorem every_inst_ok_less_pan_structs_compile_top {width : Nat} [NeZero width] {β : Type} :
    ∀ (_ctxt : β) (pan_code : List (DeclHOL width)),
      pan_code.all goodPanopsHOL = true → (compileTopExact pan_code).all goodPanopsHOL = true := by
  intro _ pan_code h
  exact every_inst_ok_less_pan_structs_compile_decs _ pan_code h

end PanToWordEveryInstOkLessPanStructs

end Flapjack
