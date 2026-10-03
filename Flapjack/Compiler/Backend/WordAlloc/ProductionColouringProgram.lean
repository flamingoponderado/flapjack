import Flapjack.Compiler.Backend.WordAlloc.ProductionColouringInstructions
import Flapjack.Compiler.Backend.WordAlloc.Colour

namespace Flapjack.WordAlloc

/-! Whole executed colouring output through the actual partial encoder. This
is implementation correspondence to the reviewed native definition, with no
separate HOL original. Only input encoding is assumed; output encoding and
all recursively coloured handlers and cutsets are proved. -/

private theorem colouringMoveZip (colour : Nat → Nat) (moves : List (Nat × Nat)) :
    moves.map (fun pair => (colour pair.1, colour pair.2)) =
      List.zip (moves.map (colour ∘ Prod.fst)) (moves.map (colour ∘ Prod.snd)) := by
  induction moves with
  | nil => rfl
  | cons pair rest ih => simp only [List.map_cons, List.zip_cons_cons, ih, Function.comp_apply]

theorem colouringProgram_production {width : Nat} [NeZero width]
    (colour : Nat → Nat) (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    wordLangProgToHOL (wordApplyColour colour program) = some (applyColour colour native) := by
  cases program
  case move priority moves =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordApplyColour, wordLangProgToHOL, applyColour, colouringMoveZip]
  case inst instruction =>
    cases hi : wordLangInstToHOL instruction <;> simp [wordLangProgToHOL, hi] at encoded
    subst native
    simp only [wordApplyColour, wordLangProgToHOL, applyColour,
      colouringInst_production _ _ _ hi, Option.map_some]
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simp only [wordApplyColour, wordLangProgToHOL, applyColour,
      colouringProgram_production colour body _ hb, Option.map_some]
  case loop names body exits =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simp [wordApplyColour, wordLangProgToHOL, applyColour,
      colouringProgram_production colour body _ hb, colouringNumSet_production]
  case seq first second =>
    cases hf : wordLangProgToHOL first <;> cases hs : wordLangProgToHOL second <;>
      simp [wordLangProgToHOL, hf, hs] at encoded
    subst native
    simp [wordApplyColour, wordLangProgToHOL, applyColour,
      colouringProgram_production colour first _ hf,
      colouringProgram_production colour second _ hs]
  case ite compare condition right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    simp [wordApplyColour, wordLangProgToHOL, applyColour, colouringRegImm_production,
      colouringProgram_production colour yes _ hy,
      colouringProgram_production colour no _ hn]
  case call returns target arguments handler =>
    cases hReturns : returns with
    | none =>
        cases hHandler : handler with
        | none =>
            simp [wordLangProgToHOL, hReturns, hHandler] at encoded
            subst native
            simp [wordApplyColour, wordLangProgToHOL, applyColour]
        | some exception =>
            rcases exception with ⟨name, body, label1, label2⟩
            cases hb : wordLangProgToHOL body <;>
              simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
            subst native
            simp [wordApplyColour, wordLangProgToHOL, applyColour,
              colouringProgram_production colour body _ hb]
    | some ret =>
        rcases ret with ⟨values, sets, body, label1, label2⟩
        cases hb : wordLangProgToHOL body <;>
          simp [wordLangProgToHOL, hReturns, hb] at encoded
        cases hHandler : handler with
        | none =>
            simp [hHandler] at encoded
            subst native
            simp [wordApplyColour, wordLangProgToHOL, applyColour,
              colouringProgram_production colour body _ hb, colouringCutsets_production]
        | some exception =>
            rcases exception with ⟨name, handlerBody, handlerLabel1, handlerLabel2⟩
            cases hh : wordLangProgToHOL handlerBody <;>
              simp [hHandler, hh] at encoded
            subst native
            simp [wordApplyColour, wordLangProgToHOL, applyColour,
              colouringProgram_production colour body _ hb,
              colouringProgram_production colour handlerBody _ hh,
              colouringCutsets_production]
  case alloc destination sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp [wordApplyColour, wordLangProgToHOL, applyColour, colouringCutsets_production]
  case install code codeLength data dataLength sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp [wordApplyColour, wordLangProgToHOL, applyColour, colouringCutsets_production]
  all_goals simp only [wordLangProgToHOL, Option.some.injEq] at encoded
  all_goals subst native
  all_goals simp [wordApplyColour, wordLangProgToHOL, applyColour,
    wordApplyColourExp_toHOL, colouringCutsets_production]
termination_by sizeOf program
decreasing_by
  all_goals simp_wf
  all_goals subst program
  all_goals try rw [hReturns]
  all_goals try rw [hHandler]
  all_goals try simp
  all_goals omega

end Flapjack.WordAlloc
