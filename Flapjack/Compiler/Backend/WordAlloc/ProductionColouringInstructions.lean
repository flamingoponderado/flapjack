import Flapjack.Compiler.Backend.WordAlloc.ProductionColouringCutsets

namespace Flapjack.WordAlloc

/-! These theorems connect the executed instruction adapter to the reviewed
native colouring operation through the actual partial encoder. They have no
separate HOL original: they prove implementation correspondence, including
rejection of the distinct five-register carry and the untouched 16-bit cases. -/

theorem colouringRegImm_production {width : Nat} [NeZero width]
    (colour : Nat → Nat) (value : WordRegImm (BitVec width)) :
    wordApplyColourRegImm colour value = applyColourImm colour value := by
  cases value <;> rfl

theorem colouringArith_production {width : Nat} [NeZero width]
    (colour : Nat → Nat) (actual : WordArith (BitVec width))
    (native : WordLangArith (BitVec width))
    (encoded : wordLangArithToHOL actual = some native) :
    (wordLangArithToHOL (wordApplyColourArith colour actual)).map WordLangInst.arith =
      some (applyColourInst colour (.arith native)) := by
  cases actual <;> simp [wordLangArithToHOL] at encoded
  all_goals subst native
  all_goals first | rfl | rename_i op dest lhs rhs; cases rhs <;> rfl

theorem colouringArith_route {width : Nat} (colour : Nat → Nat)
    (actual : WordArith (BitVec width)) :
    applyColourArithExecutable colour actual = wordApplyColourArith colour actual := by
  cases actual
  all_goals first | rfl | rename_i op dest lhs rhs; cases rhs <;> rfl

theorem colouringInst_production {width : Nat} [NeZero width]
    (colour : Nat → Nat) (actual : WordInst (BitVec width))
    (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL actual = some native) :
    wordLangInstToHOL (wordApplyColourInst colour actual) =
      some (applyColourInst colour native) := by
  cases actual with
  | const name value =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      rfl
  | arith operation =>
      cases accepted : wordLangArithToHOL operation with
      | none => simp [wordLangInstToHOL, accepted] at encoded
      | some exact =>
          simp only [wordLangInstToHOL, accepted, Option.map_some, Option.some.injEq] at encoded
          subst native
          change (wordLangArithToHOL (applyColourArithExecutable colour operation)).map
            WordLangInst.arith = _
          rw [colouringArith_route]
          exact colouringArith_production colour operation exact accepted
  | mem operator name address =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases operator <;> rfl
  | memOffset operator name address offset =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases operator <;> rfl

end Flapjack.WordAlloc
