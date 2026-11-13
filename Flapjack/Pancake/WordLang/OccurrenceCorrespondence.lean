module

public import Flapjack.Pancake.WordLang

@[expose] public section

namespace Flapjack

/-- Flapjack-only consumer boundary: the proposition-valued recursor's
instruction case is the reviewed positive-width predicate itself, so the iff
holds by definition. The legacy production `everyVarImm`/`everyVarInst`
duplicates and their two equality bridges were retired in task 156; `everyVar`
already dispatches to `everyVarInstHOL`. No assertion about the other program
cases or compiler routing is made. -/
theorem everyVar_inst_iff_exact {width : Nat} [NeZero width]
    (predicate : Nat → Bool) (instruction : WordLangInst (BitVec width)) :
    everyVar predicate (.inst instruction) ↔ everyVarInstHOL predicate instruction = true :=
  Iff.rfl

end Flapjack
