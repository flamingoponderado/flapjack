import Flapjack.Compiler.Backend.WordToStack.ProductionSelectorPrelude
import Flapjack.Pancake.WordConvs

namespace Flapjack.WordProgCarrierCodec

/-- Structural production view of the original native flat-expression
convention. This untagged Flapjack codec infrastructure has no independent HOL
original; the correspondence theorem below connects it to flatExpConventions. -/
def productionFlat {α : Type u} : WordProg α → Bool
  | .assign _ _ | .store _ _ => false
  | .set _ (.var _) => true
  | .set _ _ => false
  | .shareInst _ _ (.var _) => true
  | .shareInst _ _ (.op .add [.var _, .const _]) => true
  | .shareInst _ _ _ => false
  | .seq first second | .ite _ _ _ first second =>
      productionFlat first && productionFlat second
  | .loop _ body _ | .mustTerminate body => productionFlat body
  | .call returns _ _ handler =>
      (match returns with
       | none => true
       | some (_, _, body, _, _) => productionFlat body) &&
      (match handler with
       | none => true
       | some (_, body, _, _) => productionFlat body)
  | _ => true
termination_by program => sizeOf program

/-- Complete actual partial-codec correspondence of the flat convention.
The codec equality identifies its output; it assumes no flat property and is
not a compiler correctness theorem or a target execution hypothesis. This
Flapjack infrastructure deliberately has no separate HOL tag. -/
theorem productionFlat_codec {width : Nat}
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    flatExpConventions native = productionFlat program := by
  fun_induction wordApplyColour (fun name => name) program generalizing native
  all_goals simp only [wordLangProgToHOL, Option.map_eq_some_iff,
    Option.some.injEq] at encoded
  all_goals try subst native
  all_goals try simp_all [productionFlat, flatExpConventions]
  all_goals try simp only [Option.bind_eq_some_iff, Option.some.injEq] at encoded
  all_goals repeat' (first | (rcases encoded with ⟨a, h, encoded⟩) | (subst native))
  all_goals try simp_all [flatExpConventions]
  case case7 =>
    rename_i store value
    cases value <;> simp [wordExpToHOL, productionFlat, flatExpConventions]
  case case29 =>
    rename_i operator name address
    cases address <;> try simp [wordExpToHOL, productionFlat, flatExpConventions]
    rename_i operation arguments
    cases operation <;> try simp [productionFlat, flatExpConventions]
    cases arguments with
    | nil => simp [productionFlat, flatExpConventions]
    | cons first rest =>
        cases rest with
        | nil => simp [productionFlat, flatExpConventions]
        | cons second rest =>
            cases rest with
            | nil => cases first <;> cases second <;> simp [wordExpToHOL, productionFlat, flatExpConventions]
            | cons third rest => simp [productionFlat, flatExpConventions]

/-- Full Option-level correspondence includes codec rejection unchanged. No
successful-conversion or flat-convention premise is supplied. This is
Flapjack-only infrastructure for the executed compiler carrier. -/
theorem productionFlat_codec_map {width : Nat} (program : WordProg (BitVec width)) :
    (wordLangProgToHOL program).map flatExpConventions =
      (wordLangProgToHOL program).map (fun _ => productionFlat program) := by
  cases encoded : wordLangProgToHOL program with
  | none => rfl
  | some native =>
      simp only [Option.map_some]
      exact congrArg some (productionFlat_codec program native encoded)

end Flapjack.WordProgCarrierCodec
