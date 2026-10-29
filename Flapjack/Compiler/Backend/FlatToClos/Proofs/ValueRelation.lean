import Flapjack.Compiler.Backend.FlatToClos.Compile
import Flapjack.Compiler.Backend.FlatProps.NoMat
import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.Compiler.Backend.Semantics.FlatSem.Conversions
import Batteries.Data.List.Basic

/-! Proof-side value and environment relations for flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

mutual
/-- The source-shaped value relation, including captured environments and
recursive closures. It remains untagged until its inductive presentation and
the imported semantic carriers are reviewed against HOL. -/
inductive ValueRel : FlatSem.Value → ClosSem.Value → Prop where
  | loc (flag index) : ValueRel (.loc flag index) (.refPtr flag index)
  | int (value) : ValueRel (.litv (.intLit value)) (.number value)
  | char (value) : ValueRel (.litv (.char value)) (.number value.toNat)
  | string (value) : ValueRel (.litv (.strLit value)) (.byteVector value.explode)
  | word8 (value) : ValueRel (.litv (.word8 value)) (.number value.toNat)
  | word64 (value) : ValueRel (.litv (.word64 value)) (.word64 value)
  | float64 (value) : ValueRel (.litv (.float64 value)) (.word64 value)
  | tuple {source target} (values : List.Forall₂ ValueRel source target) :
      ValueRel (.conv none source) (.block 0 target)
  | con {source target tag typeId} (values : List.Forall₂ ValueRel source target) :
      ValueRel (.conv (some (tag, typeId)) source) (.block tag target)
  | vector {source target} (values : List.Forall₂ ValueRel source target) :
      ValueRel (.vectorv source) (.block 0 target)
  | closure {env names values name body} (related : EnvRel env names values)
      (safe : FlatProps.noMat body = true) :
      ValueRel (.closure env name body) (.closure none [] values 1 (compileExp (some name :: names) body))
  | recclosure {env names values funs index} (bound : index < funs.length)
      (related : EnvRel env names values) (distinct : (funs.map Prod.fst).Nodup)
      (safe : FlatProps.noMatFuns funs = true) :
      ValueRel (.recclosure env funs (funs[index]'bound).1)
        (.recclosure none [] values
          (compileFuns (funs.map (fun f => some f.1) ++ names) funs) index)

/-- Every visible source binding has a related value at its first de Bruijn
index. The explicit lookup result is a positivity-friendly presentation of
the corresponding HOL inductive rule. -/
inductive EnvRel : FlatSem.Environment FlatSem.Value → List (Option MlString) → List ClosSem.Value → Prop where
  | intro {env names values}
      (present : ∀ name value, env.v.lookup name = some value →
        (values[nameIndex (some name) names]?).isSome = true)
      (lookup : ∀ name value target, env.v.lookup name = some value →
        values[nameIndex (some name) names]? = some target → ValueRel value target) :
      EnvRel env names values
end

/-- The positivity-friendly environment rule is equivalent to requiring a
related target value at every source lookup. This is a Lean representation
lemma, not a cross-language correspondence proof. -/
theorem envRel_iff_lookup (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value) :
    EnvRel env names values ↔ ∀ name value, env.v.lookup name = some value →
      ∃ target, values[nameIndex (some name) names]? = some target ∧ ValueRel value target := by
  constructor
  · rintro ⟨present, lookup⟩ name value found
    cases h : values[nameIndex (some name) names]? with
    | none =>
      have impossible := present name value found
      simp [h] at impossible
    | some target => exact ⟨target, rfl, lookup name value target found h⟩
  · intro lookup
    constructor
    · intro name value found
      obtain ⟨target, h, _⟩ := lookup name value found
      simp [h]
    · intro name value target found h
      obtain ⟨target', h', related⟩ := lookup name value found
      rw [h] at h'
      cases h'
      exact related

/-- Related element lists encode to related flat and closure list values.
This proof-side lemma follows the corresponding HOL list conversion lemma. -/
theorem listToValue_related {source target} (related : List.Forall₂ ValueRel source target) :
    ValueRel (FlatSem.listToValue source) (ClosSem.listToValue target) := by
  induction related with
  | nil => exact .con .nil
  | cons head tail ih => exact .con (.cons head (.cons ih .nil))

end Flapjack.Compiler.Backend.FlatToClos
