import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Flapjack.Misc.ListEl
import Flapjack.Misc.IndexedLists

/-! Induction through the mutually recursive flat-to-closure relations. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString

/-- The executable name index implements HOL's polymorphic first-index search. -/
theorem nameIndex_eq_holFindi (name : Option MlString) (names : List (Option MlString)) :
    nameIndex name names = Flapjack.holFindi name names := by
  induction names with
  | nil => rfl
  | cons head tail ih => simp [nameIndex, Flapjack.holFindi, ih, Nat.add_comm]

/-- Rules for predicates on related values and environments. The lookup
formulation exposes a bounded target entry and is equivalent to the HOL
index-and-element formulation on valid indices. -/
structure ValueRelInductionSteps
    (P : FlatSem.Value → ClosSem.Value → Prop)
    (Q : FlatSem.Environment FlatSem.Value → List (Option MlString) → List ClosSem.Value → Prop) : Prop where
  loc : ∀ flag index, P (.loc flag index) (.refPtr flag index)
  int : ∀ value, P (.litv (.intLit value)) (.number value)
  char : ∀ value, P (.litv (.char value)) (.number value.toNat)
  string : ∀ value, P (.litv (.strLit value)) (.byteVector value.explode)
  word8 : ∀ value, P (.litv (.word8 value)) (.number value.toNat)
  word64 : ∀ value, P (.litv (.word64 value)) (.word64 value)
  float64 : ∀ value, P (.litv (.float64 value)) (.word64 value)
  tuple : ∀ source target, List.Forall₂ P source target → P (.conv none source) (.block 0 target)
  con : ∀ source target tag typeId, List.Forall₂ P source target →
    P (.conv (some (tag, typeId)) source) (.block tag target)
  vector : ∀ source target, List.Forall₂ P source target → P (.vectorv source) (.block 0 target)
  closure : ∀ env names values name body, Q env names values → FlatProps.noMat body = true →
    P (.closure env name body) (.closure none [] values 1 (compileExp (some name :: names) body))
  recclosure : ∀ env names values funs index (bound : index < funs.length), Q env names values →
    (funs.map Prod.fst).Nodup → FlatProps.noMatFuns funs = true →
    P (.recclosure env funs (funs[index]'bound).1)
      (.recclosure none [] values (compileFuns (funs.map (fun f => some f.1) ++ names) funs) index)
  env : ∀ env names values,
    (∀ name value, env.v.lookup name = some value →
      ∃ target, values[nameIndex (some name) names]? = some target ∧ P value target) → Q env names values

/-- Source-shaped mutual induction, derived from the positivity-friendly Lean
relations. This infrastructure has no separate HOL declaration. -/
theorem valueRel_source_induction
    (P : FlatSem.Value → ClosSem.Value → Prop)
    (Q : FlatSem.Environment FlatSem.Value → List (Option MlString) → List ClosSem.Value → Prop)
    (steps : ValueRelInductionSteps P Q) :
    (∀ source target, ValueRel source target → P source target) ∧
    (∀ env names values, EnvRel env names values → Q env names values) := by
  refine ⟨?_, ?_⟩
  all_goals
    intros
    first
    | refine ValueRel.rec (motive_1 := fun x y _ => P x y)
        (motive_2 := fun env names values _ => Q env names values)
        (motive_3 := fun xs ys _ => List.Forall₂ P xs ys)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ‹ValueRel _ _›
    | refine EnvRel.rec (motive_1 := fun x y _ => P x y)
        (motive_2 := fun env names values _ => Q env names values)
        (motive_3 := fun xs ys _ => List.Forall₂ P xs ys)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ‹EnvRel _ _ _›
  all_goals
    try first
    | exact steps.loc
    | exact steps.int
    | exact steps.char
    | exact steps.string
    | exact steps.word8
    | exact steps.word64
    | exact steps.float64
    | exact fun {source} {target} _ ih => steps.tuple source target ih
    | exact fun {source} {target} {tag} {typeId} _ ih => steps.con source target tag typeId ih
    | exact fun {source} {target} _ ih => steps.vector source target ih
    | exact fun _ safe ih => steps.closure _ _ _ _ _ ih safe
    | exact fun bound _ distinct safe ih => steps.recclosure _ _ _ _ _ bound ih distinct safe
    | exact .nil
    | exact fun {_} {_} {_} {_} _ _ ihHead ihTail => .cons ihHead ihTail
    | exact fun {env} {names} {values} present _ ih => steps.env env names values (by
        intro name value found
        cases selected : values[nameIndex (some name) names]? with
        | none =>
          have impossible := present name value found
          simp [selected] at impossible
        | some target => exact ⟨target, rfl, ih name value target found selected⟩)

/-- Optional indexing and the HOL bound-plus-`EL` formulation give the same
environment induction premise. This is a bounded-index representation fact. -/
theorem envLookup_source_shape
    (P : FlatSem.Value → ClosSem.Value → Prop) (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value) :
    (∀ name value, env.v.lookup name = some value →
      ∃ target, values[nameIndex (some name) names]? = some target ∧ P value target) ↔
    (∀ name value, env.v.lookup name = some value →
      nameIndex (some name) names < values.length ∧
        P value (@Flapjack.holEl ClosSem.Value ⟨.number 0⟩ (nameIndex (some name) names) values)) := by
  letI : Nonempty ClosSem.Value := ⟨.number 0⟩
  constructor
  · intro related name value found
    obtain ⟨target, selected, valid⟩ := related name value found
    obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp selected
    refine ⟨bound, ?_⟩
    rw [Flapjack.holEl_eq_getElem _ _ bound, eq]
    exact valid
  · intro related name value found
    obtain ⟨bound, valid⟩ := related name value found
    refine ⟨values[nameIndex (some name) names]'bound, List.getElem?_eq_getElem bound, ?_⟩
    simpa [Flapjack.holEl_eq_getElem _ _ bound] using valid

/-- The environment relation has exactly the source's bounded lookup case. -/
theorem envRel_hol_cases (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value) :
    EnvRel env names values ↔ ∀ name value, env.v.lookup name = some value →
      Flapjack.holFindi (some name) names < values.length ∧
        ValueRel value (@Flapjack.holEl ClosSem.Value ⟨.number 0⟩
          (Flapjack.holFindi (some name) names) values) := by
  rw [envRel_iff_lookup, envLookup_source_shape]
  simp only [nameIndex_eq_holFindi]

/-- The singleton compiler helper is the `HD` of the source list compiler. -/
theorem compileExp_eq_holHd (names : List (Option MlString)) (expression : FlatLang.Exp) :
    compileExp names expression =
      @Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile names [expression]) := by
  simp [compile, compileExps, Flapjack.holHd]

/-- The recursive-group compiler has the source's mapped singleton shape. -/
theorem compileFuns_eq_source (names : List (Option MlString))
    (funs : List (MlString × MlString × FlatLang.Exp)) :
    compileFuns names funs = funs.map (fun (_, arg, body) =>
      (1, @Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile (some arg :: names) [body]))) := by
  induction funs with
  | nil => simp [compileFuns]
  | cons first rest ih =>
    rcases first with ⟨name, arg, body⟩
    simp [compileFuns, compile, compileExps, Flapjack.holHd, ih]

/-- The recursive-group safety check is the source's elementwise predicate. -/
theorem noMatFuns_eq_source (funs : List (MlString × MlString × FlatLang.Exp)) :
    FlatProps.noMatFuns funs = true ↔ ∀ f ∈ funs, FlatProps.noMat f.2.2 = true := by
  induction funs with
  | nil => simp [FlatProps.noMatFuns]
  | cons first rest ih =>
    rcases first with ⟨name, arg, body⟩
    simp [FlatProps.noMatFuns, ih]

/-- The source induction rules written with HOL-style bounded indexing,
singleton compilation, and elementwise recursive-body safety. -/
structure ValueRelSourceSteps
    (P : FlatSem.Value → ClosSem.Value → Prop)
    (Q : FlatSem.Environment FlatSem.Value → List (Option MlString) → List ClosSem.Value → Prop) : Prop where
  loc : ∀ flag index, P (.loc flag index) (.refPtr flag index)
  int : ∀ value, P (.litv (.intLit value)) (.number value)
  char : ∀ value, P (.litv (.char value)) (.number value.toNat)
  string : ∀ value, P (.litv (.strLit value)) (.byteVector value.explode)
  word8 : ∀ value, P (.litv (.word8 value)) (.number value.toNat)
  word64 : ∀ value, P (.litv (.word64 value)) (.word64 value)
  float64 : ∀ value, P (.litv (.float64 value)) (.word64 value)
  tuple : ∀ source target, List.Forall₂ P source target → P (.conv none source) (.block 0 target)
  con : ∀ source target tag typeId, List.Forall₂ P source target →
    P (.conv (some (tag, typeId)) source) (.block tag target)
  vector : ∀ source target, List.Forall₂ P source target → P (.vectorv source) (.block 0 target)
  env : ∀ env names values,
    (∀ name value, env.v.lookup name = some value →
      Flapjack.holFindi (some name) names < values.length ∧
        P value (@Flapjack.holEl ClosSem.Value ⟨.number 0⟩ (Flapjack.holFindi (some name) names) values)) →
    Q env names values
  closure : ∀ env names values name body, Q env names values → FlatProps.noMat body = true →
    P (.closure env name body) (.closure none [] values 1
      (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile (some name :: names) [body])))
  recclosure : ∀ env names values funs index, index < funs.length → Q env names values →
    (funs.map Prod.fst).Nodup → (∀ f ∈ funs, FlatProps.noMat f.2.2 = true) →
    P (.recclosure env funs
      (@Flapjack.holEl (MlString × MlString × FlatLang.Exp)
        ⟨(ofString "", ofString "", .lit .none (.intLit 0))⟩ index funs).1)
      (.recclosure none [] values (funs.map (fun (_, arg, body) =>
        (1, @Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩
          (compile (some arg :: (funs.map (fun f => some f.1) ++ names)) [body])))) index)

/-- The Lean mutual relations satisfy the source's induction scheme. The
list-index and singleton-compiler conversions are proved above. -/
theorem valueRel_hol_induction
    (P : FlatSem.Value → ClosSem.Value → Prop)
    (Q : FlatSem.Environment FlatSem.Value → List (Option MlString) → List ClosSem.Value → Prop)
    (steps : ValueRelSourceSteps P Q) :
    (∀ env names values, EnvRel env names values → Q env names values) ∧
    (∀ source target, ValueRel source target → P source target) := by
  have derived : ValueRelInductionSteps P Q := {
    loc := steps.loc, int := steps.int, char := steps.char, string := steps.string
    word8 := steps.word8, word64 := steps.word64, float64 := steps.float64
    tuple := steps.tuple, con := steps.con, vector := steps.vector
    env := by
      intro env names values ih
      apply steps.env env names values
      simpa only [← nameIndex_eq_holFindi] using (envLookup_source_shape P env names values).mp ih
    closure := by
      intro env names values name body ih safe
      simpa only [← compileExp_eq_holHd] using steps.closure env names values name body ih safe
    recclosure := by
      intro env names values funs index bound ih distinct safe
      have bodySafe := (noMatFuns_eq_source funs).mp safe
      have result := steps.recclosure env names values funs index bound ih distinct bodySafe
      letI : Nonempty (MlString × MlString × FlatLang.Exp) :=
        ⟨(ofString "", ofString "", .lit .none (.intLit 0))⟩
      simpa only [Flapjack.holEl_eq_getElem _ _ bound, ← compileFuns_eq_source] using result }
  have induction := valueRel_source_induction P Q derived
  exact ⟨induction.2, induction.1⟩

/-- Case decomposition of the value relation in the shape of the source
mutual relation, with the original singleton compiler and bounded `EL`. -/
theorem valueRel_hol_cases (source : FlatSem.Value) (target : ClosSem.Value) :
    ValueRel source target ↔
      (∃ flag index, source = .loc flag index ∧ target = .refPtr flag index) ∨
      (∃ value, source = .litv (.intLit value) ∧ target = .number value) ∨
      (∃ value, source = .litv (.char value) ∧ target = .number value.toNat) ∨
      (∃ value, source = .litv (.strLit value) ∧ target = .byteVector value.explode) ∨
      (∃ value, source = .litv (.word8 value) ∧ target = .number value.toNat) ∨
      (∃ value, source = .litv (.word64 value) ∧ target = .word64 value) ∨
      (∃ value, source = .litv (.float64 value) ∧ target = .word64 value) ∨
      (∃ xs ys, source = .conv none xs ∧ target = .block 0 ys ∧ List.Forall₂ ValueRel xs ys) ∨
      (∃ xs ys tag typeId, source = .conv (some (tag, typeId)) xs ∧ target = .block tag ys ∧
        List.Forall₂ ValueRel xs ys) ∨
      (∃ xs ys, source = .vectorv xs ∧ target = .block 0 ys ∧ List.Forall₂ ValueRel xs ys) ∨
      (∃ env names values name body, source = .closure env name body ∧
        target = .closure none [] values 1
          (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile (some name :: names) [body])) ∧
        EnvRel env names values ∧ FlatProps.noMat body = true) ∨
      (∃ funs index env names values,
        source = .recclosure env funs
          (@Flapjack.holEl (MlString × MlString × FlatLang.Exp)
            ⟨(ofString "", ofString "", .lit .none (.intLit 0))⟩ index funs).1 ∧
        target = .recclosure none [] values (funs.map (fun (_, arg, body) =>
          (1, @Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩
            (compile (some arg :: (funs.map (fun f => some f.1) ++ names)) [body])))) index ∧
        index < funs.length ∧ EnvRel env names values ∧ (funs.map Prod.fst).Nodup ∧
        (∀ f ∈ funs, FlatProps.noMat f.2.2 = true)) := by
  letI : Nonempty (MlString × MlString × FlatLang.Exp) :=
    ⟨(ofString "", ofString "", .lit .none (.intLit 0))⟩
  constructor
  · intro related
    cases related with
    | loc flag index => exact .inl ⟨flag, index, rfl, rfl⟩
    | int value => exact .inr (.inl ⟨value, rfl, rfl⟩)
    | char value => exact .inr (.inr (.inl ⟨value, rfl, rfl⟩))
    | string value => exact .inr (.inr (.inr (.inl ⟨value, rfl, rfl⟩)))
    | word8 value => exact .inr (.inr (.inr (.inr (.inl ⟨value, rfl, rfl⟩))))
    | word64 value => exact .inr (.inr (.inr (.inr (.inr (.inl ⟨value, rfl, rfl⟩)))))
    | float64 value => exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨value, rfl, rfl⟩))))))
    | tuple values => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl, values⟩)))))))
    | con values => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, rfl, values⟩))))))))
    | vector values => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl, values⟩)))))))))
    | closure related safe =>
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
      exact ⟨_, _, _, _, _, rfl, by simp only [← compileExp_eq_holHd], related, safe⟩
    | recclosure bound related distinct safe =>
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      refine ⟨_, _, _, _, _, ?_, compileFuns_eq_source _ _ ▸ rfl, bound, related, distinct, ?_⟩
      · simp only [Flapjack.holEl_eq_getElem _ _ bound]
      · exact (noMatFuns_eq_source _).mp safe
  · rintro (⟨flag, index, rfl, rfl⟩ | ⟨value, rfl, rfl⟩ | ⟨value, rfl, rfl⟩ |
      ⟨value, rfl, rfl⟩ | ⟨value, rfl, rfl⟩ | ⟨value, rfl, rfl⟩ | ⟨value, rfl, rfl⟩ |
      ⟨xs, ys, rfl, rfl, values⟩ | ⟨xs, ys, tag, typeId, rfl, rfl, values⟩ |
      ⟨xs, ys, rfl, rfl, values⟩ | ⟨env, names, values, name, body, rfl, rfl, related, safe⟩ |
      ⟨funs, index, env, names, values, rfl, rfl, bound, related, distinct, safe⟩)
    · exact .loc flag index
    · exact .int value
    · exact .char value
    · exact .string value
    · exact .word8 value
    · exact .word64 value
    · exact .float64 value
    · exact .tuple values
    · exact .con values
    · exact .vector values
    · simpa only [← compileExp_eq_holHd] using ValueRel.closure related safe
    · simpa only [Flapjack.holEl_eq_getElem _ _ bound, ← compileFuns_eq_source] using
        ValueRel.recclosure bound related distinct ((noMatFuns_eq_source funs).mpr safe)

end Flapjack.Compiler.Backend.FlatToClos
