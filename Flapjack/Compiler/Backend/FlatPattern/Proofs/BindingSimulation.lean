import Flapjack.Compiler.Backend.FlatPattern.Proofs.BindingFold
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PatternList
import Flapjack.Compiler.Backend.FlatPattern.BindingsTotal

/-! Evaluation steps for compiled pattern bindings. These proofs use the
unreviewed clocked evaluator and are not tagged as HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (storeLookup)

/-- Projecting a reference whose contents are present is a pure evaluation
step for the generated `el 0` expression. -/
theorem evaluate_ref_projection {C F : Type} (trace : BackendCommon.Tra)
    (expression : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (flag : Bool) (index : Nat) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.loc flag index]))
    (found : storeLookup index state.refs = some (.refv value)) :
    FlatSem.evaluate env state [.app trace (.el 0) [expression]] = (state, .val [value]) := by
  simp [FlatSem.evaluate, pure, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, found]

/-- A generated constructor projection evaluates to the indexed field when
the input expression evaluates purely to that constructor value. -/
theorem evaluate_con_projection {C F : Type} (trace : BackendCommon.Tra)
    (expression : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields : List FlatSem.Value) (index : Nat)
    (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.conv stamp fields]))
    (found : fields[index]? = some value) :
    FlatSem.evaluate env state [.app trace (.el index) [expression]] = (state, .val [value]) := by
  simp [FlatSem.evaluate, pure, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, found]

/-- A sequence of constructor field projections binds the selected values in
the same order as the generated let fold. -/
theorem evaluate_con_projection_fold {C F : Type} (trace : BackendCommon.Tra)
    (expression body : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields : List FlatSem.Value)
    (entries : List (Nat × VarN × FlatSem.Value)) (newNames : VarN → Prop)
    (fresh : ∀ entry ∈ entries, newNames entry.2.1)
    (found : ∀ entry ∈ entries, fields[entry.1]? = some entry.2.2)
    (pure : ∀ env2, aLookupRel (fun name => ¬ newNames name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [expression] = (state, .val [.conv stamp fields])) :
    ∀ env2, aLookupRel (fun name => ¬ newNames name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [entries.foldr (fun entry exp =>
        .let_ trace (some entry.2.1) (.app trace (.el entry.1) [expression]) exp) body] =
      FlatSem.evaluate { env2 with v := entries.reverse.map (fun entry => (entry.2.1, entry.2.2)) ++ env2.v }
        state [body] := by
  apply evaluateBindingFold (fun entry => some entry.2.1)
    (fun entry => .app trace (.el entry.1) [expression]) (fun entry => entry.2.2)
    entries newNames env state trace body
  · simp
  · simpa using fresh
  · intro entry member env2 related
    exact evaluate_con_projection trace expression env2 state stamp fields entry.1 entry.2.2
      (pure env2 related) (found entry member)

/-- The constructor case executes the compiler's selected projections and
continues with their values bound to the corresponding generated names. -/
theorem compilePatBindings_con_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (patternStamp : Option (FlatLang.CtorId × FlatLang.TypeGroupId)) (patterns : List FlatLang.Pat)
    (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields : List FlatSem.Value)
    (lengths : patterns.length = fields.length)
    (pure : ∀ env2, aLookupRel (fun name => ¬ i < decNameToNum name) Eq env2.v env.v →
      FlatSem.evaluate env2 state [expression] = (state, .val [.conv stamp fields])) :
    let entries := patternEntries trace i 0 patterns
    let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
    let selected := entries.filter (fun entry => (sptLookup entry.2.2.1 compiled.1).isSome)
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pcon patternStamp patterns, key, expression) :: rest) body).2] =
      FlatSem.evaluate { env with v := selected.reverse.map (fun entry =>
        (entry.1.2, (fields[entry.1.1]?).getD FlatSem.unitValue)) ++ env.v } state [compiled.2] := by
  let entries := patternEntries trace i 0 patterns
  let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
  let selected := entries.filter (fun entry => (sptLookup entry.2.2.1 compiled.1).isSome)
  have props : ∀ entry ∈ selected, entry.1.1 < fields.length ∧ i < decNameToNum entry.1.2 := by
    intro entry member
    have inEntries : entry ∈ entries := (List.mem_filter.mp member).1
    have h := patternEntries_member trace i 0 patterns entry inEntries
    constructor
    · omega
    · rw [h.2.2, decEnc]
      omega
  have folded := evaluateBindingFold
    (fun entry => some entry.1.2)
    (fun entry => FlatLang.Exp.app trace (.el entry.1.1) [expression])
    (fun entry => (fields[entry.1.1]?).getD FlatSem.unitValue)
    selected (fun name => i < decNameToNum name) env state trace compiled.2
    (by simp) (by simpa using fun entry member => (props entry member).2)
    (by
      intro entry member env2 related
      have within := (props entry member).1
      have found : fields[entry.1.1]? = some ((fields[entry.1.1]?).getD FlatSem.unitValue) := by
        cases h : fields[entry.1.1]? with
        | none =>
          have absent := (List.getElem?_eq_none_iff).1 h
          omega
        | some value => simp
      exact evaluate_con_projection trace expression env2 state stamp fields entry.1.1 _ (pure env2 related) found)
    env (aLookupRel_refl _ _ _ (by intros; rfl))
  cases h : compiled with
  | mk used result =>
    simpa [compilePatBindings, entries, compiled, selected, h] using folded

/-- Selected constructor temporaries do not change lookups below the
original-name bound. -/
theorem compilePatBindings_con_lookup (trace : BackendCommon.Tra) (i bound : Nat)
    (patterns : List FlatLang.Pat) (body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (fields : List FlatSem.Value)
    (pre base : List (VarN × FlatSem.Value))
    (related : aLookupRel (fun n => decNameToNum n < bound) Eq env.v (pre ++ base))
    (fresh : bound ≤ i + 1) :
    let entries := patternEntries trace i 0 patterns
    let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
    let selected := entries.filter (fun entry => (sptLookup entry.2.2.1 compiled.1).isSome)
    aLookupRel (fun n => decNameToNum n < bound) Eq
      (selected.reverse.map (fun entry => (entry.1.2, (fields[entry.1.1]?).getD FlatSem.unitValue)) ++ env.v)
      (pre ++ base) := by
  let entries := patternEntries trace i 0 patterns
  let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
  let selected := entries.filter (fun entry => (sptLookup entry.2.2.1 compiled.1).isSome)
  apply (aLookupRel_append_left_false _ _ _ _ _ ?_).2 related
  intro binding member selectedKey
  obtain ⟨entry, entryMem, rfl⟩ := List.mem_map.mp member
  have inSelected : entry ∈ selected := by simpa only [List.mem_reverse] using entryMem
  have inEntries : entry ∈ entries := (List.mem_filter.mp inSelected).1
  have h := patternEntries_member trace i 0 patterns entry inEntries
  simp only at selectedKey
  rw [h.2.2, decEnc] at selectedKey
  omega

/-- The generated binding for a variable evaluates its source expression
and then continues with that value at the head of the environment. -/
theorem compilePatBindings_var_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (name : VarN) (expression body : FlatLang.Exp)
    (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pvar name, key, expression) :: rest) body).2] =
      FlatSem.evaluate { env with v := (name, value) :: env.v } state
        [(compilePatBindings trace i rest body).2] := by
  cases compiled : compilePatBindings trace i rest body with
  | mk used result =>
    simp [compilePatBindings, compiled, FlatSem.evaluate, pure, FlatSem.fixClock]

/-- The variable step also preserves the observed lookup relation with the
matcher bindings extended by the same value. -/
theorem compilePatBindings_var_step {C F : Type} (trace : BackendCommon.Tra) (i key bound : Nat)
    (name : VarN) (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pre base : List (VarN × FlatSem.Value))
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (related : aLookupRel (fun n => decNameToNum n < bound) Eq env.v (pre ++ base)) :
    let next := { env with v := (name, value) :: env.v }
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pvar name, key, expression) :: rest) body).2] =
      FlatSem.evaluate next state [(compilePatBindings trace i rest body).2] ∧
    aLookupRel (fun n => decNameToNum n < bound) Eq next.v (((name, value) :: pre) ++ base) := by
  constructor
  · exact compilePatBindings_var_evaluate trace i key name expression body rest env state value pure
  · exact aLookupRel_cons _ _ name value value env.v (pre ++ base) (fun _ => rfl) related

/-- Wildcard bindings introduce no code and leave the continuation untouched. -/
theorem compilePatBindings_any_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) :
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pany, key, expression) :: rest) body).2] =
      FlatSem.evaluate env state [(compilePatBindings trace i rest body).2] := by
  simp [compilePatBindings]

/-- Literal bindings introduce no code and leave the continuation untouched. -/
theorem compilePatBindings_lit_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (lit : Lit) (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) :
    FlatSem.evaluate env state [(compilePatBindings trace i ((.plit lit, key, expression) :: rest) body).2] =
      FlatSem.evaluate env state [(compilePatBindings trace i rest body).2] := by
  simp [compilePatBindings]

/-- An as-pattern binds the original value and copies it into the generated
name used by the nested pattern's continuation. -/
theorem compilePatBindings_as_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (pattern : FlatLang.Pat) (name : VarN) (expression body : FlatLang.Exp)
    (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    let generated := encNumToName (i + 1)
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pas pattern name, key, expression) :: rest) body).2] =
      FlatSem.evaluate { env with v := (generated, value) :: (name, value) :: env.v } state
        [(compilePatBindings trace (i + 2) ((pattern, i + 1, .varLocal trace generated) :: rest) body).2] := by
  cases compiled : compilePatBindings trace (i + 2)
      ((pattern, i + 1, .varLocal trace (encNumToName (i + 1))) :: rest) body with
  | mk used result =>
    simp [compilePatBindings, compiled, FlatSem.evaluate, pure, FlatSem.fixClock]

/-- The generated as-pattern name is invisible below the original-name bound,
while the user binding is visible just as it is in the matcher environment. -/
theorem compilePatBindings_as_step {C F : Type} (trace : BackendCommon.Tra) (i key bound : Nat)
    (pattern : FlatLang.Pat) (name : VarN) (expression body : FlatLang.Exp)
    (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pre base : List (VarN × FlatSem.Value))
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (related : aLookupRel (fun n => decNameToNum n < bound) Eq env.v (pre ++ base))
    (fresh : bound ≤ i + 1) :
    let generated := encNumToName (i + 1)
    let next := { env with v := (generated, value) :: (name, value) :: env.v }
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pas pattern name, key, expression) :: rest) body).2] =
      FlatSem.evaluate next state
        [(compilePatBindings trace (i + 2) ((pattern, i + 1, .varLocal trace generated) :: rest) body).2] ∧
    aLookupRel (fun n => decNameToNum n < bound) Eq next.v (((name, value) :: pre) ++ base) := by
  constructor
  · exact compilePatBindings_as_evaluate trace i key pattern name expression body rest env state value pure
  · have old := aLookupRel_cons (fun n => decNameToNum n < bound) Eq name value value env.v (pre ++ base)
      (fun _ => rfl) related
    apply ((aLookupRel_cons_false (fun n => decNameToNum n < bound) Eq (encNumToName (i + 1)) value
      ((name, value) :: env.v) (((name, value) :: pre) ++ base)).1 ?_).2 old
    simp only [decEnc]
    omega

/-- A reference-pattern binding evaluates the generated projection and passes
the referenced contents to the nested pattern through a fresh name. -/
theorem compilePatBindings_ref_step {C F : Type} (trace : BackendCommon.Tra) (i key bound : Nat)
    (pattern : FlatLang.Pat) (expression body : FlatLang.Exp)
    (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (flag : Bool) (index : Nat)
    (value : FlatSem.Value) (pre base : List (VarN × FlatSem.Value))
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.loc flag index]))
    (found : storeLookup index state.refs = some (.refv value))
    (related : aLookupRel (fun n => decNameToNum n < bound) Eq env.v (pre ++ base))
    (fresh : bound ≤ i + 1) :
    let generated := encNumToName (i + 1)
    let next := { env with v := (generated, value) :: env.v }
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pref pattern, key, expression) :: rest) body).2] =
      FlatSem.evaluate next state
        [(compilePatBindings trace (i + 2) ((pattern, i + 1, .varLocal trace generated) :: rest) body).2] ∧
    aLookupRel (fun n => decNameToNum n < bound) Eq next.v (pre ++ base) := by
  constructor
  · have projected := evaluate_ref_projection trace expression env state flag index value pure found
    cases compiled : compilePatBindings trace (i + 2)
        ((pattern, i + 1, .varLocal trace (encNumToName (i + 1))) :: rest) body with
    | mk used result =>
      simp [compilePatBindings, compiled, FlatSem.evaluate, projected, FlatSem.fixClock]
  · apply ((aLookupRel_cons_false (fun n => decNameToNum n < bound) Eq (encNumToName (i + 1)) value
      env.v (pre ++ base)).1 ?_).2 related
    simp only [decEnc]
    omega

end Flapjack.Compiler.Backend.FlatPattern
