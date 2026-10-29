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

/-- If all entries with the same key carry the same value, lookup of any
member's key returns that value, even when keys are repeated. -/
theorem holALookup_map_consistent {A K V : Type} (entries : List A) (key : A → K) (value : A → V)
    (chosen : A) (member : chosen ∈ entries)
    (consistent : ∀ entry ∈ entries, key entry = key chosen → value entry = value chosen) :
    holALookup (entries.map fun entry => (key entry, value entry)) (key chosen) = some (value chosen) := by
  classical
  induction entries with
  | nil => simp at member
  | cons first rest ih =>
    by_cases same : key chosen = key first
    · have eq := consistent first (by simp) same.symm
      simp [holALookup, same, eq]
    · have later : chosen ∈ rest := by
        rcases List.mem_cons.mp member with equal | later
        · subst chosen
          exact (same rfl).elim
        · exact later
      have restConsistent : ∀ entry ∈ rest, key entry = key chosen → value entry = value chosen := by
        intro entry inRest equal
        exact consistent entry (by simp [inRest]) equal
      simpa [holALookup, same] using ih later restConsistent

/-- Every selected constructor temporary looks up to its own projected field
in the environment built by the generated projection fold. -/
theorem compilePatBindings_con_selected_lookup (trace : BackendCommon.Tra) (i : Nat)
    (patterns : List FlatLang.Pat) (body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (fields : List FlatSem.Value)
    (entry : (Nat × VarN) × (FlatLang.Pat × Nat × FlatLang.Exp)) :
    let entries := patternEntries trace i 0 patterns
    let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
    let selected := entries.filter (fun e => (sptLookup e.2.2.1 compiled.1).isSome)
    entry ∈ selected →
    holALookup (selected.reverse.map (fun e => (e.1.2, (fields[e.1.1]?).getD FlatSem.unitValue)) ++ env.v)
      entry.1.2 = some ((fields[entry.1.1]?).getD FlatSem.unitValue) := by
  let entries := patternEntries trace i 0 patterns
  let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
  let selected := entries.filter (fun e => (sptLookup e.2.2.1 compiled.1).isSome)
  change entry ∈ selected →
    holALookup (selected.reverse.map (fun e => (e.1.2, (fields[e.1.1]?).getD FlatSem.unitValue)) ++ env.v)
      entry.1.2 = some ((fields[entry.1.1]?).getD FlatSem.unitValue)
  intro member
  have chosen : entry ∈ entries := (List.mem_filter.mp member).1
  have chosenName := (patternEntries_member trace i 0 patterns entry chosen).2.2
  have lookup := holALookup_map_consistent selected.reverse (fun e => e.1.2)
    (fun e => (fields[e.1.1]?).getD FlatSem.unitValue) entry
    (by simpa only [List.mem_reverse] using member) (by
      intro other inReverse equalName
      have inSelected : other ∈ selected := by simpa only [List.mem_reverse] using inReverse
      have inEntries : other ∈ entries := (List.mem_filter.mp inSelected).1
      have otherName := (patternEntries_member trace i 0 patterns other inEntries).2.2
      rw [otherName, chosenName] at equalName
      have equalIndex := (encNumToName_inj _ _).1 equalName
      have : other.1.1 = entry.1.1 := by omega
      simp [this])
  rw [holALookup_append, lookup]
  rfl

/-- The nested pattern's generated variable evaluates to the projected field
in any environment agreeing on the generated-name interval. -/
theorem compilePatBindings_con_selected_pure {C F : Type} (trace : BackendCommon.Tra) (i : Nat)
    (patterns : List FlatLang.Pat) (body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env env2 : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (fields : List FlatSem.Value)
    (entry : (Nat × VarN) × (FlatLang.Pat × Nat × FlatLang.Exp)) :
    let entries := patternEntries trace i 0 patterns
    let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
    let selected := entries.filter (fun e => (sptLookup e.2.2.1 compiled.1).isSome)
    let extended := selected.reverse.map (fun e => (e.1.2, (fields[e.1.1]?).getD FlatSem.unitValue)) ++ env.v
    entry ∈ selected →
    aLookupRel (fun name => i < decNameToNum name ∧ decNameToNum name < i + 2 + patterns.length)
      Eq env2.v extended →
    FlatSem.evaluate env2 state [.varLocal trace entry.1.2] =
      (state, .val [(fields[entry.1.1]?).getD FlatSem.unitValue]) := by
  let entries := patternEntries trace i 0 patterns
  let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
  let selected := entries.filter (fun e => (sptLookup e.2.2.1 compiled.1).isSome)
  let extended := selected.reverse.map (fun e => (e.1.2, (fields[e.1.1]?).getD FlatSem.unitValue)) ++ env.v
  change entry ∈ selected →
    aLookupRel (fun name => i < decNameToNum name ∧ decNameToNum name < i + 2 + patterns.length)
      Eq env2.v extended → _
  intro member related
  have inEntries : entry ∈ entries := (List.mem_filter.mp member).1
  have info := patternEntries_member trace i 0 patterns entry inEntries
  have interval : i < decNameToNum entry.1.2 ∧ decNameToNum entry.1.2 < i + 2 + patterns.length := by
    rw [info.2.2, decEnc]
    omega
  have known := compilePatBindings_con_selected_lookup trace i patterns body rest env fields entry member
  have equalLookup := aLookupRel_eq_lookup _ _ _ entry.1.2 related interval
  have found : env2.v.lookup entry.1.2 = some ((fields[entry.1.1]?).getD FlatSem.unitValue) := by
    rw [← holALookup_mlString, equalLookup]
    exact known
  simp [FlatSem.evaluate, found]

/-- Each generated constructor work item uses its associated temporary as a
local-variable expression. -/
theorem patternEntries_work_expression (trace : BackendCommon.Tra) (i j : Nat) (patterns : List FlatLang.Pat)
    (entry : (Nat × VarN) × (FlatLang.Pat × Nat × FlatLang.Exp))
    (member : entry ∈ patternEntries trace i j patterns) :
    entry.2.2.1 = i + 1 + entry.1.1 ∧ entry.2.2.2 = .varLocal trace entry.1.2 := by
  induction patterns generalizing j with
  | nil => simp [patternEntries] at member
  | cons pattern patterns ih =>
    simp only [patternEntries, List.mem_cons] at member
    rcases member with same | later
    · subst entry
      simp
    · exact ih (j + 1) later

/-- The field index stored in each entry agrees with its position in the
generated work list. -/
theorem patternEntries_index (trace : BackendCommon.Tra) (i j k : Nat) (patterns : List FlatLang.Pat)
    (entry : (Nat × VarN) × (FlatLang.Pat × Nat × FlatLang.Exp))
    (found : (patternEntries trace i j patterns)[k]? = some entry) : entry.1.1 = j + k := by
  induction patterns generalizing j k with
  | nil => simp [patternEntries] at found
  | cons pattern patterns ih =>
    cases k with
    | zero =>
      simp [patternEntries] at found
      subst entry
      simp
    | succ k =>
      simp only [patternEntries, List.getElem?_cons_succ] at found
      have h := ih (j + 1) k found
      omega

/-- The constructor work list contains one item for each subpattern. -/
theorem patternEntries_length (trace : BackendCommon.Tra) (i j : Nat) (patterns : List FlatLang.Pat) :
    (patternEntries trace i j patterns).length = patterns.length := by
  induction patterns generalizing j with
  | nil => rfl
  | cons pattern patterns ih => simp [patternEntries, ih]

/-- Equal-length lists satisfy a pointwise relation when their option-valued
lookups satisfy it at every index. -/
theorem forall₂_of_getElem {A B : Type} (relation : A → B → Prop) (left : List A) (right : List B)
    (lengths : left.length = right.length)
    (pointwise : ∀ (k : Nat) (x : A) (y : B), left[k]? = some x → right[k]? = some y → relation x y) :
    List.Forall₂ relation left right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact .nil
    | cons _ _ => simp at lengths
  | cons first left ih =>
    cases right with
    | nil => simp at lengths
    | cons second right =>
      apply List.Forall₂.cons
      · exact pointwise 0 first second rfl rfl
      · apply ih right (by simpa using lengths)
        intro k x y leftAt rightAt
        exact pointwise (k + 1) x y (by simpa using leftAt) (by simpa using rightAt)

/-- A used generated constructor work item evaluates purely to its field in
every environment related on the generated-name interval. -/
theorem compilePatBindings_con_workitem_pure {C F : Type} (trace : BackendCommon.Tra) (i : Nat)
    (patterns : List FlatLang.Pat) (body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env env2 : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (fields : List FlatSem.Value)
    (item : FlatLang.Pat × Nat × FlatLang.Exp) :
    let entries := patternEntries trace i 0 patterns
    let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
    let selected := entries.filter (fun e => (sptLookup e.2.2.1 compiled.1).isSome)
    let extended := selected.reverse.map (fun e => (e.1.2, (fields[e.1.1]?).getD FlatSem.unitValue)) ++ env.v
    item ∈ entries.map Prod.snd → (sptLookup item.2.1 compiled.1).isSome = true →
    aLookupRel (fun name => i < decNameToNum name ∧ decNameToNum name < i + 2 + patterns.length)
      Eq env2.v extended →
    ∃ value, FlatSem.evaluate env2 state [item.2.2] = (state, .val [value]) := by
  let entries := patternEntries trace i 0 patterns
  let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
  let selected := entries.filter (fun e => (sptLookup e.2.2.1 compiled.1).isSome)
  let extended := selected.reverse.map (fun e => (e.1.2, (fields[e.1.1]?).getD FlatSem.unitValue)) ++ env.v
  change item ∈ entries.map Prod.snd → (sptLookup item.2.1 compiled.1).isSome = true →
    aLookupRel (fun name => i < decNameToNum name ∧ decNameToNum name < i + 2 + patterns.length)
      Eq env2.v extended → _
  intro member used related
  obtain ⟨entry, inEntries, rfl⟩ := List.mem_map.mp member
  have inSelected : entry ∈ selected := List.mem_filter.mpr ⟨inEntries, used⟩
  have expression := (patternEntries_work_expression trace i 0 patterns entry inEntries).2
  refine ⟨(fields[entry.1.1]?).getD FlatSem.unitValue, ?_⟩
  rw [expression]
  exact compilePatBindings_con_selected_pure trace i patterns body rest env env2 state fields entry inSelected related

/-- Generated constructor work items and actual fields satisfy the pointwise
pure-evaluation premise needed by the recursive binding simulation. -/
theorem compilePatBindings_con_workitems_related {C F : Type} (trace : BackendCommon.Tra) (i : Nat)
    (patterns : List FlatLang.Pat) (body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (fields : List FlatSem.Value)
    (lengths : patterns.length = fields.length) :
    let entries := patternEntries trace i 0 patterns
    let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
    let selected := entries.filter (fun e => (sptLookup e.2.2.1 compiled.1).isSome)
    let extended := selected.reverse.map (fun e => (e.1.2, (fields[e.1.1]?).getD FlatSem.unitValue)) ++ env.v
    List.Forall₂ (fun item value => (sptLookup item.2.1 compiled.1).isSome = true →
      ∀ env2, aLookupRel (fun name => i < decNameToNum name ∧ decNameToNum name < i + 2 + patterns.length)
        Eq env2.v extended → FlatSem.evaluate env2 state [item.2.2] = (state, .val [value]))
      (entries.map Prod.snd) fields := by
  let entries := patternEntries trace i 0 patterns
  let compiled := compilePatBindings trace (i + 2 + patterns.length) (entries.map Prod.snd ++ rest) body
  let selected := entries.filter (fun e => (sptLookup e.2.2.1 compiled.1).isSome)
  let extended := selected.reverse.map (fun e => (e.1.2, (fields[e.1.1]?).getD FlatSem.unitValue)) ++ env.v
  change List.Forall₂ (fun item value => (sptLookup item.2.1 compiled.1).isSome = true →
      ∀ env2, aLookupRel (fun name => i < decNameToNum name ∧ decNameToNum name < i + 2 + patterns.length)
        Eq env2.v extended → FlatSem.evaluate env2 state [item.2.2] = (state, .val [value]))
      (entries.map Prod.snd) fields
  apply forall₂_of_getElem
  · simpa [entries, patternEntries_length] using lengths
  · intro k item value itemAt valueAt used env2 related
    cases entryAt : entries[k]? with
    | none => simp [List.getElem?_map, entryAt] at itemAt
    | some entry =>
      have itemEq : entry.2 = item := by simpa [List.getElem?_map, entryAt] using itemAt
      subst item
      have inEntries : entry ∈ entries := List.mem_of_getElem? entryAt
      have inSelected : entry ∈ selected := List.mem_filter.mpr ⟨inEntries, used⟩
      have index := patternEntries_index trace i 0 k patterns entry entryAt
      have expr := (patternEntries_work_expression trace i 0 patterns entry inEntries).2
      have h := compilePatBindings_con_selected_pure trace i patterns body rest env env2 state fields entry inSelected related
      rw [expr]
      simpa [index, valueAt] using h

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
