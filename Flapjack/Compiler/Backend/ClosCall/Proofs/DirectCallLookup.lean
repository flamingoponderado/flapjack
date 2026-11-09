module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateAppExpression

@[expose] public section

/-! Generated-code lookup for known direct calls. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps ClosSem

/-- A member of an association list with distinct keys is returned by
the HOL-shaped lookup. -/
theorem logicalAssocLookup_of_mem {V : Type} (entries : List (Nat × V)) (key : Nat) (value : V)
    (distinct : (entries.map Prod.fst).Nodup) (member : (key, value) ∈ entries) :
    logicalAssocLookup key entries = some value := by
  induction entries with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨other, otherValue⟩ := first
    simp only [List.map_cons, List.nodup_cons] at distinct
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · cases equal
      exact (logicalAssocLookup_cons key key value rest).1 rfl
    · have different : key ≠ other := by
        intro equal
        subst key
        apply distinct.1
        exact List.mem_map.mpr ⟨(other, value), member, rfl⟩
      rw [(logicalAssocLookup_cons key other otherValue rest).2 different]
      exact ih distinct.2 member

/-- Every function body in a generated code list is installed at its odd
offset from the group's base location. -/
theorem codeListSource_mem {A B C : Type} (loc : Nat) (fns : List (A × B))
    (state : C × List (Nat × A × B)) (index : Nat) (arity : A) (body : B)
    (lookup : fns[index]? = some (arity, body)) :
    (loc + 2 * index + 1, (arity, body)) ∈ (codeListSource loc fns state).2 := by
  induction fns generalizing loc state index with
  | nil => simp at lookup
  | cons fn rest ih =>
    obtain ⟨headArity, headBody⟩ := fn
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at lookup
      obtain ⟨rfl, rfl⟩ := lookup
      have suffix := codeListSource_suffix (loc + 2) rest
        (state.1, (loc + 1, headArity, headBody) :: state.2)
      have member : (loc + 1, (headArity, headBody)) ∈
          (state.1, (loc + 1, headArity, headBody) :: state.2).2 := by simp
      have result := suffix.sublist.subset member
      simpa [codeListSource] using result
    | succ index =>
      simp only [List.getElem?_cons_succ] at lookup
      have result := ih (loc + 2) (state.1, (loc + 1, headArity, headBody) :: state.2)
        index lookup
      simpa [codeListSource, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- The executable code-list generator installs the selected function body. -/
theorem codeList_mem (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (state : State)
    (index arity : Nat) (body : ClosLang.Exp) (lookup : fns[index]? = some (arity, body)) :
    (loc + 2 * index + 1, (arity, body)) ∈ (codeList loc fns state).2 := by
  rw [codeList_eq_source]
  exact codeListSource_mem loc fns state index arity body lookup

/-- The generated entries form a prefix, in reverse generation order, ahead of
all previously installed code. -/
theorem codeList_entries (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (state : State) :
    (codeList loc fns state).2 =
      ((fns.zip (List.range fns.length)).map
        (fun ((arity, body), i) => (loc + 2 * i + 1, (arity, body)))).reverse ++ state.2 := by
  have foldEntries : ∀ (pairs : List ((Nat × ClosLang.Exp) × Nat)) (acc : List (Nat × Nat × ClosLang.Exp)),
      pairs.foldl (fun code ((arity, body), i) => (loc + 2 * i + 1, arity, body) :: code) acc =
        (pairs.map (fun ((arity, body), i) => (loc + 2 * i + 1, (arity, body)))).reverse ++ acc := by
    intro pairs
    induction pairs with
    | nil => intro acc; rfl
    | cons pair rest ih =>
      obtain ⟨⟨arity, body⟩, i⟩ := pair
      intro acc
      simp only [List.foldl_cons, ih, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
  exact foldEntries _ _

/-- A successful lookup in a prefix is unaffected by entries appended after it. -/
theorem logicalAssocLookup_append_hit {V : Type} (front back : List (Nat × V)) (key : Nat) (value : V)
    (lookup : logicalAssocLookup key front = some value) :
    logicalAssocLookup key (front ++ back) = some value := by
  induction front with
  | nil => simp [logicalAssocLookup_nil] at lookup
  | cons first rest ih =>
    obtain ⟨other, otherValue⟩ := first
    by_cases same : key = other
    · subst other
      rw [(logicalAssocLookup_cons key key otherValue rest).1 rfl] at lookup
      cases lookup
      exact (logicalAssocLookup_cons key key value (rest ++ back)).1 rfl
    · rw [(logicalAssocLookup_cons key other otherValue rest).2 same] at lookup
      simpa only [List.cons_append, (logicalAssocLookup_cons key other otherValue (rest ++ back)).2 same] using ih lookup

/-- The generated prefix has distinct labels, even if older code does not. -/
theorem codeList_generated_nodup (loc : Nat) (fns : List (Nat × ClosLang.Exp)) :
    (((fns.zip (List.range fns.length)).map
      (fun ((arity, body), i) => (loc + 2 * i + 1, (arity, body)))).reverse.map Prod.fst).Nodup := by
  have labels := codeList_labels loc fns ((.ln, []) : State)
  rw [codeList_entries] at labels
  simp only [List.map_nil, List.append_nil] at labels
  have generated := codeList_newLabels_nodup loc fns.length
  rw [← labels] at generated
  exact generated

/-- Looking up a generated label returns the body at that group index,
regardless of any shadowed entry in older code. -/
theorem codeList_lookup (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (state : State)
    (index arity : Nat) (body : ClosLang.Exp) (lookup : fns[index]? = some (arity, body)) :
    logicalAssocLookup (loc + 2 * index + 1) (codeList loc fns state).2 = some (arity, body) := by
  let front := ((fns.zip (List.range fns.length)).map
    (fun ((n, e), i) => (loc + 2 * i + 1, (n, e)))).reverse
  have member : (loc + 2 * index + 1, (arity, body)) ∈ front := by
    have h := codeList_mem loc fns ((.ln, []) : State) index arity body lookup
    simpa [codeList_entries, front] using h
  have found : logicalAssocLookup (loc + 2 * index + 1) front = some (arity, body) :=
    logicalAssocLookup_of_mem front _ _ (codeList_generated_nodup loc fns) member
  rw [codeList_entries]
  exact logicalAssocLookup_append_hit front state.2 _ _ found

private theorem zip_lookup {A B : Type} (xs : List A) (ys : List B) (i : Nat) (x : A) (y : B)
    (left : xs[i]? = some x) (right : ys[i]? = some y) : (xs.zip ys)[i]? = some (x, y) := by
  induction i generalizing xs ys with
  | zero =>
    cases xs <;> cases ys <;> simp_all
  | succ i ih =>
    cases xs <;> cases ys <;> simp_all

/-- A selected body of a closed group uses only its declared arguments.
This is Flapjack-specific infrastructure for the direct-call simulation. -/
theorem groupClosed_selected (fns : List (Nat × ClosLang.Exp)) (bodies : List ClosLang.Exp)
    (index arity : Nat) (sourceBody convertedBody : ClosLang.Exp)
    (closed : groupClosed fns bodies)
    (sourceLookup : fns[index]? = some (arity, sourceBody))
    (bodyLookup : bodies[index]? = some convertedBody) :
    ∀ n, ClosProps.freeVarExp n convertedBody → n < arity := by
  induction index generalizing fns bodies with
  | zero =>
    cases fns with
    | nil => simp at sourceLookup
    | cons fn fns =>
      cases bodies with
      | nil => simp at bodyLookup
      | cons body bodies =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceLookup bodyLookup
        subst fn
        subst body
        cases closed with
        | cons head tail => exact head
  | succ index ih =>
    cases fns with
    | nil => simp at sourceLookup
    | cons fn fns =>
      cases bodies with
      | nil => simp at bodyLookup
      | cons body bodies =>
        simp only [List.getElem?_cons_succ] at sourceLookup bodyLookup
        cases closed with
        | cons head tail => exact ih fns bodies tail sourceLookup bodyLookup

/-- A generated stub keeps the source arity and calls its corresponding
odd-offset code label. -/
theorem callsListSource_lookup (trace : BackendCommon.Tra) (stubIndex loc : Nat)
    (fns : List (Nat × ClosLang.Exp)) (index arity : Nat) (body : ClosLang.Exp)
    (lookup : fns[index]? = some (arity, body)) :
    (callsListSource trace stubIndex loc fns)[index]? =
      some (arity, .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity)) := by
  have bound : index < fns.length := (List.getElem?_eq_some_iff.mp lookup).choose
  have rangeLookup : (List.range fns.length)[index]? = some index := by
    simp [bound]
  have pairLookup := zip_lookup fns (List.range fns.length) index (arity, body) index lookup rangeLookup
  rw [callsListSource_eq_range]
  simp [List.getElem?_map, pairLookup]

/-- A related closure at a location excluded from the open set must use the
extracted branch, and the target code map contains its converted body. -/
theorem recClosureRelFuel_known_lookup (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat) (sourceBody : ClosLang.Exp)
    (related : recClosureRelFuel fuel g allowed code loc sourceFns targetFns)
    (sourceLookup : sourceFns[index]? = some (arity, sourceBody))
    (notAllowed : 2 * index + loc ∉ allowed) :
    ∃ trace stubIndex convertedBody initial bodies afterProbe,
      targetFns = callsListSource trace stubIndex loc sourceFns ∧
      code.lookup (loc + 2 * index + 1) = some (arity, convertedBody) ∧
      callsListBounded fuel (sourceFns.map Prod.snd) (insertEach loc sourceFns.length initial) =
        some (bodies, afterProbe) ∧ bodies[index]? = some convertedBody := by
  have indexBound : index < sourceFns.length := (List.getElem?_eq_some_iff.mp sourceLookup).choose
  obtain ⟨initial, _, _, _, _, bodies, afterProbe, probe, alternatives⟩ := related
  rcases alternatives with ⟨_, ⟨trace, stubIndex, target⟩, growth, _, included⟩ |
      ⟨_, _, _, _, _, _, _, ownAllowed, _⟩
  · have bodyLength := callsListBounded_length fuel (sourceFns.map Prod.snd)
      (insertEach loc sourceFns.length initial) afterProbe bodies probe
    have bodyLength' : bodies.length = sourceFns.length := by simpa using bodyLength
    have bodyBound : index < bodies.length := by omega
    let convertedBody := bodies[index]
    have arityLookup : (sourceFns.map Prod.fst)[index]? = some arity := by
      simp [List.getElem?_map, sourceLookup]
    have bodyLookup : bodies[index]? = some convertedBody := List.getElem?_eq_getElem bodyBound
    have pairLookup := zip_lookup (sourceFns.map Prod.fst) bodies index arity convertedBody arityLookup bodyLookup
    have generated := codeList_lookup loc ((sourceFns.map Prod.fst).zip bodies) afterProbe index arity convertedBody pairLookup
    exact ⟨trace, stubIndex, convertedBody, initial, bodies, afterProbe, target, included _ _ generated, probe, bodyLookup⟩
  · exact False.elim (notAllowed (ownAllowed index indexBound))

/-- At a known non-open location, the installed body and stub come from the
same bounded probe traversal. The selected intermediate state is known to have
distinct emitted labels; exact well-formedness is not asserted because the
probe reserves locations before emitting their code. This is Flapjack-specific
infrastructure, not a HOL theorem port. -/
theorem recClosureRelFuel_known_probe_body (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat) (sourceBody : ClosLang.Exp)
    (related : recClosureRelFuel fuel g allowed code loc sourceFns targetFns)
    (sourceLookup : sourceFns[index]? = some (arity, sourceBody))
    (notAllowed : 2 * index + loc ∉ allowed) :
    ∃ trace convertedBody depth before after afterProbe bodies,
      targetFns[index]? = some (arity, .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity)) ∧
      code.lookup (loc + 2 * index + 1) = some (arity, convertedBody) ∧
      depth < max fuel (listBudget (sourceFns.map Prod.snd) + 1) ∧
      callsFuel depth sourceBody before = some (convertedBody, after) ∧
      (codeLocationsExp sourceBody).Nodup ∧ LabelsFresh (codeLocationsExp sourceBody) before ∧
      (before.2.map Prod.fst).Nodup ∧ weaklyWellFormed before ∧
      (∀ k ∈ codeLocationsExp sourceBody, sptDomain before.1 k → k + 1 ∈ before.2.map Prod.fst) ∧
      stateExtends before afterProbe ∧ stateExtends before g ∧
      stateExtends after afterProbe ∧ stateExtends after g ∧
      bodies[index]? = some convertedBody ∧ (∀ n, ClosProps.freeVarExp n convertedBody → n < arity) ∧
      stateExtends (codeList loc ((sourceFns.map Prod.fst).zip bodies) afterProbe) g := by
  have indexBound : index < sourceFns.length := (List.getElem?_eq_some_iff.mp sourceLookup).choose
  obtain ⟨_, bodies, afterProbe, convertedBody, depth, before, after, _, _, _, selectedBody,
    depthBound, selectedRun, distinct, fresh, beforeDistinct, beforeWeak, knownCovered, beforeExt, extended, alternatives⟩ :=
    recClosureRelFuel_probe_body fuel g allowed code loc sourceFns targetFns index arity sourceBody related sourceLookup
  rcases alternatives with ⟨closed, ⟨trace, stubIndex, targetEq⟩, probeExt, codeExt, _, included⟩ |
      ⟨_, _, _, _, _, _, _, ownAllowed, _⟩
  · have stub := callsListSource_lookup trace stubIndex loc sourceFns index arity sourceBody sourceLookup
    have targetStub : targetFns[index]? =
        some (arity, .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity)) := by
      simpa [targetEq] using stub
    have arityLookup : (sourceFns.map Prod.fst)[index]? = some arity := by
      simp [List.getElem?_map, sourceLookup]
    have pairLookup := zip_lookup (sourceFns.map Prod.fst) bodies index arity convertedBody arityLookup selectedBody
    have generated := codeList_lookup loc ((sourceFns.map Prod.fst).zip bodies) afterProbe index arity convertedBody pairLookup
    exact ⟨trace, convertedBody, depth, before, after, afterProbe, bodies, targetStub,
      included _ _ generated, depthBound, selectedRun, distinct, fresh, beforeDistinct,
      beforeWeak, knownCovered, beforeExt, stateExtends_trans _ _ _ beforeExt probeExt, extended,
      stateExtends_trans _ _ _ extended probeExt, selectedBody, groupClosed_selected sourceFns bodies index arity sourceBody convertedBody
        closed sourceLookup selectedBody, codeExt⟩
  · exact (notAllowed (ownAllowed index indexBound)).elim

/-- A selected related body either executes an extracted probe body through a
generated stub, or is the result of the open-group traversal. Both cases use
the same source group and selected index. This is Flapjack-specific proof
infrastructure for closure-body induction. -/
theorem recClosureRelFuel_body_traversal_cases (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat)
    (sourceBody targetBody : ClosLang.Exp)
    (related : recClosureRelFuel fuel g allowed code loc sourceFns targetFns)
    (sourceLookup : sourceFns[index]? = some (arity, sourceBody))
    (targetLookup : targetFns[index]? = some (arity, targetBody)) :
    (∃ trace convertedBody depth before after afterProbe bodies,
      targetBody = .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity) ∧
      code.lookup (loc + 2 * index + 1) = some (arity, convertedBody) ∧
      depth < max fuel (listBudget (sourceFns.map Prod.snd) + 1) ∧
      callsFuel depth sourceBody before = some (convertedBody, after) ∧
      (codeLocationsExp sourceBody).Nodup ∧ LabelsFresh (codeLocationsExp sourceBody) before ∧
      (before.2.map Prod.fst).Nodup ∧ weaklyWellFormed before ∧
      (∀ k ∈ codeLocationsExp sourceBody, sptDomain before.1 k → k + 1 ∈ before.2.map Prod.fst) ∧
      stateExtends before afterProbe ∧ stateExtends before g ∧
      stateExtends after afterProbe ∧ stateExtends after g ∧
      bodies[index]? = some convertedBody ∧ (∀ n, ClosProps.freeVarExp n convertedBody → n < arity) ∧
      stateExtends (codeList loc ((sourceFns.map Prod.fst).zip bodies) afterProbe) g) ∨
    (∃ depth before after, depth < max fuel (listBudget (sourceFns.map Prod.snd) + 1) ∧
      callsFuel depth sourceBody before = some (targetBody, after) ∧
      (codeLocationsExp sourceBody).Nodup ∧ LabelsFresh (codeLocationsExp sourceBody) before ∧
      wellFormed before ∧ stateExtends after g) := by
  obtain ⟨initial, bodies, afterProbe, convertedBody, depth, before, after, initialWf, initialFresh, _, selectedBody,
    depthBound, selectedRun, distinct, fresh, beforeDistinct, beforeWeak, knownCovered, beforeExt, extended, alternatives⟩ :=
    recClosureRelFuel_probe_body fuel g allowed code loc sourceFns targetFns index arity sourceBody related sourceLookup
  rcases alternatives with ⟨closed, ⟨trace, stubIndex, targetEq⟩, probeExt, codeExt, _, included⟩ |
      ⟨_, openBodies, afterOpen, openRun, targetEq, openExt, _, _, _⟩
  · left
    have stub := callsListSource_lookup trace stubIndex loc sourceFns index arity sourceBody sourceLookup
    have targetStub : targetFns[index]? =
        some (arity, .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity)) := by
      simpa [targetEq] using stub
    have bodyEq : targetBody = .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity) := by
      rw [targetLookup] at targetStub
      exact (Prod.mk.inj (Option.some.inj targetStub)).2
    have arityLookup : (sourceFns.map Prod.fst)[index]? = some arity := by
      simp [List.getElem?_map, sourceLookup]
    have pairLookup := zip_lookup (sourceFns.map Prod.fst) bodies index arity convertedBody arityLookup selectedBody
    have generated := codeList_lookup loc ((sourceFns.map Prod.fst).zip bodies) afterProbe index arity convertedBody pairLookup
    exact ⟨trace, convertedBody, depth, before, after, afterProbe, bodies, bodyEq, included _ _ generated,
      depthBound, selectedRun, distinct, fresh, beforeDistinct, beforeWeak, knownCovered, beforeExt,
      stateExtends_trans _ _ _ beforeExt probeExt, extended, stateExtends_trans _ _ _ extended probeExt, selectedBody,
      groupClosed_selected sourceFns bodies index arity sourceBody convertedBody closed sourceLookup selectedBody, codeExt⟩
  · right
    have sourceDistinct : (codeLocations (sourceFns.map Prod.snd)).Nodup := by
      obtain ⟨_, well, _, _, _, _, _, _, _⟩ := related
      exact well.2.2.2
    have zippedLookup : ((sourceFns.map Prod.fst).zip openBodies)[index]? = some (arity, targetBody) := by
      simpa [targetEq] using targetLookup
    obtain ⟨openDepth, openBefore, openAfter, openDepthBound, openSelected, openDistinct,
      openFresh, openWf, openExtended⟩ :=
      callsListBounded_open_body fuel sourceFns openBodies initial afterOpen openRun sourceDistinct initialFresh
        initialWf index arity sourceBody targetBody sourceLookup zippedLookup
    exact ⟨openDepth, openBefore, openAfter, openDepthBound, openSelected, openDistinct, openFresh, openWf,
      stateExtends_trans _ _ _ openExtended openExt⟩

/-- At a known non-open location, the selected target closure is a direct
call to the converted body present in the target code map. -/
theorem recClosureRelFuel_known_stub (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat) (sourceBody : ClosLang.Exp)
    (related : recClosureRelFuel fuel g allowed code loc sourceFns targetFns)
    (sourceLookup : sourceFns[index]? = some (arity, sourceBody))
    (notAllowed : 2 * index + loc ∉ allowed) :
    ∃ trace convertedBody,
      targetFns[index]? = some (arity, .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity)) ∧
      code.lookup (loc + 2 * index + 1) = some (arity, convertedBody) := by
  obtain ⟨trace, stubIndex, convertedBody, _, _, _, target, codeLookup, _, _⟩ :=
    recClosureRelFuel_known_lookup fuel g allowed code loc sourceFns targetFns index arity sourceBody
      related sourceLookup notAllowed
  refine ⟨trace, convertedBody, ?_, codeLookup⟩
  rw [target]
  exact callsListSource_lookup trace stubIndex loc sourceFns index arity sourceBody sourceLookup

/-- The generated direct call resolves to the converted body when supplied
with the selected function's declared number of arguments. -/
theorem recClosureRelFuel_known_findCode (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat) (sourceBody : ClosLang.Exp)
    (args : List ClosSem.Value) (argsLength : args.length = arity)
    (related : recClosureRelFuel fuel g allowed code loc sourceFns targetFns)
    (sourceLookup : sourceFns[index]? = some (arity, sourceBody))
    (notAllowed : 2 * index + loc ∉ allowed) :
    ∃ trace convertedBody,
      targetFns[index]? = some (arity, .call trace 0 (loc + 2 * index + 1) (ClosCall.variables trace arity)) ∧
      findCode (loc + 2 * index + 1) args code = some (args, convertedBody) := by
  obtain ⟨trace, convertedBody, stub, codeLookup⟩ :=
    recClosureRelFuel_known_stub fuel g allowed code loc sourceFns targetFns index arity sourceBody
      related sourceLookup notAllowed
  exact ⟨trace, convertedBody, stub, by simp [findCode, codeLookup, argsLength]⟩

/-- A known-location full application selects a direct-call stub whose code
is present at the requested label. Exact arity leaves no extra arguments. -/
theorem destClosure_known_direct (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (maxApp address : Nat)
    (source target : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (sourceBody : ClosLang.Exp) (sourceBodyEnv sourceRest : List ClosSem.Value)
    (sourceRun : destClosure maxApp (some address) source sourceArgs = some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (values : ValueRelFuel fuel g allowed code source target)
    (args : List.Forall₂ (ValueRelFuel fuel g allowed code) sourceArgs targetArgs)
    (notAllowed : address ∉ allowed) :
    ∃ (trace : BackendCommon.Tra) (targetBodyEnv : List ClosSem.Value) (convertedBody : ClosLang.Exp)
      (base index : Nat) (sourceFns : List (Nat × ClosLang.Exp)) (initial afterProbe : State)
      (bodies : List ClosLang.Exp),
      destClosure maxApp (some address) target targetArgs =
        some (.fullApp (.call trace 0 (address + 1) (ClosCall.variables trace sourceArgs.length)) targetBodyEnv []) ∧
      EnvRelFuel fuel g allowed code sourceBodyEnv targetBodyEnv 0
        [(0, .call trace 0 (address + 1) (ClosCall.variables trace sourceArgs.length))] ∧
      findCode (address + 1) targetArgs code = some (targetArgs, convertedBody) ∧ sourceRest = [] ∧
      address = 2 * index + base ∧ sourceFns[index]? = some (sourceArgs.length, sourceBody) ∧
      callsListBounded fuel (sourceFns.map Prod.snd) (insertEach base sourceFns.length initial) =
        some (bodies, afterProbe) ∧ bodies[index]? = some convertedBody := by
  obtain ⟨targetBody, targetBodyEnv, targetRest, base, sourceFns, targetFns, index, arity,
      targetRun, envs, restRel, closure, sourceLookup, targetLookup, known, _⟩ :=
    destClosure_full_fuel fuel g allowed code maxApp (some address) source target sourceArgs targetArgs
      sourceBody sourceBodyEnv sourceRest sourceRun values args
  obtain ⟨addressEq, arityEq, sourceRestEq⟩ := known address rfl
  have targetRestEq : targetRest = [] := by
    have length := restRel.length_eq
    rw [sourceRestEq] at length
    cases targetRest with
    | nil => rfl
    | cons head tail => simp at length
  have notOpen : 2 * index + base ∉ allowed := by simpa [← addressEq] using notAllowed
  have targetArity : targetArgs.length = arity := args.length_eq.symm.trans arityEq.symm
  obtain ⟨trace, stubIndex, convertedBody, initial, bodies, afterProbe, targetFnsEq, codeLookup, traversal, bodyLookup⟩ :=
    recClosureRelFuel_known_lookup fuel g allowed code base sourceFns targetFns index arity sourceBody
      closure sourceLookup notOpen
  have stub : targetFns[index]? =
      some (arity, .call trace 0 (base + 2 * index + 1) (ClosCall.variables trace arity)) := by
    rw [targetFnsEq]
    exact callsListSource_lookup trace stubIndex base sourceFns index arity sourceBody sourceLookup
  have found : findCode (base + 2 * index + 1) targetArgs code = some (targetArgs, convertedBody) := by
    simp [findCode, codeLookup, targetArity]
  rw [targetLookup] at stub
  have bodyEq : targetBody = .call trace 0 (base + 2 * index + 1) (ClosCall.variables trace arity) := by
    simpa using stub
  have labelEq : base + 2 * index + 1 = address + 1 := by omega
  subst targetBody
  subst targetRest
  refine ⟨trace, targetBodyEnv, convertedBody, base, index, sourceFns, initial, afterProbe, bodies,
    ?_, ?_, ?_, sourceRestEq, addressEq, ?_, traversal, bodyLookup⟩
  · simpa [labelEq, arityEq] using targetRun
  · simpa [labelEq, arityEq] using envs
  · simpa [labelEq] using found
  · simpa [arityEq] using sourceLookup

end Flapjack.Compiler.Backend.ClosCall
