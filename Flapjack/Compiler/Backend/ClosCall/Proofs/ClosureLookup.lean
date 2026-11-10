module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeLookup
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StubInvariants
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Direct-call closure lookup simulation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosLang

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical finite-map codec for the lookup simulation code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_destClosure_valueRel_lookup_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- A known, non-exempt direct call finds the original and compiled bodies
and constructs the target closure application and code lookup. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "dest_closure_v_rel_lookup"
  (fmap_as_finite_support_parameters := [code])]
theorem destClosure_valueRel_lookup {A : Type} [Nonempty A] (maxApp loc : Nat) (v1 : Value)
    (env1 : List Value) (x : AppKind) (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (v2 : Value) (env2 : List Value)
    (h : destClosure maxApp (some loc) v1 env1 = some x ∧
      valueRel g allowed code v1 v2 ∧ List.Forall₂ (valueRel g allowed code) env1 env2 ∧
      wellFormed g ∧ sptDomain g.1 loc ∧ ¬ allowed loc) :
    ∃ (e : ClosLang.Exp) (l1 : List Value) (xs : List (Nat × ClosLang.Exp))
      (n : Nat) (ls : List ClosLang.Exp) (g01 g1 : State) (l1' : List Value)
      (tra : BackendCommon.Tra) (_i : A),
      x = .fullApp e (env1 ++ l1) [] ∧
      holEl n xs = (env1.length, e) ∧
      calls (xs.map Prod.snd) g01 = (ls, g1) ∧ n < ls.length ∧
      stateExtends (codeListSource (loc - 2 * n) ((xs.map Prod.fst).zip ls) g1) g ∧
      holALookup g.2 (loc + 1) = some (env1.length, holEl n ls) ∧
      destClosure maxApp (some loc) v2 env2 =
        some (.fullApp (.call tra 0 (loc + 1) (variablesSource tra 1 env1.length)) (env2 ++ l1') []) ∧
      codeIncludes (codeListSource (loc - 2 * n) ((xs.map Prod.fst).zip ls) g1).2 code := by
  obtain ⟨run, related, envs, well, known, notAllowed⟩ := h
  cases v1 with
  | closure loco supplied env n body =>
    simp only [destClosure] at run
    split at run <;> try contradiction
    rename_i guard
    simp [checkLoc] at guard
    obtain ⟨⟨rfl, rfl, rfl⟩, positive⟩ := guard
    simp at run
    obtain ⟨targetLoc, targetValues, targetEnv, targetBody, group, rfl, locEq, valuesRel, envRel'⟩ :=
      (valueRel_sourceEquations g allowed code).2.1 _ _ _ _ _ _ |>.mp related
    simp only [Option.some.injEq] at locEq
    subst targetLoc
    cases valuesRel
    subst x
    unfold recClosureRel at group
    obtain ⟨g0, groupWell, stateWell, fresh, freshGroup, branch⟩ := group
    dsimp only at branch
    split at branch
    · obtain ⟨⟨tra, stubIndex, stubEq⟩, extension, locationBound, includes⟩ := branch
      simp [callsListSource] at stubEq
      subst targetBody
      cases singleRun : calls [body] (insertEachSource loc 1 g0) with
      | mk output final =>
        obtain ⟨converted, rfl⟩ := calls_sing body _ output final singleRun
        simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at extension includes
        change callsSingList [body] (insertEachSource loc 1 g0) = _ at singleRun
        rw [singleRun] at extension includes
        simp only [List.zip_cons_cons] at extension includes
        cases final with
        | mk tree entries =>
          simp only [codeListSource] at extension includes
          have lookup : holALookup g.2 (loc + 1) = some (env1.length, converted) :=
            extension.2.1 _ _ (by simp [codeListSource, holALookup])
          have len := envs.length_eq
          have sourceTake : (env1.reverse.take env1.length).reverse = env1 := by
            rw [List.take_of_length_le (by simp)]
            simp
          have targetTake : (env2.reverse.take env1.length).reverse = env2 := by
            rw [List.take_of_length_le (by simp [← len])]
            simp
          refine ⟨body, env, [(env1.length, body)], 0, [converted],
            insertEachSource loc 1 g0, (tree, entries), targetEnv, tra,
            Classical.choice inferInstance, ?_, ?_, ?_, by simp, ?_, ?_, ?_, ?_⟩
          · simp [sourceTake]
          · simp [holEl, holHd]
          · simpa [calls] using singleRun
          · simpa [codeListSource] using extension
          · simpa [holEl, holHd] using lookup
          · simpa [destClosure, checkLoc, ← len, positive, targetTake] using positive
          · simpa [codeListSource] using includes
    · have inAllowed := branch.2.2.2.1
      have hit : loc ∈ ({n | n ∈ (List.range ([(env1.length, body)] : List (Nat × ClosLang.Exp)).length).map
          (fun i => 2 * i + loc)} : Set Nat) := by simp
      exact False.elim (notAllowed (inAllowed hit))
  | recclosure loco supplied env fns index =>
    simp only [destClosure] at run
    split at run <;> try contradiction
    rename_i n body entry
    split at run <;> try contradiction
    rename_i guard
    simp [checkLoc] at guard
    obtain ⟨⟨rfl, rfl, requested⟩, positive⟩ := guard
    simp at run
    obtain ⟨targetLoc, targetValues, targetEnv, targetFns, group, rfl, locEq, valuesRel, envRel'⟩ :=
      (valueRel_sourceEquations g allowed code).2.2 _ _ _ _ _ _ |>.mp related
    subst loco
    cases valuesRel
    simp only [Option.some.injEq] at requested
    obtain ⟨_, rfl, rfl⟩ := requested
    obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp entry
    subst x
    unfold recClosureRel at group
    obtain ⟨g0, groupWell, stateWell, fresh, freshGroup, branch⟩ := group
    dsimp only at branch
    split at branch
    · obtain ⟨⟨tra, stubIndex, rfl⟩, extension, locationBound, includes⟩ := branch
      cases conversion : calls (fns.map Prod.snd) (insertEachSource targetLoc fns.length g0) with
      | mk output final =>
        have outLen := calls_length (fns.map Prod.snd) _ output final conversion
        simp only [List.length_map] at outLen
        have outBound : index < output.length := by omega
        change callsSingList (fns.map Prod.snd) (insertEachSource targetLoc fns.length g0) = _ at conversion
        rw [conversion] at extension includes
        have stubEntry : (callsListSource tra stubIndex targetLoc fns)[index]? =
            some (env1.length, .call tra 0 (targetLoc + 2 * index + 1) (variablesSource tra 1 env1.length)) := by
          have eq := congrFun (callsListSource_mapIdx (B := ClosLang.Exp) tra targetLoc () stubIndex) fns
          rw [eq]
          have mapBound : index < (fns.mapIdx (fun i p =>
              (p.1, ClosLang.Exp.call tra 0 (targetLoc + 2 * i + 1) (variablesSource tra 1 p.1)))).length := by simpa using bound
          rw [List.getElem?_eq_getElem mapBound]
          simp only [List.getElem_mapIdx, selected]
        let zipped := (fns.map Prod.fst).zip output
        have zipLen : zipped.length = fns.length := by simp [zipped, List.length_zip, outLen]
        have zipBound : index < zipped.length := by omega
        have choice : holOptionSome (fun i => i < zipped.length ∧
            2 * index + targetLoc + 1 = targetLoc + 2 * i + 1) = some index := by
          apply (holOptionSome_eq_some_iff _ (by intro x y hx hy; omega) index).2
          exact ⟨zipBound, by omega⟩
        have zipEl : holEl index zipped = (env1.length, holEl index output) := by
          rw [holEl_eq_getElem index zipped zipBound, holEl_eq_getElem index output outBound]
          simp only [zipped, List.getElem_zip, List.getElem_map, selected]
        have auxLookup : holALookup (codeListSource targetLoc zipped final).2
            (2 * index + targetLoc + 1) = some (env1.length, holEl index output) := by
          rw [codeListSource_alookup, choice]
          simp [zipEl]
        have lookup : holALookup g.2 (2 * index + targetLoc + 1) =
            some (env1.length, holEl index output) := extension.2.1 _ _ auxLookup
        have len := envs.length_eq
        have sourceTake : (env1.reverse.take env1.length).reverse = env1 := by
          rw [List.take_of_length_le (by simp)]
          simp
        have targetTake : (env2.reverse.take env1.length).reverse = env2 := by
          rw [List.take_of_length_le (by simp [← len])]
          simp
        refine ⟨body, (List.range fns.length).map (fun i => Value.recclosure (some targetLoc) [] env fns i) ++ env,
          fns, index, output, insertEachSource targetLoc fns.length g0, final,
          (List.range (callsListSource tra stubIndex targetLoc fns).length).map
            (fun i => Value.recclosure (some targetLoc) [] targetEnv (callsListSource tra stubIndex targetLoc fns) i) ++ targetEnv,
          tra, Classical.choice inferInstance, ?_, ?_, ?_, outBound, ?_, lookup, ?_, ?_⟩
        · simp [sourceTake]
        · rw [holEl_eq_getElem index fns bound, selected]
        · exact conversion
        · simpa [zipped, Nat.add_sub_cancel_left] using extension
        · simpa [destClosure, stubEntry, checkLoc, ← len, positive, targetTake, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc] using positive
        · simpa [zipped, Nat.add_sub_cancel_left] using includes
    · have inAllowed := branch.2.2.2.1
      have hit : 2 * index + targetLoc ∈
          ({n | n ∈ (List.range fns.length).map (fun i => 2 * i + targetLoc)} : Set Nat) := by
        exact List.mem_map.mpr ⟨index, List.mem_range.mpr bound, rfl⟩
      exact False.elim (notAllowed (inAllowed hit))
  | _ => simp [destClosure] at run
/-- HOL derives this pointwise relation for the generated recursive-closure
lists inside the application proof; it has no standalone HOL declaration. -/
private theorem recClosureValues (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (env1 env2 : List Value)
    (related : recClosureRel g allowed code loc fns1 fns2)
    (envs : envRel (valueRel g allowed code) env1 env2 fns2.length fns2) :
    List.Forall₂ (valueRel g allowed code)
      ((List.range fns1.length).map (fun i => Value.recclosure (some loc) [] env1 fns1 i))
      ((List.range fns2.length).map (fun i => Value.recclosure (some loc) [] env2 fns2 i)) := by
  have lengths : fns1.length = fns2.length := by
    have h := congrArg List.length (recClosureRel_arities g allowed code loc fns1 fns2 related)
    simpa using h.symm
  rw [← lengths]
  have one : ∀ i, valueRel g allowed code (.recclosure (some loc) [] env1 fns1 i)
      (.recclosure (some loc) [] env2 fns2 i) := by
    intro i
    apply (valueRel_sourceEquations g allowed code).2.2 _ _ _ _ _ _ |>.mpr
    exact ⟨loc, [], env2, fns2, related, rfl, rfl, .nil, envs⟩
  generalize List.range fns1.length = indices
  induction indices with
  | nil => exact .nil
  | cons i is ih => exact .cons (one i) ih

/-- HOL derives preservation of a selected function's arity inside the
application proof; it has no standalone HOL declaration. -/
private theorem recClosureRel_entry (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (i n : Nat) (e : ClosLang.Exp)
    (related : recClosureRel g allowed code loc fns1 fns2)
    (entry : fns1[i]? = some (n, e)) :
    ∃ e2, fns2[i]? = some (n, e2) := by
  have maps := recClosureRel_arities g allowed code loc fns1 fns2 related
  have ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp entry
  have lengths := congrArg List.length maps
  simp only [List.length_map] at lengths
  have bound2 : i < fns2.length := by omega
  have same := congrArg (fun xs => xs[i]?) maps
  simp only [List.getElem?_map, entry, Option.map_some] at same
  rw [List.getElem?_eq_getElem bound2] at same
  cases found : fns2[i] with
  | mk n2 e2 =>
    simp only [found, Option.map_some, Option.some.injEq] at same
    subst n2
    exact ⟨e2, by simpa [List.getElem?_eq_getElem bound2] using found⟩

/-- Canonical finite-map codec for the closure simulation code parameter. -/
theorem holFmapAsFiniteSupportParamWitness_destClosure_valueRel_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_destClosure_valueRel_lookup_code code key

set_option maxHeartbeats 4000000 in
/-- Related closures and arguments produce related partial or full applications,
including the original prefix, environment and recursive-group obligations. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "dest_closure_v_rel"
  (fmap_as_finite_support_parameters := [code])]
theorem destClosure_valueRel (maxApp : Nat) (loco : Option Nat) (v1 : Value) (env1 : List Value)
    (x1 : AppKind) (g : State) (allowed : Nat → Prop)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (v2 : Value) (env2 : List Value)
    (h : destClosure maxApp loco v1 env1 = some x1 ∧
      valueRel g allowed code v1 v2 ∧ List.Forall₂ (valueRel g allowed code) env1 env2) :
    ∃ x2, destClosure maxApp loco v2 env2 = some x2 ∧
      match x1 with
      | .partialApp c1 => ∃ c2, x2 = .partialApp c2 ∧ valueRel g allowed code c1 c2
      | .fullApp e1 args1 rest1 =>
        ∃ fns1 loc i fns2 args2 rest2 n,
          x2 = .fullApp (holEl i fns2).2 args2 rest2 ∧
          (let m := if isRecClosure v2 then fns2.length else 0
           n + m ≤ args1.length ∧ n + m ≤ args2.length ∧
           List.Forall₂ (valueRel g allowed code) (args1.take (n+m)) (args2.take (n+m)) ∧
           envRel (valueRel g allowed code) (args1.drop (n+m)) (args2.drop (n+m)) m [holEl i fns2]) ∧
          List.Forall₂ (valueRel g allowed code) rest1 rest2 ∧
          recClosureRel g allowed code loc fns1 fns2 ∧
          i < fns1.length ∧ holEl i fns1 = (n,e1) := by
  classical
  obtain ⟨run, related, envs⟩ := h
  cases v1 with
  | closure location supplied captured arity body =>
    obtain ⟨loc, supplied2, captured2, body2, group, rfl, rfl, suppliedRel, capturedRel⟩ :=
      (valueRel_sourceEquations g allowed code).2.1 _ _ _ _ _ _ |>.mp related
    have len := envs.length_eq
    have suppliedLen := suppliedRel.length_eq
    simp only [destClosure] at run
    split at run <;> try contradiction
    rename_i valid
    split at run
    · rename_i partialCase
      simp only [Option.some.injEq] at run
      subst x1
      refine ⟨.partialApp (.closure (some loc) (env2 ++ supplied2) captured2 arity body2), ?_, ?_⟩
      · simp [destClosure, ← len, ← suppliedLen, valid, partialCase]
      · refine ⟨_, rfl, ?_⟩
        apply (valueRel_sourceEquations g allowed code).2.1 _ _ _ _ _ _ |>.mpr
        exact ⟨loc, _, _, _, group, rfl, rfl, List.rel_append envs suppliedRel, capturedRel⟩
    · rename_i fullCase
      simp only [Option.some.injEq] at run
      subst x1
      refine ⟨.fullApp body2 ((env2.reverse.take (arity - supplied2.length)).reverse ++ (supplied2 ++ captured2))
        ((env2.reverse.drop (arity - supplied2.length)).reverse), ?_, ?_⟩
      · simp [destClosure, ← len, ← suppliedLen, valid, fullCase]
      · refine ⟨[(arity, body)], loc, 0, [(arity, body2)], ((env2.reverse.take (arity - supplied2.length)).reverse ++ (supplied2 ++ captured2)), ((env2.reverse.drop (arity - supplied2.length)).reverse), arity, ?_, ?_, ?_, group, ?_, ?_⟩
        · simp [holEl, holHd]
        · simp only [isRecClosure, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, holEl, holHd]
          let p1 := (env1.reverse.take (arity - supplied.length)).reverse
          let p2 := (env2.reverse.take (arity - supplied2.length)).reverse
          have need : arity - supplied.length ≤ env1.length := by omega
          have plen : (p1 ++ supplied).length = arity := by
            simp only [List.length_append, p1, List.length_reverse, List.length_take,
              min_eq_left need]
            have valid2 := valid
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid2
            omega
          have plen2 : (p2 ++ supplied2).length = arity := by
            simp only [List.length_append, p2, List.length_reverse, List.length_take]
            rw [← suppliedLen, ← len, min_eq_left need]
            have valid2 := valid
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid2
            omega
          have preRel : List.Forall₂ (valueRel g allowed code) p1 p2 := by
            simpa [p1, p2, ← suppliedLen] using
              List.rel_reverse (List.forall₂_take (arity - supplied.length) (List.rel_reverse envs))
          have take1 : ((p1 ++ supplied) ++ captured).take arity = p1 ++ supplied := by
            rw [← plen, List.take_append_length]
          have take2 : ((p2 ++ supplied2) ++ captured2).take arity = p2 ++ supplied2 := by
            rw [← plen2, List.take_append_length]
          have drop1 : ((p1 ++ supplied) ++ captured).drop arity = captured := by
            rw [← plen, List.drop_append_length]
          have drop2 : ((p2 ++ supplied2) ++ captured2).drop arity = captured2 := by
            rw [← plen2, List.drop_append_length]
          change arity ≤ (p1 ++ (supplied ++ captured)).length ∧
            arity ≤ (p2 ++ (supplied2 ++ captured2)).length ∧
            List.Forall₂ (valueRel g allowed code) ((p1 ++ (supplied ++ captured)).take arity)
              ((p2 ++ (supplied2 ++ captured2)).take arity) ∧
            envRel (valueRel g allowed code) ((p1 ++ (supplied ++ captured)).drop arity)
              ((p2 ++ (supplied2 ++ captured2)).drop arity) 0 [(arity, body2)]
          simp only [← List.append_assoc]
          rw [take1, take2, drop1, drop2]
          refine ⟨?_, ?_, List.rel_append preRel suppliedRel, capturedRel⟩
          · rw [← plen]; simp
          · rw [← plen2]; simp
        · simpa [← suppliedLen] using
            List.rel_reverse (List.forall₂_drop (arity - supplied.length) (List.rel_reverse envs))
        · simp
        · simp [holEl, holHd]
  | recclosure location supplied captured fns index =>
    obtain ⟨loc, supplied2, captured2, fns2, group, rfl, rfl, suppliedRel, capturedRel⟩ :=
      (valueRel_sourceEquations g allowed code).2.2 _ _ _ _ _ _ |>.mp related
    have len := envs.length_eq
    have suppliedLen := suppliedRel.length_eq
    simp only [destClosure] at run
    split at run <;> try contradiction
    rename_i arity body entry
    obtain ⟨body2, entry2⟩ := recClosureRel_entry g allowed code loc fns fns2 index arity body group entry
    split at run <;> try contradiction
    rename_i valid
    split at run
    · rename_i partialCase
      simp only [Option.some.injEq] at run
      subst x1
      refine ⟨.partialApp (.recclosure (some loc) (env2 ++ supplied2) captured2 fns2 index), ?_, ?_⟩
      · simp only [Option.map, Bool.and_eq_true, decide_eq_true_eq] at valid
        simp [destClosure, entry2, ← len, ← suppliedLen, valid, partialCase]
      · refine ⟨_, rfl, ?_⟩
        apply (valueRel_sourceEquations g allowed code).2.2 _ _ _ _ _ _ |>.mpr
        exact ⟨loc, _, _, _, group, rfl, rfl, List.rel_append envs suppliedRel, capturedRel⟩
    · rename_i fullCase
      simp only [Option.some.injEq] at run
      subst x1
      have ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp entry
      have arities := recClosureRel_arities g allowed code loc fns fns2 group
      have lengths := congrArg List.length arities
      simp only [List.length_map] at lengths
      have bound2 : index < fns2.length := by omega
      have selected2 := (List.getElem?_eq_some_iff.mp entry2).2
      let rec1 := (List.range fns.length).map (fun i => Value.recclosure (some loc) [] captured fns i)
      let rec2 := (List.range fns2.length).map (fun i => Value.recclosure (some loc) [] captured2 fns2 i)
      let p1 := (env1.reverse.take (arity - supplied.length)).reverse
      let p2 := (env2.reverse.take (arity - supplied2.length)).reverse
      have recRel : List.Forall₂ (valueRel g allowed code) rec1 rec2 :=
        recClosureValues g allowed code loc fns fns2 captured captured2 group capturedRel
      have recLen1 : rec1.length = fns2.length := by simp [rec1, lengths]
      have recLen2 : rec2.length = fns2.length := by simp [rec2]
      have captureOne : envRel (valueRel g allowed code) captured captured2 fns2.length [holEl index fns2] := by
        unfold envRel at capturedRel ⊢
        by_cases same : captured.length = captured2.length
        · simpa [same] using capturedRel
        · simp only [same, ↓reduceIte] at capturedRel ⊢
          intro x used
          apply capturedRel x
          obtain ⟨fn, membership, free⟩ := used
          have eq : fn = holEl index fns2 := by simpa using membership
          subst fn
          exact ⟨holEl index fns2, by rw [holEl_eq_getElem index fns2 bound2]; exact List.getElem_mem bound2, free⟩
      have holEntry1 : holEl index fns = (arity, body) := by
        rw [holEl_eq_getElem index fns bound, selected]
      have holEntry2 : holEl index fns2 = (arity, body2) := by
        rw [holEl_eq_getElem index fns2 bound2, selected2]
      refine ⟨.fullApp body2 (p2 ++ (supplied2 ++ rec2 ++ captured2))
        ((env2.reverse.drop (arity - supplied2.length)).reverse), ?_, ?_⟩
      · simp only [Option.map, Bool.and_eq_true, decide_eq_true_eq] at valid
        simp [destClosure, entry2, ← len, ← suppliedLen, valid, fullCase, p2, rec2, List.append_assoc]
      · refine ⟨fns, loc, index, fns2, p2 ++ (supplied2 ++ rec2 ++ captured2),
          ((env2.reverse.drop (arity - supplied2.length)).reverse), arity, ?_, ?_, ?_, group, bound, holEntry1⟩
        · simp [holEntry2]
        · simp only [isRecClosure, ↓reduceIte]
          have need : arity - supplied.length ≤ env1.length := by omega
          have plen : (p1 ++ supplied).length = arity := by
            simp only [List.length_append, p1, List.length_reverse, List.length_take,
              min_eq_left need]
            have valid2 := valid
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid2
            omega
          have plen2 : (p2 ++ supplied2).length = arity := by
            simp only [List.length_append, p2, List.length_reverse, List.length_take]
            rw [← suppliedLen, ← len, min_eq_left need]
            have valid2 := valid
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid2
            omega
          have preRel : List.Forall₂ (valueRel g allowed code) p1 p2 := by
            simpa [p1, p2, ← suppliedLen] using
              List.rel_reverse (List.forall₂_take (arity - supplied.length) (List.rel_reverse envs))
          let q1 := (p1 ++ supplied) ++ rec1
          let q2 := (p2 ++ supplied2) ++ rec2
          have qlen1 : q1.length = arity + fns2.length := by
            change ((p1 ++ supplied) ++ rec1).length = _
            rw [List.length_append, plen, recLen1]
          have qlen2 : q2.length = arity + fns2.length := by
            change ((p2 ++ supplied2) ++ rec2).length = _
            rw [List.length_append, plen2, recLen2]
          have take1 : (q1 ++ captured).take (arity + fns2.length) = q1 := by
            rw [← qlen1, List.take_append_length]
          have take2 : (q2 ++ captured2).take (arity + fns2.length) = q2 := by
            rw [← qlen2, List.take_append_length]
          have drop1 : (q1 ++ captured).drop (arity + fns2.length) = captured := by
            rw [← qlen1, List.drop_append_length]
          have drop2 : (q2 ++ captured2).drop (arity + fns2.length) = captured2 := by
            rw [← qlen2, List.drop_append_length]
          change arity + fns2.length ≤ (p1 ++ (supplied ++ rec1 ++ captured)).length ∧
            arity + fns2.length ≤ (p2 ++ (supplied2 ++ rec2 ++ captured2)).length ∧
            List.Forall₂ (valueRel g allowed code) ((p1 ++ (supplied ++ rec1 ++ captured)).take (arity + fns2.length))
              ((p2 ++ (supplied2 ++ rec2 ++ captured2)).take (arity + fns2.length)) ∧
            envRel (valueRel g allowed code) ((p1 ++ (supplied ++ rec1 ++ captured)).drop (arity + fns2.length))
              ((p2 ++ (supplied2 ++ rec2 ++ captured2)).drop (arity + fns2.length)) fns2.length [holEl index fns2]
          simp only [← List.append_assoc]
          change arity + fns2.length ≤ (q1 ++ captured).length ∧
            arity + fns2.length ≤ (q2 ++ captured2).length ∧
            List.Forall₂ (valueRel g allowed code) ((q1 ++ captured).take (arity + fns2.length))
              ((q2 ++ captured2).take (arity + fns2.length)) ∧
            envRel (valueRel g allowed code) ((q1 ++ captured).drop (arity + fns2.length))
              ((q2 ++ captured2).drop (arity + fns2.length)) fns2.length [holEl index fns2]
          rw [take1, take2, drop1, drop2]
          refine ⟨?_, ?_, List.rel_append (List.rel_append preRel suppliedRel) recRel, captureOne⟩
          · rw [← qlen1]; simp
          · rw [← qlen2]; simp
        · simpa [← suppliedLen] using
            List.rel_reverse (List.forall₂_drop (arity - supplied.length) (List.rel_reverse envs))
  | _ => simp [destClosure] at run

end Flapjack.Compiler.Backend.ClosCall
