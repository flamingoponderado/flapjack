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
end Flapjack.Compiler.Backend.ClosCall
