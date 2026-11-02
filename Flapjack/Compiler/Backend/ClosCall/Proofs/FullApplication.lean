import Flapjack.Compiler.Backend.ClosCall.Proofs.PartialApplication

/-! Full and over-application of related closures. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- Moving an argument count from the function descriptor to the environment
offset leaves the free-variable requirement unchanged. -/
theorem envRelFuel_shift_arity {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (offset arity : Nat) (body : ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv offset [(arity, body)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv (offset + arity) [(0, body)] := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  simpa [envRel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Taking and dropping the consumed suffix of related argument lists
preserves the relation on both the consumed and remaining arguments. -/
theorem valueRelFuel_splitArgs {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    {sourceArgs targetArgs : List ClosSem.Value} (needed : Nat)
    (args : List.Forall₂ (ValueRelFuel fuel g allowed code) sourceArgs targetArgs) :
    List.Forall₂ (ValueRelFuel fuel g allowed code)
      (sourceArgs.reverse.take needed).reverse (targetArgs.reverse.take needed).reverse ∧
    List.Forall₂ (ValueRelFuel fuel g allowed code)
      (sourceArgs.reverse.drop needed).reverse (targetArgs.reverse.drop needed).reverse := by
  exact ⟨List.rel_reverse (List.forall₂_take needed (List.rel_reverse args)),
    List.rel_reverse (List.forall₂_drop needed (List.rel_reverse args))⟩

/-- Related closures that fully apply select corresponding bodies, produce
related body environments, and leave related over-applied arguments. The
selected group and index are retained for the enclosing pass induction. -/
theorem destClosure_full_fuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (maxApp : Nat) (requested : Option Nat)
    (source target : ClosSem.Value) (sourceArgs targetArgs : List ClosSem.Value)
    (sourceBody : ClosLang.Exp) (sourceBodyEnv sourceRest : List ClosSem.Value)
    (sourceRun : destClosure maxApp requested source sourceArgs = some (.fullApp sourceBody sourceBodyEnv sourceRest))
    (values : ValueRelFuel fuel g allowed code source target)
    (args : List.Forall₂ (ValueRelFuel fuel g allowed code) sourceArgs targetArgs) :
    ∃ (targetBody : ClosLang.Exp) (targetBodyEnv targetRest : List ClosSem.Value)
      (loc : Nat) (sourceFns targetFns : List (Nat × ClosLang.Exp)) (index arity : Nat),
      destClosure maxApp requested target targetArgs = some (.fullApp targetBody targetBodyEnv targetRest) ∧
      EnvRelFuel fuel g allowed code sourceBodyEnv targetBodyEnv 0 [(0, targetBody)] ∧
      List.Forall₂ (ValueRelFuel fuel g allowed code) sourceRest targetRest ∧
      recClosureRelFuel fuel g allowed code loc sourceFns targetFns ∧
      sourceFns[index]? = some (arity, sourceBody) ∧ targetFns[index]? = some (arity, targetBody) ∧
      (∀ address, requested = some address →
        address = 2 * index + loc ∧ arity = sourceArgs.length ∧ sourceRest = []) := by
  have argsLength := args.length_eq
  cases values with
  | number | word64 | block | byteVector | refPtr => simp [destClosure] at sourceRun
  | @closure loc sourceSupplied targetSupplied sourceEnv targetEnv arity sourceFnBody targetFnBody closure supplied envs =>
    have suppliedLength := supplied.length_eq
    by_cases valid : checkLoc maxApp requested (some loc) arity sourceArgs.length sourceSupplied.length &&
        sourceSupplied.length < arity
    · by_cases undersaturated : sourceArgs.length + sourceSupplied.length < arity
      · simp [destClosure, valid, undersaturated] at sourceRun
      · have sourceEq : sourceBody = sourceFnBody ∧
            sourceBodyEnv = (sourceArgs.reverse.take (arity - sourceSupplied.length)).reverse ++ sourceSupplied ++ sourceEnv ∧
            sourceRest = (sourceArgs.reverse.drop (arity - sourceSupplied.length)).reverse := by
          simpa [destClosure, valid, undersaturated, List.append_assoc] using sourceRun.symm
        obtain ⟨rfl, rfl, rfl⟩ := sourceEq
        let needed := arity - sourceSupplied.length
        have splitArgs := valueRelFuel_splitArgs (code := code) needed args
        have prefixRel : List.Forall₂ (ValueRelFuel fuel g allowed code)
            ((sourceArgs.reverse.take needed).reverse ++ sourceSupplied)
            ((targetArgs.reverse.take needed).reverse ++ targetSupplied) := List.rel_append splitArgs.1 supplied
        have suppliedBound : sourceSupplied.length < arity := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.2
        have prefixLength : ((sourceArgs.reverse.take needed).reverse ++ sourceSupplied).length = arity := by
          simp only [List.length_append, List.length_reverse, List.length_take]
          dsimp [needed]
          omega
        have outer := envRelFuel_shift_arity 0 arity targetFnBody envs
        have bodyEnv : EnvRelFuel fuel g allowed code
            ((sourceArgs.reverse.take needed).reverse ++ sourceSupplied ++ sourceEnv)
            ((targetArgs.reverse.take needed).reverse ++ targetSupplied ++ targetEnv) 0 [(0, targetFnBody)] := by
          have h := envRelFuel_prepend (offset := 0) prefixRel (by simpa [prefixLength] using outer)
          simpa [List.append_assoc] using h
        refine ⟨targetFnBody, (targetArgs.reverse.take needed).reverse ++ targetSupplied ++ targetEnv,
          (targetArgs.reverse.drop needed).reverse, loc, [(arity, sourceBody)], [(arity, targetFnBody)], 0, arity,
          ?_, bodyEnv, splitArgs.2, closure, rfl, rfl, ?_⟩
        · simp [destClosure, ← argsLength, ← suppliedLength, valid, undersaturated, needed, List.append_assoc]
        · intro address request
          have both := valid
          simp only [Bool.and_eq_true, decide_eq_true_eq] at both
          have check := both.1
          rw [request] at check
          have facts : arity = sourceArgs.length ∧ sourceSupplied.length = 0 ∧ address = loc := by
            simpa [checkLoc] using check
          obtain ⟨arityEq, suppliedEq, addressEq⟩ := facts
          subst address
          simp [suppliedEq, arityEq]
    · simp [destClosure, valid] at sourceRun
  | @recclosure loc sourceSupplied targetSupplied sourceEnv targetEnv sourceFns targetFns index closure supplied envs =>
    have suppliedLength := supplied.length_eq
    cases sourceLookup : sourceFns[index]? with
    | none => simp [destClosure, sourceLookup] at sourceRun
    | some fn =>
      obtain ⟨arity, sourceFnBody⟩ := fn
      have arities := recClosureRelFuel_arities fuel g allowed code loc sourceFns targetFns closure
      have targetArity : (targetFns.map Prod.fst)[index]? = some arity := by
        rw [arities]
        simp [List.getElem?_map, sourceLookup]
      cases targetLookup : targetFns[index]? with
      | none => simp [List.getElem?_map, targetLookup] at targetArity
      | some targetFn =>
        obtain ⟨targetArity', targetFnBody⟩ := targetFn
        have arityEq : targetArity' = arity := by
          simpa [List.getElem?_map, targetLookup] using targetArity
        subst targetArity'
        by_cases valid : checkLoc maxApp requested (some (2 * index + loc)) arity
            sourceArgs.length sourceSupplied.length && sourceSupplied.length < arity
        · by_cases undersaturated : sourceArgs.length + sourceSupplied.length < arity
          · simp [destClosure, sourceLookup, valid, undersaturated] at sourceRun
          · have sourceEq : sourceBody = sourceFnBody ∧
                sourceBodyEnv = (sourceArgs.reverse.take (arity - sourceSupplied.length)).reverse ++ sourceSupplied ++
                  (List.range sourceFns.length).map (fun i => .recclosure (some loc) [] sourceEnv sourceFns i) ++ sourceEnv ∧
                sourceRest = (sourceArgs.reverse.drop (arity - sourceSupplied.length)).reverse := by
              simpa [destClosure, sourceLookup, valid, undersaturated, List.append_assoc] using sourceRun.symm
            obtain ⟨rfl, rfl, rfl⟩ := sourceEq
            let needed := arity - sourceSupplied.length
            let sourceRecursive := (List.range sourceFns.length).map (fun i => ClosSem.Value.recclosure (some loc) [] sourceEnv sourceFns i)
            let targetRecursive := (List.range targetFns.length).map (fun i => ClosSem.Value.recclosure (some loc) [] targetEnv targetFns i)
            have splitArgs := valueRelFuel_splitArgs (code := code) needed args
            have recursive := recClosureRelFuel_values closure envs
            have prefixRel : List.Forall₂ (ValueRelFuel fuel g allowed code)
                ((sourceArgs.reverse.take needed).reverse ++ sourceSupplied ++ sourceRecursive)
                ((targetArgs.reverse.take needed).reverse ++ targetSupplied ++ targetRecursive) :=
              List.rel_append (List.rel_append splitArgs.1 supplied) recursive
            have suppliedBound : sourceSupplied.length < arity := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
              exact valid.2
            have prefixLength : ((sourceArgs.reverse.take needed).reverse ++ sourceSupplied ++ sourceRecursive).length =
                arity + targetFns.length := by
              have length := recClosureRelFuel_length fuel g allowed code loc sourceFns targetFns closure
              simp only [List.length_append, List.length_reverse, List.length_take, sourceRecursive,
                List.length_map, List.length_range]
              dsimp [needed]
              omega
            have targetMember : (arity, targetFnBody) ∈ targetFns := by
              exact List.mem_of_getElem? targetLookup
            have captured : EnvRelFuel fuel g allowed code sourceEnv targetEnv targetFns.length [(arity, targetFnBody)] := by
              apply envRelFuel_subset envs
              intro item member
              simp only [List.mem_singleton] at member
              subst item
              exact targetMember
            have outer := envRelFuel_shift_arity targetFns.length arity targetFnBody captured
            have bodyEnv : EnvRelFuel fuel g allowed code
                ((sourceArgs.reverse.take needed).reverse ++ sourceSupplied ++ sourceRecursive ++ sourceEnv)
                ((targetArgs.reverse.take needed).reverse ++ targetSupplied ++ targetRecursive ++ targetEnv)
                0 [(0, targetFnBody)] := by
              have outer' : EnvRelFuel fuel g allowed code sourceEnv targetEnv
                  (0 + ((sourceArgs.reverse.take needed).reverse ++ sourceSupplied ++ sourceRecursive).length)
                  [(0, targetFnBody)] := by
                rw [prefixLength]
                simpa [Nat.add_comm] using outer
              have h := envRelFuel_prepend (offset := 0) prefixRel outer'
              simpa [List.append_assoc] using h
            refine ⟨targetFnBody,
              (targetArgs.reverse.take needed).reverse ++ targetSupplied ++ targetRecursive ++ targetEnv,
              (targetArgs.reverse.drop needed).reverse, loc, sourceFns, targetFns, index, arity,
              ?_, bodyEnv, splitArgs.2, closure, sourceLookup, targetLookup, ?_⟩
            · simp [destClosure, targetLookup, ← argsLength, ← suppliedLength, valid, undersaturated,
                needed, targetRecursive, List.append_assoc]
            · intro address request
              have both := valid
              simp only [Bool.and_eq_true, decide_eq_true_eq] at both
              have check := both.1
              rw [request] at check
              have facts : arity = sourceArgs.length ∧ sourceSupplied.length = 0 ∧ address = 2 * index + loc := by
                simpa [checkLoc] using check
              obtain ⟨arityEq, suppliedEq, addressEq⟩ := facts
              subst address
              simp [suppliedEq, arityEq]
        · simp [destClosure, sourceLookup, valid] at sourceRun

end Flapjack.Compiler.Backend.ClosCall
