module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

@[expose] public section

/-! Full closure-entry correspondence for the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

namespace ClosureRunCarrier
/-- Canonical BVL state reference-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ClosureRunCarrier

/-- A related full closure application enters installed code with a related
body environment, uniformly for every target state. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cl_rel_run"
  (fmap_as_finite_support_relation := [BvlSem.State.refs, f1, refs])]
theorem clRelRun {C F : Type} (maxApp : Nat) (loc : Option Nat)
    (f1 : HolFiniteMapExact Nat Nat) (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (code : Spt (Nat × Bvl.Exp)) (args : List ClosSem.Value) (args' : List BvlSem.Value)
    (env : List ClosSem.Value) (env' : List BvlSem.Value) (ptr : Nat) (body : ClosLang.Exp)
    (newEnv : List ClosSem.Value) (func : ClosSem.Value) (func' : BvlSem.Value)
    (rest : List ClosSem.Value) (n : Nat) (fvs : List BvlSem.Value)
    (h : func' = .block 30 (.codePtr ptr :: .number (Int.ofNat n) :: env') ∧
      destClosurePrime loc func args = some (.fullApp body newEnv rest) ∧
      vRel maxApp f1 refs code func func' ∧
      clRel maxApp (fun p => ∃ r, f1.lookup r = some p) refs code (env, fvs) func func' ∧
      List.Forall₂ (vRel maxApp f1 refs code) env fvs ∧
      List.Forall₂ (vRel maxApp f1 refs code) args args') :
    ∃ (body' : Bvl.Exp) (aux1 aux2 : List (Nat × Nat × Bvl.Exp)) (newEnv' : List BvlSem.Value) (exp' : Bvl.Exp),
      sptLookup ptr code = some (n + 2, exp') ∧
      compileExpsHOL maxApp [body] aux1 = ([body'], aux2) ∧ codeInstalled aux2 code ∧
      envRel maxApp f1 refs code newEnv newEnv' ∧
      ∀ t1 : BvlSem.State C F,
        BvlSem.evaluate [exp'] (args'.drop (args'.length - (n + 1)) ++ [func'])
          {t1 with refs := refs, code := code} =
        BvlSem.evaluate [body'] newEnv' {t1 with refs := refs, code := code} := by
  rcases h with ⟨target, destination, valueRel, closureRel, envRelated, argsRelated⟩
  cases closureRel with
  | closure bound positive locations vars compiled installed lookup =>
      rename_i arity source aux0 targetBody auxFinal loc0
      simp only [BvlSem.Value.block.injEq, List.cons.injEq, BvlSem.Value.codePtr.injEq,
        BvlSem.Value.number.injEq] at target
      simp only [destClosurePrime] at destination
      simp only [List.length_nil, Nat.add_zero, Nat.sub_zero, List.nil_append] at destination
      split at destination <;> simp_all only [reduceCtorEq, Option.some.injEq,
        Bool.and_eq_true, decide_eq_true_eq]
      split at destination <;> simp_all only [reduceCtorEq, Option.some.injEq,
        ClosSem.AppKind.fullApp.injEq]
      obtain ⟨_, _, arityNumber, _⟩ := target
      have arityEq : arity = n + 1 := by
        have eq : arity - 1 = n := Int.ofNat.inj arityNumber
        omega
      have sourceBound : arity ≤ args.length := by omega
      have lengths : args.length = args'.length := argsRelated.length_eq
      have suffixRel := List.forall₂_drop (args.length - arity) argsRelated
      have targetBound : arity ≤ args'.length := by omega
      have suffixLength : (args'.drop (args'.length - arity)).length = arity := by
        simp only [List.length_drop]
        omega
      obtain ⟨_, newEnvEq, _⟩ := destination
      have sourceEnv : newEnv = args.drop (args.length - arity) ++ env := by
        simpa [List.take_reverse] using newEnvEq.symm
      let suffix := args'.drop (args'.length - arity)
      let closure := BvlSem.Value.block 30 (.codePtr ptr :: .number (Int.ofNat n) :: env')
      refine ⟨targetBody, aux0, auxFinal, (suffix ++ env') ++ suffix ++ [closure],
        .let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) env.length) targetBody,
        ?_, compiled, installed, ?_, ?_⟩
      · simp [arityEq, Nat.add_assoc]
      · rw [sourceEnv]
        have related : List.Forall₂ (vRel maxApp f1 refs code)
            (args.drop (args.length - arity)) suffix := by
          simpa [suffix, lengths] using suffixRel
        have restRel := listRel_imp_envRel (suffix ++ [closure]) env env' envRelated
        simpa [List.append_assoc] using envRel_append env (env' ++ (suffix ++ [closure]))
          _ _ ⟨related, restRel⟩
      · intro t1
        have run := evaluate_closure_entry {t1 with refs := refs, code := code} suffix env' 30
          (.codePtr ptr) (.number (Int.ofNat n)) targetBody
        have suffixLen : suffix.length = arity := suffixLength
        rw [suffixLen, ← envRelated.length_eq] at run
        simpa [suffix, closure, arityEq, List.append_assoc] using run
  | singletonRec bound positive locations vars compiled installed lookup =>
      rename_i arity source aux0 targetBody auxFinal loc0
      simp only [BvlSem.Value.block.injEq, List.cons.injEq, BvlSem.Value.codePtr.injEq,
        BvlSem.Value.number.injEq] at target
      simp only [destClosurePrime] at destination
      simp only [List.length_nil, Nat.add_zero, Nat.sub_zero, List.nil_append,
        List.getElem?_cons_zero] at destination
      split at destination <;> simp_all only [reduceCtorEq, Option.some.injEq,
        Bool.and_eq_true, decide_eq_true_eq]
      split at destination <;> simp_all only [reduceCtorEq, Option.some.injEq,
        ClosSem.AppKind.fullApp.injEq]
      obtain ⟨_, _, arityNumber, _⟩ := target
      have arityEq : arity = n + 1 := by
        have eq : arity - 1 = n := Int.ofNat.inj arityNumber
        omega
      have sourceBound : arity ≤ args.length := by omega
      have lengths : args.length = args'.length := argsRelated.length_eq
      have suffixRel := List.forall₂_drop (args.length - arity) argsRelated
      have targetBound : arity ≤ args'.length := by omega
      have suffixLength : (args'.drop (args'.length - arity)).length = arity := by
        simp only [List.length_drop]
        omega
      obtain ⟨sourceEq, newEnvEq, _⟩ := destination
      have sourceEnv : newEnv = args.drop (args.length - arity) ++
          (.recclosure (some loc0) [] env [(arity, body)] 0 :: env) := by
        simpa [List.take_reverse, sourceEq] using newEnvEq.symm
      let suffix := args'.drop (args'.length - arity)
      let closure := BvlSem.Value.block 30 (.codePtr ptr :: .number (Int.ofNat n) :: env')
      refine ⟨targetBody, aux0, auxFinal, ((suffix ++ [closure]) ++ env') ++ suffix ++ [closure],
        .let ((List.range (arity + 1)).map Bvl.Exp.var ++ freeLet (.var arity) env.length) targetBody,
        ?_, compiled, installed, ?_, ?_⟩
      · simp [arityEq, Nat.add_assoc]
      · rw [sourceEnv]
        have related : List.Forall₂ (vRel maxApp f1 refs code)
            (args.drop (args.length - arity)) suffix := by
          simpa [suffix, lengths] using suffixRel
        have restRel := listRel_imp_envRel (suffix ++ [closure]) env env' envRelated
        have closureRel : envRel maxApp f1 refs code
            (.recclosure (some loc0) [] env [(arity, body)] 0 :: env)
            (closure :: env' ++ (suffix ++ [closure])) := ⟨valueRel, restRel⟩
        simpa [List.append_assoc] using envRel_append _ _ _ _ ⟨related, closureRel⟩
      · intro t1
        have run := evaluate_singletonRec_entry {t1 with refs := refs, code := code} suffix env' 30
          (.codePtr ptr) (.number (Int.ofNat n)) targetBody
        have suffixLen : suffix.length = arity := suffixLength
        rw [suffixLen, ← envRelated.length_eq] at run
        simpa [suffix, closure, arityEq, List.append_assoc] using run
  | mutualRec exps ps positions values fresh stored length index locations vars installed =>
      rename_i functions entries labels targets loc0 shared k
      have rel : clRel maxApp (fun p => ∃ r, f1.lookup r = some p) refs code
          (env, fvs) (.recclosure (some loc0) [] env functions k) (holEl k targets) :=
        .mutualRec exps ps positions values fresh stored length index locations vars installed
      cases entry : functions[k]? with
      | none => simp [destClosurePrime, entry] at destination
      | some pair =>
        rcases pair with ⟨arity, source⟩
        simp only [destClosurePrime, entry, List.length_nil, Nat.add_zero, Nat.sub_zero,
          List.nil_append] at destination
        split at destination <;> simp_all only [reduceCtorEq, Bool.and_eq_true, decide_eq_true_eq]
        split at destination <;> simp_all only [reduceCtorEq, Option.some.injEq,
          ClosSem.AppKind.fullApp.injEq]
        obtain ⟨address, shared2, targets2, aux0, targetBody, auxFinal, shape, stored2,
          targetsLength, groupRel, arityBound, positive, compiled, lookup, installed2⟩ :=
          clRel_mutualRec_selected_related rel envRelated length entry
        simp only [BvlSem.Value.block.injEq, List.cons.injEq, BvlSem.Value.codePtr.injEq,
          BvlSem.Value.number.injEq] at shape
        obtain ⟨_, addressEq, arityNumber, envEq⟩ := shape
        have arityEq : arity = n + 1 := by
          have eq : n = arity - 1 := Int.ofNat.inj arityNumber
          omega
        have sourceBound : arity ≤ args.length := by omega
        have lengths : args.length = args'.length := argsRelated.length_eq
        have suffixRel := List.forall₂_drop (args.length - arity) argsRelated
        have targetBound : arity ≤ args'.length := by omega
        have suffixLength : (args'.drop (args'.length - arity)).length = arity := by
          simp only [List.length_drop]
          omega
        obtain ⟨sourceEq, newEnvEq, _⟩ := destination
        have sourceEnv : newEnv = args.drop (args.length - arity) ++
            ((List.range (List.map Prod.fst entries).length).map
              (fun i => .recclosure (some loc0) [] env (List.map Prod.fst entries) i) ++ env) := by
          simpa [List.take_reverse, sourceEq] using newEnvEq.symm
        subst address
        subst env'
        let suffix := args'.drop (args'.length - arity)
        let closure := BvlSem.Value.block 30 [.codePtr ptr, .number (Int.ofNat n), .refPtr true shared2]
        refine ⟨targetBody, aux0, auxFinal,
          suffix ++ (targets2 ++ fvs) ++ [.refPtr true shared2] ++ suffix ++ [closure],
          (codeForReccCase (env.length + (List.map Prod.fst entries).length) arity targetBody).2,
          ?_, compiled, installed2, ?_, ?_⟩
        · simpa [arityEq, Nat.add_assoc] using lookup
        · rw [sourceEnv]
          have related : List.Forall₂ (vRel maxApp f1 refs code)
              (args.drop (args.length - arity)) suffix := by
            simpa [suffix, lengths] using suffixRel
          have restRel := listRel_imp_envRel ([.refPtr true shared2] ++ suffix ++ [closure]) env fvs envRelated
          have groupEnv := envRel_append env _ _ _ ⟨groupRel, restRel⟩
          simpa [List.append_assoc] using envRel_append _ _ _ _ ⟨related, groupEnv⟩
        · intro t1
          have storedState : ({t1 with refs := refs, code := code} : BvlSem.State C F).refs.lookup shared2 =
              some (.valueArray (targets2 ++ fvs)) := stored2
          have run := evaluateCodeForReccCase {t1 with refs := refs, code := code} shared2
            (targets2 ++ fvs) suffix targetBody ptr n [] storedState
          have suffixLen : suffix.length = arity := suffixLength
          have sharedLen : (targets2 ++ fvs).length = env.length + (List.map Prod.fst entries).length := by
            simp [targetsLength, ← envRelated.length_eq, Nat.add_comm]
          rw [suffixLen, sharedLen] at run
          simpa [suffix, closure, arityEq, List.append_assoc] using run
end Flapjack.Compiler.Backend.ClosToBvl
