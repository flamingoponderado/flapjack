module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureRun
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.PartialApplication
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateClockShift

@[expose] public section

/-! Entry correspondence for complete and partial closure values. -/

namespace Flapjack.Compiler.Backend.ClosToBvl

namespace ValueRunCarrier
/-- Canonical BVL state reference-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ValueRunCarrier

/-- A related full closure application enters installed code after a uniform
clock adjustment, preserving the complete body evaluation for every state. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "v_rel_run"
  (fmap_as_finite_support_relation := [BvlSem.State.refs, f1, refs])]
theorem vRelRun {C F : Type} (maxApp : Nat) (f1 : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (args : List ClosSem.Value) (args' : List BvlSem.Value) (env' : List BvlSem.Value)
    (ptr : Nat) (body : ClosLang.Exp) (newEnv : List ClosSem.Value) (func : ClosSem.Value)
    (func' : BvlSem.Value) (rest : List ClosSem.Value) (tag n : Nat) (loc : Option Nat)
    (h : args.length ≠ 0 ∧
      func' = .block tag (.codePtr ptr :: .number (Int.ofNat n) :: env') ∧
      ClosSem.destClosure maxApp loc func args = some (.fullApp body newEnv rest) ∧
      vRel maxApp f1 refs code func func' ∧
      List.Forall₂ (vRel maxApp f1 refs code) args args') :
    ∃ (ck : Nat) (body' : Bvl.Exp) (aux1 aux2 : List (Nat × Nat × Bvl.Exp))
      (newEnv' : List BvlSem.Value) (exp' : Bvl.Exp),
      sptLookup ptr code = some (n + 2, exp') ∧
      compileExpsHOL maxApp [body] aux1 = ([body'], aux2) ∧ codeInstalled aux2 code ∧
      envRel maxApp f1 refs code newEnv newEnv' ∧
      ∀ t1 : BvlSem.State C F,
        BvlSem.evaluate [exp'] (args'.drop (args'.length - (n + 1)) ++ [func'])
          (BvlProps.incClock ck {t1 with refs := refs, code := code}) =
        BvlSem.evaluate [body'] newEnv' {t1 with refs := refs, code := code} := by
  rcases h with ⟨nonempty, target, destination, related, argsRel⟩
  cases related with
  | number _ | word64 _ | block _ | byteVector _ _ | refPtr _ =>
      simp [ClosSem.destClosure] at destination
  | closure envRel closureRel =>
      rename_i env fvs p number fields
      simp only [BvlSem.Value.block.injEq, List.cons.injEq,
        BvlSem.Value.codePtr.injEq, BvlSem.Value.number.injEq] at target
      obtain ⟨tagEq, ptrEq, numEq, envEq⟩ := target
      subst tag
      subst ptr
      subst number
      subst env'
      have prime := destClosure_imp_prime maxApp loc func args (.fullApp body newEnv rest) destination
      have related := vRel.closure envRel closureRel
      obtain ⟨body', aux1, aux2, newEnv', exp', lookup, compiled, installed, envRelated, run⟩ :=
        clRelRun (C := C) (F := F) maxApp loc f1 refs code args args' env fields p body newEnv func
          (.block 30 (.codePtr p :: .number (Int.ofNat n) :: fields)) rest n fvs
          ⟨rfl, prime, related, closureRel, envRel, argsRel⟩
      refine ⟨0, body', aux1, aux2, newEnv', exp', lookup, compiled, installed, envRelated, ?_⟩
      intro t1
      simpa [BvlProps.incClock] using run t1
  | partialClosure envRel savedRel nonemptySaved savedBound stub added arity closureRel =>
      rename_i env fvs argEnv saved numArgs cl targetClosure
      simp only [BvlSem.Value.block.injEq, List.cons.injEq,
        BvlSem.Value.codePtr.injEq, BvlSem.Value.number.injEq] at target
      obtain ⟨tagEq, ptrEq, numEq, envEq⟩ := target
      subst tag
      subst ptr
      subst env'
      have savedLength : argEnv.length = saved.length := savedRel.length_eq
      have argsLength : args.length = args'.length := argsRel.length_eq
      have savedPositive : 0 < saved.length := by
        have h : 0 < argEnv.length := List.length_pos_iff.mpr nonemptySaved
        omega
      have prime := destClosure_full_of_part maxApp loc func args body newEnv rest argEnv cl numArgs
        ⟨destination, by simpa using nonemptySaved, added, arity, savedBound⟩
      have shape := clRel_dest maxApp (fun p => ∃ r, f1.lookup r = some p)
        refs code cl targetClosure env fvs closureRel
      obtain ⟨oldArgs, address, total, fields, closureShape⟩ := shape
      have baseRel : vRel maxApp f1 refs code cl targetClosure := by
        rw [closureShape] at closureRel ⊢
        exact .closure envRel closureRel
      have baseArity : total + 1 = numArgs := by
        have relation : clRel maxApp (fun p => ∃ r, f1.lookup r = some p) refs code
            (env, fvs) cl (.block 30 (.codePtr address ::
              .number (Int.ofNat (total + 1) - 1) :: fields)) := by
          simpa using closureShape ▸ closureRel
        have eq := clRel_getNumArgs maxApp (fun p => ∃ r, f1.lookup r = some p)
          refs code env fvs cl 30 (.codePtr address) (total + 1) fields relation
        simp [arity] at eq
        exact eq.symm
      have joined : List.Forall₂ (vRel maxApp f1 refs code) (args ++ argEnv) (args' ++ saved) :=
        List.rel_append argsRel savedRel
      have sourceMeta : getNumArgs func = some numArgs ∧ getOldArgs func = some argEnv := by
        cases cl <;> simp [addArgs, getOldArgs, getNumArgs] at oldArgs added arity ⊢
        all_goals subst func
        all_goals simp_all
      obtain ⟨rem, loc', num, old, captured, getLocEq, getRemaining, getNum,
        getOld, getEnv, remBound, remNum, numBound, restLength, check⟩ :=
          destClosureFullApp loc func args () () () body newEnv rest maxApp destination
      have numEq' : num = numArgs := by
        rw [sourceMeta.1] at getNum
        exact (Option.some.inj getNum).symm
      have oldEq : old = argEnv := by
        rw [sourceMeta.2] at getOld
        exact (Option.some.inj getOld).symm
      have fullBound : numArgs ≤ args'.length + saved.length := by
        rw [numEq', oldEq] at numBound
        omega
      have nEq : n = numArgs - 1 - saved.length := by
        have eq := Int.ofNat.inj numEq
        omega
      have remainingEq : n + 1 = numArgs - saved.length := by omega
      have suffixLength : (args'.drop (args'.length - (n + 1))).length = numArgs - saved.length := by
        simp only [List.length_drop]
        omega
      have joinedLength : (args' ++ saved).length - (total + 1) = args'.length - (n + 1) := by
        simp only [List.length_append]
        omega
      have savedNonzero : saved.length ≠ 0 := by omega
      have savedSmaller : saved.length < numArgs := by omega
      obtain ⟨body', aux1, aux2, newEnv', exp', lookup, compiled, installed, envRelated, run⟩ :=
        clRelRun (C := C) (F := F) maxApp loc f1 refs code (args ++ argEnv) (args' ++ saved)
          env fields address body newEnv cl targetClosure rest total fvs
          ⟨closureShape, prime, baseRel, closureRel, envRel, joined⟩
      let suffix := args'.drop (args'.length - (n + 1))
      have suffixLen : suffix.length = numArgs - saved.length := suffixLength
      have combinedDrop : (args' ++ saved).drop ((args' ++ saved).length - (total + 1)) = suffix ++ saved := by
        rw [joinedLength, List.drop_append_of_le_length (by omega)]
      have lookupPartial : sptLookup address code = some (suffix.length + saved.length + 1, exp') := by
        have eq : total + 2 = suffix.length + saved.length + 1 := by omega
        simpa only [eq] using lookup
      refine ⟨1, body', aux1, aux2, newEnv',
        generatePartialAppClosureFn (numArgs - 1) (saved.length - 1), ?_, compiled, installed,
        envRelated, ?_⟩
      · have eq : numArgs - argEnv.length + 1 = n + 2 := by omega
        simpa only [eq] using stub
      · intro t1
        have step := evaluatePartialAppFn (C := C) (F := F) numArgs suffix (.number (Int.ofNat total))
          saved 31 (.number (Int.ofNat n)) 30 address
          (.codePtr (partialAppFnLocation maxApp (numArgs - 1) (saved.length - 1))) fields exp' code
          ⟨lookupPartial, savedNonzero, savedSmaller, by omega⟩
          { t1 with refs := refs, clock := t1.clock + 1 }
        have base := run t1
        rw [combinedDrop, closureShape] at base
        have suffixTotal : suffix.length + saved.length = numArgs := by omega
        simp only [suffixTotal, Nat.sub_self, List.drop_zero] at step
        simp [BvlSem.decClock] at step
        simp only [List.append_assoc] at base
        simpa [suffix, BvlProps.incClock, BvlSem.decClock, remainingEq, closureShape, nEq, savedLength,
          List.append_assoc] using step.trans base
end Flapjack.Compiler.Backend.ClosToBvl
