module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileMemory

@[expose] public section

namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

namespace DoAppAdjustCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end DoAppAdjustCarrier

/-- Successful ordinary BVL operations are preserved by relocation in related BVI states. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "do_app_adjust"
  (fmap_as_finite_support_relation := [State.refs, BviState.refs])]
theorem doAppAdjust {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (op : ClosLang.Op) (args : List Value) (result : Value)
    (next : BvlSem.State (Nat × C) F)
    (premises : stateRel relocate source target ∧
      (∀ i, op ≠ .intOp (.const i)) ∧ op ≠ .memOp .ref ∧
      (∀ flag, op ≠ .memOp (.refByte flag)) ∧ op ≠ .memOp .refArray ∧
      (∀ n, op ≠ .globOp (.global n)) ∧ (∀ n, op ≠ .globOp (.setGlobal n)) ∧
      op ≠ .globOp .allocGlobal ∧ op ≠ .install ∧ (∀ t, op ≠ .thunkOp t) ∧
      (∀ n, op ≠ .blockOp (.fromList n)) ∧ op ≠ .memOp .fromListByte ∧
      op ≠ .memOp .toListByte ∧ (∀ c, op ≠ .blockOp (.build c)) ∧
      op ≠ .memOp .xorByte ∧ (∀ b, op ≠ .memOp (.copyByte b)) ∧
      op ≠ .memOp .concatByteVec ∧ (∀ n, op ≠ .label n) ∧
      BvlSem.doApp op args.reverse source = .val (result, next) ∧
      List.Forall (bvOk source.refs) args.reverse) :
    ∃ targetNext, BviSem.doApp op (args.reverse.map (adjustBv relocate)) target =
      .val (adjustBv relocate result, targetNext) ∧ stateRel relocate next targetNext := by
  rcases premises with ⟨related, notConst, notRef, notRefByte, notRefArray, notGlobal,
    notSetGlobal, notAllocGlobal, notInstall, notThunk, notFromList, notFromListByte,
    notToListByte, notBuild, notXor, notCopy, notConcat, notLabel, run, ok⟩
  cases op with
  | label n => exact (notLabel n rfl).elim
  | install => exact (notInstall rfl).elim
  | thunkOp t => exact (notThunk t rfl).elim
  | intOp i =>
    have nc : ∀ n, i ≠ .const n := by
      intro n h
      subst i
      exact notConst n rfl
    cases eval : BvlSem.doIntApp i args.reverse with
    | none => simp [BvlSem.doApp, BvlSem.applyNumeric, eval] at run
    | some value =>
      simp [BvlSem.doApp, BvlSem.applyNumeric, eval] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, by simpa [eval] using doIntApp_target i args.reverse relocate target nc, related⟩
  | wordOp w =>
    cases eval : BvlSem.doWordApp w args.reverse with
    | none => simp [BvlSem.doApp, BvlSem.applyNumeric, eval] at run
    | some value =>
      simp [BvlSem.doApp, BvlSem.applyNumeric, eval] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, by simpa [eval] using doWordApp_target w args.reverse relocate target, related⟩
  | blockOp b =>
    cases b with
    | fromList n => exact (notFromList n rfl).elim
    | build c => exact (notBuild c rfl).elim
    | cons tag =>
      simp [BvlSem.doApp, BvlSem.applyBlock] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, doBlockCons_target tag args.reverse relocate target, related⟩
    | tagEq wanted =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons input rest =>
        cases rest with
        | cons second tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | nil =>
          cases input with
          | block tag fields =>
            simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, ?_, related⟩
            simpa [rev, BlockObservation.op, BlockObservation.result] using
              doBlockObservation_target (.tagEq wanted) tag fields relocate target
          | _ => all_goals simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
    | lenEq wanted =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons input rest =>
        cases rest with
        | cons second tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | nil =>
          cases input with
          | block tag fields =>
            simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, ?_, related⟩
            simpa [rev, BlockObservation.op, BlockObservation.result] using
              doBlockObservation_target (.lenEq wanted) tag fields relocate target
          | _ => all_goals simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
    | tagLenEq wanted len =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons input rest =>
        cases rest with
        | cons second tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | nil =>
          cases input with
          | block tag fields =>
            simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, ?_, related⟩
            simpa [rev, BlockObservation.op, BlockObservation.result] using
              doBlockObservation_target (.tagLenEq wanted len) tag fields relocate target
          | _ => all_goals simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
    | lengthBlock  =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons input rest =>
        cases rest with
        | cons second tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | nil =>
          cases input with
          | block tag fields =>
            simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, ?_, related⟩
            simpa [rev, BlockObservation.op, BlockObservation.result] using
              doBlockObservation_target (.length) tag fields relocate target
          | _ => all_goals simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
    | elemAt index =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons input rest =>
        cases rest with
        | cons second tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | nil =>
          cases input with
          | block tag fields =>
            cases selected : fields[index]? with
            | none => simp [BvlSem.doApp, BvlSem.applyBlock, rev, selected] at run
            | some value =>
              simp [BvlSem.doApp, BvlSem.applyBlock, rev, selected] at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨target, ?_, related⟩
              simpa [rev] using doBlockElemAt_target index tag fields value relocate target selected
          | refPtr flag ptr =>
            cases lookup : source.refs.lookup ptr with
            | none => simp [BvlSem.doApp, BvlSem.applyBlock, rev, lookup] at run
            | some cell =>
              cases cell with
              | valueArray fields =>
                cases selected : fields[index]? with
                | none => simp [BvlSem.doApp, BvlSem.applyBlock, rev, lookup, selected] at run
                | some value =>
                  simp [BvlSem.doApp, BvlSem.applyBlock, rev, lookup, selected] at run
                  rcases run with ⟨rfl, rfl⟩
                  refine ⟨target, ?_, related⟩
                  simpa [rev] using doArrayElemAt_target index flag ptr fields value relocate source target related lookup selected
              | _ => all_goals simp [BvlSem.doApp, BvlSem.applyBlock, rev, lookup] at run
          | _ => all_goals simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
    | boolTest test =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons left tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | cons right rest =>
          cases rest with
          | cons other tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
          | nil =>
            cases ld : BvlSem.asBool left with
            | none => simp [BvlSem.doApp, BvlSem.applyBlock, rev, ld] at run
            | some lf =>
              cases rd : BvlSem.asBool right with
              | none => simp [BvlSem.doApp, BvlSem.applyBlock, rev, ld, rd] at run
              | some rf =>
                simp [BvlSem.doApp, BvlSem.applyBlock, rev, ld, rd] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨target, ?_, related⟩
                simpa [rev] using doBoolTest_target test left right lf rf relocate target ld rd
    | boundsCheckBlock =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons first tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | cons second rest =>
          cases rest with
          | cons other tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
          | nil =>
            cases first with
            | block tag fields =>
              cases second with
              | number index =>
                simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨target, ?_, related⟩
                simpa [rev] using doBlockBounds_target tag fields index relocate target
              | _ => all_goals simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
            | _ => all_goals simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
    | boolNot =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons value rest =>
        cases rest with
        | cons other tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | nil =>
          cases decoded : BvlSem.asBool value with
          | none => simp [BvlSem.doApp, BvlSem.applyBlock, rev, decoded] at run
          | some flag =>
            simp [BvlSem.doApp, BvlSem.applyBlock, rev, decoded] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, ?_, related⟩
            simpa [rev] using doBoolNot_target value flag relocate target decoded
    | constant part => simp [BvlSem.doApp, BvlSem.applyBlock] at run
    | equalConst part =>
      cases rev : args.reverse with
      | nil => cases part <;> simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons value rest =>
        cases rest with
        | cons second tail => cases part <;> simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | nil =>
          cases app : BvlSem.applyBlock (.equalConst part) [value] source with
          | none => simp [BvlSem.doApp, rev, app] at run
          | some pair =>
            obtain ⟨v, state⟩ := pair
            have unchanged : state = source := by
              cases part <;> cases value <;> simp [BvlSem.applyBlock] at app <;>
                repeat' first | split at app | contradiction
              all_goals simp_all
            subst state
            simp [BvlSem.doApp, rev, app] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, ?_, related⟩
            simpa [rev] using doEqualConst_target part value v relocate source target related app
    | equal =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons left tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | cons right rest =>
          cases rest with
          | cons other tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
          | nil =>
            have pairOk : List.Forall (bvOk source.refs) [left, right] := by simpa only [rev] using ok
            simp only [List.forall_cons] at pairOk
            have leftOk := pairOk.1
            have rightOk := pairOk.2.1
            cases eq : BvlSem.doEq source.refs left right with
            | typeError => simp [BvlSem.doApp, BvlSem.applyBlock, rev, eq] at run
            | val flag =>
              simp [BvlSem.doApp, BvlSem.applyBlock, rev, eq] at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨target, ?_, related⟩
              simpa [rev] using doEquality_target relocate source target left right flag related leftOk rightOk eq
    | listAppend =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
      | cons left rest =>
        cases rest with
        | nil => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
        | cons right tail =>
          cases tail with
          | cons other tail => simp [BvlSem.doApp, BvlSem.applyBlock, rev] at run
          | nil =>
            cases ld : BvlSem.valueToList left with
            | none => simp [BvlSem.doApp, BvlSem.applyBlock, rev, ld] at run
            | some xs =>
              cases rd : BvlSem.valueToList right with
              | none => simp [BvlSem.doApp, BvlSem.applyBlock, rev, ld, rd] at run
              | some ys =>
                simp [BvlSem.doApp, BvlSem.applyBlock, rev, ld, rd] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨target, ?_, related⟩
                simpa [rev] using doListAppend_target left right xs ys relocate target ld rd
    | consExtend tag =>
      cases app : BvlSem.applyBlock (.consExtend tag) args.reverse source with
      | none => simp [BvlSem.doApp, app] at run
      | some pair =>
        obtain ⟨value, state⟩ := pair
        have same := consExtend_state tag args.reverse source state value app
        subst state
        simp [BvlSem.doApp, app] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, doConsExtend_target tag args.reverse value relocate source target app, related⟩
  | globOp g =>
    cases g with
    | global n => exact (notGlobal n rfl).elim
    | setGlobal n => exact (notSetGlobal n rfl).elim
    | allocGlobal => exact (notAllocGlobal rfl).elim
    | globalsPtr => simp [BvlSem.doApp, BvlSem.applyGlobal] at run
    | setGlobalsPtr => simp [BvlSem.doApp, BvlSem.applyGlobal] at run
  | memOp m =>
    cases m with
    | ref => exact (notRef rfl).elim
    | refByte flag => exact (notRefByte flag rfl).elim
    | refArray => exact (notRefArray rfl).elim
    | fromListByte => exact (notFromListByte rfl).elim
    | toListByte => exact (notToListByte rfl).elim
    | xorByte => exact (notXor rfl).elim
    | copyByte flag => exact (notCopy flag rfl).elim
    | concatByteVec => exact (notConcat rfl).elim
    | lengthByteVec => simp [BvlSem.doApp, BvlSem.applyMemory] at run
    | derefByteVec => simp [BvlSem.doApp, BvlSem.applyMemory] at run
    | mutCons tag index => simp [BvlSem.doApp, BvlSem.applyMemory] at run
    | updateCons => simp [BvlSem.doApp, BvlSem.applyMemory] at run
    | finaliseCons => simp [BvlSem.doApp, BvlSem.applyMemory] at run
    | length =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
      | cons input rest =>
        cases rest with
        | cons second tail => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
        | nil =>
          cases input with
          | refPtr flag ptr =>
            cases lookup : source.refs.lookup ptr with
            | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
            | some cell =>
              cases cell with
              | valueArray fields =>
                simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨target, ?_, related⟩
                simpa [rev] using doArrayLength_target flag ptr fields relocate source target related lookup
              | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
          | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
    | lengthByte =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
      | cons input rest =>
        cases rest with
        | cons second tail => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
        | nil =>
          cases input with
          | refPtr flag ptr =>
            cases lookup : source.refs.lookup ptr with
            | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
            | some cell =>
              cases cell with
              | byteArray mutableRef fields =>
                simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨target, ?_, related⟩
                simpa [rev] using doByteArrayLength_target flag mutableRef ptr fields relocate source target related lookup
              | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
          | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
    | boundsCheckArray =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
      | cons first tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
        | cons second rest =>
          cases rest with
          | cons other tail => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
          | nil =>
            cases second with
            | number index =>
              cases first with
              | refPtr flag ptr =>
                cases lookup : source.refs.lookup ptr with
                | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                | some cell =>
                  cases cell with
                  | valueArray fields =>
                    simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                    rcases run with ⟨rfl, rfl⟩
                    refine ⟨target, ?_, related⟩
                    simpa [rev] using doArrayBounds_target flag ptr fields index relocate source target related lookup
                  | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
              | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
            | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
    | boundsCheckByte loose =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
      | cons first tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
        | cons second rest =>
          cases rest with
          | cons other tail => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
          | nil =>
            cases second with
            | number index =>
              cases first with
              | refPtr flag ptr =>
                cases lookup : source.refs.lookup ptr with
                | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                | some cell =>
                  cases cell with
                  | byteArray mutableRef fields =>
                    simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                    rcases run with ⟨rfl, rfl⟩
                    refine ⟨target, ?_, related⟩
                    simpa [rev] using doByteBounds_target loose flag mutableRef ptr fields index relocate source target related lookup
                  | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
              | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
            | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
    | el =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
      | cons first tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
        | cons second rest =>
          cases rest with
          | cons other tail => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
          | nil =>
            cases second with
            | number index =>
              cases first with
              | block tag fields =>
                by_cases neg : index < 0
                · simp [BvlSem.doApp, BvlSem.applyMemory, rev, neg] at run
                · cases selected : fields[index.toNat]? with
                  | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, neg, selected] at run
                  | some value =>
                    simp [BvlSem.doApp, BvlSem.applyMemory, rev, neg, selected] at run
                    rcases run with ⟨rfl, rfl⟩
                    refine ⟨target, ?_, related⟩
                    simpa [rev] using doBlockElement_target tag fields index value relocate target neg selected
              | refPtr flag ptr =>
                cases lookup : source.refs.lookup ptr with
                | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                | some cell =>
                  cases cell with
                  | valueArray fields =>
                    by_cases neg : index < 0
                    · simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, neg] at run
                    · cases selected : fields[index.toNat]? with
                      | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, neg, selected] at run
                      | some value =>
                        simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, neg, selected] at run
                        rcases run with ⟨rfl, rfl⟩
                        refine ⟨target, ?_, related⟩
                        simpa [rev] using doArrayElement_target flag ptr fields index value relocate source target related lookup neg selected
                  | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
              | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
            | _ => all_goals cases first <;> simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
    | derefByte =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
      | cons first tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
        | cons second rest =>
          cases rest with
          | cons other tail => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
          | nil =>
            cases second with
            | number index =>
              cases first with
              | refPtr flag ptr =>
                cases lookup : source.refs.lookup ptr with
                | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                | some cell =>
                  cases cell with
                  | byteArray mutableRef fields =>
                    by_cases neg : index < 0
                    · simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, neg] at run
                    · cases selected : fields[index.toNat]? with
                      | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, neg, selected] at run
                      | some value =>
                        simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, neg, selected] at run
                        rcases run with ⟨rfl, rfl⟩
                        refine ⟨target, ?_, related⟩
                        simpa [rev] using doByteRead_target flag mutableRef ptr fields index value relocate source target related lookup neg selected
                  | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
              | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
            | _ => all_goals cases first <;> simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
    | update =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
      | cons first tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
        | cons second rest =>
          cases rest with
          | nil => cases first <;> cases second <;> simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
          | cons value rest =>
            cases rest with
            | cons other tail => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
            | nil =>
              cases first with
              | refPtr flag ptr =>
                cases second with
                | number index =>
                  cases lookup : source.refs.lookup ptr with
                  | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                  | some cell =>
                    cases cell with
                    | valueArray fields =>
                      by_cases invalid : index < 0 ∨ index.toNat ≥ fields.length
                      · simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, invalid] at run
                      · simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, invalid] at run
                        rcases run with ⟨rfl, rfl⟩
                        have present : source.refs.lookup ptr ≠ none := by rw [lookup]; simp
                        have relatedWrite := stateRel_updateExisting relocate source target ptr
                          (.valueArray (fields.set index.toNat value)) related present
                        refine ⟨{ target with refs := target.refs.updateEq (relocate ptr,
                          .valueArray ((fields.set index.toNat value).map (adjustBv relocate))) }, ?_, ?_⟩
                        · simpa [rev] using doArrayUpdate_target flag ptr fields index value relocate source target related lookup invalid
                        · simpa [adjustRef] using relatedWrite
                    | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
              | _ => all_goals cases second <;> simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
    | updateByte =>
      cases rev : args.reverse with
      | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
      | cons first tail =>
        cases tail with
        | nil => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
        | cons second rest =>
          cases rest with
          | nil => cases first <;> cases second <;> simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
          | cons value rest =>
            cases rest with
            | cons other tail => simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
            | nil =>
              cases value with
              | number byte =>
                cases first with
                | refPtr flag ptr =>
                  cases second with
                  | number index =>
                    cases lookup : source.refs.lookup ptr with
                    | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                    | some cell =>
                      cases cell with
                      | byteArray mutableRef fields =>
                        by_cases invalid : index < 0 ∨ index.toNat ≥ fields.length
                        · simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, invalid] at run
                        · cases decoded : ClosSem.intToByte byte with
                          | none => simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, invalid, decoded] at run
                          | some byteValue =>
                            simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup, invalid, decoded] at run
                            rcases run with ⟨rfl, rfl⟩
                            have present : source.refs.lookup ptr ≠ none := by rw [lookup]; simp
                            have relatedWrite := stateRel_updateExisting relocate source target ptr
                              (.byteArray mutableRef (fields.set index.toNat byteValue)) related present
                            refine ⟨{ target with refs := target.refs.updateEq (relocate ptr,
                              .byteArray mutableRef (fields.set index.toNat byteValue)) }, ?_, ?_⟩
                            · simpa [rev] using doByteUpdate_target flag mutableRef ptr fields index byte byteValue relocate source target related lookup invalid decoded
                            · simpa [adjustRef] using relatedWrite
                      | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev, lookup] at run
                  | _ => all_goals simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
                | _ => all_goals cases second <;> simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
              | _ => all_goals cases first <;> cases second <;> simp [BvlSem.doApp, BvlSem.applyMemory, rev] at run
    | configGC =>
      cases app : BvlSem.applyMemory .configGC args.reverse source with
      | none => simp [BvlSem.doApp, app] at run
      | some pair =>
        obtain ⟨value, state⟩ := pair
        obtain ⟨left, right, argsEq, valueEq, stateEq⟩ :=
          configGC_shape args.reverse source state value app
        subst state
        subst value
        simp [BvlSem.doApp, app] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, ?_, related⟩
        rw [argsEq]
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyMemory, BviSem.fromBvl_toBvl, adjustBv, BvlSem.unitValue, adjustValues]
    | stringCmp fast cmp =>
      cases app : BvlSem.applyMemory (.stringCmp fast cmp) args.reverse source with
      | none => simp [BvlSem.doApp, app] at run
      | some pair =>
        obtain ⟨value, state⟩ := pair
        obtain ⟨lf, left, rf, right, leftFlag, leftBytes, rightFlag, rightBytes,
          argsEq, leftLookup, rightLookup, valueEq, stateEq⟩ :=
          stringCmp_shape fast cmp args.reverse source state value app
        subst state
        subst value
        simp [BvlSem.doApp, app] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, ?_, related⟩
        rw [argsEq]
        exact doStringCmp_target fast cmp relocate source target lf left rf right
          leftFlag leftBytes rightFlag rightBytes related leftLookup rightLookup
  | ffi name =>
    cases rev : args.reverse with
    | nil => simp [BvlSem.doApp, rev] at run
    | cons first tail =>
      cases tail with
      | nil => simp [BvlSem.doApp, rev] at run
      | cons second rest =>
        cases rest with
        | cons other tail => simp [BvlSem.doApp, rev] at run
        | nil =>
          cases first with
          | refPtr configFlag configPtr =>
            cases second with
            | refPtr flag ptr =>
              cases configLookup : source.refs.lookup configPtr with
              | none => simp [BvlSem.doApp, rev, configLookup] at run
              | some configCell =>
                cases configCell with
                | byteArray configMutable config =>
                  cases configMutable with
                  | false => simp [BvlSem.doApp, rev, configLookup] at run
                  | true =>
                    cases bytesLookup : source.refs.lookup ptr with
                    | none => simp [BvlSem.doApp, rev, configLookup, bytesLookup] at run
                    | some bytesCell =>
                      cases bytesCell with
                      | byteArray mutableFlag bytes =>
                        cases mutableFlag with
                        | true => simp [BvlSem.doApp, rev, configLookup, bytesLookup] at run
                        | false =>
                          have targetConfig := stateRel_byteArray relocate source target true config configPtr related configLookup
                          have targetBytes := stateRel_byteArray relocate source target false bytes ptr related bytesLookup
                          have ffiEq : source.ffi = target.ffi := related.2.1
                          cases ffiRun : callFFIHOL source.ffi (.extCall name) config bytes with
                          | ret ffi updated =>
                            simp [BvlSem.doApp, rev, configLookup, bytesLookup, ffiRun] at run
                            rcases run with ⟨rfl, rfl⟩
                            have present : source.refs.lookup ptr ≠ none := by rw [bytesLookup]; simp
                            have relatedWrite := stateRel_updateExisting relocate source target ptr
                              (.byteArray false updated) related present
                            have relatedFfi := stateRel_setFfi relocate _ _ ffi relatedWrite
                            refine ⟨{ target with refs := target.refs.updateEq (relocate ptr, .byteArray false updated), ffi := ffi }, ?_, ?_⟩
                            · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
                                BviSem.toBvl, BviSem.fromBvl, adjustBv, BvlSem.unitValue, adjustValues,
                                targetConfig, targetBytes, ← ffiEq, ffiRun]
                            · simpa [adjustRef] using relatedFfi
                          | final event => simp [BvlSem.doApp, rev, configLookup, bytesLookup, ffiRun] at run
                      | _ => all_goals simp [BvlSem.doApp, rev, configLookup, bytesLookup] at run
                | _ => all_goals simp [BvlSem.doApp, rev, configLookup] at run
            | _ => all_goals simp [BvlSem.doApp, rev] at run
          | _ => all_goals cases second <;> simp [BvlSem.doApp, rev] at run
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
