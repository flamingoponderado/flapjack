import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InlineHandoff
import Flapjack.Compiler.Backend.BviInline.Proofs.Pipeline

/-! Label invariants for the executed BVL-to-BVI pipeline. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- All labels emitted by initial lowering are above the data-to-word stubs. -/
theorem compileProgFuel_data_label_bound (fuel optFuel start counter targetStart targetCounter : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (lowered : List (Nat × Nat × Bvi.Exp))
    (run : compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter)) :
    ∀ name ∈ lowered.map Prod.fst, dataNumStubs ≤ name := by
  have equal := (compileProgFuel_eq_source fuel optFuel start counter program).symm.trans run
  have codeEq : stubs (bvlNumStubs + bvlToBviNamespaces * start)
      (globalCountList (program.map (fun (_, _, body) => body))) ++ (compileIncSource counter program).2 = lowered :=
    congrArg (fun p => p.2.1) (Option.some.inj equal)
  intro name member
  rw [← codeEq, List.map_append, List.mem_append] at member
  rcases member with stub | compiled
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp stub
    simp [stubs, allocGlobalLocation, copyGlobalsLocation, initGlobalsLocation, listLengthLocation,
      fromListByteLocation, toListByteLocation, sumListLengthLocation, concatByteLocation] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [dataNumStubs, wordNumStubs, stackNumStubs]
  · rcases compileIncSource_nameRange counter program name compiled with ⟨_, _, eq⟩ | ⟨_, _, _, eq⟩ <;>
      rw [eq] <;> simp [bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs] <;> omega

/-- The production sequence preserves distinct labels and reserves the data
runtime-stub range, provided its BVL input labels are distinct. -/
theorem optimizedLowerTailrecTmcInline_labels
    (bvlFuel inlineLimit cutSize bviFuel optFuel start counter : Nat) (splitSeq enabled tmcEnabled : Bool)
    (program optimized : List (Nat × Nat × Bvl.Exp)) (cache : Spt (Nat × Bvl.Exp))
    (targetStart targetCounter : Nat) (lowered beforeTmc afterTmc output : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (bviCache : Spt (Nat × Bvi.Exp))
    (distinct : (program.map Prod.fst).Nodup)
    (optimizedRun : BvlInline.compileProgFuel bvlFuel inlineLimit cutSize splitSeq program = some (cache, optimized))
    (lowerRun : compileProgFuel bviFuel optFuel start counter optimized = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel bviFuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc))
    (inlineRun : BviInline.compileProgFuel bviFuel afterTmc = some (bviCache, output)) :
    (output.map Prod.fst).Nodup ∧ ∀ name ∈ output.map Prod.fst, dataNumStubs ≤ name := by
  have optimizedDistinct : (optimized.map Prod.fst).Nodup := by
    rw [BvlInline.Proofs.compileProgFuel_names bvlFuel inlineLimit cutSize splitSeq program cache optimized optimizedRun]
    exact distinct
  have condition := lowered_tailrec_tmc_inputCondition_complete bviFuel optFuel start counter targetStart targetCounter
    enabled optimized lowered beforeTmc tailLast optimizedDistinct lowerRun tailRun
  have tmcSource : BviTmc.compileProgSource tmcEnabled (bvlNumStubs + 3) beforeTmc = (tmcLast, afterTmc) := by
    have correspondence := BviTmc.compileProgFuel_eq_source bviFuel tmcEnabled (bvlNumStubs + 3) beforeTmc
    rw [tmcRun] at correspondence
    exact (Option.some.inj correspondence).symm
  have distinctTmc := (BviTmc.compileProgSource_distinct_and_free tmcEnabled (bvlNumStubs + 3) tmcLast
    beforeTmc afterTmc tmcSource condition.2.2.1 condition.1).1
  have lowerBound := compileProgFuel_data_label_bound bviFuel optFuel start counter targetStart targetCounter optimized lowered lowerRun
  have tailBound : ∀ name ∈ beforeTmc.map Prod.fst, dataNumStubs ≤ name := by
    cases enabled with
    | false =>
      simp [BviTailrec.compileProgFuel] at tailRun
      obtain ⟨rfl, rfl⟩ := tailRun
      exact lowerBound
    | true =>
      have equal := (BviTailrec.compileEachFuel_eq_source bviFuel (bvlNumStubs + 2) lowered).symm.trans
        (by simpa [BviTailrec.compileProgFuel] using tailRun)
      have outputEq : (BviTailrec.compileEachSource (bvlNumStubs + 2) lowered).2 = beforeTmc :=
        congrArg Prod.snd (Option.some.inj equal)
      intro name member
      have sourceMember : name ∈ (BviTailrec.compileEachSource (bvlNumStubs + 2) lowered).2.map Prod.fst := by
        simpa [outputEq] using member
      rcases BviTailrec.compileEachSource_mem lowered (bvlNumStubs + 2) name sourceMember with old | ⟨bound, _, _⟩
      · exact lowerBound name old
      · simp [bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs] at bound ⊢; omega
  have tmcBound : ∀ name ∈ afterTmc.map Prod.fst, dataNumStubs ≤ name := by
    intro name member
    rcases BviTmc.compileProgSource_mem tmcEnabled (bvlNumStubs + 3) tmcLast name beforeTmc afterTmc tmcSource member with old | ⟨bound, _, _⟩
    · exact tailBound name old
    · simp [bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs] at bound ⊢; omega
  rw [BviInline.compileProgFuel_names bviFuel afterTmc output bviCache inlineRun]
  exact ⟨distinctTmc, tmcBound⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
