module

public import Flapjack.Compiler.Backend.BvlToBvi.SourcePipeline
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TmcNames
public import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation
public import Flapjack.Compiler.Backend.BvlInline.Proofs.ProgramProperties
public import Flapjack.Compiler.Backend.BviInline.Proofs.CodeLabels

@[expose] public section

/-! Whole BVL-to-BVI function-name distinctness. -/
open Flapjack Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
/-- The whole compiler preserves distinct function names and their lower bound. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_distinct_names"]
theorem compile_distinctNames (start : Nat) (c : BvlToBvi.Config) (names : Spt MlString)
    (prog : List (Nat × Nat × Bvl.Exp)) (loc : Nat) (code : List (Nat × Nat × Bvi.Exp))
    (inlines : Spt (Nat × Bvl.Exp)) (bviInlines : Spt (Nat × Bvi.Exp))
    (n1 n2 : Nat) (last : Nat × Spt MlString) (n02 : Nat)
    (assumptions : compileSource start c names prog = (loc, code, inlines, bviInlines, n1, n2, last) ∧
      (prog.map Prod.fst).Nodup ∧ c.nextName2 = bvlNumStubs + 2 + n02 * bvlToBviNamespaces) :
    (∀ x ∈ code.map Prod.fst, dataNumStubs ≤ x) ∧ (code.map Prod.fst).Nodup := by
  obtain ⟨run, distinct, _⟩ := assumptions
  rcases hi : BvlInline.compileProg c.inlineSizeLimit c.splitMainAtSeq c.expCut prog with ⟨ic, pi⟩
  rcases hl : compileProgSource start 0 pi with ⟨l, p, a⟩
  rcases ht : BviTailrec.compileProgSource c.doTailrec (bvlNumStubs + 2) p with ⟨b, pt⟩
  rcases hm : BviTmc.compileProgSource c.doTmc (bvlNumStubs + 3) pt with ⟨d, pm⟩
  rcases hb : BviInline.compileProgSource pm with ⟨bc, po⟩
  simp only [compileSource, hi, hl, ht, hm, hb, Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have inlineKeys : po.map Prod.fst = pm.map Prod.fst :=
    BviInline.Proofs.compileInc_mapFst .ln bc pm po (by simpa [BviInline.compileProgSource] using hb)
  have piDistinct : (pi.map Prod.fst).Nodup := by
    rw [BvlInline.Proofs.compileProg_names _ _ _ _ _ _ hi]
    exact distinct
  have pCondition : BviTailrec.inputCondition (bvlNumStubs + 2) p := by
    apply compileProgFuel_production_tailrec_inputCondition 0 0 start 0 l a pi p piDistinct
    simp [compileProgFuel, hl]
  have ptDistinct : (pt.map Prod.fst).Nodup := by
    apply tailrec_output_names_nodup 0 c.doTailrec (bvlNumStubs + 2) b p pt pCondition
    simp [BviTailrec.compileProgFuel_eq_source, ht]
  have pOutside : ∀ x ∈ p.map Prod.fst, bvlNumStubs ≤ x → ¬BviTmc.inWorkerNamespace x := by
    intro name member above worker
    have bound := compileProgSource_avoidsNss3 start 0 l a name pi p ⟨hl, piDistinct, worker, member⟩
    have stubMod := bvlNumStubMod
    unfold BviTmc.inWorkerNamespace at worker
    simp only [bvlToBviNamespaces] at stubMod worker
    omega
  have ptOutside : ∀ x ∈ pt.map Prod.fst, bvlNumStubs ≤ x → ¬BviTmc.inWorkerNamespace x := by
    apply tailrec_output_outside_tmc_namespace 0 c.doTailrec (bvlNumStubs + 2) b p pt
      production_tailrec_start_valid.2 pOutside
    simp [BviTailrec.compileProgFuel_eq_source, ht]
  have ptFree : ∀ entry ∈ pt, BviTmc.freeNames (bvlNumStubs + 3) entry.1 := by
    intro entry mem k equal
    by_cases small : entry.1 < bvlNumStubs
    · omega
    · have outside := ptOutside entry.1 (List.mem_map.mpr ⟨entry, mem, rfl⟩) (by omega)
      apply outside
      rw [← equal]
      unfold BviTmc.inWorkerNamespace
      have stubMod := bvlNumStubMod
      simp only [bvlToBviNamespaces] at stubMod ⊢
      omega
  have pmDistinct := (BviTmc.compileProgSource_distinct_and_free c.doTmc (bvlNumStubs + 3) d pt pm hm ptDistinct ptFree).1
  have pEq : p = stubs (bvlNumStubs + bvlToBviNamespaces * start)
      (globalCountList (pi.map (fun q => q.2.2))) ++ (compileIncSource 0 pi).2 := by
    have h := compileProgFuel_eq_source 0 0 start 0 pi
    rw [compileProgFuel, hl] at h
    simpa only [Prod.fst, Prod.snd] using
      (congrArg (fun q => q.2.1) (Option.some.inj h))
  have pLower : ∀ x ∈ p.map Prod.fst, dataNumStubs ≤ x := by
    rw [pEq, List.map_append]
    intro x hx
    rcases List.mem_append.mp hx with stub | lowered
    · simp [stubs, allocGlobalLocation, copyGlobalsLocation, initGlobalsLocation,
        listLengthLocation, fromListByteLocation, toListByteLocation,
        sumListLengthLocation, concatByteLocation] at stub
      rcases stub with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · rcases compileIncSource_nameRange 0 pi x lowered with ⟨_, _, eq⟩ | ⟨_, _, _, eq⟩ <;>
        rw [eq] <;> simp [bvlNumStubs] <;> omega
  have ptLower : ∀ x ∈ pt.map Prod.fst, dataNumStubs ≤ x := by
    intro x hx
    cases flag : c.doTailrec with
    | false =>
      simp [BviTailrec.compileProgSource, flag] at ht
      obtain ⟨_, rfl⟩ := ht
      exact pLower x hx
    | true =>
      have tailEq : BviTailrec.compileEachSource (bvlNumStubs + 2) p = (b, pt) := by
        simpa [BviTailrec.compileProgSource, flag] using ht
      have member : x ∈ (BviTailrec.compileEachSource (bvlNumStubs + 2) p).2.map Prod.fst := by
        simpa only [tailEq] using hx
      rcases BviTailrec.compileEachSource_mem p (bvlNumStubs + 2) x member with old | ⟨lower, _, _⟩
      · exact pLower x old
      · simp [bvlNumStubs] at lower
        omega
  constructor
  · intro x hx
    rw [inlineKeys] at hx
    rcases BviTmc.compileProgSource_mem c.doTmc (bvlNumStubs + 3) d x pt pm hm hx with old | ⟨lower, _, _⟩
    · exact ptLower x old
    · simp [bvlNumStubs] at lower
      omega
  · simpa only [inlineKeys] using pmDistinct
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
