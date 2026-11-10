module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownLabelOracle
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IncrementalAddresses
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileSemantics
import Mathlib.Data.List.Perm.Subperm

@[expose] public section

/-! Address preservation through the known-function optimizer oracle. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps ClosKnown BackendProps

/-- The incremental known-function pass exposes the original traversal result. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "kcompile_inc_uncurry"]
theorem kcompileInc_uncurry {α : Type} (c : ClosKnown.Config) (g : Spt ValApprox)
    (p : List ClosLang.Exp × α) :
    ClosKnown.compileInc c g p =
      ((knownListTotal (resetInlineFactor c) p.1 [] g).2,
        (knownListTotal (resetInlineFactor c) p.1 [] g).1.map Prod.fst, p.2) := by
  cases h : knownListTotal (resetInlineFactor c) p.1 [] g
  simp [ClosKnown.compileInc, h]

/-- Incremental known-function optimization does not add code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_locs_FST_SND_kcompile_inc"]
theorem codeLocations_kcompileInc {α : Type} (c : ClosKnown.Config) (g : Spt ValApprox)
    (p : List ClosLang.Exp × α) :
    ∀ label, (codeLocations (ClosKnown.compileInc c g p).2.1).count label ≤
      (codeLocations p.1).count label := by
  cases h : knownListTotal (resetInlineFactor c) p.1 [] g with
  | mk eas next =>
    have bounded := TraversalCodeBag.knownCodeLocationsBag (resetInlineFactor c) p.1 [] g eas next h
    simpa [kcompileInc_uncurry, h] using bounded

private theorem marker_extract (tr : BackendCommon.Tra) (n : Nat)
    (xs ys : List ClosLang.Exp) (length : ys.length = xs.length) :
    extractedAddrs (.op tr (.intOp (.const (Int.ofNat n))) [] :: ys) =
      extractedAddrs (.op tr (.intOp (.const (Int.ofNat n))) [] :: xs) := by
  have empty : ys = [] ↔ xs = [] := by
    constructor <;> intro h
    · subst ys; cases xs <;> simp_all
    · subst xs; cases ys <;> simp_all
  by_cases h : xs = []
  · have hy : ys = [] := empty.mpr h
    simp [extractedAddrs, extractNameSource_eq_extractName, extractName, h, hy]
  · have hy : ys ≠ [] := fun hy => h (empty.mp hy)
    simp [extractedAddrs, extractNameSource_eq_extractName, extractName, h, hy, length]

private theorem req_subperm_of_locations (xs ys : List ClosLang.Exp)
    (code : List (Nat × Nat × ClosLang.Exp))
    (entry : extractedAddrs ys = extractedAddrs xs)
    (locs : List.Subperm (codeLocations ys) (codeLocations xs)) :
    List.Subperm (reqCompileIncAddrs [Nat.succ] (ys, ([] : List (Nat × Nat × ClosLang.Exp))))
      (reqCompileIncAddrs [Nat.succ] (xs, code)) := by
  have mapped := List.Subperm.map Nat.succ_injective locs
  have core := (List.Subperm.refl (extractedAddrs xs)).append (locs.append mapped)
  have oldSub : (extractedAddrs xs ++ codeLocations xs ++
      (codeLocations xs).map Nat.succ).Sublist
      (reqCompileIncAddrs [Nat.succ] (xs, code)) := by
    simp only [reqCompileIncAddrs, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    simp [List.append_assoc]
  have targetSub : List.Subperm
      (extractedAddrs xs ++ (codeLocations xs ++ (codeLocations xs).map Nat.succ))
      (reqCompileIncAddrs [Nat.succ] (xs, code)) := by
    simpa [List.append_assoc] using oldSub.subperm
  have total := core.trans targetSub
  simpa [reqCompileIncAddrs, entry, codeLocations, List.append_assoc] using total

private def knownPipeline (c : ClosKnown.Config) (g : Spt ValApprox) (xs : List ClosLang.Exp) :
    List ClosLang.Exp :=
  let result := knownListTotal (resetInlineFactor c) (ClosFvs.compile xs) [] g
  ClosLetop.compileList (ClosTicks.removeList (result.1.map Prod.fst))

private theorem knownPipeline_properties (c : ClosKnown.Config) (g : Spt ValApprox)
    (xs : List ClosLang.Exp) (extract : canExtract xs) :
    extractedAddrs (knownPipeline c g xs) = extractedAddrs xs ∧
      canExtract (knownPipeline c g xs) ∧
      List.Subperm (codeLocations (knownPipeline c g xs)) (codeLocations xs) := by
  obtain ⟨tr, n, rest, rfl⟩ := extract
  let marker : ClosLang.Exp := .op tr (.intOp (.const (Int.ofNat n))) []
  let cf := resetInlineFactor c
  let tail := ClosFvs.compile rest
  cases hr : knownListTotal cf tail [] g with
  | mk eas next =>
    have len := knownListTotal_length_eq cf tail [] g eas next hr
    have knownRun : knownListTotal cf (ClosFvs.compile (marker :: rest)) [] g =
        ((marker, .int (Int.ofNat n)) :: eas, next) := by
      simp only [ClosFvs.compile, ClosFvs.removeList]
      change knownListTotal cf (marker :: tail) [] g = _
      rw [knownOpConst, hr]
    have lenTail : (eas.map Prod.fst).length = rest.length := by
      simpa [tail, ClosFvs.compile, ClosFvs.removeList_length] using len
    let resultTail := ClosLetop.compileList (ClosTicks.removeList (eas.map Prod.fst))
    have resultLen : resultTail.length = rest.length := by
      simp [resultTail, ClosLetop.compileList_length, ClosTicks.removeList_length, lenTail]
    have shape : knownPipeline c g (marker :: rest) = marker :: resultTail := by
      change ClosLetop.compileList (ClosTicks.removeList
        ((knownListTotal cf (ClosFvs.compile (marker :: rest)) [] g).1.map Prod.fst)) = _
      rw [knownRun]
      change ClosLetop.compileList (ClosTicks.removeList
        (.op tr (.intOp (.const (Int.ofNat n))) [] :: eas.map Prod.fst)) = _
      have ticks := removeTicks_opConst tr n (eas.map Prod.fst)
      simp only [ClosTicks.removeSource_eq_list] at ticks
      rw [ticks]
      have letop := letOp_opConst tr n (ClosTicks.removeList (eas.map Prod.fst))
      simp only [ClosLetop.compileSource_eq_list] at letop
      exact letop
    have locs := TraversalCodeBag.knownCodeLocationsBag cf (ClosFvs.compile (marker :: rest))
      [] g ((marker, .int (Int.ofNat n)) :: eas) next knownRun
    have subLoc : List.Subperm (codeLocations (knownPipeline c g (marker :: rest)))
        (codeLocations (marker :: rest)) := by
      apply List.subperm_iff_count.mpr
      intro k
      have bound := locs k
      change (codeLocations (ClosLetop.compileList (ClosTicks.removeList
        ((knownListTotal cf (ClosFvs.compile (marker :: rest)) [] g).1.map Prod.fst)))).count k ≤ _
      rw [knownRun]
      simpa [ClosLetop.compileList_codeLocations, ClosTicks.removeList_codeLocations,
        ClosFvs.compile, ClosFvs.removeList_codeLocations] using bound
    constructor
    · rw [shape]
      exact marker_extract tr n rest resultTail resultLen
    · constructor
      · rw [shape]
        exact ⟨tr, n, resultTail, rfl⟩
      · exact subLoc

/-- The known optimizer oracle preserves extractability and address distinctness,
and introduces no required addresses. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "known_co_req"]
theorem knownCo_req {C : Type} (orac : ClosSem.CompileOracle (Spt ValApprox × C))
    (n : Nat) (kc : Option ClosKnown.Config) :
    canExtract (orac n).2.1 →
      ((reqCompileIncAddrs [Nat.succ] (orac n).2).Nodup →
        (reqCompileIncAddrs [Nat.succ] (knownCo kc orac n).2).Nodup) ∧
      canExtract (knownCo kc orac n).2.1 ∧
      {x | x ∈ reqCompileIncAddrs [Nat.succ] (knownCo kc orac n).2} ⊆
        {x | x ∈ reqCompileIncAddrs [Nat.succ] (orac n).2} := by
  intro extract
  cases kc with
  | none =>
    simpa [knownCo, stateCo] using
      (show ((reqCompileIncAddrs [Nat.succ] (orac n).2).Nodup →
        (reqCompileIncAddrs [Nat.succ] (orac n).2).Nodup) ∧
        canExtract (orac n).2.1 ∧
        {x | x ∈ reqCompileIncAddrs [Nat.succ] (orac n).2} ⊆
          {x | x ∈ reqCompileIncAddrs [Nat.succ] (orac n).2} from
        ⟨id, extract, Set.Subset.rfl⟩)
  | some c =>
    have output : (knownCo (some c) orac n).2 =
        (knownPipeline c (orac n).1.1 (orac n).2.1, []) := by
      simp only [knownCo, Function.comp_apply, pureCo, stateCo, ClosFvs.compileInc,
        ClosTicks.compileInc, ClosLetop.compileInc, ClosKnown.compileInc, knownPipeline]
    have properties := knownPipeline_properties c (orac n).1.1 (orac n).2.1 extract
    have sub := req_subperm_of_locations (orac n).2.1
      (knownPipeline c (orac n).1.1 (orac n).2.1) (orac n).2.2 properties.1 properties.2.2
    rw [output]
    constructor
    · intro distinct
      obtain ⟨middle, perm, sublist⟩ := List.subperm_iff.mp sub
      exact sublist.nodup (perm.nodup_iff.mpr distinct)
    · exact ⟨properties.2.1, fun _ h => sub.subset h⟩
end Flapjack.Compiler.Backend.ClosToBvl
