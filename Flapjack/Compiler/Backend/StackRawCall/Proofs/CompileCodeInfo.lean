import Flapjack.Compiler.Backend.StackRawCall
import Flapjack.Compiler.Backend.StackRawCall.Proofs.StateOk
import Flapjack.Misc.Sptree.ToAList

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Source-local association-list consequence of successful-lookup membership.
Flapjack infrastructure without a separate HOL declaration. -/
private theorem aListLookupNoneOfNotMem {α : Type} (key : Nat)
    (entries : List (Nat × α)) (absent : key ∉ entries.map Prod.fst) :
    sptAListLookup key entries = none := by
  cases found : sptAListLookup key entries with
  | none => rfl
  | some value =>
      have member := sptAListLookup_mem key entries value found
      exact False.elim (absent (List.mem_map.mpr ⟨(key, value), member, rfl⟩))

/-- Full original unconditional code-domain preservation, including duplicate
keys and arbitrary programs. Native Spt and List carriers are unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem domainFromAListCompile {width : Nat} [NeZero width]
    (code : List (Nat × HolProg width)) :
    sptDomain (sptFromAList (compile code)) = sptDomain (sptFromAList code) := by
  simp only [sptDomainFromAList, compile, List.map_map]
  rfl

/-- Full original lookup law with exactly the ALL_DISTINCT key guard.
The supplied rest map is arbitrary; no canonical or well-formedness premise
is added. List/Spt and all positive word dimensions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem lookupCollectInfo {width : Nat} [NeZero width]
    (code : List (Nat × HolProg width)) (key : Nat) (rest : Spt Nat)
    (distinct : (code.map Prod.fst).Nodup) :
    sptLookup key (collectInfo code rest) =
      match sptAListLookup key code with
      | none => sptLookup key rest
      | some body => sptLookup key (collectInfo [(key, body)] rest) := by
  induction code generalizing rest with
  | nil => rfl
  | cons entry code ih =>
      obtain ⟨name, body⟩ := entry
      simp only [List.map_cons, List.nodup_cons] at distinct
      obtain ⟨absent, distinct⟩ := distinct
      rw [collectInfo, ih _ distinct]
      by_cases equal : key = name
      · subst key
        rw [aListLookupNoneOfNotMem name code absent]
        simp [sptAListLookup, collectInfo]
      · cases frame : seqStackAlloc body with
        | none => simp only [sptAListLookup, equal, if_false]
        | some size =>
            cases found : sptAListLookup key code with
            | none =>
                simp only [found, sptAListLookup, equal, if_false,
                  sptLookup_sptInsert_ne name key size rest equal]
            | some chosen =>
                cases chosenFrame : seqStackAlloc chosen <;>
                  simp [found, sptAListLookup, equal, collectInfo, chosenFrame,
                    sptLookup_sptInsert_same, sptLookup_sptInsert_ne name key size rest equal]

/-- Full original collected-frame invariant. Distinct source keys are the only
guard; every recorded size has the literal leading Seq(StackAlloc size) witness
in the original code map. Zero frames and arbitrary remaining bodies are kept. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateOkCollectInfo {width : Nat} [NeZero width]
    (code : List (Nat × HolProg width)) (distinct : (code.map Prod.fst).Nodup) :
    stateOk (collectInfo code .ln) (sptFromAList code) := by
  intro key size recorded
  rw [lookupCollectInfo code key .ln distinct] at recorded
  cases found : sptAListLookup key code with
  | none => simp [found, sptLookup] at recorded
  | some program =>
      simp only [found, collectInfo] at recorded
      cases frame : seqStackAlloc program with
      | none => simp [frame] at recorded
      | some allocated =>
          simp only [frame, sptLookup_sptInsert_same, Option.some.injEq] at recorded
          subst allocated
          cases program <;> simp only [seqStackAlloc] at frame
          all_goals try contradiction
          rename_i first body
          cases first <;> simp only at frame
          all_goals try contradiction
          rename_i actual
          simp only [Option.some.injEq] at frame
          subst actual
          exact ⟨body, by rw [sptLookup_sptFromAList]; exact found⟩

end Flapjack.Compiler.Backend.StackRawCall
