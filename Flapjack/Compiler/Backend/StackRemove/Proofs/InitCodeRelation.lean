import Flapjack.Compiler.Backend.StackRemove.Compile
import Flapjack.Compiler.Backend.StackRemove.Proofs.CodeRelation
import Flapjack.Compiler.Backend.StackRemove.Proofs.ProgCompEta
import Flapjack.Misc.Sptree.ToAList

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeRelation
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Flapjack first-match lookup infrastructure; duplicate labels are allowed. -/
private theorem lookupMem {α : Type} (name : Nat) (value : α)
    (entries : List (Nat × α)) (found : sptAListLookup name entries = some value) :
    (name, value) ∈ entries := by
  induction entries with
  | nil => simp [sptAListLookup] at found
  | cons entry rest ih =>
    obtain ⟨key, candidate⟩ := entry
    by_cases same : name = key
    · simp [sptAListLookup, same] at found
      subst key
      subst candidate
      exact List.mem_cons_self
    · simp [sptAListLookup, same] at found
      exact List.mem_cons_of_mem _ (ih found)

/-- Flapjack first-match lookup commutes with mapping values, without a
distinct-label premise or any assumption about the returned value. -/
private theorem lookupMap {α β : Type} (f : α → β) (name : Nat)
    (entries : List (Nat × α)) :
    sptAListLookup name (entries.map fun p => (p.1, f p.2)) =
      (sptAListLookup name entries).map f := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    by_cases same : name = key <;> simp [sptAListLookup, same, ih]

/-- Full original compiled-table relation. The original EVERY bounds/stub
condition and definition of the compiled target table are the only premises.
Both lookup preservation and the complete target-domain equality are derived.
The word carrier translation is the only representation difference: code
tables use the original Spt and association lists retain first-match lookup. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem impCodeRel {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) (source : List (Nat × HolProg width))
    (target : Spt (HolProg width))
    (hypothesis : (∀ entry ∈ source,
      StackProps.regBound entry.2 pointer ∧ stackNumStubs ≤ entry.1 + 1) ∧
      target = sptFromAList (compileHOL jump bounds generateGc maximumHeap pointer start source)) :
    codeRelHOL jump bounds pointer (sptFromAList source) target := by
  rcases hypothesis with ⟨valid, rfl⟩
  constructor
  · intro name program found
    rw [sptLookup_sptFromAList] at found
    obtain ⟨bounded, fresh⟩ := valid (name, program) (lookupMem name program source found)
    have notZero : name ≠ 0 := by simp [stackNumStubs] at fresh; omega
    have notOne : name ≠ 1 := by simp [stackNumStubs] at fresh; omega
    have notTwo : name ≠ 2 := by simp [stackNumStubs] at fresh; omega
    refine ⟨bounded, ?_⟩
    rw [sptLookup_sptFromAList]
    simpa [compileHOL, initStubs, sptAListLookup, notZero, notOne, notTwo,
      progCompEta, found] using lookupMap (comp jump bounds pointer) name source
  · rw [sptDomainFromAList, sptDomainFromAList]
    funext name
    apply propext
    simp [compileHOL, initStubs, progComp, List.map_map]
    simp only [or_comm, or_assoc]

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeRelation
