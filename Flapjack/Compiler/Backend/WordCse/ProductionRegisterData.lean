import Flapjack.Compiler.Backend.WordCse.ProductionKnowledge
import Flapjack.Compiler.Backend.WordCse.RegisterData
import Std.Data.TreeMap.Lemmas

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Sparse insertion and executed ordered-map insertion have identical lookup
observations on related inputs, including overwrite and unequal-key cases.
Flapjack representation infrastructure, with no independent HOL original. -/
private theorem insertLookup_transport (native : Spt Nat) (executed : WordCseRegMap)
    (related : ∀ register, sptLookup register native = executed[register]?)
    (key value : Nat) :
    ∀ register, sptLookup register (sptInsert key value native) =
      (wordCseInsert key value executed)[register]? := by
  intro register
  by_cases same : register = key
  · subst register
    simp [wordCseInsert, sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne key register value native same]
    simp only [wordCseInsert, Std.TreeMap.getElem?_insert, Nat.compare_eq_eq,
      Ne.symm same, if_false]
    exact related register

/-- Original odd-register tracking establishes all five output observations.
Only the input relation is assumed; unchanged fields are retained exactly.
This is actual API transport, not full CSE evaluation or production routing. -/
theorem registerRead_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (register : Nat) :
    KnowledgeRel width (registerRead native register) (wordCseRegisterRead executed register) := by
  unfold registerRead wordCseRegisterRead
  rw [keepData_transport native executed related register]
  split
  · exact ⟨insertLookup_transport _ _ related.1 register register, related.2⟩
  · exact related

/-- Literal recursive native register reads agree with the actual left fold,
for arbitrary lists and complete related knowledge states. -/
theorem registerReads_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (registers : List Nat) :
    KnowledgeRel width (registerReads native registers) (wordCseRegisterReads executed registers) := by
  induction registers generalizing native executed with
  | nil => simpa [registerReads, wordCseRegisterReads] using related
  | cons register registers ih =>
      change KnowledgeRel width (registerReads (registerRead native register) registers)
        (wordCseRegisterReads (wordCseRegisterRead executed register) registers)
      exact ih _ _ (registerRead_transport native executed related register)

/-- Both missing/default and present canonical-register lookups are preserved. -/
theorem canonicalRegs_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (register : Nat) :
    canonicalRegs native register = wordCseCanonicalRegs executed register := by
  simp only [canonicalRegs, wordCseCanonicalRegs, wordCseLookupAny, related.1 register]

/-- The original avoid-register branch retains its result on related inputs. -/
theorem canonicalRegsAvoid_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (avoid register : Nat) :
    canonicalRegs' avoid native register = wordCseCanonicalRegs' avoid executed register := by
  simp only [canonicalRegs', wordCseCanonicalRegs',
    canonicalRegs_transport native executed related register]

/-- Original MAP preserves order and duplicates under the actual canonical
lookup; this is a producer observation, not a new executed helper definition. -/
theorem canonicalMultRegs_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (registers : List Nat) :
    canonicalMultRegs native registers = registers.map (wordCseCanonicalRegs executed) := by
  unfold canonicalMultRegs
  apply List.map_congr_left
  intro register _
  exact canonicalRegs_transport native executed related register

/-- Source tail-first sparse-map insertion agrees with the actual right fold.
Repeated keys overwrite in the same order; no output-map relation is assumed. -/
theorem mapInsert_transport (native : Spt Nat) (executed : WordCseRegMap)
    (related : ∀ register, sptLookup register native = executed[register]?)
    (entries : List (Nat × Nat)) :
    ∀ register, sptLookup register (mapInsert entries native) =
      (wordCseMapInsert entries executed)[register]? := by
  induction entries with
  | nil => simpa [mapInsert, wordCseMapInsert] using related
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      exact insertLookup_transport _ _ ih key value

end Flapjack.Compiler.Backend.WordCse
