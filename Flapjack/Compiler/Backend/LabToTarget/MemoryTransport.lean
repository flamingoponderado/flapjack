import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Misc.BytesInMemory
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack

/-- Full original byte-region transport. Machine state and projection types
remain independent; memory agreement is needed only on the source domain,
including wrapped addresses. No target execution or global-memory equality is
assumed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "bytes_in_memory_eq_mem" (words_as_type_indexed_bitvec)]
theorem bytesInMemory_eqMem {width : Nat} [NeZero width]
    {machine projection : Type} (pc : BitVec width) (bytes : List (BitVec 8))
    (mcConf : MachineConfig width machine projection) (ms1 : machine)
    (t1 : AsmState width) :
    (∀ a, t1.memDomain a → mcConf.target.getByte ms1 a = t1.mem a) ∧
      bytesInMemoryHOL pc bytes t1.mem t1.memDomain →
    bytesInMemoryHOL pc bytes (mcConf.target.getByte ms1) t1.memDomain := by
  induction bytes generalizing pc with
  | nil => intro _; trivial
  | cons byte bytes ih =>
    rintro ⟨hm,hb⟩
    rcases hb with ⟨hbyte,hdom,ht⟩
    exact ⟨(hm pc hdom).trans hbyte,hdom,ih (pc+1) ⟨hm,ht⟩⟩
end Flapjack.Compiler.Backend.LabToTarget
