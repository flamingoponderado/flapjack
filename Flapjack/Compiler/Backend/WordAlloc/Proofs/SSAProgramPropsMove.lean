import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMoveFrames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full HOL Move case of the program allocation/map invariant. The original
compiler-output equality and map/allocation premises imply all three output
properties. Bounds/nonphysicality for filtered force-renaming pairs follow
from the actual arithmetic generated names; no distinctness or validity premise
is added. This is the original nonrecursive Move case, with no induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props"
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransPropsMove {width : Nat} [NeZero width]
    (priority : Nat) (moves : List (Nat × Nat)) (ssa : Spt Nat) (next : Nat)
    (loopTables : List (Spt Nat × Spt Unit × Spt Unit))
    (output : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : ssaCcTrans (.move priority moves) ssa next loopTables =
      (output, ssaOut, nextOut))
    (h : ssaMapOK next ssa ∧ isAllocVar next) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut ssaOut := by
  let names := moves.map Prod.fst
  generalize renamed : listNextVarRename names ssa next = result
  rcases result with ⟨registers, tree, counter⟩
  have frame := listNextVarRenameProps names ssa next registers tree counter renamed
    ⟨Or.inl h.2, h.1⟩
  have shape := listNextVarRenameLemma1 names ssa next registers tree counter renamed
  have bounds : ∀ register ∈ registers, register < counter ∧ ¬ isPhyVar register := by
    intro register member
    rw [shape.2.1] at member
    obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp member
    have indexBound := List.mem_range.mp inRange
    have allocated : isAllocVar (4 * index + next) := by
      simpa [isAllocVar, Nat.add_mod, Nat.mul_mod] using h.2
    constructor
    · rw [shape.2.2]; omega
    · simp only [isAllocVar, decide_eq_true_eq] at allocated
      simp only [isPhyVar, decide_eq_true_eq]; omega
  have forceBound : ∀ pair ∈ ((moves.map Prod.snd).zip registers).filter
      (fun (name, _) => decide (name ∉ names)), pair.2 < counter ∧ ¬ isPhyVar pair.2 := by
    intro pair member
    have zipped := (List.mem_filter.mp member).1
    have second := (List.of_mem_zip zipped).2
    exact bounds pair.2 second
  have forced := ssaMapOKForceRename counter _ tree ⟨frame.2.2.2, forceBound⟩
  dsimp only [names] at renamed
  simp only [ssaCcTrans, renamed, Prod.mk.injEq] at produced
  obtain ⟨_, rfl, rfl⟩ := produced
  exact ⟨frame.1, frame.2.1 h.2, forced⟩

end Flapjack.Compiler.Backend.WordAlloc
