import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveFrame
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMoveFrames

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full HOL reconciliation allocation and map bounds. Its output equality is
an equality for the native compiler definition, not an evaluation hypothesis.
Allocation and both input map bounds are the original premises; the returned
counter is monotone, remains allocated, and bounds the returned SSA map. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fixInconsistenciesProps {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (leftMap rightMap : Spt Nat) (next : Nat)
    (leftProg rightProg : WordLangProgHOL (BitVec width)) (nextOut : Nat) (outputMap : Spt Nat)
    (compiled : fixInconsistencies prio leftMap rightMap next =
      (leftProg, rightProg, nextOut, outputMap))
    (h : isAllocVar next ∧ ssaMapOK next leftMap ∧ ssaMapOK next rightMap) :
    next ≤ nextOut ∧ isAllocVar nextOut ∧ ssaMapOK nextOut outputMap := by
  let names := (sptToAList (sptUnion leftMap rightMap)).map Prod.fst
  have merged := mergeMovesFrame names next leftMap rightMap h.1
  generalize hm : mergeMoves names leftMap rightMap next = result at merged
  rcases result with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
  dsimp only at merged
  obtain ⟨allocated, bound, leftOK, rightOK⟩ := merged
  have faked := fakeMovesFrame (width := width) prio names counter leftTree rightTree allocated
  generalize hf : fakeMoves (width := width) prio names leftTree rightTree counter = result at faked
  rcases result with ⟨leftSeq, rightSeq, outputCounter, outputLeft, outputRight⟩
  dsimp only at faked
  obtain ⟨outAllocated, outBound, outLeftOK, _⟩ := faked
  dsimp only [names] at hm hf
  simp only [fixInconsistencies, hm, hf, Prod.mk.injEq] at compiled
  obtain ⟨_, _, rfl, rfl⟩ := compiled
  exact ⟨Nat.le_trans bound outBound, outAllocated, outLeftOK (leftOK h.2.1)⟩

end Flapjack.Compiler.Backend.WordAlloc
