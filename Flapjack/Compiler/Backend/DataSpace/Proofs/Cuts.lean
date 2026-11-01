import Flapjack.Compiler.Backend.DataSpace.Proofs.State
import Flapjack.Compiler.Backend.DataLive.Proofs.State

/-! Sparse-tree cuts used when reservations are combined. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Normalizing a sparse tree produces a well-formed tree. This helper is
Flapjack infrastructure for comparing the results of two environment cuts. -/
theorem sptWf_normalize {α : Type} (tree : Spt α) : sptWf (sptMkWf tree) = true := by
  induction tree with
  | ln => rfl
  | ls value => rfl
  | bn left right ihLeft ihRight =>
    simp only [sptMkWf]
    cases hleft : sptMkWf left <;> cases hright : sptMkWf right <;>
      simp_all [sptMkBN, sptWf, sptIsEmpty]
  | bs left value right ihLeft ihRight =>
    simp only [sptMkWf]
    cases hleft : sptMkWf left <;> cases hright : sptMkWf right <;>
      simp_all [sptMkBS, sptWf, sptIsEmpty]

/-- Two successful cuts equal a single cut by the intersection. -/
theorem cutEnv_twice {α : Type} (first second : NumSet) (source middle result : Spt α)
    (firstCut : cutEnv first source = some middle)
    (secondCut : cutEnv second middle = some result) :
    cutEnv (sptInter first second) source = some result := by
  classical
  have middleLookup := DataLive.cutEnv_lookup first source middle firstCut
  have resultLookup := DataLive.cutEnv_lookup second middle result secondCut
  have present : ∀ key, sptMem key (sptInter first second) → sptMem key source := by
    intro key member
    have both := (DataLive.mem_inter first second key).1 member
    unfold cutEnv at firstCut
    split at firstCut
    · rename_i allPresent
      exact allPresent key both.1
    · simp at firstCut
  let target := sptMkWf (sptInter source (sptInter first second))
  have targetCut : cutEnv (sptInter first second) source = some target := by
    simp only [cutEnv, if_pos present]
    rfl
  have resultWf : sptWf result = true := by
    unfold cutEnv at secondCut
    split at secondCut
    · simp only [Option.some.injEq] at secondCut
      subst result
      exact sptWf_normalize _
    · simp at secondCut
  have targetWf : sptWf target = true := sptWf_normalize _
  have eq : result = target := by
    apply (sptEqThm result target ⟨resultWf, targetWf⟩).2
    intro key
    rw [resultLookup key, middleLookup key, DataLive.cutEnv_lookup (sptInter first second) source target targetCut key]
    by_cases a : sptMem key first <;> by_cases b : sptMem key second <;>
      simp [a, b, DataLive.mem_inter]
  simpa [← eq] using targetCut

end Flapjack.Compiler.Backend.DataSpace
