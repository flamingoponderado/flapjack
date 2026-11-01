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

/-- Cutting before a move keeps the source binding and yields an environment
whose moved result extends the original post-move cut. -/
theorem cutEnv_before_move {α : Type} (source target : Spt α) (names : NumSet)
    (dest src : Nat) (value : α) (result : Spt α)
    (included : sptSubspt source target) (read : sptLookup src source = some value)
    (cut : cutEnv names (sptInsert dest value source) = some result) :
    ∃ before, cutEnv (sptInsert src () (sptDelete dest names)) target = some before ∧
      sptLookup src before = some value ∧ sptSubspt result (sptInsert dest value before) := by
  classical
  have postPresent : ∀ key, sptMem key names → sptMem key (sptInsert dest value source) := by
    unfold cutEnv at cut
    split at cut
    · assumption
    · simp at cut
  have targetRead : sptLookup src target = some value := (sptSubsptLookup _ _).1 included src value read
  let preNames := sptInsert src () (sptDelete dest names)
  have prePresent : ∀ key, sptMem key preNames → sptMem key target := by
    intro key member
    rcases (sptMem_sptInsert key src () _).1 member with same | rest
    · subst key
      simp [sptMem, sptDomain, targetRead]
    · have other : key ≠ dest := by
        intro same
        subst key
        simp [sptMem, sptDomain, sptLookup_sptDelete] at rest
      have post := postPresent key (by simpa [sptMem, sptDomain, sptLookup_sptDelete, other] using rest)
      have sourceMember : sptMem key source := by
        simpa [sptMem_sptInsert, other] using post
      exact (included key sourceMember).1
  let before := sptMkWf (sptInter target preNames)
  have beforeCut : cutEnv preNames target = some before := by
    simp only [cutEnv, if_pos prePresent]
    rfl
  have beforeRead : sptLookup src before = some value := by
    rw [DataLive.cutEnv_lookup preNames target before beforeCut src]
    have member : sptMem src preNames := (sptMem_sptInsert src src () _).2 (Or.inl rfl)
    simp [member, targetRead]
  refine ⟨before, beforeCut, beforeRead, ?_⟩
  rw [sptSubsptLookup]
  intro key found resultRead
  by_cases same : key = dest
  · subst key
    rw [sptLookup_sptInsert_same]
    rw [DataLive.cutEnv_lookup names (sptInsert dest value source) result cut dest] at resultRead
    by_cases member : sptMem dest names <;> simp [member, sptLookup_sptInsert_same] at resultRead
    exact congrArg some resultRead
  · rw [sptLookup_sptInsert_ne dest key value before same]
    rw [DataLive.cutEnv_lookup names (sptInsert dest value source) result cut key] at resultRead
    by_cases member : sptMem key names
    · have preMember : sptMem key preNames := by
        apply (sptMem_sptInsert key src () _).2
        right
        simpa [sptMem, sptDomain, sptLookup_sptDelete, same] using member
      have sourceRead : sptLookup key source = some found := by
        simpa [member, sptLookup_sptInsert_ne dest key value source same] using resultRead
      have targetFound := (sptSubsptLookup _ _).1 included key found sourceRead
      rw [DataLive.cutEnv_lookup preNames target before beforeCut key]
      simp [preMember, targetFound]
    · simp [member] at resultRead

end Flapjack.Compiler.Backend.DataSpace
