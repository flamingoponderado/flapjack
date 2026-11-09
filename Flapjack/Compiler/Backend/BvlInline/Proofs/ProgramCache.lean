import Flapjack.Compiler.Backend.BvlInline.Proofs.ProgramProduction
import Flapjack.Misc.Sptree.Subspt

/-! Cache invariants for BVL program inlining. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Bvl

/-- Inlining may add a cache key only if it occurs among the input labels.
This helper corresponds to a local argument in the HOL proof and has no
standalone exported HOL declaration. -/
theorem tickInlineAll_cacheDomain (limit : Nat) (program : List (Nat × Nat × Exp))
    (cache : Spt (Nat × Exp)) (acc : List (Nat × Nat × Exp)) (key : Nat) :
    sptMem key (tickInlineAll limit cache program acc).1 →
      sptMem key cache ∨ key ∈ program.map Prod.fst := by
  induction program generalizing cache acc with
  | nil => simp [tickInlineAll]
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp only [tickInlineAll]
    split
    · intro present
      have h := ih (sptInsert name (arity, tickInlineSing cache body) cache)
        ((name, arity, tickInlineSing cache body) :: acc) present
      simp only [List.map_cons, List.mem_cons]
      rcases h with inserted | restMember
      · rcases (sptMem_sptInsert key name _ cache).1 inserted with same | old
        · exact Or.inr (Or.inl same)
        · exact Or.inl old
      · exact Or.inr (Or.inr restMember)
    · intro present
      have h := ih cache ((name, arity, tickInlineSing cache body) :: acc) present
      simp only [List.map_cons, List.mem_cons]
      exact h.imp_right Or.inr

/-- Processing a program cannot change a cache lookup at an absent label.
This proof helper has no standalone HOL declaration. -/
theorem tickInlineAll_cacheUntouched (limit : Nat) (program : List (Nat × Nat × Exp))
    (cache : Spt (Nat × Exp)) (acc : List (Nat × Nat × Exp)) (key : Nat)
    (absent : key ∉ program.map Prod.fst) :
    sptLookup key (tickInlineAll limit cache program acc).1 = sptLookup key cache := by
  induction program generalizing cache acc with
  | nil => simp [tickInlineAll]
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    simp only [tickInlineAll]
    split
    · rw [ih _ _ absent.2]
      exact sptLookup_sptInsert_ne name key (arity, tickInlineSing cache body) cache absent.1
    · exact ih _ _ absent.2

/-- The original program traversal emits the current transformed entry before
the recursively compiled tail. This helper has no standalone HOL declaration. -/
theorem tickCompileProg_cons (limit : Nat) (cache : Spt (Nat × Exp))
    (name arity : Nat) (body : Exp) (rest : List (Nat × Nat × Exp)) :
    tickCompileProg limit cache ((name, arity, body) :: rest) =
      let body' := tickInlineSing cache body
      let cache' := if mustInline name limit body' then sptInsert name (arity, body') cache else cache
      let result := tickCompileProg limit cache' rest
      (result.1, (name, arity, body') :: result.2) := by
  simp only [tickCompileProg, tickInlineAll]
  rw [tickInlineAll_acc]
  simp

/-- If a previously absent key appears in the final cache, its unique
transformed program entry supplies the cached value. This helper has no
standalone HOL declaration. -/
theorem tickCompileProg_lookup_new (limit : Nat) (program : List (Nat × Nat × Exp))
    (cache : Spt (Nat × Exp)) (key : Nat) (value : Nat × Exp)
    (distinct : (program.map Prod.fst).Nodup) (fresh : sptLookup key cache = none)
    (found : sptLookup key (tickCompileProg limit cache program).1 = some value) :
    sptAListLookup key (tickCompileProg limit cache program).2 = some value := by
  induction program generalizing cache with
  | nil => simp [tickCompileProg, tickInlineAll, fresh] at found
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    have distinct' : name ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
      simpa using distinct
    let body' := tickInlineSing cache body
    let cache' := if mustInline name limit body' then sptInsert name (arity, body') cache else cache
    have step : tickCompileProg limit cache ((name, arity, body) :: rest) =
        ((tickCompileProg limit cache' rest).1, (name, arity, body') :: (tickCompileProg limit cache' rest).2) := by
      simpa [body', cache'] using tickCompileProg_cons limit cache name arity body rest
    rw [step] at found ⊢
    by_cases same : key = name
    · subst key
      have untouched := tickInlineAll_cacheUntouched limit rest cache' [] name distinct'.1
      change sptLookup name (tickCompileProg limit cache' rest).1 = sptLookup name cache' at untouched
      rw [untouched] at found
      by_cases use : mustInline name limit body' = true
      · have inserted : sptLookup name cache' = some (arity, body') := by
          simp [cache', use, sptLookup_sptInsert_same]
        rw [inserted] at found
        simp only [Option.some.injEq] at found
        subst value
        simp [sptAListLookup]
      · have unchanged : sptLookup name cache' = none := by simp [cache', use, fresh]
        rw [unchanged] at found
        contradiction
    · have fresh' : sptLookup key cache' = none := by
        dsimp [cache']
        split
        · rw [sptLookup_sptInsert_ne name key _ cache same, fresh]
        · exact fresh
      have tail := ih cache' distinct'.2 fresh' found
      simpa [sptAListLookup, same] using tail

/-- The final inlining cache is contained in the original code plus the
transformed program when incoming names are distinct and fresh. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "tick_compile_prog_res_range"]
theorem tickCompileProgResRange (program : List (Nat × Nat × Exp)) (limit : Nat)
    (output : List (Nat × Nat × Exp)) (base cache finalCache : Spt (Nat × Exp))
    (h : tickCompileProg limit cache program = (finalCache, output) ∧
      (program.map Prod.fst).Nodup ∧ sptSubspt cache base ∧
      (fun key => sptDomain base key ∧ key ∈ program.map Prod.fst) = (fun _ : Nat => False)) :
    sptSubspt finalCache (sptUnion base (sptFromAList output)) := by
  rcases h with ⟨run, distinct, initialSub, disjoint⟩
  rw [sptSubsptLookup] at initialSub ⊢
  intro key value found
  by_cases inProgram : key ∈ program.map Prod.fst
  · have baseAbsent : sptLookup key base = none := by
      cases lookup : sptLookup key base with
      | none => rfl
      | some value =>
        have member : (fun key => sptDomain base key ∧ key ∈ program.map Prod.fst) key :=
          ⟨(sptMem_iff_lookup key base).2 ⟨value, lookup⟩, inProgram⟩
        rw [disjoint] at member
        exact member.elim
    have cacheAbsent : sptLookup key cache = none := by
      cases lookup : sptLookup key cache with
      | none => rfl
      | some value =>
        have := initialSub key value lookup
        rw [baseAbsent] at this
        contradiction
    have resultFound : sptLookup key (tickCompileProg limit cache program).1 = some value := by
      simpa [run] using found
    have outputFound := tickCompileProg_lookup_new limit program cache key value distinct cacheAbsent resultFound
    rw [run] at outputFound
    rw [sptLookup_sptUnion, baseAbsent, sptLookup_sptFromAList]
    exact outputFound
  · have untouched := tickInlineAll_cacheUntouched limit program cache [] key inProgram
    change sptLookup key (tickCompileProg limit cache program).1 = sptLookup key cache at untouched
    rw [run] at untouched
    have initialFound : sptLookup key cache = some value := untouched.symm.trans found
    have baseFound := initialSub key value initialFound
    rw [sptLookup_sptUnion, baseFound]

end Flapjack.Compiler.Backend.BvlInline.Proofs
