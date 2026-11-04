import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JumpExcBounds
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.NewLocal

/-! Locals restored from a related exception frame. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Restored live locals are present in the combined word environment. -/
theorem stackEnvRel_restored_present (size size' : Option Nat) (env : Spt DataSem.Value)
    (nonGc gc : List (Nat × WordLocW 64)) (rel : stackEnvRel size size' env nonGc gc)
    (n : Nat) (present : (sptLookup n env).isSome = true) :
    (sptLookup (adjustVar n) (sptUnion (sptFromAList gc) (sptFromAList nonGc))).isSome = true := by
  have found := (rel.2.2.2.2 n).mp present
  rw [sptLookup_sptUnion]
  cases h : sptLookup (adjustVar n) (sptFromAList gc) <;> simp_all

/-- The saved return location is restored at word local zero. -/
theorem stackEnvRel_restored_zero (size size' : Option Nat) (env : Spt DataSem.Value)
    (nonGc gc : List (Nat × WordLocW 64)) (rel : stackEnvRel size size' env nonGc gc)
    (a b : Nat) (saved : sptAListLookup 0 nonGc = some (.loc a b)) :
    sptLookup 0 (sptUnion (sptFromAList gc) (sptFromAList nonGc)) = some (.loc a b) := by
  have absent : sptAListLookup 0 gc = none := by
    cases found : sptAListLookup 0 gc with
    | none => rfl
    | some value =>
      have mem := sptAListLookup_mem 0 gc value found
      have invalid := (rel.1 (0, value) mem).1
      exact False.elim (invalid rfl)
  simp [sptLookup_sptUnion, sptLookup_sptFromAList, absent, saved]

/-- Every pair formed from restored locals was already in the saved GC roots. -/
theorem stackEnvRel_restored_roots (size size' : Option Nat) (env : Spt DataSem.Value)
    (nonGc gc : List (Nat × WordLocW 64)) (rel : stackEnvRel size size' env nonGc gc) :
    joinEnv env (sptToAList (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) ⊆
      joinEnv env gc := by
  intro ⟨value, word⟩ member
  obtain ⟨n, sourceLookup, targetLookup⟩ := joinEnv_localPair env _ value word member
  rw [sptLookup_sptUnion, sptLookup_sptFromAList, sptLookup_sptFromAList] at targetLookup
  cases found : sptAListLookup (adjustVar n) gc with
  | none =>
    simp [found] at targetLookup
    have inNonGc := sptAListLookup_mem (adjustVar n) nonGc word targetLookup
    have zero := rel.2.2.1 (adjustVar n, word) inNonGc
    simp [adjustVar] at zero
  | some w =>
    simp [found] at targetLookup
    subst w
    have inGc := sptAListLookup_mem (adjustVar n) gc word found
    apply List.mem_map.mpr
    refine ⟨(adjustVar n, word), List.mem_filter.mpr ⟨inGc, ?_⟩, ?_⟩
    · simp [adjustVar]
    · simp [adjustVar, sourceLookup, holThe]

/-- A successful exception jump re-establishes the candidate state relation
at the saved return location. The exception value itself has not yet been
installed in the restored locals. -/
theorem stateRel64_jumpExc {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (jump : DataSem.jumpExc source = some next) :
    ∃ targetNext label1 label2 return1 return2 remainingLocs,
      WordSemStateFiniteExact.jumpExc target = some (targetNext, label1, label2) ∧
      locs.drop (target.stack.length - (target.handler + 1)) = (return1, return2) :: remainingLocs ∧
      stateRel64 conf return1 return2 next targetNext none remainingLocs ∧
      ∀ pair ∈ joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))),
        Memory.memoryRel conf targetNext.be (holThe next.tstamps) next.refs next.space
          targetNext.store targetNext.memory targetNext.mdomain
          (pair :: (joinEnv next.locals (sptToAList (sptInter targetNext.locals (adjustSet next.locals))) ++
            [(theGlobal next.global, holFapply targetNext.store .globals)] ++ flatStack next.stack targetNext.stack)) := by
  have oldBound := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases related with ⟨ffi, clock, handlerEq, gcFun, code, oracle, dimension, shift, timestamps,
    globals, zero, locals, stackPairs, locationPairs, stackBound, maxBound, stackSize, localSize, limits, memory⟩
  have lengths := stackPairs.length_eq
  have handlerBound : source.handler < source.stack.length := by
    by_contra notBound
    simp [DataSem.jumpExc, notBound] at jump
  cases dropped : source.stack.drop (source.stack.length - (source.handler + 1)) with
  | nil => simp [DataSem.jumpExc, handlerBound, dropped] at jump
  | cons frame rest =>
    cases frame with
    | env size env => simp [DataSem.jumpExc, handlerBound, dropped] at jump
    | exc size env saved =>
      simp [DataSem.jumpExc, handlerBound, dropped] at jump
      subst next
      have tailRel := forall₂_drop_frames stackPairs (source.stack.length - (source.handler + 1))
      rw [dropped] at tailRel
      have sameDrop : target.stack.length - (target.handler + 1) =
          source.stack.length - (source.handler + 1) := by omega
      rw [← sameDrop] at tailRel
      cases targetDropped : target.stack.drop (target.stack.length - (target.handler + 1)) with
      | nil => rw [targetDropped] at tailRel; cases tailRel
      | cons frame' rest' =>
        rw [targetDropped] at tailRel
        cases tailRel with
        | cons headRel restRel =>
          cases frame' with
          | stackFrame size' nonGc gc handler =>
            cases handler with
            | none => simp [stackRel] at headRel
            | some info =>
              obtain ⟨saved', label1, label2⟩ := info
              simp only [stackRel] at headRel
              have locationTail := forall₂_drop_frames locationPairs (target.stack.length - (target.handler + 1))
              rw [targetDropped] at locationTail
              cases locDrop : locs.drop (target.stack.length - (target.handler + 1)) with
              | nil => rw [locDrop] at locationTail; cases locationTail
              | cons returnLoc remaining =>
                rw [locDrop] at locationTail
                cases locationTail with
                | cons locHead locRest =>
                  obtain ⟨return1, return2⟩ := returnLoc
                  let targetNext := { target with handler := saved', locals := sptUnion (sptFromAList gc) (sptFromAList nonGc), stack := rest', localsSize := size' }
                  have targetJump : WordSemStateFiniteExact.jumpExc target = some (targetNext, label1, label2) := by
                    have targetBound : target.handler < target.stack.length := by omega
                    simp [WordSemStateFiniteExact.jumpExc, targetBound, wordSemLastN_eq_drop, targetDropped, targetNext]
                  refine ⟨targetNext, label1, label2, return1, return2, remaining, targetJump, rfl, ?_⟩
                  have rootSubset : joinEnv env gc ++ flatStack rest rest' ⊆ flatStack source.stack target.stack := by
                    have sub := flatStack_drop_subset source.stack target.stack (source.stack.length - (source.handler + 1))
                    rw [dropped, ← sameDrop, targetDropped] at sub
                    simpa [flatStack] using sub
                  have bound := jumpExc_stackMaxBound target targetNext label1 label2 targetJump oldBound
                  have carry : ∀ pair ∈ joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))),
                      Memory.memoryRel conf targetNext.be (holThe source.tstamps) source.refs source.space
                        targetNext.store targetNext.memory targetNext.mdomain
                        (pair :: (joinEnv env (sptToAList (sptInter targetNext.locals (adjustSet env))) ++
                          [(theGlobal source.global, holFapply targetNext.store .globals)] ++ flatStack rest rest')) := by
                    intro pair pairMember
                    apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
                      target.store target.memory target.mdomain _ _ ?_ memory
                    intro root member
                    change root ∈ pair :: (joinEnv env (sptToAList (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) ++
                      [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack rest rest') at member
                    simp only [Option.getD_none, List.nil_append, List.mem_cons, List.mem_append] at member ⊢
                    rcases member with same | (localRoot | globalRoot) | stackRoot
                    · subst root
                      exact Or.inl (Or.inl pairMember)
                    · exact Or.inr (rootSubset (List.mem_append_left _ (stackEnvRel_restored_roots size size' env nonGc gc headRel.1 localRoot)))
                    · exact Or.inl (Or.inr globalRoot)
                    · exact Or.inr (rootSubset (List.mem_append_right _ stackRoot))
                  refine ⟨?_, carry⟩
                  refine ⟨ffi, clock, ?_, gcFun, code, oracle, dimension, shift, timestamps, globals, ?_, ?_, restRel,
                    locRest, bound, maxBound, stackSize, ?_, limits, ?_⟩
                  · exact headRel.2
                  · intro _
                    exact stackEnvRel_restored_zero size size' env nonGc gc headRel.1 return1 return2 locHead
                  · intro n present
                    exact stackEnvRel_restored_present size size' env nonGc gc headRel.1 n present
                  · exact headRel.1.2.1.symm
                  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
                      target.store target.memory target.mdomain _ _ ?_ memory
                    intro pair member
                    change pair ∈ joinEnv env (sptToAList (sptInter (sptUnion (sptFromAList gc) (sptFromAList nonGc)) (adjustSet env))) ++
                      [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack rest rest' at member
                    simp only [List.mem_append, List.mem_singleton] at member ⊢
                    rcases member with (localRoot | globalRoot) | stackRoot
                    · exact Or.inr (rootSubset (List.mem_append_left _ (stackEnvRel_restored_roots size size' env nonGc gc headRel.1 localRoot)))
                    · exact Or.inl (Or.inr globalRoot)
                    · exact Or.inr (rootSubset (List.mem_append_right _ stackRoot))

/-- A related raised value can be installed in any corresponding restored
local after the handler jump. This is a candidate-relation result; the full
HOL theorem also requires the faithful unrestricted compiler relations. -/
theorem stateRel64_jumpExc_setVar {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source next : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (n : Nat) (value : DataSem.Value) (word : WordLocW 64)
    (sourceLookup : DataSem.getVar n source.locals = some value)
    (targetLookup : WordSemStateFiniteExact.getVar (adjustVar n) target = some word)
    (jump : DataSem.jumpExc source = some next) :
    ∃ targetNext label1 label2 return1 return2 remainingLocs,
      WordSemStateFiniteExact.jumpExc target = some (targetNext, label1, label2) ∧
      wordSemLastN (next.stack.length + 1) locs = (return1, return2) :: remainingLocs ∧
      ∀ dest, stateRel64 conf return1 return2 (DataSem.setVar dest value next)
        (WordSemStateFiniteExact.setVar (adjustVar dest) word targetNext) none remainingLocs := by
  obtain ⟨targetNext, a, b, r1, r2, remaining, targetJump, locations, after, carry⟩ :=
    stateRel64_jumpExc conf l1 l2 source next target locs related jump
  have root := localPair_mem_joinEnv source.locals target.locals n value word sourceLookup targetLookup
  have sourceTargetLength := after.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  have targetLocsLength := after.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  have originalLength := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
  have dropLength := congrArg List.length locations
  simp only [List.length_drop, List.length_cons] at dropLength
  have dropEq : locs.length - (next.stack.length + 1) =
      target.stack.length - (target.handler + 1) := by omega
  have lastLocations : wordSemLastN (next.stack.length + 1) locs = (r1, r2) :: remaining := by
    rw [wordSemLastN_eq_drop, dropEq, locations]
  refine ⟨targetNext, a, b, r1, r2, remaining, targetJump, lastLocations, ?_⟩
  intro dest
  exact stateRel64_setNewLocal conf r1 r2 next targetNext remaining after dest value word (carry (value, word) root)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
