module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WriteWord64

@[expose] public section

/-! Shared infrastructure for floating-point assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

/-- Reassemble the two Word64 halves used by the floating-point assignment proofs.
This is supporting bit-vector infrastructure. -/
theorem word64HalvesAppend (v : BitVec 64) :
    (v >>> (32 : Nat)).setWidth 32 ++ v.setWidth 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append (x := (v >>> (32 : Nat)).setWidth 32) (y := v.setWidth 32)]
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  split <;> simp_all
  all_goals omega

/-- Reassemble the state relation from the Word64 evaluator outcome; this supports the FP assignment proofs. -/
theorem stateRelNextFreeResult {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 dest space : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (value : DataSem.Value) (nf : WordLocW width)
    (memory : BitVec width → WordLocW width) (locals : Spt (WordLocW width))
    (fpRegs : HolFiniteMapExact Nat (BitVec 64))
    (related : stateRel conf l1 l2 source target none locs)
    (preserved : ∀ n, (sptLookup n source.locals).isSome → (sptLookup (adjustVar n) locals).isSome)
    (destPresent : (sptLookup (adjustVar dest) locals).isSome)
    (zero : sptLookup 0 locals = sptLookup 0 target.locals)
    (heap : memoryRel conf target.be (holThe source.tstamps) source.refs space
      (target.store.update (.nextFree, nf)) memory target.mdomain
      (joinEnvLocals (sptInsert dest value source.locals) locals ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) :
    stateRel conf l1 l2 (DataSem.setVar dest value {source with space := space})
      {target with store := target.store.update (.nextFree, nf), memory := memory, locals := locals, fpRegs := fpRegs}
      none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, ?_, hgood, hshift, htstamp, ?_, ?_, ?_,
    hstack, hlocs, hacc, hmax, hsizes, hlocals, ?_, ?_⟩
  · simpa [DataSem.setVar, codeOracleRel, HolFiniteMapExact.update, FUPDATE] using horacle
  · simpa [DataSem.setVar, HolFiniteMapExact.update, FUPDATE] using hglobal
  · intro _
    simpa [zero] using hzero rfl
  · intro key present
    by_cases same : key = dest
    · subst key
      exact destPresent
    · apply preserved
      simpa [DataSem.setVar, sptLookup_sptInsert_ne _ _ _ _ same] using present
  · simpa [DataSem.setVar, HolFiniteMapExact.update, FUPDATE] using hlim
  · simpa [DataSem.setVar, joinEnvLocals, holFapply, HolFiniteMapExact.update, FUPDATE] using heap


/-- Expose sequential evaluation for the assignment proof. -/
private theorem evalSeq {width : Nat} [NeZero width] {C F : Type}
    (p q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p q) s =
      match WordSemStateFiniteExact.evaluate p s with
      | (none, s1) => WordSemStateFiniteExact.evaluate q s1
      | (some res, s1) => (some res, s1) := by
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases h : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 => cases res <;> rfl

/-- Append a continuation after a successful instruction list; this supports the FP assignment proofs. -/
theorem evalListAppend {width : Nat} [NeZero width] {C F : Type}
    (xs : List (WordLangProgHOL (BitVec width))) (tail : WordLangProgHOL (BitVec width))
    (s out : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.evaluate (wordListSeq xs) s = (none, out)) :
    WordSemStateFiniteExact.evaluate (wordListSeq (xs ++ [tail])) s =
      WordSemStateFiniteExact.evaluate tail out := by
  induction xs generalizing s with
  | nil =>
    simp [wordListSeq, WordSemStateFiniteExact.evaluate] at run ⊢
    subst out
    rfl
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.cons_append, List.nil_append, wordListSeq] at run ⊢
      rw [evalSeq, run]
    | cons y ys =>
      simp only [List.cons_append, wordListSeq, evalSeq] at run ⊢
      cases h : WordSemStateFiniteExact.evaluate x s with
      | mk res s1 =>
        cases res with
        | some err => simp [h] at run
        | none =>
          simp only [h] at run ⊢
          exact ih s1 run



end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
