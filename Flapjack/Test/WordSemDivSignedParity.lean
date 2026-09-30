import Flapjack.Compiler.Backend.Semantics.WordSem.Inst

/-! Kernel replay of original wordSem inst_def observations from
scripts/hol-probes/word_sem_div_signed_probe.out. All states are updates of
arbitrary base states, as in the original HOL probe. These signed Div cases do
not certify the floating clauses or whole inst_def correspondence. -/
namespace Flapjack.Test.WordSemDivSignedParity
open Flapjack Flapjack.WordSemStateFiniteExact

private noncomputable def observeDiv {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (a b : BitVec width)
    (destination dividend divisor : Nat) :=
  (inst (.arith (.div destination dividend divisor))
    {s with locals := sptFromAList [(2, .word a), (3, .word b)]}).map
      (fun t => [1, 2, 3].map (fun k => sptLookup k t.locals))

theorem positive {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 17 5 1 2 3 = some [some (.word 3), some (.word 17), some (.word 5)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem negativeSmall {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 250 10 1 2 3 = some [some (.word 0), some (.word 250), some (.word 10)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem negativeDividend {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 239 5 1 2 3 = some [some (.word 253), some (.word 239), some (.word 5)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem negativeDivisor {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 17 251 1 2 3 = some [some (.word 253), some (.word 17), some (.word 251)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem bothNegative {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 239 251 1 2 3 = some [some (.word 3), some (.word 239), some (.word 251)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem minOverflow {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 128 255 1 2 3 = some [some (.word 128), some (.word 128), some (.word 255)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem minHalf {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 128 2 1 2 3 = some [some (.word 192), some (.word 128), some (.word 2)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem positiveMinusOne {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 127 255 1 2 3 = some [some (.word 129), some (.word 127), some (.word 255)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem zeroDivisor {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 239 0 1 2 3 = none := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem zeroDividend {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 0 251 1 2 3 = some [some (.word 0), some (.word 0), some (.word 251)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem aliasDividend {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 239 5 2 2 3 = some [none, some (.word 253), some (.word 5)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem aliasDivisor {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 239 5 3 2 3 = some [none, some (.word 239), some (.word 253)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem sameSource {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    observeDiv s 239 5 1 2 2 = some [some (.word 1), some (.word 239), some (.word 5)] := by
  simp [observeDiv, inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem missingDividend {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    inst (.arith (.div 1 2 3)) {s with locals := sptFromAList [(3, .word 5)]} = none := by
  simp [inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem locationDivisor {C F : Type} (s : WordSemStateFiniteExact 8 C F) :
    inst (.arith (.div 1 2 3))
      {s with locals := sptFromAList [(2, .word 239), (3, .loc 4 5)]} = none := by
  simp [inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem min64Overflow {C F : Type} (s : WordSemStateFiniteExact 64 C F) :
    (inst (.arith (.div 1 2 3)) {s with locals := sptFromAList [(2, .word 0x8000000000000000), (3, .word 0xFFFFFFFFFFFFFFFF)]}).map
        (fun t => sptLookup 1 t.locals) = some (some (.word 0x8000000000000000)) := by
  simp [inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

theorem min1Overflow {C F : Type} (s : WordSemStateFiniteExact 1 C F) :
    (inst (.arith (.div 1 2 3)) {s with locals := sptFromAList [(2, .word 1), (3, .word 1)]}).map (fun t => sptLookup 1 t.locals) =
        some (some (.word 1)) := by
  simp [inst, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptFromAList, sptLookup, sptInsert]
  all_goals decide +kernel

/-- Universal source sign-case equation, not a tagged external-library port. -/
theorem quotientSignCases {width : Nat} (a b : BitVec width) :
    a.sdiv b = if a.msb then
      if b.msb then (-a).udiv (-b) else -((-a).udiv b)
    else if b.msb then -(a.udiv (-b)) else a.udiv b := by
  cases ha : a.msb <;> cases hb : b.msb <;> simp [BitVec.sdiv, ha, hb]

end Flapjack.Test.WordSemDivSignedParity
