import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileHandle

/-! Code lookup correspondence for BVL-to-BVI calls. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value findCode)

private theorem adjust_holLast (relocate : Nat → Nat) (head : Value) (tail : List Value) :
    Flapjack.holLast ((head :: tail).map (adjustBv relocate)) =
      adjustBv relocate (Flapjack.holLast (head :: tail)) := by
  induction tail generalizing head with
  | nil => simp [Flapjack.holLast]
  | cons next rest ih => simpa [Flapjack.holLast] using ih next

/-- Successful direct or indirect source lookup selects the relocated target
arguments and an installed optimized version of the same body. Untagged
pending evaluator correspondence and source theorem review. -/
theorem stateRel_findCode {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (dest : Option Nat) (values args : List Value) (body : Bvl.Exp)
    (related : stateRel relocate source target)
    (found : findCode dest values source.code = some (args, body)) :
    ∃ n converted aux finalName,
      compileListSource n [body] = ([converted], aux, finalName) ∧
      findCode (dest.map (fun loc => bvlNumStubs + bvlToBviNamespaces * loc))
        (values.map (adjustBv relocate)) target.code =
          some (args.map (adjustBv relocate), BviLet.compileSing [] 0 converted) ∧
      auxCodeInstalled (appListAppend aux) target.code ∧ BvlHandle.Proofs.handleOk [body] := by
  simp only [stateRel] at related
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, codeRel⟩
  cases dest with
  | some name =>
    simp only [findCode] at found
    cases lookup : sptLookup name source.code with
    | none => simp [lookup] at found
    | some pair =>
      rcases pair with ⟨arity, expression⟩
      simp only [lookup] at found
      split at found
      · rename_i length
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        rcases found with ⟨rfl, rfl⟩
        obtain ⟨n, compiled⟩ := codeRel name arity expression lookup
        rcases result : compileSingSource n expression with ⟨converted, aux, finalName⟩
        simp only [result] at compiled
        have nilRight : smartAppend aux .nil = aux := by cases aux <;> rfl
        refine ⟨n, converted, aux, finalName, ?_, ?_, compiled.2⟩
        · simp [compileListSource, result, nilRight]
        · simp [findCode, compiled.1, length]
      · simp at found
  | none =>
    cases values with
    | nil => simp [findCode] at found
    | cons head tail =>
      simp only [findCode, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at found
      cases last : Flapjack.holLast (head :: tail) with
      | codePtr name =>
        cases lookup : sptLookup name source.code with
        | none => simp [last, lookup] at found
        | some pair =>
          rcases pair with ⟨arity, expression⟩
          simp only [last, lookup] at found
          split at found
          · rename_i length
            simp only [Option.some.injEq, Prod.mk.injEq] at found
            rcases found with ⟨rfl, rfl⟩
            obtain ⟨n, compiled⟩ := codeRel name arity expression lookup
            rcases result : compileSingSource n expression with ⟨converted, aux, finalName⟩
            simp only [result] at compiled
            have nilRight : smartAppend aux .nil = aux := by cases aux <;> rfl
            refine ⟨n, converted, aux, finalName, ?_, ?_, compiled.2⟩
            · simp [compileListSource, result, nilRight]
            · have adjustedLast := adjust_holLast relocate head tail
              rw [last] at adjustedLast
              have adjustedLast' : Flapjack.holLast (adjustBv relocate head :: tail.map (adjustBv relocate)) =
                  .codePtr (bvlNumStubs + bvlToBviNamespaces * name) := by
                simpa only [List.map_cons, adjustBv] using adjustedLast
              have tailLength : tail.length = arity := by simp at length; omega
              simp [findCode, adjustedLast', compiled.1, tailLength]
          · simp at found
      | _ => simp [last] at found

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
