module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call

@[expose] public section

/-! Shared unfolding of the recursive-closure clause of `destClosure` at a
known function entry. Flapjack proof infrastructure; no separately named HOL
declaration. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Unfold recursive-closure inspection at a known function entry. This helper
has no standalone HOL declaration. -/
theorem destClosure_rec_found (maxApp : Nat) (requested location : Option Nat)
    (supplied env args : List Value) (functions : List (Nat × ClosLang.Exp))
    (index arity : Nat) (body : ClosLang.Exp)
    (found : functions[index]? = some (arity, body)) :
    destClosure maxApp requested (.recclosure location supplied env functions index) args =
      if checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
          arity args.length supplied.length && supplied.length < arity then
        if args.length + supplied.length < arity then
          some (.partialApp (.recclosure location (args ++ supplied) env functions index))
        else
          some (.fullApp body
            ((args.reverse.take (arity - supplied.length)).reverse ++
              (supplied ++ ((List.range functions.length).map
                (fun i => Value.recclosure location [] env functions i) ++ env)))
            ((args.reverse.drop (arity - supplied.length)).reverse))
      else none := by
  simp only [destClosure, found]
  split
  · split <;> simp [List.append_assoc]
  · rfl

end Flapjack.Compiler.Backend.ClosProps
