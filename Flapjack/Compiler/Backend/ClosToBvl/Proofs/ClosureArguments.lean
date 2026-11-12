module

public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Argument accumulation for the closure-to-BVL value relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Add a prefix of arguments to a closure or recursive closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "add_args_def"]
def addArgs : ClosSem.Value → List ClosSem.Value → Option ClosSem.Value
  | .closure loc args env arity body, added => some (.closure loc (added ++ args) env arity body)
  | .recclosure loc args env funs index, added => some (.recclosure loc (added ++ args) env funs index)
  | _, _ => none

/-- Flapjack helper: successive argument prefixes associate. The source's
local theorem has not yet had its inferred HOL type captured. -/
theorem addArgs_append (cl : ClosSem.Value) (argEnv : List ClosSem.Value)
    (func : ClosSem.Value) (args : List ClosSem.Value)
    (h : addArgs cl argEnv = some func) : addArgs cl (args ++ argEnv) = addArgs func args := by
  cases cl <;> simp [addArgs] at h
  all_goals subst func
  all_goals simp [addArgs, List.append_assoc]

instance closureArgumentsInst1 : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩

/-- The arity of a closure, using HOL's total `EL` for recursive groups. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "get_num_args_def"]
noncomputable def getNumArgs : ClosSem.Value → Option Nat
  | .closure _ _ _ arity _ => some arity
  | .recclosure _ _ _ funs index => some (Flapjack.holEl index funs).1
  | _ => none

/-- Remaining arity of an ordinary or recursive closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "num_remaining_args_def"]
noncomputable def numRemainingArgs : ClosSem.Value → Option Nat
  | .closure _ args _ arity _ => some (arity - args.length)
  | .recclosure _ args _ funs index => some ((Flapjack.holEl index funs).1 - args.length)
  | _ => none

/-- A nonzero full remaining arity means no arguments were added. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "no_partial_args"]
theorem noPartialArgs (func cl : ClosSem.Value) (x : Nat) (argEnv : List ClosSem.Value)
    (premises : numRemainingArgs func = some x ∧ getNumArgs func = some x ∧
      x ≠ 0 ∧ addArgs cl argEnv = some func) : argEnv = [] := by
  rcases premises with ⟨remaining, arity, nonzero, added⟩
  cases cl <;> simp only [addArgs, Option.some.injEq, reduceCtorEq] at added
  all_goals subst func
  all_goals simp only [numRemainingArgs, getNumArgs, Option.some.injEq, List.length_append] at remaining arity
  all_goals cases argEnv <;> simp_all <;> omega

/-- Direct-call location check without the maximum-application bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "check_loc'_def"]
noncomputable def checkLocPrime {α β : Type} (requested location : Option α)
    (parameters arguments : β) (supplied : Nat) : Bool := by
  classical
  exact match requested with
    | none => true
    | some address => decide (parameters = arguments ∧ supplied = 0 ∧ some address = location)

/-- Closure application with the source proof's unbounded location check. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "dest_closure'_def"]
noncomputable def destClosurePrime (requested : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) : Option ClosSem.AppKind :=
  match function with
  | .closure location supplied env arity body =>
    if checkLocPrime requested location arity args.length supplied.length && supplied.length < arity then
      if args.length + supplied.length < arity then
        some (.partialApp (.closure location (args ++ supplied) env arity body))
      else
        let needed := arity - supplied.length
        some (.fullApp body (args.reverse.take needed |>.reverse |>.append (supplied ++ env))
          (args.reverse.drop needed |>.reverse))
    else none
  | .recclosure location supplied env functions index =>
    match functions[index]? with
    | none => none
    | some (arity, body) =>
      let codeLocation := location.map (fun loc => 2 * index + loc)
      if checkLocPrime requested codeLocation arity args.length supplied.length && supplied.length < arity then
        if args.length + supplied.length < arity then
          some (.partialApp (.recclosure location (args ++ supplied) env functions index))
        else
          let needed := arity - supplied.length
          let recursive := (List.range functions.length).map (fun i => ClosSem.Value.recclosure location [] env functions i)
          some (.fullApp body (args.reverse.take needed |>.reverse |>.append (supplied ++ recursive ++ env))
            (args.reverse.drop needed |>.reverse))
      else none
  | _ => none

/-- Any bounded closure destination is also an unbounded destination. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "dest_cl_imp_dest_cl'"]
theorem destClosure_imp_prime (maxApp : Nat) (location : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (result : ClosSem.AppKind)
    (found : ClosSem.destClosure maxApp location function args = some result) :
    destClosurePrime location function args = some result := by
  have check (loc : Option Nat) (arity count supplied : Nat)
      (valid : (ClosSem.checkLoc maxApp location loc arity count supplied && decide (supplied < arity)) = true) :
      (checkLocPrime location loc arity count supplied && decide (supplied < arity)) = true := by
    cases location <;> simp [ClosSem.checkLoc, checkLocPrime] at valid ⊢
    · exact valid.2
    · exact valid
  cases function <;> simp only [ClosSem.destClosure, destClosurePrime] at found ⊢ <;> try contradiction
  case closure loc supplied env arity body =>
    split at found
    · rename_i valid
      simp only [check loc arity args.length supplied.length valid, ↓reduceIte]
      exact found
    · simp at found
  case recclosure loc supplied env functions index =>
    cases selected : functions[index]? with
    | none => simp [selected] at found
    | some entry =>
      cases entry with
      | mk arity body =>
        simp only [selected] at found ⊢
        split at found
        · rename_i valid
          simp only [check (loc.map (fun loc => 2 * index + loc)) arity args.length supplied.length valid,
            ↓reduceIte]
          exact found
        · simp at found

end Flapjack.Compiler.Backend.ClosToBvl
