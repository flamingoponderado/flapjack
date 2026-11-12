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

/-- Extract the source location of a closure or recursive closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "get_loc_def"]
def getLoc : ClosSem.Value → Option Nat
  | .closure (some location) _ _ _ _ => some location
  | .recclosure (some location) _ _ _ index => some (location + 2 * index)
  | _ => none

/-- Previously accumulated arguments of a closure or recursive closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "get_old_args_def"]
def getOldArgs : ClosSem.Value → Option (List ClosSem.Value)
  | .closure _ args _ _ _ => some args
  | .recclosure _ args _ _ _ => some args
  | _ => none

/-- Captured environment of an ordinary or recursive source closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "get_cl_env_def"]
def getClEnv : ClosSem.Value → Option (List ClosSem.Value)
  | .closure _ _ env _ _ => some env
  | .recclosure _ _ env _ _ => some env
  | _ => none

/-- Subtracting one and the predecessor of a nonempty length. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "arith_helper_lem"]
theorem arithHelperLem {α : Type} (args : List α) (x : Nat) (nonempty : args.length ≠ 0) :
    x - 1 - (args.length - 1) = x - args.length := by
  omega

/-- Arithmetic facts for a nonempty partially supplied argument group. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "arith_helper_lem3"]
theorem arithHelperLem3 {α β : Type} (args : List α) (prev : List β) (totalArgs numArgs : Nat)
    (premises : args.length < totalArgs + 1 - prev.length ∧ args.length ≠ 0 ∧
      totalArgs - prev.length + 1 = numArgs - prev.length) :
    totalArgs - (args.length + prev.length - 1) = totalArgs + 1 - (args.length + prev.length) ∧
      args.length + prev.length < totalArgs + 1 ∧ numArgs = totalArgs + 1 := by
  omega

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

/-- A full closure application determines its source arguments and arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "dest_closure_full_app"]
theorem destClosureFullApp {α β γ : Type} (locOpt : Option Nat) (func : ClosSem.Value)
    (args : List ClosSem.Value) (_c : α) (_f1 : β) (_t1 : γ) (body : ClosLang.Exp)
    (args1 args2 : List ClosSem.Value) (maxApp : Nat)
    (found : ClosSem.destClosure maxApp locOpt func args = some (.fullApp body args1 args2)) :
    ∃ rem loc num old captured,
      getLoc func = loc ∧ numRemainingArgs func = some rem ∧ getNumArgs func = some num ∧
      getOldArgs func = some old ∧ getClEnv func = some captured ∧ rem ≤ args.length ∧ rem ≤ num ∧
      num ≤ old.length + args.length ∧ args2.length = args.length - rem ∧
      ClosSem.checkLoc maxApp locOpt loc num args.length (num - rem) = true := by
  cases func <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity expression =>
    split at found
    · rename_i valid
      split at found
      · simp at found
      · rename_i full
        simp only [Option.some.injEq, ClosSem.AppKind.fullApp.injEq] at found
        rcases found with ⟨_, _, rfl⟩
        have suppliedBound : supplied.length < arity := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.2
        have check : ClosSem.checkLoc maxApp locOpt location arity args.length supplied.length = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.1
        have back : arity - (arity - supplied.length) = supplied.length := by omega
        refine ⟨arity - supplied.length, location, arity, supplied, captured, ?_⟩
        cases location <;> simp [getLoc, numRemainingArgs, getNumArgs, getOldArgs, getClEnv,
          List.length_reverse, List.length_drop, back, check] <;> omega
    · simp at found
  case recclosure location supplied captured functions index =>
    split at found
    · simp at found
    · rename_i arity expression selected
      split at found
      · rename_i valid
        split at found
        · simp at found
        · rename_i full
          simp only [Option.some.injEq, ClosSem.AppKind.fullApp.injEq] at found
          rcases found with ⟨_, _, rfl⟩
          have suppliedBound : supplied.length < arity := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.2
          have check : ClosSem.checkLoc maxApp locOpt (location.map (fun loc => 2 * index + loc))
              arity args.length supplied.length = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.1
          have indexBound : index < functions.length := (List.getElem?_eq_some_iff.mp selected).1
          have entry : Flapjack.holEl index functions = (arity, expression) := by
            rw [Flapjack.holEl_eq_getElem _ _ indexBound]
            have h := (List.getElem?_eq_some_iff.mp selected).2
            exact h
          have back : arity - (arity - supplied.length) = supplied.length := by omega
          refine ⟨arity - supplied.length, location.map (fun loc => loc + 2 * index), arity, supplied, captured, ?_⟩
          cases location <;> simp [getLoc, numRemainingArgs, getNumArgs, getOldArgs, getClEnv,
            entry, List.length_reverse, List.length_drop, back, Nat.add_comm] <;>
              exact ⟨by omega, by simpa [Nat.add_comm] using check⟩
      · simp at found

/-- A partial application is indirect and saves a still-unsaturated argument list. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "dest_closure_part_app"]
theorem destClosurePartApp {α β : Type} (locOpt : Option Nat) (func : ClosSem.Value)
    (args : List ClosSem.Value) (result : ClosSem.Value) (_f1 : α) (_t1 : β) (maxApp : Nat)
    (premises : args.length ≠ 0 ∧ ClosSem.destClosure maxApp locOpt func args = some (.partialApp result)) :
    locOpt = none ∧ some result = addArgs func args ∧
      ∃ n, numRemainingArgs func = some n ∧ args.length < n ∧ args.length ≤ maxApp := by
  rcases premises with ⟨nonempty, found⟩
  cases func <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    split at found
    · rename_i valid
      split at found
      · rename_i undersaturated
        simp only [Option.some.injEq, ClosSem.AppKind.partialApp.injEq] at found
        subst result
        have check : ClosSem.checkLoc maxApp locOpt location arity args.length supplied.length = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.1
        cases locOpt with
        | none =>
          simp [ClosSem.checkLoc] at check
          refine ⟨rfl, ?_, arity - supplied.length, ?_, ?_, check⟩
          · simp [addArgs]
          · simp [numRemainingArgs]
          · omega
        | some address =>
          simp [ClosSem.checkLoc] at check
          omega
      · simp at found
    · simp at found
  case recclosure location supplied captured functions index =>
    split at found
    · simp at found
    · rename_i arity body selected
      split at found
      · rename_i valid
        split at found
        · rename_i undersaturated
          simp only [Option.some.injEq, ClosSem.AppKind.partialApp.injEq] at found
          subst result
          have check : ClosSem.checkLoc maxApp locOpt (location.map (fun loc => 2 * index + loc))
              arity args.length supplied.length = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.1
          have indexBound : index < functions.length := (List.getElem?_eq_some_iff.mp selected).1
          have entry : Flapjack.holEl index functions = (arity, body) := by
            rw [Flapjack.holEl_eq_getElem _ _ indexBound]
            exact (List.getElem?_eq_some_iff.mp selected).2
          cases locOpt with
          | none =>
            simp [ClosSem.checkLoc] at check
            refine ⟨rfl, ?_, arity - supplied.length, ?_, ?_, check⟩
            · simp [addArgs]
            · simp [numRemainingArgs, entry]
            · omega
          | some address =>
            simp [ClosSem.checkLoc] at check
            omega
        · simp at found
      · simp at found

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

/-- Completing a partial closure agrees with applying its original closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "dest_closure_full_of_part"]
theorem destClosure_full_of_part (maxApp : Nat) (location : Option Nat) (func : ClosSem.Value)
    (args : List ClosSem.Value) (body : ClosLang.Exp) (newEnv rest argEnv : List ClosSem.Value)
    (cl : ClosSem.Value) (numArgs : Nat)
    (premises : ClosSem.destClosure maxApp location func args = some (.fullApp body newEnv rest) ∧
      argEnv.length ≠ 0 ∧ addArgs cl argEnv = some func ∧ getNumArgs cl = some numArgs ∧
      argEnv.length < numArgs) :
    destClosurePrime location cl (args ++ argEnv) = some (.fullApp body newEnv rest) := by
  rcases premises with ⟨found, nonempty, added, arity, bound⟩
  cases cl <;> simp only [addArgs, Option.some.injEq, reduceCtorEq] at added
  all_goals subst func
  case closure loc supplied captured arity0 expression =>
    simp only [getNumArgs, Option.some.injEq] at arity
    subst numArgs
    simp only [ClosSem.destClosure] at found
    split at found
    · rename_i valid
      split at found
      · simp at found
      · rename_i enough
        simp only [Option.some.injEq, ClosSem.AppKind.fullApp.injEq] at found
        rcases found with ⟨rfl, rfl, rfl⟩
        cases location with
        | some address =>
          simp [ClosSem.checkLoc] at valid
          simp [valid.1.2.1] at nonempty
        | none =>
          simp only [ClosSem.checkLoc, Bool.and_eq_true, decide_eq_true_eq] at valid
          simp only [destClosurePrime, checkLocPrime, Bool.true_and, decide_eq_true_eq]
          have suppliedLt : supplied.length < arity0 := by
            simp only [List.length_append] at valid
            omega
          have notPartial : ¬ (args ++ argEnv).length + supplied.length < arity0 := by
            simp only [List.length_append] at enough ⊢
            omega
          simp only [if_pos suppliedLt, if_neg notPartial, Option.some.injEq,
            ClosSem.AppKind.fullApp.injEq, true_and]
          have prefixBound : argEnv.length ≤ arity0 - supplied.length := by
            simp only [List.length_append] at valid
            omega
          have reverseBound : argEnv.reverse.length ≤ arity0 - supplied.length := by simpa using prefixBound
          have takeSaved := List.take_of_length_le reverseBound
          have dropSaved := List.drop_eq_nil_of_le reverseBound
          simp [List.reverse_append, List.take_append, List.drop_append, takeSaved, dropSaved,
            List.length_append, Nat.sub_sub, Nat.add_comm, List.append_assoc]
    · simp at found
  case recclosure loc supplied captured functions index =>
    simp only [ClosSem.destClosure] at found
    cases selected : functions[index]? with
    | none => simp [selected] at found
    | some entry =>
      cases entry with
      | mk arity0 expression =>
        simp only [selected] at found
        have idx : index < functions.length := List.getElem?_eq_some_iff.mp selected |>.1
        have get := List.getElem?_eq_getElem idx
        rw [selected] at get
        simp only [Option.some.injEq] at get
        have el : Flapjack.holEl index functions = (arity0, expression) := by
          rw [Flapjack.holEl_eq_getElem index functions idx, ← get]
        simp only [getNumArgs, el, Option.some.injEq] at arity
        subst numArgs
        split at found
        · rename_i valid
          split at found
          · simp at found
          · rename_i enough
            simp only [Option.some.injEq, ClosSem.AppKind.fullApp.injEq] at found
            rcases found with ⟨rfl, rfl, rfl⟩
            cases location with
            | some address =>
              simp [ClosSem.checkLoc] at valid
              simp [valid.1.2.1] at nonempty
            | none =>
              simp only [ClosSem.checkLoc, Bool.and_eq_true, decide_eq_true_eq] at valid
              simp only [destClosurePrime, selected, checkLocPrime, Bool.true_and, decide_eq_true_eq]
              have suppliedLt : supplied.length < arity0 := by
                simp only [List.length_append] at valid
                omega
              have notPartial : ¬ (args ++ argEnv).length + supplied.length < arity0 := by
                simp only [List.length_append] at enough ⊢
                omega
              simp only [if_pos suppliedLt, if_neg notPartial, Option.some.injEq,
                ClosSem.AppKind.fullApp.injEq, true_and]
              have prefixBound : argEnv.length ≤ arity0 - supplied.length := by
                simp only [List.length_append] at valid
                omega
              have reverseBound : argEnv.reverse.length ≤ arity0 - supplied.length := by simpa using prefixBound
              have takeSaved := List.take_of_length_le reverseBound
              have dropSaved := List.drop_eq_nil_of_le reverseBound
              simp [List.reverse_append, List.take_append, List.drop_append, takeSaved, dropSaved,
                List.length_append, Nat.sub_sub, Nat.add_comm, List.append_assoc]
        · simp at found

end Flapjack.Compiler.Backend.ClosToBvl
