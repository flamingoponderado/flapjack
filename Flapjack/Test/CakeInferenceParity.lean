module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.Compiler.Inference.Unify

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Inference.InferT
public meta import Flapjack.Compiler.Inference.Unify
public meta import Flapjack.Misc.Sptree
public meta import Flapjack.Compiler.Inference.Infer
@[expose] public section

/-! Original inference substitutions and unification captured from HOL. -/
namespace Flapjack.Test.CakeInferenceParity
open Flapjack Flapjack.Compiler.Inference Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify

#guard inferDeBruijnSubst [.uvar 9, .app [] 5] (.app [.varDb 0, .varDb 1, .varDb 4] 4) ==
  .app [.uvar 9, .app [] 5, .varDb 2] 4

#guard match generalise 2 0 .ln (.app [.uvar 1, .uvar 2, .uvar 2, .uvar 4] 9) with
  | (count, s, t) => count == 2 && sptLookup 2 s == some 0 && sptLookup 4 s == some 1 &&
      t == .app [.uvar 1, .varDb 0, .varDb 0, .varDb 1] 9

-- These cases are captured from `unify_exec_walk_probe.out`.
#guard cvwalkCode .ln 7 == .inr (.uvar 7)
#guard cvwalkCode (sptInsert 2 (.varDb 4) .ln) 2 == .inr (.varDb 4)
#guard cvwalkCode (sptInsert 2 (.app [.uvar 3] 5) .ln) 2 == .inr (.app [.uvar 3] 5)
#guard cvwalkCode (sptInsert 2 (.uvar 7) .ln) 2 == .inl 7
#guard walkExecutable (sptInsert 2 (.varDb 4) .ln) (.uvar 2) == some (.varDb 4)
#guard walkExecutable (sptInsert 2 (.app [.uvar 3] 5) .ln) (.uvar 2) == some (.app [.uvar 3] 5)
#guard walkExecutable (sptInsert 2 (.uvar 7) (sptInsert 7 (.varDb 4) .ln)) (.uvar 2) == some (.varDb 4)
#guard
  let chain := (List.range 256).foldl
    (fun s n => sptInsert n (.uvar (n + 1)) s) (sptInsert 256 (.varDb 4) .ln)
  walkExecutable chain (.uvar 0) == some (.varDb 4)

-- The unifier's worklist bound no longer truncates a longer variable chain.
#guard match unifyFuel 2
    (sptInsert 2 (.uvar 7) (sptInsert 7 (.uvar 9) (sptInsert 9 (.varDb 4) .ln)))
    (.uvar 2) (.varDb 4) with
  | some (some _) => true
  | _ => false

-- These occurrences are captured from `unify_exec_walk_probe.out`.
#guard occursWorkPartial .ln 3 [[]] == some false
#guard occursPartial .ln 3 (.uvar 3) == some true
#guard occursPartial .ln 3 (.varDb 3) == some false
#guard occursPartial .ln 3 (.app [.varDb 2, .app [.uvar 3] 5] 4) == some true
#guard occursPartial (sptInsert 2 (.uvar 7) .ln) 7 (.uvar 2) == some true
#guard
  let deep := (List.range 256).foldl (fun t _ => InferT.app [t] 5) (InferT.uvar 3)
  occursPartial .ln 3 deep == some true

-- These normalization results are captured from `unify_exec_walk_probe.out`.
#guard walkStarList .ln [] == some []
#guard walkStarList .ln [.uvar 3] == some [.uvar 3]
#guard walkStarList .ln [.app [.varDb 2, .app [.uvar 3] 5] 4] ==
  some [.app [.varDb 2, .app [.uvar 3] 5] 4]
#guard walkStarList (sptInsert 2 (.uvar 7) (sptInsert 7 (.varDb 4) .ln)) [.uvar 2] ==
  some [.varDb 4]
#guard walkStarList (sptInsert 2 (.varDb 4) .ln) [.uvar 2, .varDb 1, .uvar 7] ==
  some [.varDb 4, .varDb 1, .uvar 7]
#guard
  let deep := (List.range 256).foldl (fun t _ => InferT.app [t] 5) (InferT.uvar 3)
  walkStar .ln deep == some deep

-- Occurs traversal no longer inherits the smaller worklist bound.
#guard match unifyFuel 2 .ln (.uvar 0) (.app [.varDb 1] 5) with
  | some (some _) => true
  | _ => false
#guard match unifyFuel 2 .ln (.uvar 0) (.app [.app [.uvar 0] 6] 5) with
  | some none => true
  | _ => false

#guard match unifyFuel 100 .ln (.app [.uvar 0, .uvar 1] 4) (.app [.app [] 5, .uvar 0] 4) with
  | some (some s) => sptLookup 0 s == some (.app [] 5) && sptLookup 1 s == some (.app [] 5)
  | _ => false

#guard match unifyFuel 100 .ln (.uvar 0) (.app [.uvar 0] 6) with
  | some none => true
  | _ => false

end Flapjack.Test.CakeInferenceParity
