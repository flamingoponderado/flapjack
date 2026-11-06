import Flapjack.Compiler.Inference.Infer
import Flapjack.Compiler.Inference.Unify

/-! Original inference substitutions and unification captured from HOL. -/
namespace Flapjack.Test.CakeInferenceParity
open Flapjack Flapjack.Compiler.Inference Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify

#guard inferDeBruijnSubst [.uvar 9, .app [] 5] (.app [.varDb 0, .varDb 1, .varDb 4] 4) ==
  .app [.uvar 9, .app [] 5, .varDb 2] 4

#guard match generalise 2 0 .ln (.app [.uvar 1, .uvar 2, .uvar 2, .uvar 4] 9) with
  | (count, s, t) => count == 2 && sptLookup 2 s == some 0 && sptLookup 4 s == some 1 &&
      t == .app [.uvar 1, .varDb 0, .varDb 0, .varDb 1] 9

#guard match unifyFuel 100 .ln (.app [.uvar 0, .uvar 1] 4) (.app [.app [] 5, .uvar 0] 4) with
  | some (some s) => sptLookup 0 s == some (.app [] 5) && sptLookup 1 s == some (.app [] 5)
  | _ => false

#guard match unifyFuel 100 .ln (.uvar 0) (.app [.uvar 0] 6) with
  | some none => true
  | _ => false

end Flapjack.Test.CakeInferenceParity
