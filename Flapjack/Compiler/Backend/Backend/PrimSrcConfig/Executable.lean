import Flapjack.Compiler.Backend.Backend.PrimSrcConfig

/-! Compiler realization of the existing primitive-source configuration.
The original tagged closed-form equality eliminates the unused HOL ARB store;
this Lean compilation interface has no separately named HOL declaration. -/
namespace Flapjack.Compiler.Backend.Backend
open Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString

/-- Complete primitive-source closed form from its tagged original equality. -/
def primSrcConfigExecutable : SourceToFlat.Config :=
      { next := { vidx := 0, tidx := 2, eidx := 4 }
        modEnv :=
          { c := .bind
              [(ofString "::", 0, some (1, [(0, 0), (0, 2)])),
               (ofString "[]", 0, some (1, [(0, 0), (0, 2)])),
               (ofString "True", 1, some (0, [(0, 0), (1, 0)])),
               (ofString "False", 0, some (0, [(0, 0), (1, 0)])),
               (ofString "Subscript", 3, none),
               (ofString "Div", 2, none),
               (ofString "Chr", 1, none),
               (ofString "Bind", 0, none)] []
            v := .bind [] [] }
        patternCfg := { patHeuristic := 0 }
        envs := { next := 0, envGens := .ln } }

/-- Entire source configuration equality, including the native namespace,
generation state and primitive tags; no independently selected arbitrary store. -/
theorem primSrcConfig_eq_executable : primSrcConfig = primSrcConfigExecutable := by
  rw [primSrcConfig_eq]
  rfl

end Flapjack.Compiler.Backend.Backend
