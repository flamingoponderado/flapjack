module

import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

/-! Constructor checks for the inference type well-formedness predicate. -/
open Flapjack.Compiler.Inference Flapjack.Compiler.Inference.Infer

example : checkT 2 (fun n => n = 7) (.app [.varDb 1, .uvar 7] 42) := by simp

example : ¬ checkT 2 (fun n => n = 7) (.app [.varDb 2] 42) := by simp
