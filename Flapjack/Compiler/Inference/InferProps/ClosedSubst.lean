module

public import Flapjack.Compiler.Inference.EnvRel

@[expose] public section

/-! Free-variable checks after empty named substitution. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.EnvRel

/-- Empty named substitution of closed types yields closed inference types. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "infer_type_subst_empty_check"]
theorem inferTypeSubstEmptyCheck :
    (∀ t, checkFreevars 0 [] t = true → Infer.checkT 0 (fun _ => False) (Infer.inferTypeSubst [] t)) ∧
    (∀ (ts : List SemanticT), ts.all (checkFreevars 0 []) = true →
      ∀ t ∈ ts.map (Infer.inferTypeSubst []), Infer.checkT 0 (fun _ => False) t) := by
  constructor
  · intro t free
    rw [(inferTypeSubstNil 0).1 t free]
    exact checkFreevarsToCheckT 0 t () free
  · intro ts free x xmem
    obtain ⟨t, tmem, rfl⟩ := List.mem_map.mp xmem
    have ft := List.all_eq_true.mp free t tmem
    rw [(inferTypeSubstNil 0).1 t ft]
    exact checkFreevarsToCheckT 0 t () ft
end Flapjack.Compiler.Inference.InferProps
