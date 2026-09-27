import Flapjack.Pancake.PanToCrep.CompileExact

/-!
Compiler-only support facts for the exact Pan-to-Crep expression compiler.
These Flapjack lemmas use the exact `ExpHOL`/`CrepExpHOL` syntax and
`PanToCrepContextExact` finite-map carrier.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact variable clause of `compileExpExactHOLW`: a local variable emits
    precisely the slots stored in its context binding, while a missing local
    binding emits no variable names. This is Flapjack-specific infrastructure,
    not a port of HOL `eval_var_cexp_present_ctxt`; it isolates the compiler
    lookup step used when proving that theorem over exact carriers. -/
@[simp] theorem compileExpExactHOLW_localVar_vars {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceName : MlS) :
    (compileExpExactHOLW context (.var .local sourceName)).1.flatMap
      crepExpVarsHOL =
      match context.vars.lookup sourceName with
      | some (_, slots) => slots
      | none => [] := by
  cases hlookup : context.vars.lookup sourceName <;>
    simp [compileExpExactHOLW, hlookup, crepExpVarsHOL, List.flatMap_map]

end Flapjack
