import Flapjack.Pancake.Proofs.PanToCrep.CompileExpValRel
import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge

/-!
# Production RV64 `Load` bridge for `compile_exp_val_rel`

This is Flapjack proof infrastructure for the `Load` case of HOL
`compile_exp_val_rel` (`pan_to_crepProofScript.sml:217-256`). It composes the
production RV64 source expression evaluator with the exact-carrier `Load` case
in `CompileExpValRel.lean`. The state relation and rangedness premise are the
existing production/exact representation bridge obligations; every HOL shape
constructor is admitted, with no `One`/flat-`Two` restriction. This is
Flapjack-specific infrastructure with no standalone HOL declaration: HOL's
source `Load` case is proved inside `compile_exp_val_rel`, while this theorem
also relates the executable RV64 evaluator to the exact evaluator and carrier.
The direct HOL-shaped constructor lemma is `compileExpValRelHOL_load` in
`CompileExpValRel.lean`; the complete parent theorem is assembled separately.
-/

namespace Flapjack
namespace CompileExpValRelProduction

open Flapjack.Pancake.PanLang

end CompileExpValRelProduction
end Flapjack
