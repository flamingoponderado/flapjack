import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.HolRef

/-! Flat evaluator installation configuration used in backend composition. -/
namespace Flapjack.Compiler.Backend.FlatProps

/-- Construct the flat evaluator's compiler and oracle configuration. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "mk_flat_install_conf_def"]
def mkFlatInstallConf {C : Type}
    (cc : C → List FlatLang.Exp → Option (List (BitVec 8) × List (BitVec 64) × C))
    (co : Nat → C × List FlatLang.Exp) : FlatSem.InstallConfig C :=
  ⟨cc, co⟩

end Flapjack.Compiler.Backend.FlatProps
