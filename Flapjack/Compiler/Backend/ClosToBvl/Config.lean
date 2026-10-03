import Flapjack.Compiler.Backend.ClosKnown.Config
import Flapjack.NamespaceHOL
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Complete source configuration, including retained call-state syntax.
HOL num_set is Spt Unit and the alist is a literal List of key/value pairs;
the actual closures use ClosLang.Exp, not an arbitrary expression carrier. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "config"]
structure Config where
  nextLoc : Nat
  start : Nat
  doMti : Bool
  knownConf : Option ClosKnown.Config
  doCall : Bool
  callState : NumSet × List (Nat × (Nat × ClosLang.Exp))
  maxApp : Nat

/-- Original full initializer, including the nonempty known-configuration option. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "default_config_def"]
def defaultConfig : Config :=
  ⟨0, 1, true, some (ClosKnown.defaultConfig 10), true, (.ln, []), 10⟩

end Flapjack.Compiler.Backend.ClosToBvl
