import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.PresLang

/-- Complete presentation configuration retained by the backend record. -/
@[hol "cakeml/compiler/backend/presLangScript.sml" "tap_config"]
structure TapConfig where
  exploreFlag : Bool
  deriving DecidableEq, Repr

/-- The source default disables presentation exploration. -/
@[hol "cakeml/compiler/backend/presLangScript.sml" "default_tap_config_def"]
def defaultTapConfig : TapConfig := ⟨false⟩

end Flapjack.Compiler.Backend.PresLang
