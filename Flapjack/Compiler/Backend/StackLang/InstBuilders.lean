import Flapjack.Compiler.Backend.StackLang.Overloads

/-! Compatibility names for earlier Flapjack consumers. The canonical HOL ports
live in Overloads.lean; this module adds no logical port or HOL tag.
-/
namespace Flapjack.Compiler.Backend.StackLang

/-- Flapjack compatibility alias of the canonical native While port. -/
abbrev whileProg := @whileHOL

/-- Flapjack compatibility alias of the canonical native move port. -/
abbrev moveInst := @moveHOL

end Flapjack.Compiler.Backend.StackLang
