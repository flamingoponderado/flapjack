import Flapjack.HolRef
import Flapjack.Pancake.WordLang

/-!
# `word_remove`: removing `MustTerminate`

Counterpart of `cakeml/compiler/backend/word_removeScript.sml`. This is a
proof-side port; whether the executed compiler needs this pass is tracked
separately.
-/

namespace Flapjack.Compiler.Backend.WordRemove

/-- Exact HOL `remove_must_terminate_def` (`word_removeScript.sml:16-31`), clause by
clause with HOL's final catchall: `MustTerminate p` is replaced by its body, and
the recursion descends through `Seq`, `If`, both `Call` bodies and `Loop`. -/
@[hol "cakeml/compiler/backend/word_removeScript.sml" "remove_must_terminate_def"
  (words_as_type_indexed_bitvec)]
def removeMustTerminate {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .seq p0 p1 => .seq (removeMustTerminate p0) (removeMustTerminate p1)
  | .ite cmp r1 ri e2 e3 => .ite cmp r1 ri (removeMustTerminate e2) (removeMustTerminate e3)
  | .mustTerminate p => removeMustTerminate p
  | .call ret dest args h =>
      let ret := match ret with
        | none => none
        | some (v, cutset, retHandler, l1, l2) =>
            some (v, cutset, removeMustTerminate retHandler, l1, l2)
      let h := match h with
        | none => none
        | some (v, prog, l1, l2) => some (v, removeMustTerminate prog, l1, l2)
      .call ret dest args h
  | .loop names body exitNames => .loop names (removeMustTerminate body) exitNames
  | prog => prog

end Flapjack.Compiler.Backend.WordRemove
