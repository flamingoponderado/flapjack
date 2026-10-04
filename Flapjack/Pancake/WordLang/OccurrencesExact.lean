import Flapjack.Pancake.WordLang

/-!
# Exact WordLang occurrence conventions

Counterpart of wordLangScript.sml:127-205. Cut sets use the reviewed Spt
carrier and literal toAList key enumeration, rather than the legacy function
map/domain model. HOL EVERY and conjunction are Boolean List.all and &&.
The Call handler is inspected only under SOME return, as in the source.
-/
namespace Flapjack

@[hol "cakeml/compiler/backend/wordLangScript.sml" "every_name_def"]
def everyNameHOL (predicate : Nat → Bool) (cutsets : WordLangCutsetsHOL) : Bool :=
  ((sptToAList cutsets.1).map Prod.fst).all predicate &&
    ((sptToAList cutsets.2).map Prod.fst).all predicate

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def everyVarHOL {width : Nat} [NeZero width] (predicate : Nat → Bool) :
    WordLangProgHOL (BitVec width) → Bool
  | .skip => true
  | .move _ moves => (moves.map Prod.fst).all predicate && (moves.map Prod.snd).all predicate
  | .inst instruction => everyVarInstHOL predicate instruction
  | .assign destination expression => predicate destination && everyVarExpHOL predicate expression
  | .get destination _ => predicate destination
  | .store expression source => predicate source && everyVarExpHOL predicate expression
  | .locValue destination _ => predicate destination
  | .install a b c d names =>
      predicate a && predicate b && predicate c && predicate d && everyNameHOL predicate names
  | .codeBufferWrite a b => predicate a && predicate b
  | .dataBufferWrite a b => predicate a && predicate b
  | .ffi _ a b c d names =>
      predicate a && predicate b && predicate c && predicate d && everyNameHOL predicate names
  | .mustTerminate body => everyVarHOL predicate body
  | .call returns _ arguments handler =>
      arguments.all predicate &&
        match returns with
        | none => true
        | some (values, names, body, _, _) =>
            values.all predicate && everyNameHOL predicate names && everyVarHOL predicate body &&
              match handler with
              | none => true
              | some (value, body, _, _) => predicate value && everyVarHOL predicate body
  | .seq first second => everyVarHOL predicate first && everyVarHOL predicate second
  | .ite _ left right first second =>
      predicate left && everyVarImmHOL predicate right &&
        everyVarHOL predicate first && everyVarHOL predicate second
  | .alloc destination names => predicate destination && everyNameHOL predicate names
  | .storeConsts a b c d _ => predicate a && predicate b && predicate c && predicate d
  | .raise value => predicate value
  | .return value values => predicate value && values.all predicate
  | .opCurrHeap _ left right => predicate left && predicate right
  | .tick => true
  | .set _ expression => everyVarExpHOL predicate expression
  | .shareInst _ destination expression => predicate destination && everyVarExpHOL predicate expression
  | .loop liveIn body liveOut =>
      ((sptToAList liveIn).map Prod.fst).all predicate && everyVarHOL predicate body &&
        ((sptToAList liveOut).map Prod.fst).all predicate
  | _ => true

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def everyStackVarHOL {width : Nat} [NeZero width] (predicate : Nat → Bool) :
    WordLangProgHOL (BitVec width) → Bool
  | .ffi _ _ _ _ _ names => everyNameHOL predicate names
  | .install _ _ _ _ names => everyNameHOL predicate names
  | .call returns _ _ handler =>
      match returns with
      | none => true
      | some (_, names, body, _, _) =>
          everyNameHOL predicate names && everyStackVarHOL predicate body &&
            match handler with
            | none => true
            | some (_, body, _, _) => everyStackVarHOL predicate body
  | .alloc _ names => everyNameHOL predicate names
  | .mustTerminate body => everyStackVarHOL predicate body
  | .seq first second => everyStackVarHOL predicate first && everyStackVarHOL predicate second
  | .ite _ _ _ first second => everyStackVarHOL predicate first && everyStackVarHOL predicate second
  | .loop _ body _ => everyStackVarHOL predicate body
  | _ => true

end Flapjack
