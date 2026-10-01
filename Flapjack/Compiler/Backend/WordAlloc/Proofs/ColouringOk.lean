import Flapjack.Compiler.Backend.WordAlloc.ProgramLiveness
import Flapjack.Compiler.Backend.WordAlloc.ProgramWrites

/-!
# Liveness-scoped colouring relation `colouring_ok`

Counterpart of `word_allocProofScript.sml:100-146`. HOL sets are predicates on
`Nat`; `INJ f s UNIV` is rendered, as in the other word_alloc ports, as
injectivity of `f` on `s` (its codomain condition is trivial for `UNIV`).
-/

namespace Flapjack.WordAlloc

/-- Exact HOL `colouring_ok_def` (`word_allocProofScript.sml:100-146`), clause by
clause: `Seq` (live set before `s1` and both internal clash sets), `If`
(merged branch live set with the condition registers), returning `Call`
(cut sets with arguments, returned variables with cut sets, return handler and
optional exception handler), `MustTerminate`, `Loop` (both live sets and the
body under the extended loop table) and the catch-all, which requires
injectivity on the live-before set and on the writes together with the
live-after set. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "colouring_ok_def"
  (words_as_type_indexed_bitvec)]
def colouringOk {width : Nat} [NeZero width] (f : Nat → Nat) :
    WordLangProgHOL (BitVec width) → NumSet → List (NumSet × NumSet) → Prop
  | .seq s1 s2, live, lt =>
      let s2Live := getLive s2 live lt
      let s1Live := getLive s1 s2Live lt
      (∀ a b, sptDomain s1Live a → sptDomain s1Live b → f a = f b → a = b) ∧
        colouringOk f s2 live lt ∧ colouringOk f s1 s2Live lt
  | .ite _cmp r1 ri e2 e3, live, lt =>
      let e2Live := getLive e2 live lt
      let e3Live := getLive e3 live lt
      let unionLive := sptUnion e2Live e3Live
      let merged := match ri with
        | .reg r2 => sptInsert r2 () (sptInsert r1 () unionLive)
        | _ => sptInsert r1 () unionLive
      (∀ a b, sptDomain merged a → sptDomain merged b → f a = f b → a = b) ∧
        colouringOk f e2 live lt ∧ colouringOk f e3 live lt
  | .call (some (v, cutset, retHandler, _l1, _l2)) _dest args h, live, lt =>
      let argsSet := numsetListInsert args .ln
      let allNames := sptUnion cutset.2 cutset.1
      (∀ a b, sptDomain (sptUnion allNames argsSet) a →
        sptDomain (sptUnion allNames argsSet) b → f a = f b → a = b) ∧
      (∀ a b, sptDomain (numsetListInsert v allNames) a →
        sptDomain (numsetListInsert v allNames) b → f a = f b → a = b) ∧
      colouringOk f retHandler live lt ∧
      (match h with
        | none => True
        | some (v, prog, _l1, _l2) =>
            (∀ a b, sptDomain (sptInsert v () allNames) a →
              sptDomain (sptInsert v () allNames) b → f a = f b → a = b) ∧
            colouringOk f prog live lt)
  | .mustTerminate p, live, lt => colouringOk f p live lt
  | .loop names body exitNames, _live, lt =>
      (∀ a b, sptDomain names a → sptDomain names b → f a = f b → a = b) ∧
      (∀ a b, sptDomain exitNames a → sptDomain exitNames b → f a = f b → a = b) ∧
      colouringOk f body names ((names, exitNames) :: lt)
  | prog, live, lt =>
      let lset := getLive prog live lt
      let iset := sptUnion (getWrites prog) live
      (∀ a b, sptDomain lset a → sptDomain lset b → f a = f b → a = b) ∧
        (∀ a b, sptDomain iset a → sptDomain iset b → f a = f b → a = b)

end Flapjack.WordAlloc
