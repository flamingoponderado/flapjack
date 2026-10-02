import Flapjack.HolRef
import Flapjack.Compiler.Backend.StackAlloc
import Flapjack.Compiler.Backend.StackAlloc.GcCode

/-!
# `stack_alloc` compiler pass over the exact carrier

`next_lab`, `comp`, `prog_comp`, `stubs` and `compile` of
`cakeml/compiler/backend/stack_allocScript.sml:638-722`, over the exact
width-indexed `HolProg width` carrier.  `next_lab` is the generic `nextLab` of
`Flapjack/Compiler/Backend/StackAlloc.lean` at that carrier.  The executed
compiler still runs the separate `Flapjack/StackAlloc.lean` pass.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack.Compiler.Backend.StackLang

/-- Exact HOL `next_lab_def` (`stack_allocScript.sml:649-662`) over the exact
`HolProg width` carrier: the generic `nextLab` at that carrier. -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "next_lab_def"
  (words_as_type_indexed_bitvec)]
def nextLabHOL {width : Nat} [NeZero width] (p : HolProg width) (aux : Nat) : Nat :=
  nextLab p aux

/-- Exact HOL `comp_def` (`stack_allocScript.sml:678-703`): `Alloc` and
`StoreConsts _ _ (SOME loc)` become returning calls to their stubs with fresh
return labels `(n, m)`; the exception handler of a non-returning call is
dropped, as in HOL. -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "comp_def"
  (words_as_type_indexed_bitvec)]
def comp {width : Nat} [NeZero width] (n m : Nat) : HolProg width → HolProg width × Nat
  | .seq p1 p2 =>
      let (q1, m) := comp n m p1
      let (q2, m) := comp n m p2
      (.seq q1 q2, m)
  | .ite c r ri p1 p2 =>
      let (q1, m) := comp n m p1
      let (q2, m) := comp n m p2
      (.ite c r ri q1 q2, m)
  | .loop p1 =>
      let (q1, m) := comp n m p1
      (.loop q1, m)
  | .call none dest _ => (.call none dest none, m)
  | .call (some (p1, lr, l1, l2)) dest exc =>
      let (q1, m) := comp n m p1
      match exc with
      | none => (.call (some (q1, lr, l1, l2)) dest none, m)
      | some (p2, k1, k2) =>
          let (q2, m) := comp n m p2
          (.call (some (q1, lr, l1, l2)) dest (some (q2, k1, k2)), m)
  | .alloc _ => (.call (some (.skip, 0, n, m)) (.inl gcStubLocation) none, m + 1)
  | .storeConsts _ _ (some loc) => (.call (some (.skip, 0, n, m)) (.inl loc) none, m + 1)
  | p => (p, m)

/-- Exact HOL `prog_comp_def` (`stack_allocScript.sml:716-718`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "prog_comp_def"
  (words_as_type_indexed_bitvec)]
def progComp {width : Nat} [NeZero width] : Nat × HolProg width → Nat × HolProg width
  | (n, p) => (n, (comp n (nextLabHOL p 2) p).1)

/-- Exact HOL `stubs_def` (`stack_allocScript.sml:638-640`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "stubs_def"
  (words_as_type_indexed_bitvec)]
def stubs {width : Nat} [NeZero width] (conf : DataToWord.Config) :
    List (Nat × HolProg width) :=
  [(gcStubLocation, .seq (wordGcCode conf) (.ret 0))]

/-- Exact HOL `compile_def` (`stack_allocScript.sml:720-722`). -/
@[hol "cakeml/compiler/backend/stack_allocScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
def compile {width : Nat} [NeZero width] (c : DataToWord.Config)
    (prog : List (Nat × HolProg width)) : List (Nat × HolProg width) :=
  stubs c ++ prog.map progComp

end Flapjack.Compiler.Backend.StackAlloc
