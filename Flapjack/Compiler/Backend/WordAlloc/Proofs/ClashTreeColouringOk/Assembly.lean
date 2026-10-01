import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Control
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.CutSets
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.LoopCases
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.ShareInst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.CallNone
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.ReturnNoHandler
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.CallHandler

namespace Flapjack.WordAlloc
open Flapjack.RegAlloc

/-- Flapjack proof factoring: structural recursion discharges the universally
quantified per-program motive using the reviewed constructor cases. It has no
separate HOL original; the theorem below exposes HOL's full statement. -/
private theorem clashTreeGoal_all {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) : clashTreeGoal prog := by
  cases prog with
  | skip => exact clashTreeColouringOk_Skip
  | move priority moves => exact clashTreeColouringOk_Move priority moves
  | inst instruction => exact clashTreeColouringOk_Inst instruction
  | assign name value => exact clashTreeColouringOk_Assign name value
  | get destination store => exact clashTreeColouringOk_Get destination store
  | set store value => exact clashTreeColouringOk_Set store value
  | store address value => exact clashTreeColouringOk_Store address value
  | mustTerminate body =>
      exact clashTreeColouringOk_MustTerminate body (clashTreeGoal_all body)
  | call returns target arguments handler =>
      cases returns with
      | none => exact clashTreeColouringOk_CallNone target arguments handler
      | some ret =>
          obtain ⟨vs, cuts, body, l1, l2⟩ := ret
          cases handler with
          | none =>
              exact clashTreeColouringOk_ReturnNoHandler vs cuts body l1 l2
                target arguments (clashTreeGoal_all body)
          | some h =>
              obtain ⟨v, hp, h1, h2⟩ := h
              exact clashTreeColouringOk_CallHandler vs cuts body l1 l2 target arguments
                v hp h1 h2 (clashTreeGoal_all body) (clashTreeGoal_all hp)
  | seq first second =>
      exact clashTreeColouringOk_Seq first second
        (clashTreeGoal_all first) (clashTreeGoal_all second)
  | ite operator condition right first second =>
      exact clashTreeColouringOk_If operator condition right first second
        (clashTreeGoal_all first) (clashTreeGoal_all second)
  | loop names body exitNames =>
      exact clashTreeColouringOk_Loop names exitNames body (clashTreeGoal_all body)
  | alloc destination cutsets => exact clashTreeColouringOk_Alloc destination cutsets
  | storeConsts a b c d values => exact clashTreeColouringOk_StoreConsts a b c d values
  | raise exception => exact clashTreeColouringOk_Raise exception
  | «return» label values => exact clashTreeColouringOk_Return label values
  | «break» index => exact clashTreeColouringOk_Break index
  | «continue» index => exact clashTreeColouringOk_Continue index
  | tick => exact clashTreeColouringOk_Tick
  | opCurrHeap operator destination source =>
      exact clashTreeColouringOk_OpCurrHeap operator destination source
  | locValue destination source => exact clashTreeColouringOk_LocValue destination source
  | install a b c d cutsets => exact clashTreeColouringOk_Install a b c d cutsets
  | codeBufferWrite a b => exact clashTreeColouringOk_CodeBufferWrite a b
  | dataBufferWrite a b => exact clashTreeColouringOk_DataBufferWrite a b
  | ffi function cptr clen ptr len cutsets =>
      exact clashTreeColouringOk_FFI function cptr clen ptr len cutsets
  | shareInst operator name address =>
      cases operator with
      | store => exact clashTreeColouringOk_ShareStore name address
      | store8 => exact clashTreeColouringOk_ShareStore8 name address
      | store16 => exact clashTreeColouringOk_ShareStore16 name address
      | store32 => exact clashTreeColouringOk_ShareStore32 name address
      | load => exact clashTreeColouringOk_ShareLoad name address
      | load8 => exact clashTreeColouringOk_ShareLoad8 name address
      | load16 => exact clashTreeColouringOk_ShareLoad16 name address
      | load32 => exact clashTreeColouringOk_ShareLoad32 name address
termination_by sizeOf prog
decreasing_by all_goals decreasing_trivial

/-- Full HOL checker soundness theorem, assembled over all native program
constructors, including arbitrary ignored handlers on tail calls. The six
premises and five conclusions are those of source2813-2826; HOL `hide` is
definitionally the identity. Predicate sets express `IMAGE` and `INJ ... UNIV`.
Only the standard positive-width word translation is qualified. This theorem
does not route the checker into the executed allocator or establish allocation
semantics/compiler correctness; those remain separate dependencies. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "clash_tree_colouring_ok" (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) (lt : List (NumSet × NumSet))
    (f : Nat → Nat) (live flive livein flivein : NumSet)
    (h : wfCutsets prog ∧ sptWf live = true ∧
      (∀ p, p ∈ lt → sptWf p.1 = true ∧ sptWf p.2 = true) ∧
      sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y) ∧
      (∀ a b, sptDomain live a → sptDomain live b → f a = f b → a = b) ∧
      checkClashTree f (getClashTree prog lt) live flive = some (livein, flivein)) :
    sptWf livein = true ∧
      (∀ a b, sptDomain livein a → sptDomain livein b → f a = f b → a = b) ∧
      colouringOk f prog live lt ∧
      livein = getLive prog live lt ∧
      sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ f x = y) :=
  clashTreeGoal_all prog lt f live flive livein flivein h

end Flapjack.WordAlloc
