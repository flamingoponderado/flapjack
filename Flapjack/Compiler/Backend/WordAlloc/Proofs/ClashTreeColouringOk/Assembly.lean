import Flapjack.Pancake.WordLang.MaxVar
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
  set_option tactic.fun_induction.unfolding false in
    fun_induction maxVarHOL prog with
    | case25 operator name address =>
        cases operator <;> solve_by_elim (maxDepth := 12) [clashTreeColouringOk_ShareStore, clashTreeColouringOk_ShareStore8, clashTreeColouringOk_ShareStore16,
          clashTreeColouringOk_ShareStore32, clashTreeColouringOk_ShareLoad, clashTreeColouringOk_ShareLoad8,
          clashTreeColouringOk_ShareLoad16, clashTreeColouringOk_ShareLoad32]
    | case27 program =>
        cases program <;> solve_by_elim (maxDepth := 12) [clashTreeColouringOk_Break, clashTreeColouringOk_Continue]
    | _ =>
        solve_by_elim (maxDepth := 12) [clashTreeColouringOk_Skip, clashTreeColouringOk_Move, clashTreeColouringOk_Inst,
          clashTreeColouringOk_Assign, clashTreeColouringOk_Get, clashTreeColouringOk_Set,
          clashTreeColouringOk_Store, clashTreeColouringOk_MustTerminate, clashTreeColouringOk_CallNone,
          clashTreeColouringOk_ReturnNoHandler, clashTreeColouringOk_CallHandler, clashTreeColouringOk_Seq,
          clashTreeColouringOk_If, clashTreeColouringOk_Loop, clashTreeColouringOk_Alloc,
          clashTreeColouringOk_StoreConsts, clashTreeColouringOk_Raise, clashTreeColouringOk_Return,
          clashTreeColouringOk_Break, clashTreeColouringOk_Continue, clashTreeColouringOk_Tick,
          clashTreeColouringOk_OpCurrHeap, clashTreeColouringOk_LocValue, clashTreeColouringOk_Install,
          clashTreeColouringOk_CodeBufferWrite, clashTreeColouringOk_DataBufferWrite, clashTreeColouringOk_FFI]

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
