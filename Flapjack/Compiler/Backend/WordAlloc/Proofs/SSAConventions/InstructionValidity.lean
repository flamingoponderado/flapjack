import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions
import Flapjack.Pancake.WordConvs.FullInstOkLess

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Original unconditional fake-sequence instruction validity, with arbitrary
assembler configuration and source list. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "fake_seq_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem fakeSeq_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (names : List Nat) :
    fullInstOkLessExact config
      ((names.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip) = true := by
  induction names with
  | nil => simp [fullInstOkLessExact, fullInstOkLessWith]
  | cons name names ih =>
      simpa [fullInstOkLessExact, fullInstOkLessWith, fakeMove,
        HolInst.ofWordLangInst, instOkLessExact] using ih

/-- Original loop setup validity with the actual producer equation as sole
premise; no SSA map or register-bound assumptions are added. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "loop_setup_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem loopSetup_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat)
    (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    fullInstOkLessExact config setupProg = true := by
  unfold loopSetup at setup
  generalize hr : listNextVarRename
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isNone) ssa na = renamed at setup
  rcases renamed with ⟨fresh, extended, next⟩
  generalize hm : listNextVarRenameMove (width := width) extended next
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isSome) = moved at setup
  rcases moved with ⟨moves, refreshed, nextOut⟩
  simp only [hr, hm] at setup
  have fake := fakeSeq_fullInstOkLess config fresh
  have moveConvention : fullInstOkLessExact config moves = true := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [fullInstOkLessExact, fullInstOkLessWith]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  rw [fullInstOkLessExactSeq, fake, moveConvention]
  rfl

/-- Original reconciliation validity and destination-distinctness conclusions,
with the actual fake-move producer equality as the sole premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "fake_moves_conventions2" (words_as_type_indexed_bitvec)]
theorem fakeMoves_instructionConventions {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (prio : Option (Unit ⊕ Unit)) (names : List Nat)
    (ssaL ssaR : Spt Nat) (next : Nat)
    (left right : WordLangProgHOL (BitVec width)) (finalNext : Nat)
    (finalL finalR : Spt Nat)
    (produced : fakeMoves prio names ssaL ssaR next = (left, right, finalNext, finalL, finalR)) :
    fullInstOkLessExact config left = true ∧ fullInstOkLessExact config right = true ∧
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) left = true ∧
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) right = true := by
  have all : ∀ (ls : List Nat) (l r : Spt Nat) (na : Nat),
      let (a, b, _, _, _) := fakeMoves (width := width) prio ls l r na
      fullInstOkLessExact config a = true ∧ fullInstOkLessExact config b = true ∧
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) a = true ∧
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) b = true := by
    intro ls
    induction ls with
    | nil => intro l r na; simp [fakeMoves, fullInstOkLessExact, fullInstOkLessWith, everyInst]
    | cons x xs ih =>
        intro l r na
        generalize he : fakeMoves (width := width) prio xs l r na = result
        rcases result with ⟨a, b, count, treeL, treeR⟩
        have previous := ih l r na
        rw [he] at previous
        simp only [fakeMoves, he]
        cases hl : sptLookup x treeL <;> cases hr : sptLookup x treeR <;>
          simp_all [fullInstOkLessExact, fullInstOkLessWith, everyInst, fakeMove,
            HolInst.ofWordLangInst, instOkLessExact, distinctTarRegExact]
  have result := all names ssaL ssaR next
  rw [produced] at result
  exact result

/-- Original complete address-extraction characterization used by ShareInst;
all source expressions are quantified, not a restricted address subset. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "exp_to_addr_ShareInst" (words_as_type_indexed_bitvec)]
theorem expToAddr_shareInst {width : Nat} [NeZero width]
    (expression : WordLangExpHOL (BitVec width)) (name : Nat) (offset : BitVec width) :
    expToAddrHOL expression = some (.addr name offset) ↔
      (expression = .var name ∧ offset = 0) ∨
        expression = .op .add [.var name, .const offset] := by
  fun_cases expToAddrHOL expression <;> simp_all
  intro _
  exact eq_comm

end Flapjack.WordAlloc
