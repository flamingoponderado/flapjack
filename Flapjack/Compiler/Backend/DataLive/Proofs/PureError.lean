module

public import Flapjack.Compiler.Backend.DataLive.Proofs.Simulation
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyErrors

@[expose] public section

/-! Error behavior of pure data-language primitive applications. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A pure operation cannot be an FFI call. -/
theorem isPure_ne_ffi (op : ClosLang.Op) (pure : isPure op = true)
    (name : Flapjack.Basis.Pure.MlString.MlString) : op ≠ .ffi name := by
  intro equal
  subst op
  simp [isPure] at pure

/-- A pure primitive application can fail only with a type error. This
statement is untagged until the source evaluator and carriers are reviewed. -/
theorem pure_doApp_error {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (error : ErrorResult DataSem.Value)
    (pure : isPure op = true) (run : doApp op args state = .err error) :
    error = .abort .typeError := by
  rcases DataProps.doApp_err op args state error run with typeError | ⟨name, _, ffi, _⟩
  · exact typeError
  · exact False.elim (isPure_ne_ffi op pure name ffi)

/-- Pure word primitives do not consume or reset heap space. -/
theorem pure_word_doSpace {C F : Type} (op : ClosLang.WordOp) (args : List DataSem.Value)
    (state : State C F) (pure : isPure (.wordOp op) = true) : doSpace (.wordOp op) args state = some state := by
  cases op <;> simp [isPure] at pure
  case wordOpw size operation =>
    cases size <;> simp_all [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  case wordShift size operation amount =>
    cases size <;> simp_all [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  case wordTest size test =>
    cases size <;> simp [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  case fpCmp cmp => simp [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]

/-- The liveness state relation is transitive at a fixed live set. -/
theorem stateRel_trans {C F : Type} (first middle last : State C F) (live : NumSet)
    (left : stateRel first middle live) (right : stateRel middle last live) : stateRel first last live := by
  rcases left with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, al⟩
  rcases right with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, bl⟩
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8, a9.trans b9, a10.trans b10, a11.trans b11, a12.trans b12, a13.trans b13,
    fun key member => (al key member).trans (bl key member)⟩

/-- Updating a dead local cannot affect the liveness relation. -/
theorem stateRel_setVar_dead {C F : Type} (source target : State C F) (live : NumSet)
    (dest : Nat) (value : DataSem.Value) (related : stateRel source target live)
    (dead : sptLookup dest live = none) : stateRel (setVar dest value source) target live := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  refine ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, ?_⟩
  intro key member
  have different : key ≠ dest := by
    intro same
    subst key
    simp [sptMem, sptDomain, dead] at member
  simpa [setVar, sptLookup_sptInsert_ne dest key value _ different] using locals key member

end Flapjack.Compiler.Backend.DataLive
