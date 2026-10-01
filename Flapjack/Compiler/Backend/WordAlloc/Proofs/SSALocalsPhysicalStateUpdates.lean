import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalInsert
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack list induction infrastructure, with no separate HOL original.
Each written target register is physical, so it lies outside the SSA image.
The simultaneous list recursion also stops when either input list is empty. -/
theorem ssaLocalsPhysicalListUpdate {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (names : List Nat) (values : List α)
    (valid : ssaMapOK next ssa) (related : ssaLocalsRel next ssa source target)
    (physical : ∀ name ∈ names, isPhyVar name) :
    ssaLocalsRel next ssa source
      (LoopSemStateFiniteExact.sptAlistInsert names values target) := by
  induction names generalizing values with
  | nil => exact related
  | cons name names ih =>
    cases values with
    | nil => exact related
    | cons value values =>
      exact ssaLocalsRelIgnoreInsert next ssa source _ name value
        ⟨valid, ih values (fun n member => physical n (List.mem_cons_of_mem name member)),
          physical name List.mem_cons_self⟩

/-- Full native physical-target setVar wrapper. HOL infers independent source
and target code/FFI carriers, sharing only the word dimension. Only locals are
traversed; no finite-map state-field translation is used by this statement. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_ignore_set_var"
  (words_as_type_indexed_bitvec)]
theorem ssaLocalsRelIgnoreSetVar {width : Nat} [NeZero width]
    {C₁ F₁ C₂ F₂ : Type} (next : Nat) (ssa : Spt Nat)
    (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂) (name : Nat)
    (value : WordLocW width)
    (h : ssaMapOK next ssa ∧ ssaLocalsRel next ssa source.locals target.locals ∧
      isPhyVar name) :
    ssaLocalsRel next ssa source.locals
      (WordSemStateFiniteExact.setVar name value target).locals :=
  ssaLocalsRelIgnoreInsert next ssa source.locals target.locals name value h

/-- Full native physical-target list wrapper. The original length equality is
retained despite the stronger list infrastructure above. Source and target
code/FFI carriers remain independent; only the word dimension is shared. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_ignore_list_insert"
  (words_as_type_indexed_bitvec)]
theorem ssaLocalsRelIgnoreListInsert {width : Nat} [NeZero width]
    {C₁ F₁ C₂ F₂ : Type} (next : Nat) (ssa : Spt Nat)
    (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂)
    (names : List Nat) (values : List (WordLocW width))
    (h : ssaMapOK next ssa ∧ ssaLocalsRel next ssa source.locals target.locals ∧
      (∀ name ∈ names, isPhyVar name) ∧ names.length = values.length) :
    ssaLocalsRel next ssa source.locals
      (LoopSemStateFiniteExact.sptAlistInsert names values target.locals) :=
  ssaLocalsPhysicalListUpdate next ssa source.locals target.locals names values
    h.1 h.2.1 h.2.2.1

end Flapjack.Compiler.Backend.WordAlloc
