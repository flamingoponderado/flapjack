import Flapjack.Misc.FindIndex
import Flapjack.Misc.ListEl
namespace Flapjack.Misc

/-- Full original distinct-list search equivalence, retaining an arbitrary
starting offset and the bounded existential EL index. EL is reduced only under
that original bound; no past-end default or extra outer bound is used.
Nonempty exposes HOL's intrinsic inhabited type carrier, and DecidableEq is
the propositional equality used by the reviewed find_index definition. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_ALL_DISTINCT_EL_eq"]
theorem findIndex_allDistinct_elEq {α : Type} [DecidableEq α] [Nonempty α]
    (values : List α) : values.Nodup → ∀ (target : α) (offset index : Nat),
    findIndex target values offset = some index ↔
    ∃ j, index = offset+j ∧ j < values.length ∧ target = holEl j values := by
  induction values with
  | nil => simp [findIndex]
  | cons head tail ih =>
    intro hn target offset index
    obtain ⟨hnot,ht⟩ := List.nodup_cons.mp hn
    by_cases he : head = target
    · rw [findIndex,if_pos he]
      constructor
      · intro h
        refine ⟨0,by simpa using (Option.some.inj h).symm,by simp,?_⟩
        simpa only [holEl,holHd] using he.symm
      · rintro ⟨j,hidx,hbound,hval⟩
        cases j with
        | zero => simpa using congrArg some hidx.symm
        | succ j =>
          have hb : j < tail.length := by simpa using hbound
          have hm : holEl j tail ∈ tail := by
            rw [holEl_eq_getElem j tail hb]
            exact List.getElem_mem hb
          have hv : head = holEl j tail := by
            simpa only [holEl,List.tail_cons,←he] using hval
          exact False.elim (hnot (hv ▸ hm))
    · rw [findIndex,if_neg he,ih ht target (offset+1) index]
      constructor
      · rintro ⟨j,hidx,hbound,hval⟩
        refine ⟨j+1,by omega,by simpa using hbound,?_⟩
        simpa only [holEl,List.tail_cons] using hval
      · rintro ⟨j,hidx,hbound,hval⟩
        cases j with
        | zero =>
          have hv : target = head := by simpa only [holEl,holHd] using hval
          exact False.elim (he hv.symm)
        | succ j =>
          refine ⟨j,by omega,by simpa using hbound,?_⟩
          simpa only [holEl,List.tail_cons] using hval
end Flapjack.Misc
