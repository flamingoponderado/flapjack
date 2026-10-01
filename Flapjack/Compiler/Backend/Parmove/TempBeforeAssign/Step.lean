import Flapjack.Compiler.Backend.Parmove.Steps
import Flapjack.Compiler.Backend.Parmove.Invariants
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Append

namespace Flapjack.Compiler.Backend.Parmove

/-- Flapjack proof infrastructure: an ordinary move cannot change the ordered
scratch predicate, at any position. This local Boolean equation has no separate
HOL declaration; HOL uses the concatenation law for the same reasoning. -/
private theorem ordinaryMoveNeutral {α : Type} (before after : List (Move α))
    (destination source : α) :
    notUseTempBeforeAssign (before ++ (some destination, some source) :: after) =
      notUseTempBeforeAssign (before ++ after) := by
  induction before with
  | nil => simp [notUseTempBeforeAssign]
  | cons move before ih =>
      rcases move with ⟨d, s⟩
      cases d <;> cases s
      · rfl
      · rfl
      · rfl
      · simpa only [List.cons_append, notUseTempBeforeAssign] using ih

/-- Primitive scheduler steps preserve chronological scratch safety, with
exactly the original source well-formedness and source-safety premises. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "step_not_use_temp_before_assign"]
theorem stepNotUseTempBeforeAssign {α : Type} (first second : State α) :
    Step first second → wf first →
      notUseTempBeforeAssign (first.2.1 ++ first.2.2).reverse = true →
      notUseTempBeforeAssign (second.2.1 ++ second.2.2).reverse = true := by
  intro transition valid safe
  cases transition with
  | removeSelf r before after active emitted => exact safe
  | start d s before after emitted =>
      have hd := valid.2.1 (d,s) (by simp)
      have hs := valid.2.2.1 (d,s) (by simp)
      cases d with
      | none => simp at hd
      | some d =>
        cases s with
        | none => simp at hs
        | some s =>
          simpa [List.reverse_append, ordinaryMoveNeutral] using safe
  | extend d r s before after active emitted =>
      have hr := valid.2.1 (r,d) (by simp)
      have hd := valid.2.2.1 (r,d) (by simp)
      cases r with
      | none => simp at hr
      | some r =>
        cases d with
        | none => simp at hd
        | some d =>
          have neutral := ordinaryMoveNeutral
            (emitted.reverse ++ active.reverse ++ [(some d,s)]) [] r d
          have result := neutral.trans (by simpa [List.reverse_append, List.append_assoc] using safe)
          simpa [List.reverse_append, List.append_assoc] using result
  | save d s pending active emitted =>
      have hd := valid.2.2.2.2.1 (d,s) (by simp)
      cases d <;> cases s <;>
        simp_all [Option.isSome, List.reverse_append, List.append_assoc,
          notUseTempBeforeAssignAppend, notUseTempBeforeAssign]
  | emitHead d0 dn s0 sn pending active emitted noRead distinct =>
      have hd := valid.2.2.2.2.1 (dn,sn) (by simp)
      have hs := valid.2.2.2.1 (by simp) (dn,sn) (by
        change (dn,sn) ∈ (((dn,sn) :: active) ++ [(d0,s0)]).dropLast
        rw [List.dropLast_concat]
        exact List.mem_cons_self)
      cases dn with
      | none => simp at hd
      | some dn =>
        cases sn with
        | none => simp at hs
        | some sn =>
          have inputNeutral := ordinaryMoveNeutral
            (emitted.reverse ++ [(d0,s0)] ++ active.reverse) [] dn sn
          have outputNeutral := ordinaryMoveNeutral emitted.reverse
            ((d0,s0) :: active.reverse) dn sn
          have inputSafe : notUseTempBeforeAssign
              ((emitted.reverse ++ [(d0,s0)] ++ active.reverse) ++
                [(some dn, some sn)]) = true := by
            simpa [List.reverse_append, List.append_assoc] using safe
          have reduced := inputNeutral.symm.trans inputSafe
          have result := outputNeutral.trans (by
            simpa [List.append_assoc] using reduced)
          simpa [List.reverse_append, List.append_assoc] using result
  | emitLast d s pending emitted noRead =>
      simpa [List.reverse_append] using safe

end Flapjack.Compiler.Backend.Parmove
