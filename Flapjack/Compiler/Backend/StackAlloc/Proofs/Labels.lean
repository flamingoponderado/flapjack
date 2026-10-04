import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.StackProps.OrderedLabels

/-!
# `stack_allocProof` label lemmas

`next_lab_EQ_MAX`, `MAX_SIMP`, `next_lab_thm`, `extract_labels_next_lab` and
`stack_alloc_lab_pres` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (6111-6215): the
labels `comp` introduces are fresh, above `next_lab`, and keep the label
conventions of the input program.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.Compiler.Backend.StackLang

/-- `next_lab` is a maximum with its accumulator (the recursion of HOL's
`next_lab_EQ_MAX` proof, over the generic `nextLab`). -/
theorem nextLab_max {width : Nat} [NeZero width] :
    ∀ (q : HolProg width) (aux : Nat), nextLab q aux = max aux (nextLab q 0)
  | .seq a b, aux => by
      rw [nextLab, nextLab, nextLab_max a (nextLab b aux), nextLab_max b aux,
        nextLab_max a (nextLab b 0)]
      omega
  | .ite cmp r ri a b, aux => by
      rw [nextLab, nextLab, nextLab_max a (nextLab b aux), nextLab_max b aux,
        nextLab_max a (nextLab b 0)]
      omega
  | .loop body, aux => by
      rw [nextLab, nextLab, nextLab_max body aux]
  | .call none dest none, aux => by
      simp only [nextLab]; omega
  | .call none dest (some (hp, k1, k2)), aux => by
      simp only [nextLab]; omega
  | .call (some (rp, lr, l1, l2)) dest none, aux => by
      rw [nextLab, nextLab, nextLab_max rp (max aux (l2 + 2)), nextLab_max rp (max 0 (l2 + 2))]
      omega
  | .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), aux => by
      rw [nextLab, nextLab, nextLab_max rp (nextLab hp (max (max l2 k2 + 2) aux)),
        nextLab_max hp (max (max l2 k2 + 2) aux),
        nextLab_max rp (nextLab hp (max (max l2 k2 + 2) 0)),
        nextLab_max hp (max (max l2 k2 + 2) 0)]
      omega
  | .skip, aux | .halt _, aux | .tick, aux | .ret _, aux | .raise _, aux
  | .break _, aux | .continue _, aux | .inst _, aux | .get _ _, aux
  | .set _ _, aux | .opCurrHeap _ _ _, aux | .alloc _, aux
  | .storeConsts _ _ _, aux | .jumpLower _ _ _, aux | .rawCall _, aux
  | .install _ _ _ _ _, aux | .shMemOp _ _ _, aux | .codeBufferWrite _ _, aux
  | .dataBufferWrite _ _, aux | .ffi _ _ _ _ _ _, aux | .locValue _ _ _, aux
  | .stackAlloc _, aux | .stackFree _, aux | .stackLoad _ _, aux
  | .stackLoadAny _ _, aux | .stackStore _ _, aux | .stackStoreAny _ _, aux
  | .stackGetSize _, aux | .stackSetSize _, aux | .bitmapLoad _ _, aux => by
      simp only [nextLab]; omega
termination_by q => sizeOf q
decreasing_by all_goals simp_wf <;> omega

/-- Exact HOL `next_lab_EQ_MAX` (`stack_allocProofScript.sml:6111-6121`). HOL's
`n` is a vacuous binder of the source statement and is kept. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem next_lab_EQ_MAX {width : Nat} [NeZero width] :
    ∀ (q : HolProg width) (_n aux : Nat), nextLabHOL q aux = max aux (nextLabHOL q 0) :=
  fun q _ aux => nextLab_max q aux

/-- Exact HOL `MAX_SIMP` (`stack_allocProofScript.sml:6123-6127`). -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "MAX_SIMP"]
theorem MAX_SIMP {n m : Nat} : max n (max n m) = max n m := by omega

/-- Exact HOL `next_lab_thm` (`stack_allocProofScript.sml:6129-6154`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem next_lab_thm {width : Nat} [NeZero width] :
    ∀ p : HolProg width,
      nextLabHOL p 2 =
        match p with
        | .seq p1 p2 => max (nextLabHOL p1 2) (nextLabHOL p2 2)
        | .ite _ _ _ p1 p2 => max (nextLabHOL p1 2) (nextLabHOL p2 2)
        | .loop p => nextLabHOL p 2
        | .call none _ none => 2
        | .call none _ (some (_, _, l2)) => max (l2 + 2) 2
        | .call (some (p, _, _, l2)) _ none => max (nextLabHOL p 2) (l2 + 2)
        | .call (some (p, _, _, l2)) _ (some (p', _, l3)) =>
            max (max (nextLabHOL p 2) (nextLabHOL p' 2)) (max l2 l3 + 2)
        | _ => 2 := by
  intro p
  cases p with
  | seq a b =>
      simp only [nextLabHOL]; rw [nextLab, nextLab_max a, nextLab_max a 2, nextLab_max b 2]; omega
  | ite cmp r ri a b =>
      simp only [nextLabHOL]; rw [nextLab, nextLab_max a, nextLab_max a 2, nextLab_max b 2]; omega
  | loop body => simp only [nextLabHOL]; rw [nextLab]
  | call ret dest handler =>
      rcases ret with _ | ⟨rp, lr, l1, l2⟩ <;> rcases handler with _ | ⟨hp, k1, k2⟩
      · simp only [nextLabHOL, nextLab]
      · simp only [nextLabHOL, nextLab]; omega
      · simp only [nextLabHOL]; rw [nextLab, nextLab_max rp, nextLab_max rp 2]; omega
      · simp only [nextLabHOL]
        rw [nextLab, nextLab_max rp, nextLab_max hp, nextLab_max rp 2, nextLab_max hp 2]; omega
  | _ => simp only [nextLabHOL, nextLab]

/-- Exact HOL `extract_labels_next_lab` (`stack_allocProofScript.sml:6156-6165`):
every label of a program is below its `next_lab`. HOL's `aux` is a vacuous binder
of the source statement and is kept. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem extract_labels_next_lab {width : Nat} [NeZero width] :
    ∀ (p : HolProg width) (_aux : Nat) (e : Nat × Nat),
      e ∈ StackPropsCodeLabels.extractLabels p → e.2 < nextLabHOL p 2
  | .seq a b, aux, e, h => by
      rw [StackPropsCodeLabels.extractLabels, List.mem_append] at h
      rw [next_lab_thm]
      rcases h with h | h
      · have := extract_labels_next_lab a aux e h; dsimp only; omega
      · have := extract_labels_next_lab b aux e h; dsimp only; omega
  | .ite cmp r ri a b, aux, e, h => by
      rw [StackPropsCodeLabels.extractLabels, List.mem_append] at h
      rw [next_lab_thm]
      rcases h with h | h
      · have := extract_labels_next_lab a aux e h; dsimp only; omega
      · have := extract_labels_next_lab b aux e h; dsimp only; omega
  | .loop body, aux, e, h => by
      rw [StackPropsCodeLabels.extractLabels] at h
      rw [next_lab_thm]
      exact extract_labels_next_lab body aux e h
  | .call none dest handler, aux, e, h => by
      simp [StackPropsCodeLabels.extractLabels] at h
  | .call (some (rp, lr, l1, l2)) dest none, aux, e, h => by
      simp only [StackPropsCodeLabels.extractLabels, List.mem_append, List.mem_singleton] at h
      rw [next_lab_thm]
      rcases h with rfl | h
      · dsimp only; omega
      · have := extract_labels_next_lab rp aux e h; dsimp only; omega
  | .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), aux, e, h => by
      simp only [StackPropsCodeLabels.extractLabels, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rw [next_lab_thm]
      rcases h with ((rfl | rfl) | h) | h
      · dsimp only; omega
      · dsimp only; omega
      · have := extract_labels_next_lab rp aux e h; dsimp only; omega
      · have := extract_labels_next_lab hp aux e h; dsimp only; omega
  | .skip, _, _, h | .halt _, _, _, h | .tick, _, _, h | .ret _, _, _, h | .raise _, _, _, h
  | .break _, _, _, h | .continue _, _, _, h | .inst _, _, _, h | .get _ _, _, _, h
  | .set _ _, _, _, h | .opCurrHeap _ _ _, _, _, h | .alloc _, _, _, h
  | .storeConsts _ _ _, _, _, h | .jumpLower _ _ _, _, _, h | .rawCall _, _, _, h
  | .install _ _ _ _ _, _, _, h | .shMemOp _ _ _, _, _, h | .codeBufferWrite _ _, _, _, h
  | .dataBufferWrite _ _, _, _, h | .ffi _ _ _ _ _ _, _, _, h | .locValue _ _ _, _, _, h
  | .stackAlloc _, _, _, h | .stackFree _, _, _, h | .stackLoad _ _, _, _, h
  | .stackLoadAny _ _, _, _, h | .stackStore _ _, _, _, h | .stackStoreAny _ _, _, _, h
  | .stackGetSize _, _, _, h | .stackSetSize _, _, _, h | .bitmapLoad _ _, _, _, h => by
      simp [StackPropsCodeLabels.extractLabels] at h
termination_by p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

namespace LabPresSupport

/-- Freshness of two consecutive compiled label lists (the `ALL_DISTINCT_APPEND`
step of HOL's `stack_alloc_lab_pres` proof). -/
theorem pres_append {nl m1 m2 : Nat} {La Lb Lq1 Lq2 : List (Nat × Nat)}
    (hdisj : ∀ x ∈ La, ∀ y ∈ Lb, x ≠ y) (hA : ∀ x ∈ La, x.2 < nl) (hB : ∀ x ∈ Lb, x.2 < nl)
    (nd1 : Lq1.Nodup) (nd2 : Lq2.Nodup)
    (mem1 : ∀ x ∈ Lq1, x ∈ La ∨ (nl ≤ x.2 ∧ x.2 < m1))
    (mem2 : ∀ x ∈ Lq2, x ∈ Lb ∨ (m1 ≤ x.2 ∧ x.2 < m2)) (h1 : nl ≤ m1) (h2 : m1 ≤ m2) :
    (Lq1 ++ Lq2).Nodup ∧ ∀ x ∈ Lq1 ++ Lq2, x ∈ La ++ Lb ∨ (nl ≤ x.2 ∧ x.2 < m2) := by
  refine ⟨List.nodup_append.2 ⟨nd1, nd2, ?_⟩, ?_⟩
  · rintro x hx y hy rfl
    rcases mem1 x hx with ha | ⟨ha1, ha2⟩ <;> rcases mem2 x hy with hb | ⟨hb1, hb2⟩
    · exact hdisj x ha x hb rfl
    · have := hA x ha; omega
    · have := hB x hb; omega
    · omega
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases mem1 x hx with h | h
      · exact Or.inl (List.mem_append.2 (Or.inl h))
      · exact Or.inr ⟨h.1, by omega⟩
    · rcases mem2 x hx with h | h
      · exact Or.inl (List.mem_append.2 (Or.inr h))
      · exact Or.inr ⟨by omega, h.2⟩

end LabPresSupport

open LabPresSupport StackPropsCodeLabels in
/-- Exact HOL `stack_alloc_lab_pres` (`stack_allocProofScript.sml:6167-6215`):
`comp` keeps the label conventions and distinctness of its input, and every new
label lies in `[nl, nl')`. HOL's `EVERY (λ(l1,l2). P l1 l2)` is a bounded
quantifier over the pairs, `ALL_DISTINCT` is `List.Nodup`, the `let (cp,nl')`
destructuring is the pair projections of `comp n nl p`, and HOL's `aux` is a
vacuous binder of the source statement, kept. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stack_alloc_lab_pres {width : Nat} [NeZero width] :
    ∀ (n nl : Nat) (p : HolProg width) (_aux : Nat),
      (∀ lab ∈ extractLabels p, lab.1 = n ∧ lab.2 ≠ 0 ∧ lab.2 ≠ 1) ∧
      (extractLabels p).Nodup ∧ nextLabHOL p 2 ≤ nl →
      (∀ lab ∈ extractLabels (comp n nl p).1, lab.1 = n ∧ lab.2 ≠ 0 ∧ lab.2 ≠ 1) ∧
      (extractLabels (comp n nl p).1).Nodup ∧
      (∀ lab ∈ extractLabels (comp n nl p).1,
        lab ∈ extractLabels p ∨ (nl ≤ lab.2 ∧ lab.2 < (comp n nl p).2)) ∧
      nl ≤ (comp n nl p).2
  | n, nl, .seq a b, aux, ⟨hok, hnd, hnl⟩ => by
      rw [next_lab_thm] at hnl
      dsimp only at hnl
      rw [extractLabels] at hok hnd
      obtain ⟨ndA, ndB, hdisj⟩ := List.nodup_append.1 hnd
      rcases ha : comp n nl a with ⟨q1, m1⟩
      rcases hb : comp n m1 b with ⟨q2, m2⟩
      have IA := stack_alloc_lab_pres n nl a aux
        ⟨fun l hl => hok l (List.mem_append.2 (Or.inl hl)), ndA, by omega⟩
      rw [ha] at IA
      obtain ⟨okA, ndA', memA, leA⟩ := IA
      have IB := stack_alloc_lab_pres n m1 b aux
        ⟨fun l hl => hok l (List.mem_append.2 (Or.inr hl)), ndB, by dsimp only at leA; omega⟩
      rw [hb] at IB
      obtain ⟨okB, ndB', memB, leB⟩ := IB
      simp only [comp, ha, hb]
      rw [extractLabels, extractLabels]
      obtain ⟨hn, hm⟩ := pres_append hdisj
        (fun x hx => by have := extract_labels_next_lab a aux x hx; omega)
        (fun x hx => by have := extract_labels_next_lab b aux x hx; omega) ndA' ndB' memA memB leA leB
      refine ⟨fun l hl => ?_, hn, hm, by dsimp only at leA leB ⊢; omega⟩
      rcases List.mem_append.1 hl with hl | hl
      · exact okA l hl
      · exact okB l hl
  | n, nl, .ite cmp r ri a b, aux, ⟨hok, hnd, hnl⟩ => by
      rw [next_lab_thm] at hnl
      dsimp only at hnl
      rw [extractLabels] at hok hnd
      obtain ⟨ndA, ndB, hdisj⟩ := List.nodup_append.1 hnd
      rcases ha : comp n nl a with ⟨q1, m1⟩
      rcases hb : comp n m1 b with ⟨q2, m2⟩
      have IA := stack_alloc_lab_pres n nl a aux
        ⟨fun l hl => hok l (List.mem_append.2 (Or.inl hl)), ndA, by omega⟩
      rw [ha] at IA
      obtain ⟨okA, ndA', memA, leA⟩ := IA
      have IB := stack_alloc_lab_pres n m1 b aux
        ⟨fun l hl => hok l (List.mem_append.2 (Or.inr hl)), ndB, by dsimp only at leA; omega⟩
      rw [hb] at IB
      obtain ⟨okB, ndB', memB, leB⟩ := IB
      simp only [comp, ha, hb]
      rw [extractLabels, extractLabels]
      obtain ⟨hn, hm⟩ := pres_append hdisj
        (fun x hx => by have := extract_labels_next_lab a aux x hx; omega)
        (fun x hx => by have := extract_labels_next_lab b aux x hx; omega) ndA' ndB' memA memB leA leB
      refine ⟨fun l hl => ?_, hn, hm, by dsimp only at leA leB ⊢; omega⟩
      rcases List.mem_append.1 hl with hl | hl
      · exact okA l hl
      · exact okB l hl
  | n, nl, .loop body, aux, ⟨hok, hnd, hnl⟩ => by
      rw [next_lab_thm] at hnl
      rw [extractLabels] at hok hnd
      have IB := stack_alloc_lab_pres n nl body aux ⟨hok, hnd, hnl⟩
      simp only [comp]
      rw [show extractLabels (.loop (comp n nl body).1) = extractLabels (comp n nl body).1 from by
          rw [extractLabels],
        show extractLabels (.loop body) = extractLabels body from by rw [extractLabels]]
      exact IB
  | n, nl, .alloc k, aux, ⟨hok, hnd, hnl⟩ => by
      rw [next_lab_thm] at hnl
      simp only [comp, extractLabels, List.append_nil, List.mem_singleton, List.nodup_cons,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, forall_eq, true_and]
      dsimp only at hnl
      omega
  | n, nl, .storeConsts t1 t2 (some loc), aux, ⟨hok, hnd, hnl⟩ => by
      rw [next_lab_thm] at hnl
      simp only [comp, extractLabels, List.append_nil, List.mem_singleton, List.nodup_cons,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, forall_eq, true_and]
      dsimp only at hnl
      omega
  | n, nl, .call none dest handler, aux, ⟨hok, hnd, hnl⟩ => by
      simp [comp, extractLabels]
  | n, nl, .call (some (rp, lr, l1, l2)) dest none, aux, ⟨hok, hnd, hnl⟩ => by
      rw [next_lab_thm] at hnl
      dsimp only at hnl
      simp only [extractLabels, List.singleton_append, List.nodup_cons, List.mem_cons] at hok hnd
      obtain ⟨hnot, ndR⟩ := hnd
      rcases ha : comp n nl rp with ⟨q1, m1⟩
      have IA := stack_alloc_lab_pres n nl rp aux
        ⟨fun l hl => hok l (Or.inr hl), ndR, by omega⟩
      rw [ha] at IA
      obtain ⟨okA, ndA', memA, leA⟩ := IA
      simp only [comp, ha]
      simp only [extractLabels, List.singleton_append, List.nodup_cons, List.mem_cons]
      refine ⟨?_, ⟨fun hm => ?_, ndA'⟩, ?_, leA⟩
      · rintro l (rfl | hl)
        · exact hok _ (Or.inl rfl)
        · exact okA l hl
      · rcases memA _ hm with h | h
        · exact hnot h
        · dsimp only at h; omega
      · rintro l (rfl | hl)
        · exact Or.inl (Or.inl rfl)
        · rcases memA l hl with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
  | n, nl, .call (some (rp, lr, l1, l2)) dest (some (hp, k1, k2)), aux, ⟨hok, hnd, hnl⟩ => by
      rw [next_lab_thm] at hnl
      dsimp only at hnl
      simp only [extractLabels, List.cons_append, List.nil_append, List.nodup_cons,
        List.mem_cons, List.mem_append] at hok hnd
      obtain ⟨hnot1, hnot2, hnd⟩ := hnd
      obtain ⟨ndR, ndH, hdisj⟩ := List.nodup_append.1 hnd
      rcases ha : comp n nl rp with ⟨q1, m1⟩
      rcases hb : comp n m1 hp with ⟨q2, m2⟩
      have IA := stack_alloc_lab_pres n nl rp aux
        ⟨fun l hl => hok l (Or.inr (Or.inr (Or.inl hl))), ndR, by omega⟩
      rw [ha] at IA
      obtain ⟨okA, ndA', memA, leA⟩ := IA
      have IB := stack_alloc_lab_pres n m1 hp aux
        ⟨fun l hl => hok l (Or.inr (Or.inr (Or.inr hl))), ndH, by dsimp only at leA; omega⟩
      rw [hb] at IB
      obtain ⟨okB, ndB', memB, leB⟩ := IB
      obtain ⟨hn, hm⟩ := pres_append hdisj
        (fun x hx => by have := extract_labels_next_lab rp aux x hx; omega)
        (fun x hx => by have := extract_labels_next_lab hp aux x hx; omega) ndA' ndB' memA memB leA leB
      simp only [comp, ha, hb]
      simp only [extractLabels, List.cons_append, List.nil_append, List.nodup_cons,
        List.mem_cons]
      dsimp only at leA leB
      refine ⟨?_, ⟨?_, ?_, hn⟩, ?_, by omega⟩
      · rintro l (rfl | rfl | hl)
        · exact hok _ (Or.inl rfl)
        · exact hok _ (Or.inr (Or.inl rfl))
        · rcases List.mem_append.1 hl with hl | hl
          · exact okA l hl
          · exact okB l hl
      · rintro (h | h)
        · exact hnot1 (Or.inl h)
        · rcases hm _ h with h | h
          · exact hnot1 (Or.inr (List.mem_append.1 h))
          · dsimp only at h; omega
      · intro h
        rcases hm _ h with h | h
        · exact hnot2 (List.mem_append.1 h)
        · dsimp only at h; omega
      · rintro l (rfl | rfl | hl)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (Or.inl rfl))
        · rcases hm l hl with h | h
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr ⟨h.1, by omega⟩
  | n, nl, .storeConsts t1 t2 none, _, _
  | n, nl, .skip, _, _ | n, nl, .halt _, _, _ | n, nl, .tick, _, _ | n, nl, .ret _, _, _
  | n, nl, .raise _, _, _ | n, nl, .break _, _, _ | n, nl, .continue _, _, _
  | n, nl, .inst _, _, _ | n, nl, .get _ _, _, _ | n, nl, .set _ _, _, _
  | n, nl, .opCurrHeap _ _ _, _, _ | n, nl, .jumpLower _ _ _, _, _ | n, nl, .rawCall _, _, _
  | n, nl, .install _ _ _ _ _, _, _ | n, nl, .shMemOp _ _ _, _, _
  | n, nl, .codeBufferWrite _ _, _, _ | n, nl, .dataBufferWrite _ _, _, _
  | n, nl, .ffi _ _ _ _ _ _, _, _ | n, nl, .locValue _ _ _, _, _
  | n, nl, .stackAlloc _, _, _ | n, nl, .stackFree _, _, _ | n, nl, .stackLoad _ _, _, _
  | n, nl, .stackLoadAny _ _, _, _ | n, nl, .stackStore _ _, _, _
  | n, nl, .stackStoreAny _ _, _, _ | n, nl, .stackGetSize _, _, _
  | n, nl, .stackSetSize _, _, _ | n, nl, .bitmapLoad _ _, _, _ => by
      simp [comp, extractLabels]
termination_by _ _ p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

end Flapjack.Compiler.Backend.StackAlloc
