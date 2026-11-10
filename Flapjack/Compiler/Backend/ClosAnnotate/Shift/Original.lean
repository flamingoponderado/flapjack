module

public import Flapjack.Compiler.Backend.ClosAnnotate.Shift
public import Flapjack.Misc.ListEl
public import Mathlib.Tactic

@[expose] public section

/-! Source-shaped closure variable shifting. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang

/-- The original list-shaped shifting recursion. The attached map supplies
termination evidence for recursive function bodies. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shift_def"]
noncomputable def shiftSource : List Exp → Nat → Nat → Spt Nat → List Exp
  | [], _, _, _ => []
  | x :: y :: xs, m, l, i => shiftSource [x] m l i ++ shiftSource (y :: xs) m l i
  | [.var t v], m, l, i => [.var t (getVar m l i v)]
  | [.ifThenElse t x y z], m, l, i =>
      [.ifThenElse t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m l i))
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [y] m l i))
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [z] m l i))]
  | [.let t xs x], m, l, i =>
      [.let t (shiftSource xs m l i)
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m (l + xs.length) i))]
  | [.raise t x], m, l, i =>
      [.raise t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m l i))]
  | [.tick t x], m, l, i =>
      [.tick t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m l i))]
  | [.op t op xs], m, l, i => [.op t op (shiftSource xs m l i)]
  | [.app t loc x xs], m, l, i =>
      [.app t loc (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m l i))
        (shiftSource xs m l i)]
  | [.fn name loc vs args x], m, l, i =>
      let k := m + l
      let live := (vs.getD []).filter (· < k)
      let vars := live.map (getVar m l i)
      [.fn name loc (some vars) args
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] k args (shiftedEnv 0 live)))]
  | [.letrec names loc vs fs x], m, l, i =>
      let k := m + l
      let live := (vs.getD []).filter (· < k)
      let vars := live.map (getVar m l i)
      let newI := shiftedEnv 0 live
      let cs := fs.attach.map fun ⟨entry, _member⟩ =>
        (entry.1, @Flapjack.holHd Exp ⟨.var .none 0⟩
          (shiftSource [entry.2] k (entry.1 + fs.length) newI))
      [.letrec names loc (some vars) cs
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m (l + fs.length) i))]
  | [.handle t x y], m, l, i =>
      [.handle t (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m l i))
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [y] m (l + 1) i))]
  | [.call t ticks dest xs], m, l, i => [.call t ticks dest (shiftSource xs m l i)]
termination_by expressions => sizeOf expressions
decreasing_by
  all_goals try (have h := List.sizeOf_lt_of_mem ‹_›)
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals (cases entry; simp only [Prod.mk.sizeOf_spec] at *; omega)

/-- The recursive-group clause with the original ordinary map. This equation
is supporting infrastructure for comparing the source traversal with the
executable traversal. -/
theorem shiftSource_letrec (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (fs : List (Nat × Exp))
    (x : Exp) (m l : Nat) (i : Spt Nat) :
    shiftSource [.letrec names loc vs fs x] m l i =
      let k := m + l
      let live := (vs.getD []).filter (· < k)
      let vars := live.map (getVar m l i)
      let newI := shiftedEnv 0 live
      let cs := fs.map fun (n, body) =>
        (n, @Flapjack.holHd Exp ⟨.var .none 0⟩
          (shiftSource [body] k (n + fs.length) newI))
      [.letrec names loc (some vars) cs
        (@Flapjack.holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m (l + fs.length) i))] := by
  simp only [shiftSource, List.map_attach_eq_pmap, List.pmap_eq_map]

end Flapjack.Compiler.Backend.ClosAnnotate
