module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.StateRel
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Call

@[expose] public section

/-! Common state structure for arity-preserving BVL code transformations. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- A generic arity-preserving code map and its induced compiler and oracle
adapters. This is proof infrastructure for BVL optimization, not a separate
HOL declaration. -/
def mappedStateRel {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp) (s t : State C F) : Prop :=
  t = { s with
    code := sptMap (fun (arity, body) => (arity, transform arity body)) s.code
    compile := t.compile
    compileOracle := fun n => ((s.compileOracle n).1,
      (s.compileOracle n).2.map fun (name, arity, body) => (name, arity, transform arity body)) } ∧
  s.compile = fun config program =>
    t.compile config (program.map fun (name, arity, body) => (name, arity, transform arity body))

/-- Program freshness is invariant under the matching code and program maps. -/
theorem mappedProgram_disjoint (transform : Nat → Bvl.Exp → Bvl.Exp)
    (code : Spt (Nat × Bvl.Exp)) (program : List (Nat × Nat × Bvl.Exp)) :
    (∀ entry ∈ program.map (fun (name, arity, body) => (name, arity, transform arity body)),
      sptLookup entry.1 (sptMap (fun (arity, body) => (arity, transform arity body)) code) = none) ↔
    (∀ entry ∈ program, sptLookup entry.1 code = none) := by
  simp only [List.mem_map, sptLookup_sptMap, Option.map_eq_none_iff]
  constructor
  · intro h entry mem
    exact h (entry.1, entry.2.1, transform entry.2.1 entry.2.2) ⟨entry, mem, rfl⟩
  · intro h entry ⟨original, mem, equal⟩
    subst entry
    exact h original mem

/-- Mapped code lookup preserves selected arguments and transforms the body
at the arity checked by the original lookup. -/
theorem findCode_mapped (transform : Nat → Bvl.Exp → Bvl.Exp) (dest : Option Nat)
    (args : List BvlSem.Value) (code : Spt (Nat × Bvl.Exp)) :
    findCode dest args (sptMap (fun (arity, body) => (arity, transform arity body)) code) =
      (findCode dest args code).map (fun (values, body) => (values, transform values.length body)) := by
  unfold findCode
  simp only [sptLookup_sptMap]
  repeat' (split <;> try simp_all)
  all_goals try omega
  all_goals aesop

/-- Related states resolve a call to the same arguments and the mapped body. -/
theorem mappedStateRel_findCode {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (s t : State C F) (related : mappedStateRel transform s t)
    (dest : Option Nat) (args : List BvlSem.Value) :
    findCode dest args t.code =
      (findCode dest args s.code).map (fun (values, body) => (values, transform values.length body)) := by
  have code := congrArg (fun state : State C F => state.code) related.1
  rw [code]
  exact findCode_mapped transform dest args s.code

/-- Decrementing both related clocks preserves the relation. -/
theorem mappedStateRel_decClock {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (s t : State C F) (related : mappedStateRel transform s t) (amount : Nat) :
    mappedStateRel transform (decClock amount s) (decClock amount t) := by
  obtain ⟨fields, compiler⟩ := related
  constructor
  · have clock := congrArg (fun state : State C F => state.clock) fields
    cases s
    cases t
    simp_all [decClock]
  · simpa [decClock] using compiler

end Flapjack.Compiler.Backend.BvlInline.Proofs
