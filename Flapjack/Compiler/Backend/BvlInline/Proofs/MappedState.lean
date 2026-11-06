import Flapjack.Compiler.Backend.BvlInline.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call

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

/-- Mapped states have equal code domains. -/
theorem mappedStateRel_codeDomain {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (s t : State C F) (related : mappedStateRel transform s t) : sptDomain t.code = sptDomain s.code := by
  have code := congrArg (fun state : State C F => state.code) related.1
  rw [code, sptDomain_sptMap]

/-- Replacing mapped code fields recovers the source state. -/
theorem mappedStateRel_unframe {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (s t : State C F) (related : mappedStateRel transform s t) :
    { t with code := s.code, compile := s.compile, compileOracle := s.compileOracle } = s := by
  have fields := related.1
  cases s
  cases t
  simp_all

/-- Related states remain related after an update retaining the mapped code
fields. -/
theorem mappedStateRel_reframe {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (s t next : State C F) (related : mappedStateRel transform s t)
    (frame : next.code = t.code ∧ next.compile = t.compile ∧ next.compileOracle = t.compileOracle) :
    mappedStateRel transform
      { next with code := s.code, compile := s.compile, compileOracle := s.compileOracle } next := by
  have code := congrArg (fun state : State C F => state.code) related.1
  have oracle := congrArg (fun state : State C F => state.compileOracle) related.1
  obtain ⟨hcode, hcompile, horacle⟩ := frame
  constructor
  · cases next
    simp_all
  · simpa [hcompile] using related.2

/-- Mapping bodies preserves program labels. -/
theorem mappedProgram_labels (transform : Nat → Bvl.Exp → Bvl.Exp)
    (program : List (Nat × Nat × Bvl.Exp)) :
    (program.map (fun (name, arity, body) => (name, arity, transform arity body))).map Prod.fst =
      program.map Prod.fst := by
  simp [List.map_map, Function.comp_def]

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

/-- Mapping installed entries commutes with the code-tree union. -/
theorem mappedProgram_codeUnion (transform : Nat → Bvl.Exp → Bvl.Exp)
    (code : Spt (Nat × Bvl.Exp)) (program : List (Nat × Nat × Bvl.Exp)) :
    sptUnion (sptMap (fun (arity, body) => (arity, transform arity body)) code)
      (sptFromAList (program.map fun (name, arity, body) => (name, arity, transform arity body))) =
    sptMap (fun (arity, body) => (arity, transform arity body)) (sptUnion code (sptFromAList program)) := by
  rw [sptMap_sptUnion, sptMap_sptFromAList]

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
