import Mathlib.Data.List.Nodup
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownPipelineSemantics
import Flapjack.Compiler.Backend.ClosKnown.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberedPrepared

/-! Label accounting for the incremental known-function optimizer. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosProps Flapjack.Compiler.Backend.ClosKnown
open Flapjack.Compiler.Backend.BackendProps

/-- The source optimizer preserves a leading integer entry marker. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "known_Op_Const"]
theorem knownOpConst (c : ClosKnown.Config) (trace : BackendCommon.Tra) (n : Nat)
    (xs : List ClosLang.Exp) (env : List ValApprox) (g : Spt ValApprox) :
    knownListTotal c (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs) env g =
      let (eas, next) := knownListTotal c xs env g
      ((.op trace (.intOp (.const (Int.ofNat n))) [], .int (Int.ofNat n)) :: eas, next) := by
  have marker : knownListTotal c [.op trace (.intOp (.const (Int.ofNat n))) []] env g =
      ([(.op trace (.intOp (.const (Int.ofNat n))) [], .int (Int.ofNat n))], g) := by
    simp [knownListTotal_op, knownListTotal, knownOpHOL, ClosOp.smartOp, ClosOp.smartOp']
  cases xs with
  | nil => simpa [knownListTotal] using marker
  | cons x xs =>
    rw [knownListTotal_cons_cons, marker]
    cases h : knownListTotal c (x :: xs) env g; simp [h]

/-- The incremental optimizer preserves the entry marker and the number of
following expressions. This is Lean-side composition of the source passes. -/
theorem knownCompileInc_marker {A : Type} (c : ClosKnown.Config) (g : Spt ValApprox)
    (trace : BackendCommon.Tra) (n : Nat) (xs : List ClosLang.Exp) (aux : List A) :
    ∃ output : List ClosLang.Exp,
      (knownCompileInc (some c) g
        (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs, aux)).2.1 =
          .op trace (.intOp (.const (Int.ofNat n))) [] :: output ∧ output.length = xs.length := by
  let cleaned := ClosFvs.removeList 0 xs
  cases run : knownListTotal (resetInlineFactor c) cleaned [] g with
  | mk eas next =>
    have len := knownListTotal_length (resetInlineFactor c) cleaned [] g
    rw [run] at len
    have cleanupLen : cleaned.length = xs.length := ClosFvs.removeList_length 0 xs
    refine ⟨ClosLetop.compileList (ClosTicks.removeList (eas.map Prod.fst)), ?_, ?_⟩
    · simp only [knownCompileInc, ClosFvs.compileInc, ClosKnown.compileInc, ClosFvs.compile,
        ClosFvs.removeList, ClosFvs.removeSing, ClosTicks.compileInc, ClosLetop.compileInc]
      change ClosLetop.compileList (ClosTicks.removeList
        ((knownListTotal (resetInlineFactor c)
          (.op trace (.intOp (.const (Int.ofNat n))) [] :: cleaned) [] g).1.map Prod.fst)) = _
      rw [knownOpConst, run]
      rfl
    · have ticksLength : ∀ es : List ClosLang.Exp, (ClosTicks.removeList es).length = es.length := by
        intro es
        induction es with
        | nil => rfl
        | cons e es ih => simp [ClosTicks.removeList, ih]
      have letopLength : ∀ es : List ClosLang.Exp, (ClosLetop.compileList es).length = es.length := by
        intro es
        induction es with
        | nil => rfl
        | cons e es ih => simp [ClosLetop.compileList, ih]
      simpa [letopLength, ticksLength, cleanupLen] using len


/-- Incremental optimization cannot increase a label's multiplicity in the
main expression list. This is Lean-side composition of the source passes. -/
theorem knownCompileInc_codeLocations {A : Type} (c : ClosKnown.Config) (g : Spt ValApprox)
    (program : List ClosLang.Exp × List A) (label : Nat) :
    (codeLocations (knownCompileInc (some c) g program).2.1).count label ≤
      (codeLocations program.1).count label := by
  cases run : knownListTotal (resetInlineFactor c) (ClosFvs.compile program.1) [] g with
  | mk eas next =>
    have bound := ClosKnown.TraversalCodeBag.knownCodeLocationsBag (resetInlineFactor c)
      (ClosFvs.compile program.1) [] g eas next run label
    have run' : knownListTotal (resetInlineFactor c) (ClosFvs.removeList 0 program.1) [] g = (eas, next) := by
      simpa [ClosFvs.compile] using run
    simpa [knownCompileInc, ClosFvs.compileInc, ClosKnown.compileInc, run',
      ClosTicks.compileInc, ClosLetop.compileInc, ClosLetop.compileList_codeLocations,
      ClosTicks.removeList_codeLocations, ClosFvs.compile, ClosFvs.removeList_codeLocations] using bound

/-- Each future optimized expression list has no more copies of a code label
than the corresponding numbered list. This is Lean-side oracle composition. -/
theorem knownClosureFuture_codeLocations {C : Type} (c : ClosKnown.Config)
    (oracle : ClosSem.CompileOracle (Nat × (Spt ValApprox × C))) (i label : Nat) :
    (codeLocations (knownClosureFuture c oracle i).2.1).count label ≤
      (codeLocations (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle i).2.1).count label := by
  let numbered := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle
  have bound := knownCompileInc_codeLocations c (numbered i).1.1 (numbered i).2 label
  simpa [knownClosureFuture, numbered, knownCompileInc, stateCo, pureCo,
    ClosFvs.compileInc, ClosTicks.compileInc, ClosLetop.compileInc, fvsInc, ticksInc, letopInc] using bound

/-- Incremental optimization introduces no new closure-code locations. -/
theorem knownClosureFuture_codeLocations_subset {C : Type} (c : ClosKnown.Config)
    (oracle : ClosSem.CompileOracle (Nat × (Spt ValApprox × C))) (i : Nat) :
    codeLocations (knownClosureFuture c oracle i).2.1 ⊆
      codeLocations (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) oracle i).2.1 := by
  intro label member
  exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
    (knownClosureFuture_codeLocations c oracle i label))

/-- Numbering and incremental optimization produce distinct code locations. -/
theorem knownClosureFuture_codeLocations_nodup {C : Type} (c : ClosKnown.Config)
    (oracle : ClosSem.CompileOracle (Nat × (Spt ValApprox × C))) (i : Nat) :
    (codeLocations (knownClosureFuture c oracle i).2.1).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro label
  apply Nat.le_trans (knownClosureFuture_codeLocations c oracle i label)
  apply List.nodup_iff_count_le_one.mp ?_ label
  simpa [stateCo, ClosNumber.ignoreTable] using
    ClosNumber.compileInc_codeLocations_nodup (oracle i).1.1 (oracle i).2.1

/-- Numbering and the incremental optimizer preserve the entry marker and
one output expression per original expression. -/
theorem knownClosureFuture_marker {C : Type} (c : ClosKnown.Config)
    (oracle : ClosSem.CompileOracle (Nat × (Spt ValApprox × C))) (i : Nat) :
    ∃ output : List ClosLang.Exp,
      (knownClosureFuture c oracle i).2.1 =
        .op .none (.intOp (.const (Int.ofNat (oracle i).1.1))) [] :: output ∧
      output.length = (oracle i).2.1.length := by
  let start := (oracle i).1.1
  let expressions := (oracle i).2.1
  let next := start + max expressions.length 1
  let aligned := if next % 2 = 0 then next else next + 1
  cases numbered : ClosNumber.renumberList aligned expressions with
  | mk nextLoc numberedExpressions =>
    have length := ClosNumber.renumberList_length expressions aligned
    rw [numbered] at length
    have result := knownCompileInc_marker c (oracle i).1.2.1 .none start numberedExpressions (oracle i).2.2
    obtain ⟨output, result, outputLength⟩ := result
    refine ⟨output, ?_, ?_⟩
    · simpa [knownClosureFuture, knownCompileInc, stateCo, pureCo, ClosNumber.ignoreTable,
        ClosNumber.compileInc, start, expressions, next, aligned, numbered,
        fvsInc, ticksInc, letopInc, ClosFvs.compileInc, ClosTicks.compileInc, ClosLetop.compileInc] using result
    · simpa [start, expressions] using outputLength.trans length

/-- Numbering followed by incremental optimization and annotation emits
unique BVL labels within the corresponding numbering interval. -/
theorem knownClosureFuture_labels {C : Type} (maxApp : Nat) (c : ClosKnown.Config)
    (oracle : ClosSem.CompileOracle (Nat × (Spt ValApprox × C)))
    (state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) oracle) :
    ∀ i, ((compileInc maxApp (ClosAnnotate.compileInc (knownClosureFuture c oracle i).2)).map Prod.fst).Nodup ∧
      ∀ label ∈ (compileInc maxApp (ClosAnnotate.compileInc (knownClosureFuture c oracle i).2)).map Prod.fst,
        (oracle i).1.1 + numStubs maxApp ≤ label ∧ label < (oracle (i + 1)).1.1 + numStubs maxApp := by
  intro i
  let start := (oracle i).1.1
  let expressions := (oracle i).2.1
  let future := (knownClosureFuture c oracle i).2.1
  let program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp) :=
    (ClosAnnotate.annotateList 0 future, [])
  have emptyAux : (knownClosureFuture c oracle i).2.2 = [] := by
    simp [knownClosureFuture, pureCo, letopInc, ClosLetop.compileInc]
  have programEq : ClosAnnotate.compileInc (knownClosureFuture c oracle i).2 = program := by
    change (ClosAnnotate.annotateList 0 future, ClosAnnotate.compile (knownClosureFuture c oracle i).2.2) = program
    rw [emptyAux]
    rfl
  obtain ⟨output, marker, outputLength⟩ := knownClosureFuture_marker c oracle i
  have marker' : future = .op .none (.intOp (.const (Int.ofNat start))) [] :: output := by
    simpa [future, start] using marker
  have shape := extractName_numbered_marker start (ClosAnnotate.annotateList 0 output)
  have annotatedMarker : program.1 = .op .none (.intOp (.const (Int.ofNat start))) [] ::
      ClosAnnotate.annotateList 0 output := by
    simpa [program, marker'] using ClosAnnotate.annotateList_name_marker start output
  let real := (extractName program.1).2
  have startEq : (extractName program.1).1 = start := by simpa [annotatedMarker] using shape.1
  have lengthEq : real.length = max 1 expressions.length := by
    have length' : real.length = max 1 output.length := by
      simpa [real, annotatedMarker, ClosAnnotate.annotateList_length] using shape.2.1
    simpa [expressions, outputLength] using length' 
  have extract : extractName program.1 = (start, real) := by
    cases h : extractName program.1 with
    | mk first second => simp [real, h] at startEq ⊢; exact startEq
  have realSub : codeLocations real ⊆ codeLocations future := by
    rw [show codeLocations real = codeLocations (ClosAnnotate.annotateList 0 output) by
      simpa [real, annotatedMarker] using shape.2.2]
    have sub := ClosAnnotate.annotateList_codeLocations 0 output
    simpa [marker', codeLocations, codeLocationsExp] using sub
  have numberedSub := knownClosureFuture_codeLocations_subset c oracle i
  have mainDistinct : (codeLocations real).Nodup := by
    rw [show codeLocations real = codeLocations (ClosAnnotate.annotateList 0 output) by
      simpa [real, annotatedMarker] using shape.2.2]
    apply ClosAnnotate.annotateList_codeLocations_nodup
    have distinct : (codeLocations future).Nodup := knownClosureFuture_codeLocations_nodup c oracle i
    simpa [marker', codeLocations, codeLocationsExp] using distinct
  have auxDistinct : ((program.2.map Prod.fst) ++
      codeLocations (program.2.map (fun (_, _, body) => body))).Nodup := by simp [program, codeLocations]
  have mainBounds : ∀ location ∈ codeLocations real,
      start ≤ location ∧ location < (oracle (i + 1)).1.1 := by
    intro location member
    exact numberingOracle_location_bounds oracle state i location (numberedSub (realSub member))
  have mainAbove : ∀ location ∈ codeLocations real, start + max 1 real.length ≤ location := by
    intro location member
    have after := ClosNumber.compileInc_location_after_entries start location expressions (by
      simpa [stateCo, ClosNumber.ignoreTable, start, expressions] using numberedSub (realSub member))
    simpa [lengthEq, start, expressions] using after
  have entriesBound : start + max 1 real.length ≤ (oracle (i + 1)).1.1 := by
    have reserve := ClosNumber.compileInc_reservation start expressions
    have next := state i
    simp only [ClosNumber.ignoreTable] at next
    simpa [lengthEq, start, expressions, next] using reserve
  have unique := compileInc_labels_nodup maxApp start program real extract mainDistinct auxDistinct
    mainAbove (by simp [program, codeLocations]) (by simp [program, codeLocations])
  have ranges := compileInc_labels_range maxApp start (oracle (i + 1)).1.1 program real extract
    entriesBound mainBounds (by simp [program])
  rw [programEq]
  exact ⟨unique, ranges⟩

end Flapjack.Compiler.Backend.ClosToBvl
