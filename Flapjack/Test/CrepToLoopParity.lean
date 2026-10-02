import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas
import Flapjack.Pancake.CrepToLoop.Proofs.LocalsRelHelpers
import Flapjack.Misc.Sptree

/-!
Direct parity for `crep_to_loop$compile` (`crep_to_loopScript.sml:120`).
The checked-in HOL fixture covers `Skip` and `Raise`; the latter observes the
compiler-generated temporary assignment before the terminal raise.
-/
namespace Flapjack.Test.CrepToLoopParity

def compileContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

def originalCompileSkip : LoopProg Nat := .skip

def originalCompileRaise : LoopProg Nat :=
  .seq (.assign 1 (.const 17)) (.raise 1)

def leanCompileSkip : LoopProg Nat :=
  compileCrepToLoop compileContext [] (.skip : CrepProg Nat)

def leanCompileRaise : LoopProg Nat :=
  compileCrepToLoop compileContext [] (.raise 17 : CrepProg Nat)

#eval leanCompileSkip
#eval leanCompileRaise

def parityGuard : Bool :=
  match leanCompileSkip, originalCompileSkip, leanCompileRaise, originalCompileRaise with
  | .skip, .skip,
    .seq (.assign 1 (.const 17)) (.raise 1),
    .seq (.assign 1 (.const 17)) (.raise 1) => true
  | _, _, _, _ => false

#eval parityGuard
#guard parityGuard

/-! Cake's `compile Dec` equation (`crep_to_loopScript.sml:167-175`) binds the
    declaration to the fresh expression temporary, then inserts that temporary
    into the continuation live set. -/
def declarationContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 4, target := .rv64i }

def declarationRenamingMatches : Bool :=
  match compileCrepToLoop declarationContext []
      (.dec 9 (.const 7) (.assign 9 (.var 9))) with
  | .seq .skip
      (.seq (.assign 5 (.const 7))
        (.seq (.assign 5 (.var 5)) .skip)) => true
  | _ => false

#guard declarationRenamingMatches

/-- Context used for the call-lowering characterization. Function `1` maps to
    loop label `3`, so the generated call targets `some 3`. -/
def callContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [("f", (3, 1))], maxVar := 4, target := .rv64i }

/-- `crep_to_loop$compile` on `call (SOME ([9], NONE)) 1 [Const 3]`.

    The original always emits a default handler `rt2` for a call returning
    through an exception channel (`crep_to_loopScript.sml:193-206`); for
    `handler = NONE` that `rt2` binds the caught exception and immediately
    re-raises it, which is observationally indistinguishable from an absent
    source handler. -/
def leanCompileCallNoHandler : LoopProg Nat :=
  compileCrepToLoop callContext [] (.call (some ([9], none)) "f" [.const 3])

/-- `crep_to_loop$compile` on a call that names an exception handler, which
    must carry an `rt2` handler exactly like the original. -/
def leanCompileCallWithHandler : LoopProg Nat :=
  compileCrepToLoop callContext []
    (.call (some ([9], some (7, .skip))) "f" [.const 3])

/-- A handler-less source call still carries Cake's default raise handler. -/
def handlerlessCallCarriesRaiseHandler : Bool :=
  match leanCompileCallNoHandler with
  | .seq _ (.seq (.call _ (some 3) _ (some (5, .raise 5, .skip, []))) .skip) => true
  | _ => false

/-! Cake's `rt_vars` maps call return source variables through `ctxt.vars`,
with the documented impossible-case fallback `ctxt.vmax + 1`.  The source
return slot `9` is absent from this probe context, so the HOL equation
requires the fallback destination `6`, not the source slot itself. -/
def callReturnDestinationMappingMatches : Bool :=
  match leanCompileCallNoHandler with
  | .seq _ (.seq (.call (some ([6], [])) (some 3) _ _) .skip) => true
  | _ => false

def leanCompileCallMappedReturn : LoopProg Nat :=
  compileCrepToLoop callContext [] (.call (some ([1], none)) "f" [.const 3])

def callReturnSourceVariableMaps : Bool :=
  match leanCompileCallMappedReturn with
  | .seq _ (.seq (.call (some ([5], [])) (some 3) _ _) .skip) => true
  | _ => false

/-- A call that names an exception handler does emit an `rt2`. -/
def handledCallCarriesRaiseHandler : Bool :=
  match leanCompileCallWithHandler with
  | .seq _ (.seq (.call _ (some 3) _ (some _)) .skip) => true
  | _ => false

#eval leanCompileCallNoHandler
#eval leanCompileCallWithHandler

#guard handlerlessCallCarriesRaiseHandler
#guard callReturnDestinationMappingMatches
#guard callReturnSourceVariableMaps
#guard handledCallCarriesRaiseHandler

/-! Cake's RV64 `compile_crepop` places the long-multiply destination after the
    argument temporaries and returns that destination as the expression result
    (`crep_to_loopScript.sml:67-75`).  Its final live set inserts both
    argument and result temporaries. -/
def crepOpLongMulMatches : Bool :=
  match loopCompileExp compileContext 5 []
      (.crepOp .mul [.const 3, .const 4]) with
  | { code := [.assign 5 (.const 3), .assign 6 (.const 4),
      .arith (.longMul 7 7 5 6)], expression := .var 7,
      nextTemp := 8, live := [5, 6, 7] } => true
  | _ => false

#guard crepOpLongMulMatches

/-! Cake's `crep_to_loop$compile` resolves all four ExtCall operands through
`ctxt.vars` (`crep_to_loopScript.sml:198-213`).  Keep both sides of that
oracle explicit: a complete context emits the mapped FFI payload, while a
missing lookup emits `Skip` rather than leaking an unresolved source slot. -/
def ffiContext : LoopContext Nat :=
  { vars := [(10, 41), (11, 42), (12, 43), (13, 44)],
    functions := [], maxVar := 20, target := .rv64i }

def ffiContextMapped : LoopProg Nat :=
  compileCrepToLoop ffiContext [7]
    (.extCall "halt" 10 11 12 13)

def ffiContextMappingMatches : Bool :=
  match ffiContextMapped with
  | .ffi function configuration configurationLength array arrayLength live =>
      function == "halt" && configuration == 41 &&
        configurationLength == 42 && array == 43 && arrayLength == 44 &&
        live == [7]
  | _ => false

def ffiContextMissing : LoopContext Nat :=
  { ffiContext with vars := [(10, 41), (11, 42), (12, 43)] }

def ffiMissingLookupSkips : Bool :=
  match compileCrepToLoop ffiContextMissing [7]
      (.extCall "halt" 10 11 12 13) with
  | .skip => true
  | _ => false

#guard ffiContextMappingMatches
#guard ffiMissingLookupSkips

/-! Cake resolves a shared-memory destination through `find_var` too
(`crep_to_loopScript.sml:214`); retaining the raw source slot changes the
post-loop store in the hello oracle. -/
def shMemContext : LoopContext Nat :=
  { vars := [(3, 8)], functions := [], maxVar := 0, target := .rv64i }

def leanCompileShMemMapped : LoopProg Nat :=
  compileCrepToLoop shMemContext [] (.shMem .store 3 (.var 1))

def shMemDestinationMappingMatches : Bool :=
  match leanCompileShMemMapped with
  | .seq (.shMem .store 8 (.var 0)) .skip => true
  | _ => false

#guard shMemDestinationMappingMatches

/- Cake's `ShMem` equation skips the statement when its destination source
   variable is absent from `ctxt.vars` (`crep_to_loopScript.sml:214-220`). -/
def shMemMissingLookupSkips : Bool :=
  let missingContext : LoopContext Nat :=
    { shMemContext with vars := [] }
  match compileCrepToLoop missingContext [] (.shMem .store 3 (.var 1)) with
  | .skip => true
  | _ => false

#guard shMemMissingLookupSkips

/- Cake's `StoreGlob` equation uses `nested_seq (p ++ [SetGlobal ...])`, so
   even a side-effect-free initializer ends with the canonical trailing Skip. -/
def storeGlobalNestedSeqMatches : Bool :=
  match compileCrepToLoop compileContext [] (.storeGlob 9 (.const 7)) with
  | .seq (.setGlobal 9 (.const 7)) .skip => true
  | _ => false

#guard storeGlobalNestedSeqMatches

def storeNestedSeqMatches : Bool :=
  match compileCrepToLoop compileContext [] (.store (.const 9) (.const 7)) with
  | .seq (.assign 1 (.const 7))
      (.seq (.store (.const 9) 1) .skip) => true
  | _ => false

def store32NestedSeqMatches : Bool :=
  match compileCrepToLoop compileContext [] (.store32 (.const 9) (.const 7)) with
  | .seq (.assign 1 (.const 9))
      (.seq (.assign 2 (.const 7))
        (.seq (.store32 1 2) .skip)) => true
  | _ => false

def ifNestedSeqMatches : Bool :=
  match compileCrepToLoop compileContext []
      (.ite (.const 1) .skip .skip) with
  | .seq (.assign 1 (.const 1))
      (.seq (.ite .notEqual 1 (.imm 0) .skip .skip []) .skip) => true
  | _ => false

def callNestedSeqMatches : Bool :=
  match leanCompileCallNoHandler with
  | .seq (.assign 5 (.const 3))
      (.seq (.call (some ([6], [])) (some 3) [5]
        (some (5, .raise 5, .skip, []))) .skip) => true
  | _ => false

#guard storeNestedSeqMatches
#guard store32NestedSeqMatches
#guard ifNestedSeqMatches
#guard callNestedSeqMatches

/- Cake's `Primitive` equation maps both destination and argument slots through
   `ctxt.vars`; leaving the source numbers untouched shifts every subsequent
   `ctxt.vars`; keeping source slots here changes the allocator input even when
   the primitive itself is otherwise unchanged. -/
def primitiveContext : LoopContext Nat :=
  { vars := [(2, 8), (3, 9), (4, 10), (5, 11), (6, 12)],
    functions := [], maxVar := 20, target := .rv64i }

def primitiveMappingMatches : Bool :=
  match compileCrepToLoop primitiveContext []
      (.primitive [2, 3] .addCarry [4, 5, 6]) with
  | .primitive [8, 9] .addCarry [10, 11, 12] => true
  | _ => false

#guard primitiveMappingMatches

def assignDestinationMappingMatches : Bool :=
  match compileCrepToLoop shMemContext [] (.assign 3 (.var 1)) with
  | .seq (.assign 8 (.var 0)) .skip => true
  | _ => false

#guard assignDestinationMappingMatches

/-- Context for the comparison-lowering characterization. Variable `5` is a
    local that is live across the comparison (for example a value assigned
    before a `while`). -/
def comparisonContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

/-- `crep_to_loop$compile` on `Assign 1 (Cmp Less (Var 3) (Var 5))` with an
    incoming live set containing `5`. The comparison case threads the incoming
    live set into the materialising `ite`'s live field
    (`loopListInsert [leftTemp, rightTemp] live`, `crep_to_loopScript.sml`), so a
    value that is live across the comparison is retained by `loop_live`.
    Dropping that set made `loopShrink` delete the pre-loop assignment and the
    result variable read back the stale value (bead flapjack-8tb.1; original
    CakeML keeps `ori a0,zero,7` and returns 7 for the minimal reproducer). -/
def leanCompileComparisonKeepingLive : LoopProg Nat :=
  compileCrepToLoop comparisonContext [5] (.assign 1 (.cmp .less (.var 3) (.var 5)))

/-- All live sets attached to `ite` nodes in a loop program. -/
def loopIteLives : LoopProg Nat → List (List Nat)
  | .ite _ _ _ _ _ live => [live]
  | .seq first second => loopIteLives first ++ loopIteLives second
  | .loop _ body _ => loopIteLives body
  | .call _ _ _ (some (_, handler, _, _)) => loopIteLives handler
  | _ => []

/-- The materialising comparison keeps the incoming live variable. -/
def comparisonKeepsIncomingLive : Bool :=
  (loopIteLives leanCompileComparisonKeepingLive).any (fun live => live.contains 5)

/-- With no incoming live variable the comparison does not invent one. -/
def comparisonWithoutLiveDropsIt : Bool :=
  !((loopIteLives (compileCrepToLoop comparisonContext []
        (.assign 1 (.cmp .less (.var 3) (.const 2))))).any (fun live => live.contains 5))

#eval leanCompileComparisonKeepingLive
#guard comparisonKeepsIncomingLive
#guard comparisonWithoutLiveDropsIt

/-! ## Exact-carrier `state_rel` (`crep_to_loopProofScript.sml:31-41`)

Fixtures over the exact `crepSem$state`/`loopSem$state` ports
(`CrepSemHOLState`/`LoopSemStateFiniteExact`), pinning the direct HOL-EVAL rows
in `scripts/hol-probes/crep_to_loop_state_rel_probe.out`
(`memaddrs_mdomain_mem`, `sh_memaddrs_sh_mdomain_mem`, `clock_eq`, `be_eq`,
`base_eq`, `top_eq`). -/

def stateRelExactFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }

def stateRelExactCrep : CrepSemHOLState 64 Unit :=
  { locals := HolFiniteMapExact.empty
    globals := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := stateRelExactFfi
    baseAddr := 0
    topAddr := 0 }

def stateRelExactLoop : LoopSemStateFiniteExact 64 Unit :=
  { locals := Spt.ln
    globals := HolFiniteMapExact.empty
    memory := fun _ => .word 0
    mdomain := fun _ => false
    shMdomain := fun _ => false
    clock := 5
    code := Spt.ln
    be := false
    ffi := stateRelExactFfi
    baseAddr := 0
    topAddr := 0 }

/-- The exact-carrier relation holds for the matching fixtures (the HOL oracle
    rows above are all `T`). -/
example : crepToLoopStateRelExact stateRelExactCrep stateRelExactLoop := by
  rw [crepToLoopStateRelExact]
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · funext address
    exact propext (iff_of_false (by simp [stateRelExactCrep])
      (by simp [stateRelExactLoop]))
  · funext address
    exact propext (iff_of_false (by simp [stateRelExactCrep])
      (by simp [stateRelExactLoop]))

/-- Field-level guard reproducing the oracle rows at address `7`. -/
def stateRelExactGuard : Bool :=
  letI : Decidable (stateRelExactCrep.memaddrs 7) :=
    isFalse (by simp [stateRelExactCrep])
  letI : Decidable (stateRelExactCrep.shMemaddrs 7) :=
    isFalse (by simp [stateRelExactCrep])
  decide (stateRelExactCrep.memaddrs 7 ↔ stateRelExactLoop.mdomain 7 = true) &&
    decide (stateRelExactCrep.shMemaddrs 7 ↔ stateRelExactLoop.shMdomain 7 = true) &&
    (stateRelExactCrep.clock == stateRelExactLoop.clock) &&
    (stateRelExactCrep.be == stateRelExactLoop.be) &&
    (stateRelExactCrep.baseAddr == stateRelExactLoop.baseAddr) &&
    (stateRelExactCrep.topAddr == stateRelExactLoop.topAddr)

#guard stateRelExactGuard

/-- HOL `state_rel_clock_add_zero` (`crep_to_loopProofScript.sml:219-223`) over
    the exact carriers: advancing the target clock preserves the relation. -/
example (h : crepToLoopStateRelExact stateRelExactCrep stateRelExactLoop) :
    ∃ ck, crepToLoopStateRelExact stateRelExactCrep
      { stateRelExactLoop with clock := ck + stateRelExactLoop.clock } :=
  crepToLoopStateRelExact_clock_add_zero stateRelExactCrep stateRelExactLoop h

/-- Exact-carrier `ctxt_fc` reproduces the direct HOL-EVAL rows in
    `scripts/hol-probes/crep_to_loop_ctxt_fc_probe.out` (`vars_zip`,
    `vars_zip_truncates`, `funcs_projection`, `vmax_nonempty_list`,
    `vmax_empty_list`, `target_kept`). -/
example :
    (ctxtFcExact Compiler.Encoders.Asm.AsmArchitecture.armv7
        (HolFiniteMapExact.empty.update
          (Flapjack.Basis.Pure.MlString.ofString "f", (3, 2)))
        [1, 2] [10, 20]).vmax = 20 := rfl

/-- Field-level guard reproducing the `ctxt_fc` oracle rows. -/
def ctxtFcExactGuard : Bool :=
  let cvs : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (Nat × Nat) :=
    HolFiniteMapExact.empty.update
      (Flapjack.Basis.Pure.MlString.ofString "f", (3, 2))
  let ctx := ctxtFcExact Compiler.Encoders.Asm.AsmArchitecture.armv7 cvs [1, 2] [10, 20]
  decide
      (ctx.vars.lookup 1 = some 10 ∧ ctx.vars.lookup 2 = some 20 ∧
        ctx.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString "f") = some (3, 2) ∧
        ctx.target = Compiler.Encoders.Asm.AsmArchitecture.armv7) &&
    decide ((ctxtFcExact Compiler.Encoders.Asm.AsmArchitecture.armv7
        HolFiniteMapExact.empty [] []).vmax = 0) &&
    decide ((ctxtFcExact Compiler.Encoders.Asm.AsmArchitecture.armv7
        HolFiniteMapExact.empty [1, 2, 3] [10]).vars.lookup 3 = none)

#guard ctxtFcExactGuard

/-- Exact-carrier fixtures for `crepToLoopLocalsRelExact`, reproducing the
    direct HOL-EVAL rows in `scripts/hol-probes/crep_to_loop_locals_rel_probe.out`
    (`ctxt_vars_lookup`, `distinct_component`, `ctxt_max_component`,
    `set_domain_mem`, `map_lookup`, `subset_domain_component`). `vars` is keyed
    by the exact `varname = num`, `funcs` by `mlstring`, `l` is the exact
    `sptree$num_set`, and `tLocals` the exact `word_loc` `num_map`. -/
def localsRelExactCtxt : CrepToLoopContextExact where
  vars := (HolFiniteMapExact.empty.update (0, 2)).update (1, 4)
  funcs := HolFiniteMapExact.empty
  vmax := 4
  target := Compiler.Encoders.Asm.AsmArchitecture.armv7

/-- Exact `sptree$num_set` with members 1 and 2 (cf. probe `set_domain_mem`). -/
def localsRelExactSet : NumSet := sptFromAList [(1, ()), (2, ())]

/-- Exact `sptree$num_map` over `word_loc` with entries 1, 2 and 4 (cf. probe
    `map_lookup` and the `domain l ⊆ domain t_locals` row). -/
def localsRelExactTarget : Spt (WordLocW 8) :=
  sptFromAList
    [(1, WordLocW.word 0), (2, WordLocW.word 9), (4, WordLocW.word 7)]

/-- Exact source `num |-> 'a word_lab` local map with vars 0 and 1. -/
def localsRelExactSource : HolFiniteMapExact Nat (HolWordLab 8) :=
  (HolFiniteMapExact.empty.update (0, HolWordLab.word 9)).update
    (1, HolWordLab.word 7)

/-- Field-level guard reproducing the `locals_rel` oracle rows on the exact
    carriers. -/
def localsRelExactGuard : Bool :=
  decide (localsRelExactCtxt.vars.lookup 0 = some 2) &&
    decide (localsRelExactCtxt.vars.lookup 1 = some 4) &&
    decide (localsRelExactCtxt.vmax = 4) &&
    (sptLookup 1 localsRelExactSet).isSome &&
    (sptLookup 2 localsRelExactSet).isSome &&
    decide ((sptLookup 2 localsRelExactTarget : Option (WordLocW 8)) =
      some (WordLocW.word 9)) &&
    decide ((sptLookup 4 localsRelExactTarget : Option (WordLocW 8)) =
      some (WordLocW.word 7)) &&
    decide ((wlabWlocHOL (HolWordLab.word 9) : WordLocW 8) = WordLocW.word 9)

#guard localsRelExactGuard

/-- The exact `locals_rel` unfolds to the HOL clause structure, over the exact
    carriers (`crepToLoopLocalsRelExact_iff`). -/
example :
    crepToLoopLocalsRelExact localsRelExactCtxt localsRelExactSet
        localsRelExactSource localsRelExactTarget ↔
      crepToLoopDistinctVars localsRelExactCtxt.vars.lookup ∧
        crepToLoopCtxtMaxExact localsRelExactCtxt.vmax localsRelExactCtxt.vars ∧
        (∀ n, sptMem n localsRelExactSet → sptMem n localsRelExactTarget) ∧
        ∀ vname value, localsRelExactSource.lookup vname = some value →
          ∃ n, localsRelExactCtxt.vars.lookup vname = some n ∧
            sptMem n localsRelExactSet ∧
            sptLookup n localsRelExactTarget = some (wlabWlocHOL value) :=
  crepToLoopLocalsRelExact_iff _ _ _ _

/-- The tagged introduction lemma unpacks the same four HOL conjuncts as
    `crepToLoopLocalsRelExact_iff` (`crepToLoopLocalsRelExact_intro`, the port
    of HOL `locals_rel_intro`). -/
example (h : crepToLoopLocalsRelExact localsRelExactCtxt localsRelExactSet
    localsRelExactSource localsRelExactTarget) :
    crepToLoopDistinctVars localsRelExactCtxt.vars.lookup ∧
      crepToLoopCtxtMaxExact localsRelExactCtxt.vmax localsRelExactCtxt.vars ∧
      (∀ n, sptMem n localsRelExactSet → sptMem n localsRelExactTarget) ∧
      ∀ vname value, localsRelExactSource.lookup vname = some value →
        ∃ n, localsRelExactCtxt.vars.lookup vname = some n ∧
          sptMem n localsRelExactSet ∧
          sptLookup n localsRelExactTarget = some (wlabWlocHOL value) :=
  crepToLoopLocalsRelExact_intro _ _ _ _ h

/-! ## Direct `locals_rel` oracle rows

The direct rows in `scripts/hol-probes/crep_to_loop_locals_rel_probe.out`
(`locals_rel_true`, `locals_rel_domain_false`, `locals_rel_value_false`) decide
the whole HOL `locals_rel` on a concrete num-keyed carrier instance by kernel
proof: `EVAL` alone cannot decide the universally quantified relation. The Lean
counterparts below are kernel-checked `example`s on the same instance -- a proof
plus two refutations -- so the tagged `crepToLoopLocalsRelExact` is exercised on
a concrete context rather than only through its components. -/

/-- Oracle context: `vars` keyed by the exact `varname = num` with `0 |-> 0`,
    `vmax = 0`, empty `funcs`. -/
abbrev localsRelOracleCtxt : CrepToLoopContextExact where
  vars := HolFiniteMapExact.empty.update (0, 0)
  funcs := HolFiniteMapExact.empty
  vmax := 0
  target := Compiler.Encoders.Asm.AsmArchitecture.armv7

/-- Exact `sptree$num_set` with member `0` (probe `set_domain_mem`). -/
abbrev localsRelOracleSet : NumSet := Spt.ls ()

/-- Exact source `num |-> 'a word_lab` with `0 |-> Word 9`. -/
abbrev localsRelOracleSource : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.empty.update (0, HolWordLab.word 9)

/-- Target `num_map` with `0 |-> Word 9` (probe `locals_rel_true`). -/
abbrev localsRelOracleTarget : Spt (WordLocW 8) := Spt.ls (WordLocW.word 9)

/-- Same lookup function as the oracle target, with a redundant overwrite at
    its existing key. This gives a distinct Spt representation for testing
    `locals_rel_lookup_same`. -/
abbrev localsRelOracleTargetSameLookup : Spt (WordLocW 8) :=
  sptInsert 0 (WordLocW.word 9) localsRelOracleTarget

/-- Empty target `num_map` (probe `locals_rel_domain_false`). -/
abbrev localsRelOracleTargetEmpty : Spt (WordLocW 8) := Spt.ln

/-- Target `num_map` with `0 |-> Word 12` (probe `locals_rel_value_false`). -/
abbrev localsRelOracleTargetBad : Spt (WordLocW 8) := Spt.ls (WordLocW.word 12)

/-- Kernel-checked true row (HOL `locals_rel_true`). -/
theorem localsRelOracleTargetRel :
    crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSet
      localsRelOracleSource localsRelOracleTarget := by
  rw [crepToLoopLocalsRelExact]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y n m hx hy _
    simp only [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_empty,
      FUPDATE, beq_iff_eq] at hx hy
    split at hx
    · split at hy
      · simp only [Option.some.injEq] at hx hy
        omega
      · simp at hy
    · simp at hx
  · intro v m hv
    simp only [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_empty,
      FUPDATE, beq_iff_eq] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      omega
    · simp at hv
  · intro n hn
    rw [sptMem_iff_lookup] at hn ⊢
    obtain ⟨v, hv⟩ := hn
    simp only [sptLookup] at hv ⊢
    split at hv
    · rename_i hn0
      exact ⟨WordLocW.word 9, by rw [if_pos hn0]⟩
    · simp at hv
  · intro vname value hv
    simp only [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_empty,
      FUPDATE, beq_iff_eq] at hv
    split at hv
    · rename_i hv0
      simp only [Option.some.injEq] at hv
      subst hv
      refine ⟨0, ?_, ?_, ?_⟩
      · rw [← hv0]
        decide
      · rw [sptMem_iff_lookup]
        exact ⟨(), by simp [sptLookup]⟩
      · simp [sptLookup, wlabWlocHOL]
    · simp at hv

/-- The two Spt trees are pointwise lookup-equal although the second contains a
    redundant insertion. -/
theorem localsRelOracleTargetsAgree :
    ∀ n, sptLookup n localsRelOracleTarget =
      sptLookup n localsRelOracleTargetSameLookup := by
  intro n
  by_cases hn : n = 0
  · subst n
    rw [sptLookup_sptInsert_same]
    rfl
  · exact (sptLookup_sptInsert_ne 0 n (WordLocW.word 9)
      localsRelOracleTarget hn).symm

/-- Kernel-checked instance of the tagged `locals_rel_lookup_same` port using
    the direct HOL `locals_rel_true` row and a distinct but lookup-equivalent
    target tree. The theorem itself is universally quantified, so its proof is
    checked by Lean rather than represented as an EVAL Boolean oracle row. -/
example :
    crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSet
      localsRelOracleSource localsRelOracleTargetSameLookup := by
  exact crepToLoopLocalsRelExact_lookup_same _ _ _ _ _
    localsRelOracleTargetRel localsRelOracleTargetsAgree

/-- Kernel-checked domain-false row: `0` is in the source set but absent from
    the target map (HOL `locals_rel_domain_false`). -/
example :
    ¬ crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSet
      localsRelOracleSource localsRelOracleTargetEmpty := by
  intro h
  rw [crepToLoopLocalsRelExact] at h
  obtain ⟨_, _, hsub, _⟩ := h
  have hmem : sptMem 0 localsRelOracleSet := by
    rw [sptMem_iff_lookup]
    exact ⟨(), by simp [sptLookup]⟩
  have hbad := hsub 0 hmem
  simp [sptMem, sptDomain, sptLookup] at hbad

/-- Kernel-checked value-false row: the target maps `0` to the wrong word
    (HOL `locals_rel_value_false`). -/
example :
    ¬ crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSet
      localsRelOracleSource localsRelOracleTargetBad := by
  intro h
  rw [crepToLoopLocalsRelExact] at h
  obtain ⟨_, _, _, hpoint⟩ := h
  obtain ⟨n, _, hmem, hn⟩ := hpoint 0 (HolWordLab.word 9) (by decide)
  have hn0 : n = 0 := by
    rw [sptMem_iff_lookup] at hmem
    obtain ⟨u, hu⟩ := hmem
    simp only [sptLookup] at hu
    split at hu
    · assumption
    · simp at hu
  subst hn0
  simp only [sptLookup, wlabWlocHOL] at hn
  exact absurd hn (by decide)

/-- Field-level guard for the decidable parts of the direct oracle rows. -/
def localsRelOracleGuard : Bool :=
  decide (localsRelOracleCtxt.vars.lookup 0 = some 0) &&
    (sptLookup 0 localsRelOracleSet).isSome &&
    decide ((sptLookup 0 localsRelOracleTarget : Option (WordLocW 8)) =
      some (WordLocW.word 9)) &&
    !(sptLookup 0 localsRelOracleTargetEmpty).isSome &&
    decide ((sptLookup 0 localsRelOracleTargetBad : Option (WordLocW 8)) =
      some (WordLocW.word 12))

#guard localsRelOracleGuard

/-- The direct HOL relation row's target and the redundant-insert target have
    equal lookups at the populated key and an absent key. -/
def localsRelLookupSameGuard : Bool :=
  (sptLookup 0 localsRelOracleTarget ==
      sptLookup 0 localsRelOracleTargetSameLookup) &&
    (sptLookup 1 localsRelOracleTarget ==
      sptLookup 1 localsRelOracleTargetSameLookup)

#guard localsRelLookupSameGuard

/-! Direct cut-set oracle rows for HOL `locals_rel_cutset_prop`
(`crep_to_loopProofScript.sml:236-244`), matching
`locals_rel_cutset_second_true` / `locals_rel_cutset_after_true` and
`cutset_set_lookup` / `cutset_target_lookup` in
`scripts/hol-probes/crep_to_loop_locals_rel_probe.out`. -/

abbrev localsRelOracleSetBig : NumSet := sptInsert 1 () localsRelOracleSet

abbrev localsRelOracleCutsetTarget : Spt (WordLocW 8) :=
  sptInsert 1 (WordLocW.word 3) localsRelOracleTarget

/-- The rendered HOL `subspt` holds for the concrete sets of the cut-set rows. -/
example : sptSubspt localsRelOracleSet localsRelOracleSetBig := by
  intro k hk
  have hk' : sptMem k (Spt.ls ()) := by simpa only [localsRelOracleSet] using hk
  have hk0 : k = 0 := (sptMem_ls k ()).mp hk'
  subst hk0
  constructor
  · rw [sptMem_iff_lookup]
    exact ⟨(), by simp [localsRelOracleSetBig, sptInsert, sptLookup]⟩
  · simp [localsRelOracleSetBig, localsRelOracleSet, sptInsert, sptLookup]

def localsRelCutsetGuard : Bool :=
  (sptLookup 1 localsRelOracleSetBig).isSome &&
    decide ((sptLookup 1 localsRelOracleCutsetTarget : Option (WordLocW 8)) =
      some (WordLocW.word 3)) &&
    decide ((sptLookup 0 localsRelOracleCutsetTarget : Option (WordLocW 8)) =
      some (WordLocW.word 9))

#guard localsRelCutsetGuard

/-- Shape check of the tagged `locals_rel_cutset_prop` against the HOL statement. -/
example
    (h1 : crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSet
      localsRelOracleSource localsRelOracleTarget)
    (h2 : crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSetBig
      localsRelOracleSource localsRelOracleCutsetTarget)
    (hsub : sptSubspt localsRelOracleSet localsRelOracleSetBig) :
    crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSet
      localsRelOracleSource localsRelOracleCutsetTarget :=
  crepToLoopLocalsRelExact_cutset_prop _ _ _ _ _ _ h1 h2 hsub

/-- `n = 5 > ctxt.vmax = 0`, so inserting a fresh wloc leaves the relation intact.
    Matches `locals_rel_insert_after_true` / `insert_gt_vmax_lookup_unchanged` in
    `scripts/hol-probes/crep_to_loop_locals_rel_probe.out` and the insert rows in
    `scripts/hol-probes/crep_to_loop_locals_insert_probe.out`. -/

abbrev localsRelOracleInsertTarget : Spt (WordLocW 8) :=
  sptInsert 5 (WordLocW.word 3) localsRelOracleTarget

def localsRelInsertGuard : Bool :=
  decide ((sptLookup 5 localsRelOracleInsertTarget : Option (WordLocW 8)) =
    some (WordLocW.word 3)) &&
  decide ((sptLookup 0 localsRelOracleInsertTarget : Option (WordLocW 8)) =
    some (WordLocW.word 9))

#guard localsRelInsertGuard

/-- Shape check of the tagged `locals_rel_insert_gt_vmax` against the HOL statement. -/
example
    (h : crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSet
      localsRelOracleSource localsRelOracleTarget)
    (hgt : localsRelOracleCtxt.vmax < 5) :
    crepToLoopLocalsRelExact localsRelOracleCtxt localsRelOracleSet
      localsRelOracleSource localsRelOracleInsertTarget :=
  crepToLoopLocalsRelExact_insert_gt_vmax _ _ _ _ _ _ h hgt

-- `evaluate_io_mono_rephrases` (`crep_to_loopProofScript.sml:4066`): the two
-- `evaluate_add_clock_io_events_mono` rephrasings at `clock := k` vs
-- `clock := k + extra`, over the exact Crep and loopSem evaluators.
example :
    ((evalCrepSemHOLProgExact { stateRelExactCrep with clock := 2 } (CrepProgHOL.skip)).2.ffi.ioEvents <+:
        (evalCrepSemHOLProgExact { stateRelExactCrep with clock := 2 + 3 } (CrepProgHOL.skip)).2.ffi.ioEvents) ∧
      ((LoopSemStateFiniteExact.evaluate (HolLoopProg.skip) { stateRelExactLoop with clock := 2 }).2.ffi.ioEvents <+:
        (LoopSemStateFiniteExact.evaluate (HolLoopProg.skip) { stateRelExactLoop with clock := 2 + 3 }).2.ffi.ioEvents) :=
  ⟨(evaluateIOMonoRephrases (CrepProgHOL.skip) stateRelExactCrep (HolLoopProg.skip) stateRelExactLoop 2).1 3,
    (evaluateIOMonoRephrases (CrepProgHOL.skip) stateRelExactCrep (HolLoopProg.skip) stateRelExactLoop 2).2 3⟩

def evaluateIOMonoGuard : Bool :=
  decide ((LoopSemStateFiniteExact.evaluate (HolLoopProg.skip) { stateRelExactLoop with clock := 2 }).2.ffi.ioEvents.length = 0)

#guard evaluateIOMonoGuard

def runChecks : IO Bool := do
  let results := [declarationRenamingMatches,
    handlerlessCallCarriesRaiseHandler, handledCallCarriesRaiseHandler,
    callReturnDestinationMappingMatches,
    callReturnSourceVariableMaps,
    shMemDestinationMappingMatches, assignDestinationMappingMatches,
    comparisonKeepsIncomingLive,
    comparisonWithoutLiveDropsIt,
    stateRelExactGuard, ctxtFcExactGuard, localsRelExactGuard,
    localsRelOracleGuard, localsRelLookupSameGuard,
    localsRelCutsetGuard, localsRelInsertGuard]
  let names := [
    "crep_to_loop declaration renaming and live seed",
    "crep_to_loop default call handler",
    "crep_to_loop explicit call handler",
    "crep_to_loop call return destination mapping",
    "crep_to_loop call return source variable mapping",
    "crep_to_loop shared-memory destination mapping",
    "crep_to_loop assignment destination mapping",
    "crep_to_loop comparison keeps the incoming live set",
    "crep_to_loop comparison without live does not invent one",
    "crep_to_loop exact-carrier state_rel matches the HOL oracle rows",
    "crep_to_loop exact ctxt_fc matches the HOL oracle rows",
    "crep_to_loop exact locals_rel matches the HOL oracle rows",
    "crep_to_loop exact locals_rel direct oracle rows (true/domain-false/value-false)",
    "crep_to_loop exact locals_rel_lookup_same kernel example and lookup guard",
    "crep_to_loop exact locals_rel_cutset_prop oracle rows (subspt/second/after)",
    "crep_to_loop exact locals_rel_insert_gt_vmax oracle rows (fresh-key/unchanged)"]
  let mut all := true
  for (name, result) in names.zip results do
    if result then IO.println s!"PASS {name}" else IO.println s!"FAIL {name}"
    all := all && result
  pure all

/-- HOL `crep_to_loopProofScript.sml` `state_rel_intro`: the Crepe-to-Loop
    state relation unfolds to the seven-field conjunction, matching the direct
    HOL-EVAL rows in `scripts/hol-probes/crep_to_loop_state_rel_probe.out`. -/
example (s : CrepHolState (BitVec 64) Unit) (t : LoopMachineState (BitVec 64) Unit) :
    crepToLoopStateRel s t ↔
      s.memaddrs = t.mdomain ∧
        s.shMemaddrs = t.shMdomain ∧
        s.clock = t.clock ∧
        s.bigEndian = t.be ∧
        s.ffi = t.ffi ∧
        s.baseAddress = t.baseAddr ∧
        s.topAddress = t.topAddr :=
  crepToLoopStateRel_intro s t

/-- HOL `wlab_wloc_def` (`crep_to_loopProofScript.sml:45-47`) on a word payload:
    both datatypes use the single `word` constructor. -/
example : wlabWloc (PanWordLab.word (7 : BitVec 64)) = LoopValue.word (7 : BitVec 64) := rfl

/-- HOL `globals_rel_intro` (`crep_to_loopProofScript.sml:203-209`) is an
    implication: from the relation, conclude the universally quantified lookup
    agreement. -/
example (sglobals : BitVec 5 → Option (PanWordLab (BitVec 64)))
    (tglobals : BitVec 5 → Option (LoopValue (BitVec 64)))
    (h : crepToLoopGlobalsRel sglobals tglobals) :
    ∀ address value, sglobals address = some value →
        tglobals address = some (wlabWloc value) :=
  crepToLoopGlobalsRel_intro sglobals tglobals h

/-- Untagged iff form used for rewriting the relation to its unfolding. -/
example (sglobals : BitVec 5 → Option (PanWordLab (BitVec 64)))
    (tglobals : BitVec 5 → Option (LoopValue (BitVec 64))) :
    crepToLoopGlobalsRel sglobals tglobals ↔
      ∀ address value, sglobals address = some value →
        tglobals address = some (wlabWloc value) :=
  crepToLoopGlobalsRel_iff sglobals tglobals

/-- Concrete target global map for the `globals_rel` oracle row
    `globals_lookup_match=T` in `scripts/hol-probes/crep_to_loop_globals_rel_probe.out`. -/
def globalsRelFixture : BitVec 5 → Option (LoopValue (BitVec 64)) :=
  FUPDATE (FEMPTY : FiniteMap (BitVec 5) (LoopValue (BitVec 64))) (4, .word (7 : BitVec 64))

/-- Reproduces the direct HOL oracle rows `globals_lookup_match=T` and
    `globals_lookup_absent=T` (`crep_to_loop_globals_rel_probe.out`). -/
def globalsRelGuard : Bool :=
  (FLOOKUP (FUPDATE (FEMPTY : FiniteMap (BitVec 5) (PanWordLab (BitVec 64))) (4, PanWordLab.word (7 : BitVec 64))) 4
      == some (PanWordLab.word (7 : BitVec 64))) &&
    (FLOOKUP globalsRelFixture 4 == some (wlabWloc (PanWordLab.word (7 : BitVec 64)))) &&
    (FLOOKUP globalsRelFixture 9).isNone

#guard globalsRelGuard

/-- HOL `state_rel_clock_add_zero` (`crep_to_loopProofScript.sml:219-223`): a
    state relation is preserved by advancing the target clock by zero. -/
example (s : CrepHolState (BitVec 64) Unit) (t : LoopMachineState (BitVec 64) Unit)
    (h : crepToLoopStateRel s t) :
    ∃ ck, crepToLoopStateRel s { t with clock := ck + t.clock } :=
  crepToLoopStateRel_clock_add_zero s t h

/-- HOL `mem_rel_intro` (`crep_to_loopProofScript.sml:203-209`) is an
    implication: from the total-memory relation, conclude the pointwise
    equation. -/
example (smem : BitVec 64 → PanWordLab (BitVec 64))
    (tmem : BitVec 64 → LoopValue (BitVec 64)) (dom : BitVec 64 → Bool)
    (h : crepToLoopMemRel smem tmem dom) :
    ∀ ad, dom ad = true → wlabWloc (smem ad) = tmem ad :=
  crepToLoopMemRel_intro smem tmem dom h

/-- Untagged iff form of `crepToLoopMemRel`. -/
example (smem : BitVec 64 → PanWordLab (BitVec 64))
    (tmem : BitVec 64 → LoopValue (BitVec 64)) (dom : BitVec 64 → Bool) :
    crepToLoopMemRel smem tmem dom ↔
      ∀ ad, dom ad = true → wlabWloc (smem ad) = tmem ad :=
  crepToLoopMemRel_iff smem tmem dom

/-- Total-view bridge: the total HOL memory agrees with the Option-valued
    `LoopMachineState.memory` at a defined address. -/
example (default : LoopValue (BitVec 64)) (t : LoopMachineState (BitVec 64) Unit)
    (ad : BitVec 64) (v : LoopValue (BitVec 64)) (h : t.memory ad = some v) :
    loopMemoryTotal default t ad = v :=
  loopMemoryTotal_eq_some default t ad v h

/-- Concrete total loop memory used to reproduce the `mem_rel_match`/
    `mem_rel_wrong` oracle rows: `4 ↦ .word 7`, other addresses defaulting. -/
def memRelFixture : LoopMachineState (BitVec 64) Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun ad => if ad == (4 : BitVec 64) then some (.word (7 : BitVec 64)) else none
    mdomain := fun _ => false
    shMdomain := fun _ => false
    clock := 0
    code := []
    be := false
    ffi := trivialFfiState Unit ()
    baseAddr := 0
    topAddr := 0 }

/-- Reproduces the `mem_rel_match=T` / `mem_rel_wrong=F` oracle rows via the
    total view of the Option-valued loop memory. -/
def memRelGuard : Bool :=
  let t := loopMemoryTotal (LoopValue.word (0 : BitVec 64)) memRelFixture
  (t 4 == LoopValue.word (7 : BitVec 64)) && (t 9 == LoopValue.word (0 : BitVec 64))

#guard memRelGuard

/-- Concrete function table used to reproduce the `distinct_funcs_*` oracle
    rows: `«a» ↦ (1,10)`, `«b» ↦ (2,20)`, `«c» ↦ (1,30)`. -/
def distinctFuncsFm : FiniteMap String (Nat × Nat) :=
  FUPDATE
    (FUPDATE
      (FUPDATE (FEMPTY : FiniteMap String (Nat × Nat)) ("a", (1, 10)))
      ("b", (2, 20)))
    ("c", (1, 30))

/-- `distinct_funcs_sep=T`: two entries with different labels satisfy the
    pointwise obligation `n = m → x = y` vacuously. -/
example (h : crepToLoopDistinctFuncs distinctFuncsFm) :
    (1 : Nat) = 2 → (("a" : String) = "b") :=
  h "a" "b" 1 2 10 20
    (by simp [distinctFuncsFm, FLOOKUP_update])
    (by simp [distinctFuncsFm, FLOOKUP_update])

/-- `distinct_funcs_collision=F`: two distinct keys with the same label violate
    the relation, so it does not hold for a colliding table. -/
example : ¬ crepToLoopDistinctFuncs distinctFuncsFm := by
  intro h
  have hkey : ("a" : String) = "c" :=
    h "a" "c" 1 1 10 30
      (by simp [distinctFuncsFm, FLOOKUP_update])
      (by simp [distinctFuncsFm, FLOOKUP_update])
      rfl
  exact absurd hkey (by decide)

/-- Concrete variable map used to reproduce the `distinct_vars_*` oracle rows:
    `1 ↦ 10`, `2 ↦ 20`, `3 ↦ 10`. -/
def distinctVarsFm : FiniteMap Nat Nat :=
  FUPDATE
    (FUPDATE
      (FUPDATE (FEMPTY : FiniteMap Nat Nat) (1, 10))
      (2, 20))
    (3, 10)

/-- `distinct_vars_sep=T`: two entries with different slots satisfy the
    pointwise obligation `n = m → x = y` vacuously. -/
example (h : crepToLoopDistinctVars distinctVarsFm) :
    (10 : Nat) = 20 → ((1 : Nat) = 2) :=
  h 1 2 10 20
    (by simp [distinctVarsFm, FLOOKUP_update])
    (by simp [distinctVarsFm, FLOOKUP_update])

/-- `distinct_vars_collision=F`: two distinct keys sharing a slot violate the
    relation. -/
example : ¬ crepToLoopDistinctVars distinctVarsFm := by
  intro h
  have hkey : (1 : Nat) = 3 :=
    h 1 3 10 10
      (by simp [distinctVarsFm, FLOOKUP_update])
      (by simp [distinctVarsFm, FLOOKUP_update])
      rfl
  exact absurd hkey (by decide)

/-- HOL `ctxt_max_def` (`crep_to_loopProofScript.sml:90-93`) on the concrete
    table `1 ↦ 10`, matching oracle rows `ctxt_max_within=T` and
    `ctxt_max_absent=T` (absent keys are vacuous). -/
def ctxtMaxFm : FiniteMap Nat Nat :=
  FUPDATE (FEMPTY : FiniteMap Nat Nat) (1, 10)

example : crepToLoopCtxtMax 20 ctxtMaxFm := by
  intro v m h
  rw [ctxtMaxFm, FLOOKUP_update] at h
  split at h
  · simp_all
    omega
  · simp at h

/-- Oracle row `ctxt_max_exceeds=F`: the bound `5` does not admit the stored
    value `10`. -/
example : ¬ crepToLoopCtxtMax 5 ctxtMaxFm := by
  intro h
  have hle := h 1 10 (by simp [ctxtMaxFm, FLOOKUP_update])
  omega

/-- Polymorphism witnesses pinning the exact HOL inferred types of the three
    un-annotated HOL `Definition`s.  `distinct_funcs` is polymorphic in the key
    and both tuple components (`'a |-> ('b # 'c)`); `distinct_vars` in the key
    and value (`'a |-> 'b`); `ctxt_max` in the key only (`'a |-> num`).  Empty
    maps satisfy each relation vacuously. -/
example : crepToLoopDistinctFuncs
    (fun _ : Bool => none : FiniteMap Bool (Bool × Bool)) := by
  intro x y n m rm rm' hx
  change (fun _ : Bool => none) x = some (n, rm) at hx
  simp at hx

example : crepToLoopDistinctVars (fun _ : Bool => none : FiniteMap Bool Bool) := by
  intro x y n m hx
  change (fun _ : Bool => none) x = some n at hx
  simp at hx

example : crepToLoopCtxtMax (κ := String) 5
    (fun _ : String => none : FiniteMap String Nat) := by
  intro v m hv
  change (fun _ : String => none) v = some m at hv
  simp at hv

/-- Untagged `locals_rel` rendering (bead `flapjack-pxn.18.5.6.9`): the empty
    context/source/target tuple satisfies every side condition vacuously. -/
def localsRelContext : LoopContext Unit :=
  { vars := [], functions := [], maxVar := 0, target := .rv64i }

example : crepToLoopLocalsRel localsRelContext (fun _ => false)
    (FEMPTY : FiniteMap Nat (PanWordLab (BitVec 64)))
    (fun _ => none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y n m hx
    simp [localsRelContext, lookupNatInfo] at hx
  · intro v m hv
    simp [localsRelContext, lookupNatInfo] at hv
  · intro n hn
    simp at hn
  · intro vname v hv
    simp [FLOOKUP, FEMPTY] at hv

/-- Finite-map context carrier for the untagged documented-mismatch `crepToLoopLocalsRelHOL` rendering of `locals_rel_def`
    (bead `flapjack-pxn.18.5.6.9.1`); empty vars/maxVar satisfy the two
    context clauses vacuously. -/
def localsRelHOLContext : CrepToLoopFiniteMapContext :=
  { vars := (FEMPTY : FiniteMap Nat Nat),
    funcs := (FEMPTY : FiniteMap FunName (Nat × Nat)),
    vmax := 5, target := .riscv }

/-- The untagged `crepToLoopLocalsRelHOL` rendering of `locals_rel_def` satisfies every clause vacuously for
    an empty context and empty source locals. -/
example : crepToLoopLocalsRelHOL (width := 64) localsRelHOLContext
    (fun _ => false) (FEMPTY : FiniteMap Nat (PanWordLab (BitVec 64)))
    (fun _ => (none : Option (LoopValue (BitVec 64)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y n m hx
    exact absurd hx (fun h => Option.some_ne_none n h.symm)
  · intro v m hv
    exact absurd hv (fun h => Option.some_ne_none m h.symm)
  · intro n hn
    exact absurd hn (Bool.false_ne_true)
  · intro vname v hv
    exact absurd hv (fun h => Option.some_ne_none v h.symm)

/-- HOL `locals_rel_insert_gt_vmax` oracle rows (`insert_same`,
    `insert_other_unchanged`, `gt_vmax_bounded_survives`, `subset_preserved` in
    `scripts/hol-probes/crep_to_loop_locals_insert_probe.out`): inserting a
    fresh `num_map` binding above `ctxt.vmax` preserves the relation and
    is visible at its own key. -/
example :
    crepToLoopLocalsRelHOL (width := 64) localsRelHOLContext
      (fun _ => false) (FEMPTY : FiniteMap Nat (PanWordLab (BitVec 64)))
      (fun m => if m = 7 then some (LoopValue.word (5 : BitVec 64)) else none) :=
  crepToLoopLocalsRelHOL_insert_gt_vmax localsRelHOLContext (fun _ => false)
    (FEMPTY : FiniteMap Nat (PanWordLab (BitVec 64)))
    (fun _ => (none : Option (LoopValue (BitVec 64))))
    7 (LoopValue.word (5 : BitVec 64))
    (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x y n m hx
        exact absurd hx (fun h => Option.some_ne_none n h.symm)
      · intro v m hv
        exact absurd hv (fun h => Option.some_ne_none m h.symm)
      · intro n hn
        exact absurd hn (Bool.false_ne_true)
      · intro vname v hv
        exact absurd hv (fun h => Option.some_ne_none v h.symm))
    (by decide)

/-- The `∃n` clause of the untagged `crepToLoopLocalsRelHOL` relation for a present binding: source
    local `1 ↦ wlab 9` sits at finite-map slot `5`, which is live and holds the
    `wlab` value in the target map. -/
example : ∃ n, FLOOKUP (FUPDATE (FEMPTY : FiniteMap Nat Nat) (1, 5)) 1 = some n ∧
    (fun m => m == 5) n = true ∧
    (fun m => if m == 5 then some (LoopValue.word (9 : BitVec 64)) else none) n =
      some (wlabWloc (PanWordLab.word (9 : BitVec 64))) :=
  ⟨5, by simp [FLOOKUP, FUPDATE], by decide, by simp [wlabWloc]⟩

/-- HOL `locals_rel_cutset_prop` oracle rows (`cutset_sub_0`, `cutset_sub_1`,
    `cutset_sub_absent`, `cutset_lookup_preserved`, `cutset_lookup_other`,
    `cutset_domain_trans` in
    `scripts/hol-probes/crep_to_loop_locals_cutset_probe.out`): shrinking the
    live set (`subspt cset cset'` rendered as `live n = true → live' n = true`)
    preserves the relation against the same target locals. -/
example :
    crepToLoopLocalsRelHOL (width := 64) localsRelHOLContext
      (fun _ => false) (FEMPTY : FiniteMap Nat (PanWordLab (BitVec 64)))
      (fun _ => (none : Option (LoopValue (BitVec 64)))) :=
  crepToLoopLocalsRelHOL_cutset_prop localsRelHOLContext
    (fun _ => false) (fun _ => false)
    (FEMPTY : FiniteMap Nat (PanWordLab (BitVec 64)))
    (fun _ => (none : Option (LoopValue (BitVec 64))))
    (fun _ => (none : Option (LoopValue (BitVec 64))))
    (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x y n m hx
        exact absurd hx (fun h => Option.some_ne_none n h.symm)
      · intro v m hv
        exact absurd hv (fun h => Option.some_ne_none m h.symm)
      · intro n hn
        exact absurd hn (Bool.false_ne_true)
      · intro vname v hv
        exact absurd hv (fun h => Option.some_ne_none v h.symm))
    (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x y n m hx
        exact absurd hx (fun h => Option.some_ne_none n h.symm)
      · intro v m hv
        exact absurd hv (fun h => Option.some_ne_none m h.symm)
      · intro n hn
        exact absurd hn (Bool.false_ne_true)
      · intro vname v hv
        exact absurd hv (fun h => Option.some_ne_none v h.symm))
    (by intro n hn; exact absurd hn Bool.false_ne_true)

/-- The `∃n` clause of `crepToLoopLocalsRel` for a present binding: the source
    local `1 ↦ wlab 9` maps to varname `5`, which is live, and the target
    locals hold `wlab 9` at `5`. -/
def localsRelLive : Nat → Bool := fun n => n == 5

example : ∃ n, lookupNatInfo 1 [(1, 5)] = some n ∧ localsRelLive n = true ∧
    (fun m => if m == 5 then some (LoopValue.word (9 : BitVec 64)) else none) n =
      some (wlabWloc (PanWordLab.word (9 : BitVec 64))) :=
  ⟨5, rfl, by decide, by simp [wlabWloc]⟩

/-! `find_var`/`find_lab` over the finite-map context carrier, mirroring
    `scripts/hol-probes/crep_to_loop_context_defs_probe.out`. -/
def contextDefsContext : CrepToLoopFiniteMapContext :=
  { vars := FUPDATE (FEMPTY : FiniteMap Nat Nat) (1, 7),
    funcs := FUPDATE (FEMPTY : FiniteMap FunName (Nat × Nat)) ("f", (3, 2)),
    vmax := 9, target := .riscv }

example : findVarHOL contextDefsContext 1 = 7 := by
  simp [findVarHOL, contextDefsContext, FLOOKUP_update]

example : findVarHOL contextDefsContext 2 = 0 := by
  simp [findVarHOL, contextDefsContext, FLOOKUP_update]

example : findLabHOL contextDefsContext "f" = 3 := by
  simp [findLabHOL, contextDefsContext, FLOOKUP_update]

example : findLabHOL contextDefsContext "g" = 0 := by
  simp [findLabHOL, contextDefsContext, FLOOKUP_update]

/-! `mk_ctxt`/`make_vmap` over the finite-map carrier, mirroring
    `scripts/hol-probes/crep_to_loop_mk_ctxt_probe.out`. -/
example :
    (mkCtxtHOL .riscv (FUPDATE (FEMPTY : FiniteMap Nat Nat) (1, 7))
      (FUPDATE (FEMPTY : FiniteMap FunName (Nat × Nat)) ("f", (3, 2))) 9).vars =
      FUPDATE (FEMPTY : FiniteMap Nat Nat) (1, 7) := rfl

example : (mkCtxtHOL .riscv (FEMPTY : FiniteMap Nat Nat)
      (FEMPTY : FiniteMap FunName (Nat × Nat)) 9).vmax = 9 := rfl

example : (mkCtxtHOL .riscv (FEMPTY : FiniteMap Nat Nat)
      (FEMPTY : FiniteMap FunName (Nat × Nat)) 9).target = .riscv := rfl

example : (mkCtxtHOL .armv7 (FEMPTY : FiniteMap Nat Nat)
      (FEMPTY : FiniteMap FunName (Nat × Nat)) 9).target = .armv7 := rfl

example : FLOOKUP (makeVmapHOL [5]) 5 = some 0 := by
  simp [makeVmapHOL, FUPDATE_LIST, FUPDATE, FLOOKUP]

example : makeVmapHOL [5, 6] =
    FUPDATE (FUPDATE (FEMPTY : FiniteMap Nat Nat) (5, 0)) (6, 1) := rfl

example : FLOOKUP (makeVmapHOL [5, 6]) 6 = some 1 := by
  rw [show makeVmapHOL [5, 6] =
    FUPDATE (FUPDATE (FEMPTY : FiniteMap Nat Nat) (5, 0)) (6, 1) from rfl]
  simp [FLOOKUP_update]

example : FLOOKUP (makeVmapHOL []) 5 = none := rfl

/-- HOL `make_funcs` oracle rows (`mkf_*` in
    `scripts/hol-probes/crep_to_loop_make_funcs_probe.out`). -/
example :
    FLOOKUP (crepToLoopMakeFuncsHOL
      ([("f", [1, 2], ()), ("g", [], ())] : List (String × List Nat × Unit)))
      "f" = some (64, 2) := by decide

example : FLOOKUP (crepToLoopMakeFuncsHOL
      ([("f", [1, 2], ()), ("g", [], ())] : List (String × List Nat × Unit)))
      "g" = some (65, 0) := by decide

example : FLOOKUP (crepToLoopMakeFuncsHOL
      ([("f", [1, 2], ()), ("g", [], ())] : List (String × List Nat × Unit)))
      "h" = none := by decide

/-- Duplicate names keep the first-inserted binding (`alist_to_fmap`). -/
example : FLOOKUP (crepToLoopMakeFuncsHOL
      ([("f", [1], ()), ("f", [1, 2, 3], ())] : List (String × List Nat × Unit)))
      "f" = some (64, 1) := by decide

/-- Replay the same direct HOL `mkf_*` oracle rows through the canonical
    finite-support result carrier, rather than only through the raw-map helper. -/
def exactMakeFuncsProg :
    List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 8) :=
  [(Flapjack.Basis.Pure.MlString.ofString "f", [1, 2], .skip),
   (Flapjack.Basis.Pure.MlString.ofString "g", [], .skip)]

example :
    (crepToLoopMakeFuncsExactHOL exactMakeFuncsProg).lookup
      (Flapjack.Basis.Pure.MlString.ofString "f") = some (64, 2) := by
  rw [← crepToLoopMakeFuncsHOL_lookup_eq_exact]
  decide

example :
    (crepToLoopMakeFuncsExactHOL exactMakeFuncsProg).lookup
      (Flapjack.Basis.Pure.MlString.ofString "g") = some (65, 0) := by
  rw [← crepToLoopMakeFuncsHOL_lookup_eq_exact]
  decide

example :
    (crepToLoopMakeFuncsExactHOL exactMakeFuncsProg).lookup
      (Flapjack.Basis.Pure.MlString.ofString "h") = none := by
  rw [← crepToLoopMakeFuncsHOL_lookup_eq_exact]
  decide

/-- Duplicate names keep the first association, as required by HOL
    `alist_to_fmap` (`mkf_dup_first`). -/
example :
    (crepToLoopMakeFuncsExactHOL
      ([(Flapjack.Basis.Pure.MlString.ofString "f", [1], .skip),
        (Flapjack.Basis.Pure.MlString.ofString "f", [1, 2, 3], .skip)] :
          List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 8))).lookup
      (Flapjack.Basis.Pure.MlString.ofString "f") = some (64, 1) := by
  rw [← crepToLoopMakeFuncsHOL_lookup_eq_exact]
  decide

/-! The following proofs exercise the *relation itself* on the same 8-bit
    cases as the checked-in HOL oracle, rather than only its total-memory view. -/
example : crepToLoopMemRel
    (fun _ : BitVec 8 => .word 7)
    (fun _ : BitVec 8 => .word 7)
    (fun ad => ad == 4) := by
  intro ad _
  rfl

example : ¬ crepToLoopMemRel
    (fun _ : BitVec 8 => .word 7)
    (fun _ : BitVec 8 => .word 9)
    (fun ad => ad == 4) := by
  intro h
  have h4 := h 4 (by decide)
  simp [wlabWloc] at h4

example : crepToLoopMemRel
    (fun _ : BitVec 8 => .word 7)
    (fun _ : BitVec 8 => .word 9)
    (fun _ => false) := by
  intro _ h
  cases h

/-! Pure-num `crep_to_loopScript.sml` helper definitions (`gen_temps_def`,
    `rt_var_def`, `rt_vars_def`, `first_name_def`), matching oracle rows
    `gen_temps_3`, `first_name`, `rt_var_some/none/absent`,
    `rt_vars_some/absent` in `scripts/hol-probes/crep_to_loop_helpers_probe.out`. -/
example : genTemps 5 3 = [5, 6, 7] := by decide

example : firstLoopName = 64 := rfl

def rtVarFm : FiniteMap Nat Nat :=
  FUPDATE (FUPDATE (FEMPTY : FiniteMap Nat Nat) (1, 10)) (2, 7)

example : rtVar rtVarFm (some 2) 9 99 = 7 := by
  simp [rtVar, rtVarFm, FLOOKUP_update]

example : rtVar rtVarFm none 9 99 = 9 := rfl

example : rtVar rtVarFm (some 4) 9 99 = 100 := by
  simp [rtVar, rtVarFm, FLOOKUP_update]

example : rtVars rtVarFm [1, 2] 99 = [10, 7] := by
  simp [rtVars, rtVarFm, FLOOKUP_update]

example : rtVars rtVarFm [1, 4] 99 = [100] := by
  simp [rtVars, rtVarFm, FLOOKUP_update]

/-- Polymorphism witness: `rtVar`/`rtVars` accept any finite-map key, exactly the
    inferred HOL type `'a |-> num`. -/
example : rtVar (fun _ : Bool => none : FiniteMap Bool Nat) (some true) 1 2 = 3 := by
  simp [rtVar, FLOOKUP]

example : rtVars (fun _ : Bool => none : FiniteMap Bool Nat) [true] 2 = [3] := by
  simp [rtVars, FLOOKUP]

/-! Exact `Spt` regression for HOL `mem_lookup_fromalist_some`; these checks
    reproduce `ml_hit`, `ml_miss`, and `ml_distinct` in
    `scripts/hol-probes/crep_to_loop_mem_lookup_probe.out`. -/
private def memLookupOracleEntries : List (Nat × Nat) := [(1, 7), (2, 9)]

example : memLookupOracleEntries.map Prod.fst = [1, 2] := by decide

example : (memLookupOracleEntries.map Prod.fst).Nodup := by decide

example : (2, 9) ∈ memLookupOracleEntries := by decide

example : sptLookup 2 (sptFromAList memLookupOracleEntries) = some 9 :=
  memLookupFromAListSomeExact (by decide) (by decide)

example : sptLookup 3 (sptFromAList memLookupOracleEntries) = none := by
  simp [sptFromAList, memLookupOracleEntries, sptLookup, sptInsert]

/-- HOL `make_vmap` is a left fold of `|+`, so a duplicate parameter keeps the
    LAST binding (`mvd_dup_last_wins` in
    `scripts/hol-probes/crep_to_loop_make_vmap_dup_probe.out`).  The executed
    `crepMakeVmap` replays the positional pairs most-recent-first so its
    first-match lookup reproduces that, and agrees with the tagged
    `makeVmapHOL` for every parameter list. -/
example : lookupNatInfo 7 (crepMakeVmap [7, 7]) = some 1 := by decide

example : lookupNatInfo 7 (crepMakeVmap [7, 7]) = FLOOKUP (makeVmapHOL [7, 7]) 7 :=
  lookupNatInfo_crepMakeVmap_eq_flookup_makeVmapHOL [7, 7] 7

/-- HOL `map_map2_fst` oracle rows (`mm2_*` in
    `scripts/hol-probes/crep_to_loop_map_map2_fst_probe.out`). -/
example :
    (panMap2
        (fun x y =>
          (x, List.range y.2.1.length, (fun (_ : List Nat) (_ : Unit) => true) y.2.1 y.2.2))
        [1, 2] ([(0, [], ()), (1, [7, 8], ())] : List (Nat × List Nat × Unit))).map
      Prod.fst = [1, 2] :=
  mapMap2FstHOL [1, 2] [(0, [], ()), (1, [7, 8], ())] (fun _ _ => true) rfl

/-- HOL `alookup_el_pair_eq_el` oracle rows (`ael_*` in
    `scripts/hol-probes/crep_to_loop_alookup_el_probe.out`). -/
def alookupElProg : List (String × List Nat × Nat) :=
  [("a", ([], 7)), ("b", ([], 9))]

example : alookupElProg[1]'(by decide) = ("b", [], 9) :=
  alookupElPairEqEl alookupElProg "b" 9 1
    (by decide) (by decide) (by decide) (by decide)

/-- HOL `all_distinct_ctxt_lookup_all_distinct` oracle rows (`acd_*` in
    `scripts/hol-probes/crep_to_loop_rt_vars_distinct_probe.out`): a distinct
    context (`1 ↦ 10`, `2 ↦ 20`) keeps `rt_vars` distinct on the success list
    `[1, 2]`, and the `OPT_MMAP`-failure list `[1, 3]` still yields `[n+1]`. -/
def rtVarsCtxtFm : FiniteMap Nat Nat :=
  FUPDATE (FUPDATE (FEMPTY : FiniteMap Nat Nat) (1, 10)) (2, 20)

theorem rtVarsCtxtFm_distinct : crepToLoopDistinctVars rtVarsCtxtFm := by
  intro x y n m hx hy h
  simp only [rtVarsCtxtFm, FLOOKUP_update] at hx hy
  split at hx <;> split at hy <;> simp_all <;> omega

def rtVarsCtxt : CrepToLoopFiniteMapContext :=
  { vars := rtVarsCtxtFm, funcs := (FEMPTY : FiniteMap FunName (Nat × Nat)),
    vmax := 5, target := .riscv }

example : (rtVars rtVarsCtxtFm [1, 2] 0).Nodup :=
  allDistinctCtxtLookupAllDistinct rtVarsCtxt [1, 2] 0 (by decide) rtVarsCtxtFm_distinct

example : (rtVars rtVarsCtxtFm [1, 3] 0).Nodup :=
  allDistinctCtxtLookupAllDistinct rtVarsCtxt [1, 3] 0 (by decide) rtVarsCtxtFm_distinct

/-- Exact-carrier replay of the same direct HOL rows (`acd_*` in
    `scripts/hol-probes/crep_to_loop_rt_vars_distinct_probe.out`): the exact
    `CrepToLoopContextExact` keeps `vars` as `HolFiniteMapExact Nat Nat`
    (matching HOL `num |-> num`), so the tagged
    `allDistinctCtxtLookupAllDistinctExact` applies to it directly. -/
def exactRtVarsFm : HolFiniteMapExact Nat Nat :=
  (HolFiniteMapExact.empty.updateEq (1, 10)).updateEq (2, 20)

theorem exactRtVarsFm_flookup (k : Nat) :
    FLOOKUP exactRtVarsFm.lookup k =
      if k = 1 then some 10 else if k = 2 then some 20 else none := by
  simp only [FLOOKUP, exactRtVarsFm, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    HolFiniteMapExact.empty]
  by_cases h1 : k = 1 <;> by_cases h2 : k = 2 <;> simp_all

theorem exactRtVarsFm_distinct : crepToLoopDistinctVars exactRtVarsFm.lookup := by
  intro x y n m hx hy h
  rw [exactRtVarsFm_flookup] at hx hy
  split at hx <;> split at hy <;> simp_all <;> omega

def exactRtVarsCtxt : CrepToLoopContextExact :=
  { vars := exactRtVarsFm, funcs := HolFiniteMapExact.empty, vmax := 5, target := .riscv }

example : (rtVars exactRtVarsFm.lookup [1, 2] 0).Nodup :=
  allDistinctCtxtLookupAllDistinctExact exactRtVarsCtxt [1, 2] 0 (by decide) exactRtVarsFm_distinct

example : (rtVars exactRtVarsFm.lookup [1, 3] 0).Nodup :=
  allDistinctCtxtLookupAllDistinctExact exactRtVarsCtxt [1, 3] 0 (by decide) exactRtVarsFm_distinct

/-- HOL `list_insert_SNOC` oracle rows (`li_*` in
    `scripts/hol-probes/crep_to_loop_list_insert_probe.out`): `list_insert [3;4]`
    records 3 and 4 but not 5; appending 5 records it; and the SNOC form agrees
    with `insert 5 ()` after `list_insert [3;4]`. -/
example : sptLookup 3 (sptListInsert [3, 4] (Spt.ln : NumSet)) = some () := by
  simp [sptLookup, sptInsert, sptListInsert]

example : sptLookup 4 (sptListInsert [3, 4] (Spt.ln : NumSet)) = some () := by
  simp [sptLookup, sptInsert, sptListInsert]

example : sptLookup 5 (sptListInsert [3, 4] (Spt.ln : NumSet)) = none := by
  simp [sptLookup, sptInsert, sptListInsert]

example : sptLookup 5 (sptListInsert ([3, 4] ++ [5]) (Spt.ln : NumSet)) = some () := by
  simp [sptLookup, sptInsert, sptListInsert]

example :
    sptLookup 9 (sptListInsert ([3, 4] ++ [5]) (Spt.ln : NumSet)) =
      sptLookup 9 (sptInsert 5 () (sptListInsert [3, 4] (Spt.ln : NumSet))) := by
  simp [sptLookup, sptInsert, sptListInsert]

/-- HOL `list_insert_SNOC` (`crep_to_loopProofScript.sml:386`): appending a key
    to a key list is the same as inserting it into the resulting set. -/
example (x : Nat) (ys : List Nat) (tree : NumSet) :
    sptListInsert (ys ++ [x]) tree = sptInsert x () (sptListInsert ys tree) :=
  sptListInsert_snoc x ys tree

/-- HOL `insert_insert_eq` oracle rows (`iie_*` in
    `scripts/hol-probes/crep_to_loop_insert_insert_probe.out`): inserting the
    same key with the same value twice overwrites rather than duplicates, so
    the inserted key reads back the value, a neighbouring key is preserved, and
    the double insert agrees with the single insert. -/
example : sptLookup 5 (sptInsert 5 7 (sptInsert 5 7 (Spt.ln : Spt Nat))) = some 7 := by
  simp [sptLookup, sptInsert]

example :
    sptLookup 11 (sptInsert 11 7 (sptInsert 11 7 (sptInsert 5 3 (Spt.ln : Spt Nat)))) =
      some 7 := by
  simp [sptLookup, sptInsert]

example :
    sptLookup 5 (sptInsert 11 7 (sptInsert 11 7 (sptInsert 5 1 (Spt.ln : Spt Nat)))) =
      some 1 := by
  simp [sptLookup, sptInsert]

example : sptLookup 4 (sptInsert 5 7 (sptInsert 5 7 (Spt.ln : Spt Nat))) = none := by
  simp [sptLookup, sptInsert]

example :
    sptLookup 5 (sptInsert 5 7 (sptInsert 5 7 (Spt.ln : Spt Nat))) =
      sptLookup 5 (sptInsert 5 7 (Spt.ln : Spt Nat)) := by
  simp [sptLookup, sptInsert]

example :
    sptLookup 11 (sptInsert 11 7 (sptInsert 11 7 (sptInsert 5 3 (Spt.ln : Spt Nat)))) =
      sptLookup 11 (sptInsert 11 7 (sptInsert 5 3 (Spt.ln : Spt Nat))) := by
  simp [sptLookup, sptInsert]

/-- HOL `insert_insert_eq` (`crep_to_loopProofScript.sml:380`): inserting the
    same key with the same value twice is the same as inserting it once. -/
example {α : Type} (a : Nat) (b : α) (tree : Spt α) :
    sptInsert a b (sptInsert a b tree) = sptInsert a b tree :=
  sptInsert_insert_eq a b tree

/-- HOL `list_insert_insert` oracle rows (`lii_*` in
    `scripts/hol-probes/crep_to_loop_list_insert2_probe.out`): moving a lone
    `insert` across `list_insert` preserves the tree both for a non-member and a
    member key, and the inserted key reads back while neighbours and absent keys
    are unchanged. -/
example :
    sptInsert 5 () (sptListInsert [3, 4] (Spt.ln : NumSet)) =
      sptListInsert [3, 4] (sptInsert 5 () (Spt.ln : NumSet)) :=
  sptListInsert_insert 5 [3, 4] (Spt.ln : NumSet)

example :
    sptInsert 3 () (sptListInsert [3, 4] (Spt.ln : NumSet)) =
      sptListInsert [3, 4] (sptInsert 3 () (Spt.ln : NumSet)) :=
  sptListInsert_insert 3 [3, 4] (Spt.ln : NumSet)

example :
    sptLookup 5 (sptInsert 5 () (sptListInsert [3, 4] (Spt.ln : NumSet))) = some () := by
  simp [sptLookup, sptInsert, sptListInsert]

example :
    sptLookup 4 (sptInsert 5 () (sptListInsert [3, 4] (Spt.ln : NumSet))) = some () := by
  simp [sptLookup, sptInsert, sptListInsert]

example :
    sptLookup 7 (sptInsert 5 () (sptListInsert [3, 4] (Spt.ln : NumSet))) = none := by
  simp [sptLookup, sptInsert, sptListInsert]

/-- HOL `list_insert_append` oracle rows (`lia_*` in
    `scripts/hol-probes/crep_to_loop_list_insert2_probe.out`): inserting a
    concatenation equals inserting the two lists in turn, with each member
    present and an absent key still missing. -/
example :
    sptListInsert ([3, 4] ++ [5, 6]) (Spt.ln : NumSet) =
      sptListInsert [3, 4] (sptListInsert [5, 6] (Spt.ln : NumSet)) :=
  sptListInsert_append [3, 4] [5, 6] (Spt.ln : NumSet)

example :
    sptLookup 6 (sptListInsert ([3, 4] ++ [5, 6]) (Spt.ln : NumSet)) = some () := by
  simp [sptLookup, sptInsert, sptListInsert]

example :
    sptLookup 3 (sptListInsert ([3, 4] ++ [5, 6]) (Spt.ln : NumSet)) = some () := by
  simp [sptLookup, sptInsert, sptListInsert]

example :
    sptLookup 7 (sptListInsert ([3, 4] ++ [5, 6]) (Spt.ln : NumSet)) = none := by
  simp [sptLookup, sptInsert, sptListInsert]

/-- HOL `list_insert_insert` (`crep_to_loopProofScript.sml:406`): a lone
    `insert` may be moved to the front of `list_insert` when it keeps the same
    key and unit value. -/
example (x : Nat) (xs : List Nat) (tree : NumSet) :
    sptInsert x () (sptListInsert xs tree) = sptListInsert xs (sptInsert x () tree) :=
  sptListInsert_insert x xs tree

/-- HOL `list_insert_append` (`crep_to_loopProofScript.sml:414`): inserting a
    concatenated key list equals inserting the two lists in turn. -/
example (xs ys : List Nat) (tree : NumSet) :
    sptListInsert (xs ++ ys) tree = sptListInsert xs (sptListInsert ys tree) :=
  sptListInsert_append xs ys tree

end Flapjack.Test.CrepToLoopParity
