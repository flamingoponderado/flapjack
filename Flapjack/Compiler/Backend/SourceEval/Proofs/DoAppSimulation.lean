import Flapjack.Compiler.Backend.SourceEval.Proofs.DoAppIndexed
import Flapjack.Compiler.Backend.SourceEval.Proofs.Store
import Flapjack.Compiler.Backend.SourceEval.Proofs.Equality
import Flapjack.Compiler.Backend.SourceEval.Proofs.PrimitiveTest
import Flapjack.Compiler.Backend.SourceEval.Proofs.PrimitiveArithmetic
import Flapjack.Compiler.Backend.SourceEval.Proofs.PrimitiveConversion
import Flapjack.Compiler.Backend.SourceEval.Proofs.Conversions
import Flapjack.SemanticPrimitivesHOL.ApplyNumeric
import Flapjack.SemanticPrimitivesProps.ResultRelation
import Flapjack.Misc.RichList
import Mathlib.Data.List.Forall2

/-! Complete source primitive-application simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL

/-- Flapjack proof infrastructure: compare the outcomes of thunk inspection. -/
def destRel (oracle : EvalOracleState) : DestThunkResult → DestThunkResult → Prop
  | .badRef, .badRef => True
  | .notThunk, .notThunk => True
  | .isThunk mode x, .isThunk mode' y => mode = mode' ∧ ValueRel oracle x y
  | _, _ => False

/-- Flapjack proof infrastructure: related stores preserve thunk inspection. -/
theorem destRelated (oracle : EvalOracleState) (s t : Store Value) (v w : Value)
    (stores : List.Forall₂ (storeValueRel (ValueRel oracle)) s t)
    (values : ValueRel oracle v w) : destRel oracle (destThunk [v] s) (destThunk [w] t) := by
  cases values with
  | env decoded lookup environments =>
    have encoded := valueToEnvId_some _ _ decoded
    subst_vars
    simp [destThunk, destRel]
  | loc flag index =>
    cases found : storeLookup index s with
    | none =>
      have targetFound := storeValueRel_lookup_none stores index found
      simp [destThunk, found, targetFound, destRel]
    | some source =>
      obtain ⟨target, targetFound, related⟩ := storeValueRel_lookup stores index source found
      cases source <;> cases target <;> simp_all [destThunk, destRel, storeValueRel]
      case thunk.thunk mode x mode' y =>
        obtain ⟨rfl, related⟩ := related
        cases flag <;> simp [related]
  | _ => simp [destThunk, destRel]

/-- Flapjack infrastructure for the force case: related stores and operands preserve successful thunk updates. HOL proves this inline in the evaluator simulation. -/
theorem updateThunk_related (oracle : EvalOracleState) (source target : Store Value)
    (targets targets' values values' : List Value) (updated : Store Value)
    (stores : List.Forall₂ (storeValueRel (ValueRel oracle)) source target)
    (targetRel : List.Forall₂ (ValueRel oracle) targets targets')
    (valueRel : List.Forall₂ (ValueRel oracle) values values')
    (run : updateThunk targets source values = some updated) :
    ∃ updated', updateThunk targets' target values' = some updated' ∧
      List.Forall₂ (storeValueRel (ValueRel oracle)) updated updated' := by
  cases targets with
  | nil => simp [updateThunk] at run
  | cons v vs =>
    cases targetRel with
    | cons vRel vsRel =>
      cases vs with
      | cons v vs => simp [updateThunk] at run
      | nil =>
        cases vsRel
        cases values with
        | nil => simp [updateThunk] at run
        | cons value rest =>
          cases valueRel with
          | @cons _ value' _ _ valRel restRel =>
            cases rest with
            | cons value rest => simp [updateThunk] at run
            | nil =>
              cases restRel
              cases vRel with
              | loc flag index =>
                cases flag with
                | true => simp [updateThunk] at run
                | false =>
                  have inspection := destRelated oracle source target value value' stores valRel
                  cases src : destThunk [value] source <;>
                    cases dst : destThunk [value'] target <;>
                    simp_all [updateThunk, destRel]
                  obtain ⟨updated', assigned, rel⟩ :=
                    storeAssign_related stores index (show storeValueRel (ValueRel oracle)
                      (.thunk .evaluated value) (.thunk .evaluated value') from ⟨rfl, valRel⟩) run
                  exact ⟨updated', assigned, rel⟩
              | _ => simp [updateThunk] at run

/-- Flapjack proof infrastructure: related operands agree on invalid thunk updates. -/
private theorem badRelated (oracle : EvalOracleState) (s t : Store Value) (v w : Value) (mode : ThunkMode)
    (stores : List.Forall₂ (storeValueRel (ValueRel oracle)) s t)
    (values : ValueRel oracle v w) : badThunkUpdate mode v s = badThunkUpdate mode w t := by
  have related := destRelated oracle s t v w stores values
  cases mode <;> simp only [badThunkUpdate]
  · cases hs : destThunk [v] s <;> cases ht : destThunk [w] t <;> simp_all [destRel]
  · rfl


/-- Primitive applications preserve related stores and results.
The unused HOL existential `ref1` has an independent inhabited type `β`.
Primitive evaluation inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "do_app_sim"]
theorem doApp_sim {Config F β : Type} [Nonempty β] (s : State F) (op : Op)
    (xs : List Value) (refs : Store Value) (ffi : HolFfiState F) (r : Result Value Value)
    (ci : CompilerInstance Config) (t : State F) (ys : List Value)
    (premises : doApp (s.refs, s.ffi) op xs.reverse = some ((refs, ffi), r) ∧
      stateRel ci s t ∧ List.Forall₂ (ValueRel (oracleState t.evalState)) xs ys ∧
      r ≠ .err (.abort .typeError)) :
    ∃ (_ref1 : β) (refs' : Store Value) (r' : Result Value Value) (es : EvalOracleState),
      es = oracleState t.evalState ∧ doApp (t.refs, t.ffi) op ys.reverse = some ((refs', ffi), r') ∧
      List.Forall₂ (storeValueRel (ValueRel es)) refs refs' ∧ resultRel (ValueRel es) (ValueRel es) r r' := by
  cases op with
  | arith action typ =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    obtain ⟨refEq, ffiEq, targetRun, resultRel⟩ := arithmeticApp_transport oracle (s.refs, s.ffi)
      (targetRefs, s.ffi) action typ xs.reverse ys.reverse refs ffi r run reversed
    simp only at refEq ffiEq
    subst refs
    subst ffi
    exact ⟨Classical.choice inferInstance, targetRefs, r, oracle, rfl, targetRun, stores, resultRel⟩
  | fromTo sourceType targetType =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    obtain ⟨refEq, ffiEq, targetRun, resultRel⟩ := conversionApp_transport oracle (s.refs, s.ffi)
      (targetRefs, s.ffi) sourceType targetType xs.reverse ys.reverse refs ffi r run reversed
    simp only at refEq ffiEq
    subst refs
    subst ffi
    exact ⟨Classical.choice inferInstance, targetRefs, r, oracle, rfl, targetRun, stores, resultRel⟩
  | shift size shift amount =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => cases size <;> simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => cases size <;> simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | lit lit =>
          cases size <;> cases lit <;> simp [doApp, doAppNumericCore, doAppBasic] at run
          all_goals obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
          case w8.word8 word =>
            refine ⟨Classical.choice inferInstance, targetRefs,
              .val (.litv (.word8 (shift8Lookup shift word amount))), oracle, rfl, ?_, stores, ?_⟩
            · simp [doApp, doAppNumericCore, doAppBasic]
            · exact ValueRel.lit _
          case w64.word64 word =>
            refine ⟨Classical.choice inferInstance, targetRefs,
              .val (.litv (.word64 (shift64Lookup shift word amount))), oracle, rfl, ?_, stores, ?_⟩
            · simp [doApp, doAppNumericCore, doAppBasic]
            · exact ValueRel.lit _
        | _ => cases size <;> simp [doApp, doAppNumericCore, doAppBasic] at run
  | equality =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons second second' rest rest' secondRel tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases compare : doEq source second with
          | typeError => simp [doApp, doAppNumericCore, doAppBasic, compare] at run
          | val bit =>
            have targetCompare := (doEq_simulation oracle).1 source second target second' bit
              ⟨compare, head, secondRel⟩
            simp [doApp, doAppNumericCore, doAppBasic, compare] at run
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
            refine ⟨Classical.choice inferInstance, targetRefs, .val (boolValue bit), oracle,
              rfl, ?_, stores, ?_⟩
            · simp [doApp, doAppNumericCore, doAppBasic, targetCompare]
            · cases bit <;> exact .con .nil
  | test test typ =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp] at run
    | @cons x x' rest rest' first tail =>
      cases tail with
      | nil => simp [doApp] at run
      | @cons y y' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp] at run
        | nil =>
          simp only [doApp] at run ⊢
          cases testRun : doTest test typ x y with
          | typeError => simp [testRun] at run
          | val bit =>
            have targetRun := doTest_simulation oracle test typ x y x' y' bit testRun first second
            simp only [testRun] at run
            cases run
            refine ⟨Classical.choice inferInstance, targetRefs, .val (boolValue bit), oracle, rfl, ?_, stores, ?_⟩
            · simp [targetRun]
            · cases bit <;> exact .con .nil
  | opapp =>
    simp [doApp, doAppNumericCore, doAppBasic] at premises
  | opassign =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons value value' rest rest' valueRel tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | loc flag index =>
            simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
            cases assigned : storeAssign index (.refv value) s.refs with
            | none => simp [assigned] at run
            | some updated =>
              obtain ⟨updated', assign', related⟩ :=
                storeAssign_related stores index (show storeValueRel (ValueRel oracle) (.refv value) (.refv value') from valueRel) assigned
              simp only [assigned] at run
              cases run
              refine ⟨Classical.choice inferInstance, updated', .val (.conv none []), oracle, rfl, ?_, related, ?_⟩
              · simp [assign']
              · exact .con .nil
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | opref =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | cons h tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        simp only [doApp, doAppNumericCore, doAppBasic, storeAlloc] at run ⊢
        cases run
        refine ⟨Classical.choice inferInstance, _, _, oracle, rfl, rfl, ?_, ?_⟩
        · exact List.rel_append stores (.cons h .nil)
        · simp [resultRel, List.Forall₂.length_eq stores]
          exact .loc true _
  | opderef =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | loc flag index =>
          simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
          cases found : storeLookup index s.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry with
            | refv value =>
              obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores index (.refv value) found
              cases entry' with
              | refv value' =>
                have valueRel : ValueRel oracle value value' := related
                simp only [found] at run
                cases run
                refine ⟨Classical.choice inferInstance, targetRefs, .val value', oracle, rfl, ?_, stores, ?_⟩
                · simp [found']
                · exact valueRel
              | _ => simp [storeValueRel] at related
            | _ => simp [found] at run
        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aw8alloc =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons size size' rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons value value' rest rest' valueRel tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | lit lit =>
            cases lit with
            | intLit size =>
              cases valueRel with
              | lit lit =>
                cases lit with
                | word8 byte =>
                  simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
                  by_cases negative : size < 0
                  · simp [negative, boundsFailure] at run
                    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                    refine ⟨Classical.choice inferInstance, targetRefs, .err (.raise subExnV), oracle,
                      rfl, ?_, stores, ?_⟩
                    · simp [negative, boundsFailure]
                    · simp [resultRel, excRel, subExnV]
                      exact .con .nil
                  · simp [negative, storeAlloc] at run
                    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                    refine ⟨Classical.choice inferInstance,
                      targetRefs ++ [.w8array (List.replicate size.toNat byte)],
                      .val (.loc true targetRefs.length), oracle, rfl, ?_, ?_, ?_⟩
                    · simp [negative, storeAlloc]
                    · exact List.rel_append stores (.cons rfl .nil)
                    · simp [resultRel, List.Forall₂.length_eq stores]
                      exact .loc true _
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aw8sub =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | loc flag address =>
            cases second with
            | lit lit =>
              cases lit with
              | intLit index =>
                have safeFlag : (Op.aw8sub == Op.aw8subUnsafe) = false := by decide
                cases found : storeLookup address s.refs with
                | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                | some entry =>
                  cases entry with
                  | w8array items =>
                    obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array items) found
                    cases entry' with
                    | w8array items' =>
                      have itemsEq : items = items' := related
                      subst items'
                      have itemsRel : List.Forall₂ (· = ·) items items := List.forall₂_refl _
                      have sourceRun : readIndexed (s.refs, s.ffi) false items index (.litv ∘ Lit.word8) = some ((refs, ffi), r) := by
                        simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found] using run
                      obtain ⟨stateEq, r', targetRun, resultRelated⟩ := indexedRead_related oracle (s.refs, s.ffi) (targetRefs, s.ffi) (refs, ffi)
                        false index items items (· = ·) (.litv ∘ Lit.word8) (.litv ∘ Lit.word8)
                        itemsRel (fun _ _ h => by subst_vars; exact ValueRel.lit _) r sourceRun
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj stateEq
                      exact ⟨Classical.choice inferInstance, targetRefs, r', oracle, rfl,
                        by simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found'] using targetRun,
                        stores, resultRelated⟩
                    | _ => simp [storeValueRel] at related
                  | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aw8length =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | loc flag index =>
          simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
          cases found : storeLookup index s.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry with
            | w8array items =>
              obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores index (.w8array items) found
              cases entry' with
              | w8array items' =>
                have itemsEq : items = items' := related
                subst items'
                simp only [found] at run
                cases run
                refine ⟨Classical.choice inferInstance, targetRefs, .val (.litv (.intLit items.length)), oracle,
                  rfl, ?_, stores, ?_⟩
                · simp [found']
                · simp only [resultRel]
                  exact ValueRel.lit _
              | _ => simp [storeValueRel] at related
            | _ => simp [found] at run
        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aw8update =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | @cons value value' rest rest' third tail =>
          cases tail with
          | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | nil =>
            cases head with
            | loc flag address =>
              cases second with
              | lit lit =>
                cases lit with
                | intLit index =>
                  cases third with
                  | lit word =>
                    cases word with
                    | word8 word =>
                      have safeFlag : (Op.aw8update == Op.aw8updateUnsafe) = false := by decide
                      cases found : storeLookup address s.refs with
                      | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                      | some entry =>
                        cases entry with
                        | w8array items =>
                          obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array items) found
                          cases entry' with
                          | w8array items' =>
                            have itemsEq : items = items' := related
                            subst items'
                            have itemsRel : List.Forall₂ (· = ·) items items := List.forall₂_refl _
                            have sourceRun : updateIndexed (s.refs, s.ffi) false address items index word .w8array =
                                some ((refs, ffi), r) := by
                              simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found] using run
                            obtain ⟨refs', r', targetRun, targetStores, resultRelated⟩ :=
                              indexedUpdate_related oracle s.refs targetRefs s.ffi ffi false address index items items
                                word word (· = ·) .w8array .w8array stores itemsRel rfl
                                (fun _ _ h => by simpa [storeValueRel, List.forall₂_eq_eq_eq] using h) refs r sourceRun
                            exact ⟨Classical.choice inferInstance, refs', r', oracle, rfl,
                              by simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found'] using targetRun,
                              targetStores, resultRelated⟩
                          | _ => simp [storeValueRel] at related
                        | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                    | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                  | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | copyStrStr =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons offset offset' rest rest' second tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | @cons count count' rest rest' third tail =>
          cases tail with
          | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | nil =>
            cases head with
            | lit lit =>
              cases lit with
              | strLit text =>
                cases second with
                | lit lit =>
                  cases lit with
                  | intLit offset =>
                    cases third with
                    | lit lit =>
                      cases lit with
                      | intLit count =>
                        cases copied : copyArray (text.explode, offset) count none with
                        | none =>
                          simp [doApp, doAppNumericCore, doAppBasic, copied, boundsFailure] at run
                          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                          refine ⟨Classical.choice inferInstance, targetRefs, .err (.raise subExnV), oracle,
                            rfl, ?_, stores, ?_⟩
                          · simp [doApp, doAppNumericCore, doAppBasic, copied, boundsFailure]
                          · simp [resultRel, excRel, subExnV]
                            exact .con .nil
                        | some chars =>
                          simp [doApp, doAppNumericCore, doAppBasic, copied] at run
                          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                          refine ⟨Classical.choice inferInstance, targetRefs, .val (.litv (.strLit (.implode chars))),
                            oracle, rfl, ?_, stores, ?_⟩
                          · simp [doApp, doAppNumericCore, doAppBasic, copied]
                          · exact ValueRel.lit _
                      | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                    | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                  | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | copyStrAw8 =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons a a' rest rest' first tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons b b' rest rest' second tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | @cons c c' rest rest' third tail =>
          cases tail with
          | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
          | @cons d d' rest rest' fourth tail =>
            cases tail with
            | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
            | @cons e e' rest rest' fifth tail =>
              cases tail with
              | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | nil =>
                cases first with
                | lit lit =>
                  cases lit with
                  | strLit text =>
                    cases second with
                    | lit lit =>
                      cases lit with
                      | intLit offset =>
                        cases third with
                        | lit lit =>
                          cases lit with
                          | intLit count =>
                            cases fourth with
                            | loc flag address =>
                              cases fifth with
                              | lit lit =>
                                cases lit with
                                | intLit dstOffset =>
                                  cases found : storeLookup address s.refs with
                                  | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                                  | some entry =>
                                    cases entry with
                                    | w8array bytes =>
                                      obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array bytes) found
                                      cases entry' with
                                      | w8array bytes' =>
                                        have same : bytes = bytes' := related
                                        subst bytes'
                                        cases copied : copyArray (text.explode, offset) count (some (bytes, dstOffset)) with
                                        | none =>
                                          simp [doApp, doAppNumericCore, doAppBasic, found, copied, boundsFailure] at run
                                          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                                          refine ⟨Classical.choice inferInstance, targetRefs, .err (.raise subExnV), oracle,
                                            rfl, ?_, stores, ?_⟩
                                          · simp [doApp, doAppNumericCore, doAppBasic, found', copied, boundsFailure]
                                          · simp [resultRel, excRel, subExnV]
                                            exact .con .nil
                                        | some output =>
                                          cases assigned : storeAssign address (.w8array output) s.refs with
                                          | none => simp [doApp, doAppNumericCore, doAppBasic, found, copied, assigned] at run
                                          | some updated =>
                                            obtain ⟨updated', assign', related⟩ := storeAssign_related stores address
                                              (show storeValueRel (ValueRel oracle) (.w8array output) (.w8array output) from rfl) assigned
                                            simp [doApp, doAppNumericCore, doAppBasic, found, copied, assigned] at run
                                            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                                            refine ⟨Classical.choice inferInstance, updated', .val (.conv none []), oracle,
                                              rfl, ?_, related, ?_⟩
                                            · simp [doApp, doAppNumericCore, doAppBasic, found', copied, assign']
                                            · exact .con .nil
                                      | _ => simp [storeValueRel] at related
                                    | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                      | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                    | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                  | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | copyAw8Str =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons offset offset' rest rest' second tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | @cons count count' rest rest' third tail =>
          cases tail with
          | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | nil =>
            cases head with
            | loc flag address =>
                cases second with
                | lit lit =>
                  cases lit with
                  | intLit offset =>
                    cases third with
                    | lit lit =>
                      cases lit with
                      | intLit count =>
                        cases found : storeLookup address s.refs with
                        | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                        | some entry =>
                          cases entry with
                          | w8array bytes =>
                            obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array bytes) found
                            cases entry' with
                            | w8array bytes' =>
                              have same : bytes = bytes' := related
                              subst bytes'
                              cases copied : copyArray (bytes, offset) count none with
                              | none =>
                                simp [doApp, doAppNumericCore, doAppBasic, found, copied, boundsFailure] at run
                                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                                refine ⟨Classical.choice inferInstance, targetRefs, .err (.raise subExnV), oracle,
                                  rfl, ?_, stores, ?_⟩
                                · simp [doApp, doAppNumericCore, doAppBasic, found', copied, boundsFailure]
                                · simp [resultRel, excRel, subExnV]
                                  exact .con .nil
                              | some chars =>
                                simp [doApp, doAppNumericCore, doAppBasic, found, copied] at run
                                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                                refine ⟨Classical.choice inferInstance, targetRefs, .val (.litv (.strLit (.implode chars))),
                                  oracle, rfl, ?_, stores, ?_⟩
                                · simp [doApp, doAppNumericCore, doAppBasic, found', copied]
                                · exact ValueRel.lit _
                            | _ => simp [storeValueRel] at related
                          | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                      | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                    | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                  | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | copyAw8Aw8 =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons a a' rest rest' first tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons b b' rest rest' second tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | @cons c c' rest rest' third tail =>
          cases tail with
          | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
          | @cons d d' rest rest' fourth tail =>
            cases tail with
            | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
            | @cons e e' rest rest' fifth tail =>
              cases tail with
              | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | nil =>
                cases first with
                | loc srcFlag srcAddress =>
                    cases second with
                    | lit lit =>
                      cases lit with
                      | intLit offset =>
                        cases third with
                        | lit lit =>
                          cases lit with
                          | intLit count =>
                            cases fourth with
                            | loc flag address =>
                              cases fifth with
                              | lit lit =>
                                cases lit with
                                | intLit dstOffset =>
                                  cases sourceFound : storeLookup srcAddress s.refs with
                                  | none => simp [doApp, doAppNumericCore, doAppBasic, sourceFound] at run
                                  | some sourceEntry =>
                                    cases sourceEntry with
                                    | w8array srcBytes =>
                                      obtain ⟨sourceEntry', sourceFound', sourceRelated⟩ := storeValueRel_lookup stores srcAddress (.w8array srcBytes) sourceFound
                                      cases sourceEntry' with
                                      | w8array srcBytes' =>
                                        have sourceSame : srcBytes = srcBytes' := sourceRelated
                                        subst srcBytes'
                                        cases found : storeLookup address s.refs with
                                        | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                                        | some entry =>
                                          cases entry with
                                          | w8array bytes =>
                                            obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array bytes) found
                                            cases entry' with
                                            | w8array bytes' =>
                                              have same : bytes = bytes' := related
                                              subst bytes'
                                              cases copied : copyArray (srcBytes, offset) count (some (bytes, dstOffset)) with
                                              | none =>
                                                simp [doApp, doAppNumericCore, doAppBasic, sourceFound, found, copied, boundsFailure] at run
                                                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                                                refine ⟨Classical.choice inferInstance, targetRefs, .err (.raise subExnV), oracle,
                                                  rfl, ?_, stores, ?_⟩
                                                · simp [doApp, doAppNumericCore, doAppBasic, sourceFound', found', copied, boundsFailure]
                                                · simp [resultRel, excRel, subExnV]
                                                  exact .con .nil
                                              | some output =>
                                                cases assigned : storeAssign address (.w8array output) s.refs with
                                                | none => simp [doApp, doAppNumericCore, doAppBasic, sourceFound, found, copied, assigned] at run
                                                | some updated =>
                                                  obtain ⟨updated', assign', related⟩ := storeAssign_related stores address
                                                    (show storeValueRel (ValueRel oracle) (.w8array output) (.w8array output) from rfl) assigned
                                                  simp [doApp, doAppNumericCore, doAppBasic, sourceFound, found, copied, assigned] at run
                                                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                                                  refine ⟨Classical.choice inferInstance, updated', .val (.conv none []), oracle,
                                                    rfl, ?_, related, ?_⟩
                                                  · simp [doApp, doAppNumericCore, doAppBasic, sourceFound', found', copied, assign']
                                                  · exact .con .nil
                                            | _ => simp [storeValueRel] at related
                                          | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                                      | _ => simp [storeValueRel] at sourceRelated
                                    | _ => simp [doApp, doAppNumericCore, doAppBasic, sourceFound] at run
                                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                      | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                    | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | xorAw8StrUnsafe =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons string string' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | loc flag address =>
            cases second with
            | lit lit =>
              cases lit with
              | strLit text =>
                cases found : storeLookup address s.refs with
                | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                | some entry =>
                  cases entry with
                  | w8array bytes =>
                    obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array bytes) found
                    cases entry' with
                    | w8array bytes' =>
                      have same : bytes = bytes' := related
                      subst bytes'
                      cases computed : xorBytes text.explode bytes with
                      | none => simp [doApp, doAppNumericCore, doAppBasic, found, computed] at run
                      | some output =>
                        cases assigned : storeAssign address (.w8array output) s.refs with
                        | none => simp [doApp, doAppNumericCore, doAppBasic, found, computed, assigned] at run
                        | some updated =>
                          obtain ⟨updated', assign', related⟩ := storeAssign_related stores address
                            (show storeValueRel (ValueRel oracle) (.w8array output) (.w8array output) from rfl) assigned
                          simp [doApp, doAppNumericCore, doAppBasic, found, computed, assigned] at run
                          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                          refine ⟨Classical.choice inferInstance, updated', .val (.conv none []), oracle, rfl, ?_, related, ?_⟩
                          · simp [doApp, doAppNumericCore, doAppBasic, found', computed, assign']
                          · exact .con .nil
                    | _ => simp [storeValueRel] at related
                  | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | implode =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
        cases decoded : valueToCharList source with
        | none => simp [decoded] at run
        | some chars =>
          have decodedTarget := valueToCharList_related oracle source target chars ⟨decoded, head⟩
          simp only [decoded] at run
          cases run
          refine ⟨Classical.choice inferInstance, targetRefs, .val (.litv (.strLit (.implode chars))), oracle, rfl, ?_, stores, ?_⟩
          · simp [decodedTarget]
          · exact ValueRel.lit _
  | explode =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | lit lit =>
          cases lit with
          | strLit str =>
            simp [doApp, doAppNumericCore, doAppBasic] at run
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
            refine ⟨Classical.choice inferInstance, targetRefs,
              .val (listToValue (str.explode.map (.litv ∘ Lit.char))), oracle, rfl, ?_, stores, ?_⟩
            · simp [doApp, doAppNumericCore, doAppBasic]
            · apply (vRelListToValue oracle _ _).mpr
              induction str.explode with
              | nil => exact .nil
              | cons x xs ih => exact .cons (.lit _) ih
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | strsub =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | lit lit =>
            cases lit with
            | strLit text =>
              cases second with
              | lit lit =>
                cases lit with
                | intLit index =>
                  have itemsRel : List.Forall₂ (· = ·) text.explode text.explode := List.forall₂_refl _
                  have sourceRun : readIndexed (s.refs, s.ffi) false text.explode index (.litv ∘ Lit.char) =
                      some ((refs, ffi), r) := by
                    simpa [doApp, doAppNumericCore, doAppBasic] using run
                  obtain ⟨stateEq, r', targetRun, related⟩ := indexedRead_related oracle (s.refs, s.ffi) (targetRefs, s.ffi) (refs, ffi)
                    false index text.explode text.explode (· = ·) (.litv ∘ Lit.char) (.litv ∘ Lit.char)
                    itemsRel (fun _ _ h => by subst_vars; exact ValueRel.lit _) r sourceRun
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj stateEq
                  exact ⟨Classical.choice inferInstance, targetRefs, r', oracle, rfl,
                    by simpa [doApp, doAppNumericCore, doAppBasic] using targetRun, stores, related⟩
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | strlen =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | lit lit =>
          cases lit with
          | strLit str =>
            simp [doApp, doAppNumericCore, doAppBasic] at run
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
            refine ⟨Classical.choice inferInstance, targetRefs,
              .val (.litv (.intLit str.explode.length)), oracle, rfl, ?_, stores, ?_⟩
            · simp [doApp, doAppNumericCore, doAppBasic]
            · exact ValueRel.lit _
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | strcat =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
        cases decoded : valueToList source with
        | none => simp [decoded] at run
        | some parts =>
          obtain ⟨parts', decodedTarget, relatedParts⟩ := valueToList_related oracle source target parts ⟨decoded, head⟩
          cases strings : valuesToString parts with
          | none => simp [decoded, strings] at run
          | some result =>
            have targetStrings := valuesToString_related oracle parts parts' result ⟨strings, relatedParts⟩
            simp [decoded, strings] at run
            obtain ⟨⟨refEq, ffiEq⟩, rfl⟩ := run
            subst refs
            subst ffi
            refine ⟨Classical.choice inferInstance, targetRefs, .val (.litv (.strLit result)), oracle, rfl, ?_, stores, ?_⟩
            · simp [decodedTarget, targetStrings]
            · exact ValueRel.lit _
  | vfromList =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
        cases decoded : valueToList source with
        | none => simp [decoded] at run
        | some parts =>
          obtain ⟨parts', decodedTarget, relatedParts⟩ := valueToList_related oracle source target parts ⟨decoded, head⟩
          simp [decoded] at run
          obtain ⟨⟨refEq, ffiEq⟩, rfl⟩ := run
          subst refs
          subst ffi
          refine ⟨Classical.choice inferInstance, targetRefs, .val (.vectorv parts'), oracle, rfl, ?_, stores, ?_⟩
          · simp [decodedTarget]
          · exact ValueRel.vector relatedParts
  | vsub =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | @vector items items' itemsRel =>
            cases second with
            | lit lit =>
              cases lit with
              | intLit index =>
                have flag : (Op.vsub == Op.vsubUnsafe) = false := by decide
                have sourceRun : readIndexed (s.refs, s.ffi) false items index id = some ((refs, ffi), r) := by
                  simpa [doApp, doAppNumericCore, doAppBasic, flag] using run
                obtain ⟨stateEq, r', targetRun, related⟩ := indexedRead_related oracle (s.refs, s.ffi)
                  (targetRefs, s.ffi) (refs, ffi) false index items items' (ValueRel oracle) id id
                  itemsRel (fun _ _ h => h) r sourceRun
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj stateEq
                exact ⟨Classical.choice inferInstance, targetRefs, r', oracle, rfl,
                  by simpa [doApp, doAppNumericCore, doAppBasic, flag] using targetRun, stores, related⟩
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | vlength =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | @vector sourceItems targetItems related =>
          simp [doApp, doAppNumericCore, doAppBasic] at run
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
          refine ⟨Classical.choice inferInstance, targetRefs, .val (.litv (.intLit targetItems.length)), oracle, rfl, ?_, stores, ?_⟩
          · simp [doApp, doAppNumericCore, doAppBasic]
          · simp only [resultRel, List.Forall₂.length_eq related]
            exact ValueRel.lit _
        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aalloc =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons size size' rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons value value' rest rest' valueRel tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | lit lit =>
            cases lit with
            | intLit size =>
              simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
              by_cases negative : size < 0
              · simp [negative, boundsFailure] at run
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                refine ⟨Classical.choice inferInstance, targetRefs, .err (.raise subExnV), oracle,
                  rfl, ?_, stores, ?_⟩
                · simp [negative, boundsFailure]
                · simp [resultRel, excRel, subExnV]
                  exact .con .nil
              · simp [negative, storeAlloc] at run
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                refine ⟨Classical.choice inferInstance,
                  targetRefs ++ [.varray (List.replicate size.toNat value')],
                  .val (.loc true targetRefs.length), oracle, rfl, ?_, ?_, ?_⟩
                · simp [negative, storeAlloc]
                · exact List.rel_append stores (.cons ((Flapjack.forall₂_replicate_iff _ _ _ _).mpr
                    (fun _ => valueRel)) .nil)
                · simp [resultRel, List.Forall₂.length_eq stores]
                  exact .loc true _
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aallocEmpty =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | @con left right stamp related =>
          cases stamp with
          | some stamp => simp [doApp, doAppNumericCore, doAppBasic] at run
          | none =>
            cases related with
            | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | nil =>
              simp [doApp, doAppNumericCore, doAppBasic, storeAlloc] at run
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
              refine ⟨Classical.choice inferInstance, targetRefs ++ [.varray []],
                .val (.loc true targetRefs.length), oracle, rfl, ?_, ?_, ?_⟩
              · simp [doApp, doAppNumericCore, doAppBasic, storeAlloc]
              · exact List.rel_append stores (.cons .nil .nil)
              · simp [resultRel, List.Forall₂.length_eq stores]
                exact .loc true _
        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aallocFixed =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    simp only [doApp, doAppNumericCore, doAppBasic, storeAlloc] at run ⊢
    cases run
    refine ⟨Classical.choice inferInstance, _, _, oracle, rfl, rfl, ?_, ?_⟩
    · exact List.rel_append stores (.cons reversed .nil)
    · simp [resultRel, List.Forall₂.length_eq stores]
      exact .loc true _
  | asub =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | loc flag address =>
            cases second with
            | lit lit =>
              cases lit with
              | intLit index =>
                have safeFlag : (Op.asub == Op.asubUnsafe) = false := by decide
                cases found : storeLookup address s.refs with
                | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                | some entry =>
                  cases entry with
                  | varray items =>
                    obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.varray items) found
                    cases entry' with
                    | varray items' =>
                      have itemsRel : List.Forall₂ (ValueRel oracle) items items' := related
                      have sourceRun : readIndexed (s.refs, s.ffi) false items index id = some ((refs, ffi), r) := by
                        simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found] using run
                      obtain ⟨stateEq, r', targetRun, resultRelated⟩ := indexedRead_related oracle (s.refs, s.ffi) (targetRefs, s.ffi) (refs, ffi)
                        false index items items' (ValueRel oracle) id id itemsRel (fun _ _ h => h) r sourceRun
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj stateEq
                      exact ⟨Classical.choice inferInstance, targetRefs, r', oracle, rfl,
                        by simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found'] using targetRun,
                        stores, resultRelated⟩
                    | _ => simp [storeValueRel] at related
                  | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | alength =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | loc flag index =>
          simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
          cases found : storeLookup index s.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry with
            | varray items =>
              obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores index (.varray items) found
              cases entry' with
              | varray items' =>
                have itemsRel : List.Forall₂ (ValueRel oracle) items items' := related
                simp only [found] at run
                cases run
                refine ⟨Classical.choice inferInstance, targetRefs, .val (.litv (.intLit items'.length)), oracle,
                  rfl, ?_, stores, ?_⟩
                · simp [found']
                · simp only [resultRel, List.Forall₂.length_eq itemsRel]
                  exact ValueRel.lit _
              | _ => simp [storeValueRel] at related
            | _ => simp [found] at run
        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aupdate =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | @cons value value' rest rest' third tail =>
          cases tail with
          | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | nil =>
            cases head with
            | loc flag address =>
              cases second with
              | lit lit =>
                cases lit with
                | intLit index =>
                  have safeFlag : (Op.aupdate == Op.aupdateUnsafe) = false := by decide
                  cases found : storeLookup address s.refs with
                  | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                  | some entry =>
                    cases entry with
                    | varray items =>
                      obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.varray items) found
                      cases entry' with
                      | varray items' =>
                        have itemsRel : List.Forall₂ (ValueRel oracle) items items' := related
                        have sourceRun : updateIndexed (s.refs, s.ffi) false address items index value .varray =
                            some ((refs, ffi), r) := by
                          simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found] using run
                        obtain ⟨refs', r', targetRun, targetStores, resultRelated⟩ :=
                          indexedUpdate_related oracle s.refs targetRefs s.ffi ffi false address index items items'
                            value value' (ValueRel oracle) .varray .varray stores itemsRel third
                            (fun _ _ h => h) refs r sourceRun
                        exact ⟨Classical.choice inferInstance, refs', r', oracle, rfl,
                          by simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found'] using targetRun,
                          targetStores, resultRelated⟩
                      | _ => simp [storeValueRel] at related
                    | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | vsubUnsafe =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | @vector items items' itemsRel =>
            cases second with
            | lit lit =>
              cases lit with
              | intLit index =>
                have flag : (Op.vsubUnsafe == Op.vsubUnsafe) = true := by decide
                have sourceRun : readIndexed (s.refs, s.ffi) true items index id = some ((refs, ffi), r) := by
                  simpa [doApp, doAppNumericCore, doAppBasic, flag] using run
                obtain ⟨stateEq, r', targetRun, related⟩ := indexedRead_related oracle (s.refs, s.ffi) (targetRefs, s.ffi) (refs, ffi)
                  true index items items' (ValueRel oracle) id id itemsRel (fun _ _ h => h) r sourceRun
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj stateEq
                exact ⟨Classical.choice inferInstance, targetRefs, r', oracle, rfl,
                  by simpa [doApp, doAppNumericCore, doAppBasic, flag] using targetRun, stores, related⟩
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | asubUnsafe =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | loc flag address =>
            cases second with
            | lit lit =>
              cases lit with
              | intLit index =>
                have safeFlag : (Op.asubUnsafe == Op.asubUnsafe) = true := by decide
                cases found : storeLookup address s.refs with
                | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                | some entry =>
                  cases entry with
                  | varray items =>
                    obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.varray items) found
                    cases entry' with
                    | varray items' =>
                      have itemsRel : List.Forall₂ (ValueRel oracle) items items' := related
                      have sourceRun : readIndexed (s.refs, s.ffi) true items index id = some ((refs, ffi), r) := by
                        simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found] using run
                      obtain ⟨stateEq, r', targetRun, resultRelated⟩ := indexedRead_related oracle (s.refs, s.ffi) (targetRefs, s.ffi) (refs, ffi)
                        true index items items' (ValueRel oracle) id id itemsRel (fun _ _ h => h) r sourceRun
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj stateEq
                      exact ⟨Classical.choice inferInstance, targetRefs, r', oracle, rfl,
                        by simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found'] using targetRun,
                        stores, resultRelated⟩
                    | _ => simp [storeValueRel] at related
                  | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aupdateUnsafe =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | @cons value value' rest rest' third tail =>
          cases tail with
          | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | nil =>
            cases head with
            | loc flag address =>
              cases second with
              | lit lit =>
                cases lit with
                | intLit index =>
                  have safeFlag : (Op.aupdateUnsafe == Op.aupdateUnsafe) = true := by decide
                  cases found : storeLookup address s.refs with
                  | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                  | some entry =>
                    cases entry with
                    | varray items =>
                      obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.varray items) found
                      cases entry' with
                      | varray items' =>
                        have itemsRel : List.Forall₂ (ValueRel oracle) items items' := related
                        have sourceRun : updateIndexed (s.refs, s.ffi) true address items index value .varray =
                            some ((refs, ffi), r) := by
                          simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found] using run
                        obtain ⟨refs', r', targetRun, targetStores, resultRelated⟩ :=
                          indexedUpdate_related oracle s.refs targetRefs s.ffi ffi true address index items items'
                            value value' (ValueRel oracle) .varray .varray stores itemsRel third
                            (fun _ _ h => h) refs r sourceRun
                        exact ⟨Classical.choice inferInstance, refs', r', oracle, rfl,
                          by simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found'] using targetRun,
                          targetStores, resultRelated⟩
                      | _ => simp [storeValueRel] at related
                    | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aw8subUnsafe =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | loc flag address =>
            cases second with
            | lit lit =>
              cases lit with
              | intLit index =>
                have safeFlag : (Op.aw8subUnsafe == Op.aw8subUnsafe) = true := by decide
                cases found : storeLookup address s.refs with
                | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                | some entry =>
                  cases entry with
                  | w8array items =>
                    obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array items) found
                    cases entry' with
                    | w8array items' =>
                      have itemsEq : items = items' := related
                      subst items'
                      have itemsRel : List.Forall₂ (· = ·) items items := List.forall₂_refl _
                      have sourceRun : readIndexed (s.refs, s.ffi) true items index (.litv ∘ Lit.word8) = some ((refs, ffi), r) := by
                        simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found] using run
                      obtain ⟨stateEq, r', targetRun, resultRelated⟩ := indexedRead_related oracle (s.refs, s.ffi) (targetRefs, s.ffi) (refs, ffi)
                        true index items items (· = ·) (.litv ∘ Lit.word8) (.litv ∘ Lit.word8)
                        itemsRel (fun _ _ h => by subst_vars; exact ValueRel.lit _) r sourceRun
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj stateEq
                      exact ⟨Classical.choice inferInstance, targetRefs, r', oracle, rfl,
                        by simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found'] using targetRun,
                        stores, resultRelated⟩
                    | _ => simp [storeValueRel] at related
                  | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | aw8updateUnsafe =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons index index' rest rest' second tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
        | @cons value value' rest rest' third tail =>
          cases tail with
          | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | nil =>
            cases head with
            | loc flag address =>
              cases second with
              | lit lit =>
                cases lit with
                | intLit index =>
                  cases third with
                  | lit word =>
                    cases word with
                    | word8 word =>
                      have safeFlag : (Op.aw8updateUnsafe == Op.aw8updateUnsafe) = true := by decide
                      cases found : storeLookup address s.refs with
                      | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                      | some entry =>
                        cases entry with
                        | w8array items =>
                          obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array items) found
                          cases entry' with
                          | w8array items' =>
                            have itemsEq : items = items' := related
                            subst items'
                            have itemsRel : List.Forall₂ (· = ·) items items := List.forall₂_refl _
                            have sourceRun : updateIndexed (s.refs, s.ffi) true address items index word .w8array =
                                some ((refs, ffi), r) := by
                              simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found] using run
                            obtain ⟨refs', r', targetRun, targetStores, resultRelated⟩ :=
                              indexedUpdate_related oracle s.refs targetRefs s.ffi ffi true address index items items
                                word word (· = ·) .w8array .w8array stores itemsRel rfl
                                (fun _ _ h => by simpa [storeValueRel, List.forall₂_eq_eq_eq] using h) refs r sourceRun
                            exact ⟨Classical.choice inferInstance, refs', r', oracle, rfl,
                              by simpa [doApp, doAppNumericCore, doAppBasic, safeFlag, found'] using targetRun,
                              targetStores, resultRelated⟩
                          | _ => simp [storeValueRel] at related
                        | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                    | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                  | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | thunkOp thunk =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases thunk with
    | allocThunk mode =>
      cases reversed with
      | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
      | @cons x y xs ys head tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
        | nil =>
          have badEq := badRelated oracle s.refs targetRefs x y mode stores head
          simp only [doApp, doAppNumericCore, doAppBasic, thunkOp] at run ⊢
          cases bad : badThunkUpdate mode x s.refs with
          | true => simp [bad] at run
          | false =>
            have targetBad : badThunkUpdate mode y targetRefs = false := by rw [← badEq, bad]
            simp [bad, storeAlloc] at run
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
            refine ⟨Classical.choice inferInstance, targetRefs ++ [.thunk mode y],
              .val (.loc false targetRefs.length), oracle, rfl, ?_, ?_, ?_⟩
            · simp [targetBad, storeAlloc]
            · exact List.rel_append stores (.cons ⟨rfl, head⟩ .nil)
            · simp [resultRel, List.Forall₂.length_eq stores]
              exact .loc false _
    | updateThunk mode =>
      cases reversed with
      | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
      | @cons source target rest rest' head tail =>
        cases tail with
        | nil => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
        | @cons value value' rest rest' valueRel tail =>
          cases tail with
          | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
          | nil =>
            cases head with
            | loc flag index =>
              cases flag with
              | true => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
              | false =>
                have badEq := badRelated oracle s.refs targetRefs value value' mode stores valueRel
                simp only [doApp, doAppNumericCore, doAppBasic, thunkOp] at run ⊢
                cases bad : badThunkUpdate mode value s.refs with
                | true => simp [bad] at run
                | false =>
                  have targetBad : badThunkUpdate mode value' targetRefs = false := by rw [← badEq, bad]
                  cases assigned : storeAssign index (.thunk mode value) s.refs with
                  | none => simp [bad, assigned] at run
                  | some updated =>
                    obtain ⟨updated', assign', related⟩ := storeAssign_related stores index
                      (show storeValueRel (ValueRel oracle) (.thunk mode value) (.thunk mode value') from
                        ⟨rfl, valueRel⟩) assigned
                    simp [bad, assigned] at run
                    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                    refine ⟨Classical.choice inferInstance, updated', .val (.conv none []),
                      oracle, rfl, ?_, related, ?_⟩
                    · simp [targetBad, assign']
                    · exact .con .nil
            | _ => simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
    | forceThunk =>
      cases xsr <;> simp [doApp, doAppNumericCore, doAppBasic, thunkOp] at run
  | listAppend =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons source2 target2 rest rest' head2 tail2 =>
        cases tail2 with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          simp only [doApp, doAppNumericCore, doAppBasic] at run ⊢
          cases first : valueToList source with
          | none => simp [first] at run
          | some left =>
            obtain ⟨left', first', leftRel⟩ := valueToList_related oracle source target left ⟨first, head⟩
            cases second : valueToList source2 with
            | none => simp [first, second] at run
            | some right =>
              obtain ⟨right', second', rightRel⟩ := valueToList_related oracle source2 target2 right ⟨second, head2⟩
              simp [first, second] at run
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
              refine ⟨Classical.choice inferInstance, targetRefs, .val (listToValue (left' ++ right')),
                oracle, rfl, ?_, stores, ?_⟩
              · simp [first', second']
              · exact (vRelListToValue oracle _ _).mpr (List.rel_append leftRel rightRel)
  | configGC =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons second second' rest rest' secondRel tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | lit lit =>
            cases lit with
            | intLit first =>
              cases secondRel with
              | lit lit =>
                cases lit with
                | intLit second =>
                  simp [doApp, doAppNumericCore, doAppBasic] at run
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                  refine ⟨Classical.choice inferInstance, targetRefs, .val (.conv none []), oracle,
                    rfl, ?_, stores, ?_⟩
                  · simp [doApp, doAppNumericCore, doAppBasic]
                  · exact .con .nil
                | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | ffi name =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
      | @cons location location' rest rest' second tail =>
        cases tail with
        | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
        | nil =>
          cases head with
          | lit lit =>
            cases lit with
            | strLit configuration =>
              cases second with
              | loc flag address =>
                cases found : storeLookup address s.refs with
                | none => simp [doApp, doAppNumericCore, doAppBasic, found] at run
                | some entry =>
                  cases entry with
                  | w8array bytes =>
                    obtain ⟨entry', found', related⟩ := storeValueRel_lookup stores address (.w8array bytes) found
                    cases entry' with
                    | w8array bytes' =>
                      have same : bytes = bytes' := related
                      subst bytes'
                      cases called : callFFIHOL s.ffi (.extCall name) configuration.explode bytes with
                      | ret newFfi resultBytes =>
                        cases assigned : storeAssign address (.w8array resultBytes) s.refs with
                        | none => simp [doApp, doAppNumericCore, doAppBasic, found, called, assigned] at run
                        | some updated =>
                          obtain ⟨updated', assign', related⟩ := storeAssign_related stores address
                            (show storeValueRel (ValueRel oracle) (.w8array resultBytes) (.w8array resultBytes) from rfl) assigned
                          simp [doApp, doAppNumericCore, doAppBasic, found, called, assigned] at run
                          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                          refine ⟨Classical.choice inferInstance, updated', .val (.conv none []), oracle, rfl, ?_, related, ?_⟩
                          · simp [doApp, doAppNumericCore, doAppBasic, found', called, assign']
                          · exact .con .nil
                      | final event =>
                        simp [doApp, doAppNumericCore, doAppBasic, found, called] at run
                        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                        refine ⟨Classical.choice inferInstance, targetRefs, .err (.abort (.ffiError event)), oracle,
                          rfl, ?_, stores, ?_⟩
                        · simp [doApp, doAppNumericCore, doAppBasic, found', called]
                        · simp [resultRel, excRel]
                    | _ => simp [storeValueRel] at related
                  | _ => simp [doApp, doAppNumericCore, doAppBasic, found] at run
              | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
            | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
          | _ => simp [doApp, doAppNumericCore, doAppBasic] at run
  | eval =>
    simp [doApp, doAppNumericCore, doAppBasic] at premises
  | envId =>
    obtain ⟨run, ⟨dec, oracle, targetRefs, target, stores, rem⟩, values, safe⟩ := premises
    subst t
    simp only [oracleState] at values ⊢
    have reversed := (List.forall₂_reverse_iff).2 values
    generalize hx : xs.reverse = xsr at run reversed
    generalize hy : ys.reverse = ysr at reversed ⊢
    cases reversed with
    | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
    | @cons source target rest rest' head tail =>
      cases tail with
      | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
      | nil =>
        cases head with
        | @env env env' id encoded decoded lookup relation =>
          have encodedEq := valueToEnvId_some target id decoded
          subst target
          rcases id with ⟨generation, index⟩
          simp [doApp, doAppNumericCore, doAppBasic] at run
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
          refine ⟨Classical.choice inferInstance, targetRefs,
            .val (.conv none [natToValue generation, natToValue index]), oracle, rfl, ?_, stores, ?_⟩
          · simp [doApp, doAppNumericCore, doAppBasic]
          · apply ValueRel.con
            simp only [natToValue]
            exact .cons (ValueRel.lit _) (.cons (ValueRel.lit _) .nil)
        | @con left right stamp related =>
          cases stamp with
          | some stamp => simp [doApp, doAppNumericCore, doAppBasic] at run
          | none =>
            cases related with
            | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
            | @cons first first' rest rest' firstRel tail =>
              cases tail with
              | nil => simp [doApp, doAppNumericCore, doAppBasic] at run
              | @cons second second' rest rest' secondRel tail =>
                cases tail with
                | cons _ _ => simp [doApp, doAppNumericCore, doAppBasic] at run
                | nil =>
                  simp [doApp, doAppNumericCore, doAppBasic] at run
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
                  refine ⟨Classical.choice inferInstance, targetRefs,
                    .val (.conv none [first', second']), oracle, rfl, ?_, stores, ?_⟩
                  · simp [doApp, doAppNumericCore, doAppBasic]
                  · exact .con (.cons firstRel (.cons secondRel .nil))
        | _ => simp [doApp, doAppNumericCore, doAppBasic] at run

end Flapjack.Compiler.Backend.SourceEval.Proofs
