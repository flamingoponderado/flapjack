module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.BoundEvaluation
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileString
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.GeneratedShape

@[expose] public section

/-! Environment independence of BVI code emitted by BVL-to-BVI. -/

namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value expsWeight expWeight expWeight_pos)
open Flapjack.Compiler.Backend.BvlProps (bVarBound)

namespace IEvalBoundCarrier
/-- Canonical BVI reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end IEvalBoundCarrier

/-- Compiled bounded, handler-safe BVL expressions cannot observe an appended
BVI environment. The first counter is the vacuous outer binder in HOL's
original statement. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "iEval_bVarBound"
  (fmap_as_finite_support := [refs])]
theorem iEvalBound {C F : Type} (_outer : Nat) (xs : List Bvl.Exp) (n : Nat)
    (vs : List Value) (state : BviSem.BviState C F) (env : List Value)
    (premises : bVarBound vs.length xs ∧ BvlHandle.Proofs.handleOk xs) :
    BviSem.evaluate (compileListSource n xs).1 (vs ++ env) state =
      BviSem.evaluate (compileListSource n xs).1 vs state := by
  cases xs with
  | nil => simp [compileListSource, BviSem.evaluate]
  | cons first rest =>
    cases rest with
    | nil =>
      cases first with
      | var index =>
        simp only [bVarBound] at premises
        simp [compileListSource, compileSingSource, smartAppend, BviSem.evaluate,
          List.getElem?_append_left premises.1]
      | force location index =>
        simp only [bVarBound] at premises
        simp [compileListSource, compileSingSource, smartAppend, BviSem.evaluate,
          List.getElem?_append_left premises.1]
      | tick body =>
        simp only [bVarBound, BvlHandle.Proofs.handleOk] at premises
        rcases hx : compileSingSource n body with ⟨converted, code, nextName⟩
        have nilRight : smartAppend code .nil = code := by cases code <;> rfl
        have bodySame := iEvalBound _outer [body] n vs (BviSem.decClock 1 state) env premises
        simp only [compileListSource, hx, nilRight] at bodySame
        simp only [compileListSource, compileSingSource, hx, nilRight]
        rw [BviSem.evaluate, BviSem.evaluate]
        by_cases zero : state.clock = 0
        · simp [zero]
        · simpa [zero] using bodySame
      | «let» bindings body =>
        cases bindings with
        | nil =>
          cases body with
          | «let» bindings inner =>
            have shapes : bindings.all BvlProps.isVar = true ∧ bVarBound bindings.length [inner] := by
              have h := premises.2
              simp [BvlHandle.Proofs.handleOk, BvlHandle.Proofs.letOk] at h
              simpa using h.1
            have argBound : bVarBound vs.length bindings := by
              have h := premises.1
              simp only [bVarBound] at h
              exact h.2.1
            obtain ⟨aux, compiledArgs, empty⟩ := compileExps_varList bindings n shapes.1
            rcases innerCode : compileSingSource n inner with ⟨converted, innerAux, nextName⟩
            obtain ⟨ts, left, right⟩ := evaluate_varMapBound bindings vs env state ⟨argBound, shapes.1⟩
            simp only [compileListSource, compileSingSource, List.isEmpty_nil, if_true,
              destLet, compiledArgs, innerCode]
            rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
              BviSem.fixClock_evaluate, left, right]
          | _ => simp [BvlHandle.Proofs.handleOk, BvlHandle.Proofs.letOk] at premises
        | cons first rest =>
          simp only [bVarBound] at premises
          have handlers : BvlHandle.Proofs.handleOk (first :: rest) ∧ BvlHandle.Proofs.handleOk [body] := by
            exact (BvlHandle.Proofs.handleOk_nonemptyLet (first :: rest) body (by simp)).mp premises.2
          rcases hx : compileListSource n (first :: rest) with ⟨bindingCode, bindingAux, n1⟩
          rcases hb : compileSingSource n1 body with ⟨bodyCode, bodyAux, n2⟩
          have bodyNil : smartAppend bodyAux .nil = bodyAux := by cases bodyAux <;> rfl
          have argsSame := iEvalBound _outer (first :: rest) n vs state env ⟨premises.1.1, handlers.1⟩
          simp only [hx] at argsSame
          simp only [compileListSource, compileSingSource, List.isEmpty_cons, Bool.false_eq_true,
            if_false, hx, hb]
          rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
            BviSem.fixClock_evaluate, argsSame]
          cases run : BviSem.evaluate bindingCode vs state with
          | mk result next =>
            cases result with
            | err error => rfl
            | val values =>
              dsimp only
              have valLen := BviSem.evaluate_length bindingCode vs state next values run
              have codeLen := compileListSource_length n (first :: rest)
              simp only [hx] at codeLen
              have bodyBound : bVarBound (values ++ vs).length [body] := by
                simpa [List.length_append, valLen, codeLen, Nat.add_comm] using premises.1.2
              have bodySame := iEvalBound _outer [body] n1 (values ++ vs) next env
                ⟨bodyBound, handlers.2⟩
              simp only [compileListSource, hb, bodyNil] at bodySame
              simpa [List.append_assoc] using bodySame
      | handle body handler =>
        cases body with
        | «let» bindings inner =>
          have handlers : bindings.all BvlProps.isVar = true ∧ bVarBound bindings.length [inner] ∧
              BvlHandle.Proofs.handleOk [inner] ∧ BvlHandle.Proofs.handleOk [handler] := by
            simpa [BvlHandle.Proofs.handleOk] using premises.2
          have boundBody : bVarBound vs.length bindings ∧ bVarBound (vs.length + bindings.length) [inner] := by
            have h := premises.1
            simp only [bVarBound] at h
            exact h.1
          have boundHandler : bVarBound (vs.length + 1) [handler] := by
            have h := premises.1
            simp only [bVarBound] at h
            exact h.2
          obtain ⟨aux, compiledArgs, empty⟩ := compileExps_varList bindings n handlers.1
          rcases innerCode : compileSingSource n inner with ⟨converted, innerAux, n1⟩
          rcases handlerCode : compileSingSource n1 handler with ⟨convertedHandler, handlerAux, n2⟩
          have handlerNil : smartAppend handlerAux .nil = handlerAux := by cases handlerAux <;> rfl
          obtain ⟨ts, left, right⟩ := evaluate_varMapBound bindings vs env state ⟨boundBody.1, handlers.1⟩
          simp only [compileListSource, compileSingSource, destLet, compiledArgs, innerCode, handlerCode]
          rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
            BviSem.fixClock_evaluate, left, right]
          have handlerSame (value : Value) (next : BviSem.BviState C F) :
              BviSem.evaluate [convertedHandler] (value :: (vs ++ env)) next =
                BviSem.evaluate [convertedHandler] (value :: vs) next := by
            have bound : bVarBound (value :: vs).length [handler] := by simpa [Nat.add_comm] using boundHandler
            have h := iEvalBound _outer [handler] n1 (value :: vs) next env ⟨bound, handlers.2.2.2⟩
            simpa only [compileListSource, handlerCode, handlerNil, List.cons_append] using h
          simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, handlerSame]
        | _ => simp [BvlHandle.Proofs.handleOk] at premises
      | ifThenElse condition yes no =>
        simp only [bVarBound, BvlHandle.Proofs.handleOk] at premises
        rcases hc : compileSingSource n condition with ⟨condCode, condAux, n1⟩
        rcases hy : compileSingSource n1 yes with ⟨yesCode, yesAux, n2⟩
        rcases hn : compileSingSource n2 no with ⟨noCode, noAux, n3⟩
        have condNil : smartAppend condAux .nil = condAux := by cases condAux <;> rfl
        have yesNil : smartAppend yesAux .nil = yesAux := by cases yesAux <;> rfl
        have noNil : smartAppend noAux .nil = noAux := by cases noAux <;> rfl
        have condSame := iEvalBound _outer [condition] n vs state env ⟨premises.1.1, premises.2.1⟩
        simp only [compileListSource, hc, condNil] at condSame
        simp only [compileListSource, compileSingSource, hc, hy, hn]
        rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
          BviSem.fixClock_evaluate, condSame]
        cases run : BviSem.evaluate [condCode] vs state with
        | mk result next =>
          cases result with
          | err error => rfl
          | val values =>
            dsimp only
            have yesSame := iEvalBound _outer [yes] n1 vs next env ⟨premises.1.2.1, premises.2.2.1⟩
            have noSame := iEvalBound _outer [no] n2 vs next env ⟨premises.1.2.2, premises.2.2.2⟩
            simp only [compileListSource, hy, hn, yesNil, noNil] at yesSame noSame
            simp only [yesSame, noSame]
      | call ticks dest args =>
        simp only [bVarBound, BvlHandle.Proofs.handleOk] at premises
        rcases hx : compileListSource n args with ⟨converted, code, nextName⟩
        have nilRight : smartAppend code .nil = code := by cases code <;> rfl
        have argsSame := iEvalBound _outer args n vs state env premises
        simp only [hx] at argsSame
        simp only [compileListSource, compileSingSource, hx, nilRight]
        rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
          BviSem.fixClock_evaluate, argsSame]
      | raise body =>
        simp only [bVarBound, BvlHandle.Proofs.handleOk] at premises
        rcases hx : compileSingSource n body with ⟨converted, code, nextName⟩
        have nilRight : smartAppend code .nil = code := by cases code <;> rfl
        have bodySame := iEvalBound _outer [body] n vs state env premises
        simp only [compileListSource, hx, nilRight] at bodySame
        simp only [compileListSource, compileSingSource, hx, nilRight]
        rw [BviSem.evaluate, BviSem.evaluate, bodySame]
      | op op args =>
        simp only [bVarBound, BvlHandle.Proofs.handleOk] at premises
        rcases hx : compileListSource n args with ⟨converted, code, nextName⟩
        have argsSame := iEvalBound _outer args n vs state env premises
        simp only [hx] at argsSame
        simp only [compileListSource, compileSingSource, hx]
        have zeroRun (e : List Value) (s : BviSem.BviState C F) :
            BviSem.evaluate [.op (.intOp (.const 0)) []] e s = (.val [.number 0], s) := by
          apply evaluate_smallConst
          decide
        cases op with
        | label label => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
        | ffi name => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
        | wordOp word => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
        | thunkOp op => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
        | intOp op =>
          cases op with
          | const value =>
            cases converted with
            | nil => simp [compileOp, evaluate_compileInt]
            | cons first rest =>
              simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame,
                evaluate_compileInt]
          | _ => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
        | blockOp op =>
          cases op with
          | fromList tag =>
            cases converted with
            | nil =>
              change BviSem.evaluate [.let [.op (.intOp (.const 0)) []]
                (.op (.blockOp (.fromList tag)) [.var 0,
                  .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none])]
                (vs ++ env) state =
                BviSem.evaluate [.let [.op (.intOp (.const 0)) []]
                (.op (.blockOp (.fromList tag)) [.var 0,
                  .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none])]
                vs state
              simp [BviSem.evaluate, BviSem.fixClock, zeroRun]
            | cons first rest =>
              change BviSem.evaluate [.let (first :: rest)
                (.op (.blockOp (.fromList tag)) [.var 0,
                  .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none])]
                (vs ++ env) state =
                BviSem.evaluate [.let (first :: rest)
                (.op (.blockOp (.fromList tag)) [.var 0,
                  .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none])]
                vs state
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, argsSame]
              cases run : BviSem.evaluate (first :: rest) vs state with
              | mk result next =>
                cases result with
                | err error => rfl
                | val values =>
                  have len := BviSem.evaluate_length (first :: rest) vs state next values run
                  cases values with
                  | nil => simp at len
                  | cons value values =>
                    simp [BviSem.evaluate, BviSem.fixClock, zeroRun]
          | _ => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
        | globOp op =>
          cases op with
          | global index =>
            cases converted with
            | nil => simp [compileOp, BviSem.evaluate]
            | cons first rest =>
              simp only [compileOp, List.isEmpty_cons, Bool.false_eq_true, if_false]
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, argsSame]
              cases run : BviSem.evaluate (first :: rest) vs state with
              | mk result next =>
                cases result with
                | err error => rfl
                | val values =>
                  have len := BviSem.evaluate_length (first :: rest) vs state next values run
                  cases values with
                  | nil => simp at len
                  | cons value values =>
                    simp [BviSem.evaluate]
          | allocGlobal => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
          | _ => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
        | memOp op =>
          cases op with
          | fromListByte =>
            cases converted with
            | nil =>
              change BviSem.evaluate [.let [.op (.intOp (.const 0)) []] (.call 0 (some fromListByteLocation) [.var 0, .op (.intOp (.const 0)) [], .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none)] (vs ++ env) state =
                BviSem.evaluate [.let [.op (.intOp (.const 0)) []] (.call 0 (some fromListByteLocation) [.var 0, .op (.intOp (.const 0)) [], .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none)] vs state
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, zeroRun, zeroRun]
              simp [BviSem.evaluate, BviSem.fixClock, zeroRun]
            | cons first rest =>
              change BviSem.evaluate [.let (first :: rest) (.call 0 (some fromListByteLocation) [.var 0, .op (.intOp (.const 0)) [], .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none)] (vs ++ env) state =
                BviSem.evaluate [.let (first :: rest) (.call 0 (some fromListByteLocation) [.var 0, .op (.intOp (.const 0)) [], .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none)] vs state
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, argsSame]
              cases run : BviSem.evaluate (first :: rest) vs state with
              | mk result next =>
                cases result with
                | err error => rfl
                | val values =>
                  have len := BviSem.evaluate_length (first :: rest) vs state next values run
                  cases values with
                  | nil => simp at len
                  | cons value values =>
                    simp [BviSem.evaluate, BviSem.fixClock, zeroRun]
          | toListByte =>
            cases converted with
            | nil =>
              change BviSem.evaluate [.let [.op (.intOp (.const 0)) []] (.call 0 (some toListByteLocation) [.op (.blockOp (.cons 0)) [], .op (.memOp .lengthByte) [.var 0], .var 0] none)] (vs ++ env) state =
                BviSem.evaluate [.let [.op (.intOp (.const 0)) []] (.call 0 (some toListByteLocation) [.op (.blockOp (.cons 0)) [], .op (.memOp .lengthByte) [.var 0], .var 0] none)] vs state
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, zeroRun, zeroRun]
              simp [BviSem.evaluate, BviSem.fixClock]
            | cons first rest =>
              change BviSem.evaluate [.let (first :: rest) (.call 0 (some toListByteLocation) [.op (.blockOp (.cons 0)) [], .op (.memOp .lengthByte) [.var 0], .var 0] none)] (vs ++ env) state =
                BviSem.evaluate [.let (first :: rest) (.call 0 (some toListByteLocation) [.op (.blockOp (.cons 0)) [], .op (.memOp .lengthByte) [.var 0], .var 0] none)] vs state
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, argsSame]
              cases run : BviSem.evaluate (first :: rest) vs state with
              | mk result next =>
                cases result with
                | err error => rfl
                | val values =>
                  have len := BviSem.evaluate_length (first :: rest) vs state next values run
                  cases values with
                  | nil => simp at len
                  | cons value values =>
                    simp [BviSem.evaluate, BviSem.fixClock]
          | concatByteVec =>
            cases converted with
            | nil =>
              change BviSem.evaluate [.let [.op (.intOp (.const 0)) []] (.call 0 (some concatByteLocation) [.var 0, .op (.intOp (.const 0)) [], .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .call 0 (some sumListLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none)] (vs ++ env) state =
                BviSem.evaluate [.let [.op (.intOp (.const 0)) []] (.call 0 (some concatByteLocation) [.var 0, .op (.intOp (.const 0)) [], .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .call 0 (some sumListLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none)] vs state
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, zeroRun, zeroRun]
              simp [BviSem.evaluate, BviSem.fixClock, zeroRun]
            | cons first rest =>
              change BviSem.evaluate [.let (first :: rest) (.call 0 (some concatByteLocation) [.var 0, .op (.intOp (.const 0)) [], .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .call 0 (some sumListLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none)] (vs ++ env) state =
                BviSem.evaluate [.let (first :: rest) (.call 0 (some concatByteLocation) [.var 0, .op (.intOp (.const 0)) [], .op (.memOp (.refByte true)) [.op (.intOp (.const 0)) [], .call 0 (some sumListLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none]] none)] vs state
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, argsSame]
              cases run : BviSem.evaluate (first :: rest) vs state with
              | mk result next =>
                cases result with
                | err error => rfl
                | val values =>
                  have len := BviSem.evaluate_length (first :: rest) vs state next values run
                  cases values with
                  | nil => simp at len
                  | cons value values =>
                    simp [BviSem.evaluate, BviSem.fixClock, zeroRun]
          | copyByte flag =>
            cases flag with
            | false => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
            | true =>
              let z : Bvi.Exp := .op (.intOp (.const 0)) []
              let padded := if converted.length < 3 then converted ++ List.replicate 3 z else converted
              have paddedSame : BviSem.evaluate padded (vs ++ env) state = BviSem.evaluate padded vs state := by
                dsimp only [padded]
                split
                · change BviSem.evaluateTuple (converted ++ List.replicate 3 z, vs ++ env, state) =
                    BviSem.evaluateTuple (converted ++ List.replicate 3 z, vs, state)
                  conv_lhs => rw [BviSem.evaluateAppend]
                  conv_rhs => rw [BviSem.evaluateAppend]
                  change BviSem.evaluateTuple (converted, vs ++ env, state) =
                    BviSem.evaluateTuple (converted, vs, state) at argsSame
                  rw [argsSame]
                  cases run : BviSem.evaluateTuple (converted, vs, state) with
                  | mk result next =>
                    cases result with
                    | err error => rfl
                    | val values =>
                      simp [BviSem.evaluateTuple, BviSem.evaluate, BviSem.fixClock, z, zeroRun]
                · exact argsSame
              have paddedLen : 3 ≤ padded.length := by
                dsimp only [padded]
                split <;> simp_all
              change BviSem.evaluate [.let padded
                (.let [.op (.memOp (.refByte true)) [z, .var 0]]
                  (.let [.op (.memOp (.copyByte false)) [z, .var 0, .var 1, .var 2, .var 3]] (.var 1)))]
                (vs ++ env) state =
                BviSem.evaluate [.let padded
                (.let [.op (.memOp (.refByte true)) [z, .var 0]]
                  (.let [.op (.memOp (.copyByte false)) [z, .var 0, .var 1, .var 2, .var 3]] (.var 1)))]
                vs state
              rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                BviSem.fixClock_evaluate, paddedSame]
              cases run : BviSem.evaluate padded vs state with
              | mk result next =>
                cases result with
                | err error => rfl
                | val values =>
                  have len := BviSem.evaluate_length padded vs state next values run
                  cases values with
                  | nil => simp only [List.length_nil] at len; omega
                  | cons a values =>
                    cases values with
                    | nil => simp at len; omega
                    | cons b values =>
                      cases values with
                      | nil => simp at len; omega
                      | cons c values =>
                        let initial : Bvi.Exp := .op (.memOp (.refByte true)) [z, .var 0]
                        have initialSame :
                            BviSem.evaluate [initial] ((a :: b :: c :: values) ++ (vs ++ env)) next =
                              BviSem.evaluate [initial] ((a :: b :: c :: values) ++ vs) next := by
                          simp [initial, BviSem.evaluate, BviSem.fixClock, z, zeroRun]
                        change BviSem.evaluate [.let [initial] _] _ _ = BviSem.evaluate [.let [initial] _] _ _
                        rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                          BviSem.fixClock_evaluate, initialSame]
                        cases initialRun : BviSem.evaluate [initial] ((a :: b :: c :: values) ++ vs) next with
                        | mk initialResult middle =>
                          cases initialResult with
                          | err error => rfl
                          | val initialValues =>
                            obtain ⟨value, rfl⟩ := BviSem.evaluate_singleton initial _ next middle initialValues initialRun
                            let copy : Bvi.Exp := .op (.memOp (.copyByte false)) [z, .var 0, .var 1, .var 2, .var 3]
                            have copySame :
                                BviSem.evaluate [copy] ((value :: a :: b :: c :: values) ++ (vs ++ env)) middle =
                                  BviSem.evaluate [copy] ((value :: a :: b :: c :: values) ++ vs) middle := by
                              simp [copy, BviSem.evaluate, BviSem.fixClock, z, zeroRun]
                            change BviSem.evaluate [.let [copy] (.var 1)] _ _ =
                              BviSem.evaluate [.let [copy] (.var 1)] _ _
                            rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
                              BviSem.fixClock_evaluate]
                            simp only [List.cons_append, List.nil_append]
                            simp only [List.cons_append] at copySame
                            rw [copySame]
                            cases copyRun : BviSem.evaluate [copy] (value :: a :: b :: c :: (values ++ vs)) middle with
                            | mk copyResult last =>
                              cases copyResult with
                              | err error => rfl
                              | val copyValues =>
                                obtain ⟨resultValue, rfl⟩ :=
                                  BviSem.evaluate_singleton copy _ middle last copyValues copyRun
                                simp [BviSem.evaluate]

          | mutCons tag index | updateCons | finaliseCons =>
            all_goals simp only [compileOp]
            all_goals change BviSem.evaluate [.let converted (.op (.intOp (.const 0)) [])] (vs ++ env) state =
              BviSem.evaluate [.let converted (.op (.intOp (.const 0)) [])] vs state
            all_goals simp [BviSem.evaluate, BviSem.fixClock_evaluate, argsSame,
              BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BackendCommon.smallEnoughInt]
          | _ => simp [compileOp, BviSem.evaluate, BviSem.fixClock_evaluate, argsSame]
        | install =>
          let z : Bvi.Exp := .op (.intOp (.const 0)) []
          let installArgs := if converted.length ≠ 2 then [.let converted z, z] else converted
          have argsLen : installArgs.length = 2 := by
            dsimp only [installArgs]
            split <;> simp_all
          have installSame : BviSem.evaluate installArgs (vs ++ env) state = BviSem.evaluate installArgs vs state := by
            dsimp only [installArgs]
            split
            · have innerSame : BviSem.evaluate [.let converted z] (vs ++ env) state =
                  BviSem.evaluate [.let converted z] vs state := by
                simp [BviSem.evaluate, BviSem.fixClock_evaluate, argsSame, z, zeroRun]
              change BviSem.evaluateTuple ([.let converted z, z], vs ++ env, state) =
                BviSem.evaluateTuple ([.let converted z, z], vs, state)
              conv_lhs => rw [BviSem.evaluateCons]
              conv_rhs => rw [BviSem.evaluateCons]
              change BviSem.evaluateTuple ([.let converted z], vs ++ env, state) =
                BviSem.evaluateTuple ([.let converted z], vs, state) at innerSame
              rw [innerSame]
              cases innerRun : BviSem.evaluateTuple ([.let converted z], vs, state) with
              | mk result next =>
                cases result with
                | err error => rfl
                | val values =>
                  simp [BviSem.evaluateTuple, z, zeroRun]
            · exact argsSame
          change BviSem.evaluate [.let installArgs
            (.op .install [.call 0 (some listLengthLocation) [.var 0, z] none,
              .call 0 (some listLengthLocation) [.var 1, z] none, .var 0, .var 1])] (vs ++ env) state =
            BviSem.evaluate [.let installArgs
            (.op .install [.call 0 (some listLengthLocation) [.var 0, z] none,
              .call 0 (some listLengthLocation) [.var 1, z] none, .var 0, .var 1])] vs state
          rw [BviSem.evaluate, BviSem.evaluate, BviSem.fixClock_evaluate,
            BviSem.fixClock_evaluate, installSame]
          cases run : BviSem.evaluate installArgs vs state with
          | mk result next =>
            cases result with
            | err error => rfl
            | val values =>
              have len := BviSem.evaluate_length installArgs vs state next values run
              rw [argsLen] at len
              cases values with
              | nil => simp at len
              | cons a values =>
                cases values with
                | nil => simp at len
                | cons b values =>
                  cases values with
                  | nil => simp [BviSem.evaluate, BviSem.fixClock, z, zeroRun]
                  | cons c rest => simp at len
    | cons second tail =>
      simp only [bVarBound, BvlHandle.Proofs.handleOk] at premises
      rcases hx : compileSingSource n first with ⟨converted, code, nextName⟩
      rcases ht : compileListSource nextName (second :: tail) with ⟨compiledTail, aux, finalName⟩
      have nilRight : smartAppend code .nil = code := by cases code <;> rfl
      have headSame := iEvalBound _outer [first] n vs state env ⟨premises.1.1, premises.2.1⟩
      simp only [compileListSource, hx, nilRight] at headSame
      simp only [compileListSource, hx, ht]
      change BviSem.evaluateTuple (converted :: compiledTail, vs ++ env, state) =
        BviSem.evaluateTuple (converted :: compiledTail, vs, state)
      conv_lhs => rw [BviSem.evaluateCons]
      conv_rhs => rw [BviSem.evaluateCons]
      change BviSem.evaluateTuple ([converted], vs ++ env, state) =
        BviSem.evaluateTuple ([converted], vs, state) at headSame
      rw [headSame]
      cases headRun : BviSem.evaluateTuple ([converted], vs, state) with
      | mk headResult next =>
        cases headResult with
        | err error => rfl
        | val values =>
          dsimp only
          have tailSame := iEvalBound _outer (second :: tail) nextName vs next env ⟨premises.1.2, premises.2.2⟩
          simp only [ht] at tailSame
          change BviSem.evaluateTuple (compiledTail, vs ++ env, next) =
            BviSem.evaluateTuple (compiledTail, vs, next) at tailSame
          rw [tailSame]
termination_by expsWeight xs
decreasing_by
  all_goals subst_vars
  all_goals simp only [expsWeight, expWeight]
  all_goals try (have := expWeight_pos second)
  all_goals omega
/-- Naming the compiled list preserves environment independence. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "iEval_bVarBound_extra"
  (fmap_as_finite_support := [refs])]
theorem iEvalBound_extra {Outer C F : Type} (_outer : Outer) (xs : List Bvl.Exp) (n : Nat)
    (vs : List Value) (state : BviSem.BviState C F) (env : List Value) (d : List Bvi.Exp)
    (premises : bVarBound vs.length xs ∧ BvlHandle.Proofs.handleOk xs ∧
      d = (compileListSource n xs).1) :
    BviSem.evaluate d (vs ++ env) state = BviSem.evaluate d vs state := by
  rcases premises with ⟨bounded, handlers, rfl⟩
  exact iEvalBound 0 xs n vs state env ⟨bounded, handlers⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
