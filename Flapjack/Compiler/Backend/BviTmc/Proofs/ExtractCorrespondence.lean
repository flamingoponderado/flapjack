import Flapjack.Compiler.Backend.BviTmc.Proofs.PureCorrespondence
import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractTotal

/-! Source-shaped constructor extraction and its executable correspondence. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

/-- Number consecutive bindings in source order. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bind_def"]
def bind {α : Type} (n : Nat) : List α → List Nat × Nat
  | [] => ([], n)
  | _ :: xs => let (vs, last) := bind (n + 1) xs; (n :: vs, last)

private theorem bind_eq_range {α : Type} (n : Nat) (xs : List α) :
    bind n xs = (List.range' n xs.length, n + xs.length) := by
  induction xs generalizing n with
  | nil => simp [bind]
  | cons x xs ih => simp [bind, ih, List.range', Nat.add_comm, Nat.add_left_comm]

/-- Convert a direct self-call into its binding skeleton. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "call_to_cb_def"]
def callToBlockSource (loc ticks : Nat) (dest : Option Nat) (args : List Exp)
    (handler : Option Exp) : Option (List Exp × CallBlock) :=
  if dest = some loc ∧ handler = none then
    let (vs, _) := bind 0 args
    some (args, .rCall ticks vs)
  else none

private theorem callToBlock_eq_source (loc ticks : Nat) (dest : Option Nat) (args : List Exp)
    (handler : Option Exp) :
    (match dest, handler with
      | some d, none => if d == loc then some (args, CallBlock.rCall ticks (List.range args.length)) else none
      | _, _ => none) = callToBlockSource loc ticks dest args handler := by
  cases dest <;> cases handler <;> simp [callToBlockSource, bind_eq_range, List.range_eq_range']

/-- Shift source variable indices. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "shift_vars_def"]
def shiftVarsSource (n : Nat) (xs : List Nat) : List Nat := xs.map (· + n)

private abbrev ExtractResult := List Exp × Sum (List Nat) CallBlock

mutual
/-- Source extraction from one expression. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_aux_def"]
def extractOneSource (n loc tag : Nat) : Exp → Option ExtractResult
  | .call ticks dest args handler =>
      (callToBlockSource loc ticks dest args handler).map fun (bs, cb) =>
        (bs, .inr (.callBlock tag [] cb []))
  | .op (.blockOp (.cons childTag)) args =>
      match extractListSource n loc childTag args with
      | none => none
      | some (_, .inl _) =>
        if pureExp n (.op (.blockOp (.cons childTag)) args) then
          some ([.op (.blockOp (.cons childTag)) args], .inl [0]) else none
      | some (bs, .inr cb) => some (bs, .inr (.callBlock tag [] cb []))
  | e => if pureExp n e then some ([e], .inl [0]) else none
termination_by e => expBudget e
decreasing_by all_goals simp [expBudget] <;> omega

/-- Source right-to-left extraction from an expression list. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_aux_def"]
def extractListSource (n loc tag : Nat) : List Exp → Option ExtractResult
  | [] => some ([], .inl [])
  | [x] => extractOneSource n loc tag x
  | x :: y :: xs =>
      match extractListSource n loc tag (y :: xs) with
      | none => none
      | some (bs2, .inl vs2) =>
        match extractOneSource n loc tag x with
        | none => none
        | some (bs1, .inl vs1) =>
          if vs1.length + vs2.length ≤ 268435457 then
            some (bs1 ++ bs2, .inl (vs1 ++ shiftVarsSource bs1.length vs2)) else none
        | some (bs1, .inr (.callBlock _ [] child [])) =>
          some (bs1 ++ bs2, .inr (.callBlock tag [] child (shiftVarsSource bs1.length vs2)))
        | some (_, .inr _) => none
      | some (bs2, .inr cb) =>
        match shiftBlock 1 cb with
        | .callBlock t left child right => some (x :: bs2, .inr (.callBlock t (0 :: left) child right))
        | _ => none
termination_by xs => listBudget xs
decreasing_by all_goals simp [listBudget] <;> omega
end

mutual
/-- Every successful single-expression traversal returns the source result. -/
theorem extractOneFuel_success_eq (fuel n loc tag : Nat) (e : Exp) (result : Option ExtractResult)
    (run : extractOneFuel fuel n loc tag e = some result) : result = extractOneSource n loc tag e := by
  cases fuel with
  | zero => simp [extractOneFuel] at run
  | succ fuel =>
    cases e with
    | call ticks dest args handler =>
      change (match (match dest, handler with
        | some d, none => if d == loc then some (args, CallBlock.rCall ticks (List.range args.length)) else none
        | _, _ => none) with
        | some (bs, cb) => some (some (bs, Sum.inr (CallBlock.callBlock tag [] cb [])))
        | none => some none) = some result at run
      rw [callToBlock_eq_source] at run
      simp only [extractOneSource]
      cases h : callToBlockSource loc ticks dest args handler with
      | none => simp [h] at run ⊢; exact run.symm
      | some pair => obtain ⟨bs, cb⟩ := pair; simp [h] at run ⊢; exact run.symm
    | op op xs =>
      cases op with
      | blockOp block =>
        cases block with
        | cons childTag =>
          cases extracted : extractListFuel fuel n loc childTag xs with
          | none => simp [extractOneFuel, extracted] at run
          | some value =>
            have equal := extractListFuel_success_eq fuel n loc childTag xs value extracted
            simp only [extractOneFuel, extracted, pureBounded_eq_pureExp] at run
            simp only [extractOneSource, ← equal]
            clear equal extracted
            cases value with
            | none => simpa using (Option.some.inj run).symm
            | some item =>
              obtain ⟨bs, kind⟩ := item
              cases kind <;> simp_all <;> split at run <;> simp_all
        | _ => simp_all [extractOneFuel, extractOneSource, pureBounded_eq_pureExp] <;> split at run <;> simp_all
      | _ => simp_all [extractOneFuel, extractOneSource, pureBounded_eq_pureExp] <;> split at run <;> simp_all
    | _ => simp_all [extractOneFuel, extractOneSource, pureBounded_eq_pureExp] <;> split at run <;> simp_all
termination_by fuel

/-- Every successful list traversal returns the source right-to-left result. -/
theorem extractListFuel_success_eq (fuel n loc tag : Nat) (xs : List Exp) (result : Option ExtractResult)
    (run : extractListFuel fuel n loc tag xs = some result) : result = extractListSource n loc tag xs := by
  cases xs with
  | nil => simpa [extractListFuel, extractListSource] using (Option.some.inj run).symm
  | cons x xs =>
    cases fuel with
    | zero => simp [extractListFuel] at run
    | succ fuel =>
      cases xs with
      | nil =>
        have eq := extractOneFuel_success_eq fuel n loc tag x result (by simpa [extractListFuel] using run)
        simpa [extractListSource] using eq
      | cons y ys =>
        cases rest : extractListFuel fuel n loc tag (y :: ys) with
        | none => simp [extractListFuel, rest] at run
        | some restValue =>
          have restEq := extractListFuel_success_eq fuel n loc tag (y :: ys) restValue rest
          simp only [extractListFuel, rest] at run
          simp only [extractListSource, ← restEq]
          clear restEq rest
          cases restValue with
          | none => simpa using (Option.some.inj run).symm
          | some item =>
            obtain ⟨bs2, kind⟩ := item
            cases kind with
            | inr cb =>
              cases shifted : shiftBlock 1 cb <;> simp_all
            | inl vs2 =>
              cases first : extractOneFuel fuel n loc tag x with
              | none => simp [first] at run
              | some firstValue =>
                have firstEq := extractOneFuel_success_eq fuel n loc tag x firstValue first
                simp only [first] at run
                simp only [← firstEq]
                clear firstEq first
                cases firstValue with
                | none => simpa using (Option.some.inj run).symm
                | some item =>
                  obtain ⟨bs1, kind⟩ := item
                  cases kind with
                  | inl vs1 =>
                    change (if vs1.length + vs2.length ≤ 268435457 then
                      some (some (bs1 ++ bs2, Sum.inl (vs1 ++ vs2.map (· + bs1.length))))
                      else some none) = some result at run
                    split at run <;> simp_all [shiftVarsSource] <;> omega
                  | inr cb =>
                    cases cb with
                    | rCall ticks args => simp_all
                    | callBlock t left child right =>
                      cases left <;> cases right <;> simp_all [shiftVarsSource] <;> exact run.symm
termination_by fuel
end

/-- The executable retry always returns the source extraction result. -/
theorem extractListBounded_eq_source (fuel n loc tag : Nat) (xs : List Exp) :
    extractListBounded fuel n loc tag xs = some (extractListSource n loc tag xs) := by
  obtain ⟨result, run⟩ := extractListBounded_succeeds fuel n loc tag xs
  cases first : extractListFuel fuel n loc tag xs with
  | some value =>
    have equal := extractListFuel_success_eq fuel n loc tag xs value first
    simp [extractListBounded, first, equal]
  | none =>
    have retry : extractListFuel (max fuel (listBudget xs + 1)) n loc tag xs = some result := by
      simpa [extractListBounded, first] using run
    have equal := extractListFuel_success_eq _ n loc tag xs result retry
    simpa [equal] using run

/-- Source conversion of a direct call or constructor to a call block. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_def"]
def toBlockSource (n loc : Nat) : Exp → Option (List Exp × CallBlock)
  | .call ticks dest args handler => callToBlockSource loc ticks dest args handler
  | .op (.blockOp (.cons tag)) xs =>
      match extractListSource n loc tag xs with
      | some (bs, .inr cb) => some (bs, cb)
      | _ => none
  | _ => none

/-- The production block-extraction wrapper agrees with the source result. -/
theorem toBlockFuel_eq_source (fuel n loc : Nat) (expression : Exp) :
    toBlockFuel fuel n loc expression = some (toBlockSource n loc expression) := by
  cases expression with
  | call ticks dest args handler =>
    simp only [toBlockFuel, toBlockSource]
    congr 1
    exact callToBlock_eq_source loc ticks dest args handler
  | op op xs =>
    cases op with
    | blockOp block =>
      cases block with
      | cons tag =>
        simp only [toBlockFuel, toBlockSource, extractListBounded_eq_source]
        cases h : extractListSource n loc tag xs with
        | none => rfl
        | some value => obtain ⟨bs, kind⟩ := value; cases kind <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

end Flapjack.Compiler.Backend.BviTmc
