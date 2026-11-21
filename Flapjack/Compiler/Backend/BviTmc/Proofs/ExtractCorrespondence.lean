module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.PureCorrespondence
public import Flapjack.Compiler.Backend.BackendCommon.SmallInt
public import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractTotal
public import Flapjack.Compiler.Backend.Bvi.GeneratedSize

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

/-- HOL `bind_size`: binding never changes the argument count. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bind_size"]
theorem bind_length {α : Type} (args : List α) (n : Nat) (vs : List Nat) (n' : Nat)
    (run : bind n args = (vs, n')) : args.length = vs.length := by
  have pairs : (vs, n') = (List.range' n args.length, n + args.length) := by
    rw [← run, bind_eq_range]
  have vsEq : vs = List.range' n args.length := congrArg Prod.fst pairs
  rw [vsEq, List.length_range']

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
          if BackendCommon.smallEnoughInt (Int.ofNat (vs1.length + vs2.length)) then
            some (bs1 ++ bs2, .inl (vs1 ++ shiftVars bs1.length vs2)) else none
        | some (bs1, .inr (.callBlock _ [] child [])) =>
          some (bs1 ++ bs2, .inr (.callBlock tag [] child (shiftVars bs1.length vs2)))
        | some (_, .inr _) => none
      | some (bs2, .inr cb) =>
        match shiftBlock 1 cb with
        | .callBlock t left child right => some (x :: bs2, .inr (.callBlock t (0 :: left) child right))
        | _ => none
termination_by xs => listBudget xs
decreasing_by all_goals simp [listBudget] <;> omega
end

/-- The HOL expression-list size of the empty list. -/
private theorem expListSizeHOL_nil : expListSizeHOL ([] : List Exp) = 0 := rfl

/-- The HOL expression-list size of a cons. -/
private theorem expListSizeHOL_cons (x : Exp) (xs : List Exp) :
    expListSizeHOL (x :: xs) = 1 + (expSizeHOL x + expListSizeHOL xs) := by
  rw [expListSizeHOL.eq_def]

/-- Prepending the same expression preserves the size order of two lists. -/
private theorem expListSizeHOL_cons_le (x : Exp) (xs ys : List Exp)
    (bound : expListSizeHOL xs ≤ expListSizeHOL ys) :
    expListSizeHOL (x :: xs) ≤ expListSizeHOL (x :: ys) := by
  rw [expListSizeHOL_cons, expListSizeHOL_cons]
  omega

/-- Concatenating binding lists adds their sizes. -/
private theorem expListSizeHOL_append (xs ys : List Exp) :
    expListSizeHOL (xs ++ ys) = expListSizeHOL xs + expListSizeHOL ys := by
  induction xs with
  | nil => simp [expListSizeHOL_nil]
  | cons x xs ih =>
    rw [List.cons_append, expListSizeHOL_cons, expListSizeHOL_cons, ih]
    omega

/-- A successful call-block conversion keeps the call's argument list. -/
private theorem callToBlockSource_bindings (loc ticks : Nat) (dest : Option Nat)
    (args : List Exp) (handler : Option Exp) (bs : List Exp) (cb : CallBlock)
    (run : callToBlockSource loc ticks dest args handler = some (bs, cb)) : bs = args := by
  unfold callToBlockSource at run
  split at run
  · obtain ⟨rfl, rfl⟩ := run.symm
    rfl
  · simp at run

/-- A pure single expression extracts to a singleton, which is at most one
larger than its size. -/
private theorem pureExp_size (n : Nat) (e : Exp) (bs : List Exp)
    (sum : Sum (List Nat) CallBlock)
    (run : (if pureExp n e then some ([e], Sum.inl [0]) else none) = some (bs, sum)) :
    expListSizeHOL bs ≤ expSizeHOL e + 1 := by
  split at run
  · have bsEq : bs = [e] := (Prod.mk.inj (Option.some.inj run.symm)).1
    rw [bsEq, expListSizeHOL_cons, expListSizeHOL_nil]
    omega
  · simp at run

mutual
/-- A successful single-expression extraction yields bindings no larger than
the source expression plus one. -/
private theorem extractOne_size (n loc tag : Nat) (e : Exp) (bs : List Exp)
    (sum : Sum (List Nat) CallBlock)
    (run : extractOneSource n loc tag e = some (bs, sum)) :
    expListSizeHOL bs ≤ expSizeHOL e + 1 := by
  cases e with
  | call ticks dest args handler =>
    simp only [extractOneSource] at run
    cases h : callToBlockSource loc ticks dest args handler with
    | none => simp [h] at run
    | some pair =>
      obtain ⟨bs', cb⟩ := pair
      simp only [h, Option.map_some] at run
      have bsEq : bs = args := by
        have pairEq := Option.some.inj run.symm
        exact (Prod.mk.inj pairEq).1.trans
          (callToBlockSource_bindings loc ticks dest args handler bs' cb h)
      rw [bsEq]
      rw [expSizeHOL.eq_def]
      dsimp only
      simp only [expOptionSizeHOL.eq_def, Flapjack.optionSizeHOL]
      omega
  | op actual args =>
    cases actual with
    | blockOp block =>
      cases block with
      | cons childTag =>
        simp only [extractOneSource] at run
        cases h : extractListSource n loc childTag args with
        | none => simp [h] at run
        | some result =>
          obtain ⟨bindings, kind⟩ := result
          cases kind with
          | inr cb =>
            simp only [h] at run
            have bsEq : bs = bindings := (Prod.mk.inj (Option.some.inj run.symm)).1
            rw [bsEq]
            have bound := extractList_size n loc childTag args bindings (.inr cb) h
            rw [expSizeHOL.eq_def]
            dsimp only
            omega
          | inl indices =>
            simp only [h] at run
            split at run
            · have bsEq : bs = [.op (.blockOp (.cons childTag)) args] :=
                (Prod.mk.inj (Option.some.inj run.symm)).1
              rw [bsEq, expListSizeHOL_cons, expListSizeHOL_nil]
              rw [expSizeHOL.eq_def]
              dsimp only
              omega
            · simp at run
      | _ =>
        simp only [extractOneSource] at run
        exact pureExp_size n _ bs sum run
    | _ =>
      simp only [extractOneSource] at run
      exact pureExp_size n _ bs sum run
  | _ =>
    simp only [extractOneSource] at run
    exact pureExp_size n _ bs sum run
termination_by expBudget e
decreasing_by
  all_goals simp_wf
  all_goals simp_all [expBudget]
  all_goals omega

/-- A successful list extraction yields bindings no larger than the input. -/
private theorem extractList_size (n loc tag : Nat) (args : List Exp) (bs : List Exp)
    (sum : Sum (List Nat) CallBlock)
    (run : extractListSource n loc tag args = some (bs, sum)) :
    expListSizeHOL bs ≤ expListSizeHOL args := by
  cases args with
  | nil =>
    simp only [extractListSource] at run
    have bsEq : bs = [] := (Prod.mk.inj (Option.some.inj run.symm)).1
    rw [bsEq, expListSizeHOL_nil]
    omega
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [extractListSource] at run
      rw [expListSizeHOL_cons, expListSizeHOL_nil]
      have bound := extractOne_size n loc tag x bs sum run
      omega
    | cons y ys =>
      simp only [extractListSource] at run
      cases tail : extractListSource n loc tag (y :: ys) with
      | none => simp [tail] at run
      | some result =>
        obtain ⟨bs2, kind2⟩ := result
        cases kind2 with
        | inr cb =>
          simp only [tail] at run
          cases shifted : shiftBlock 1 cb with
          | rCall ticks cargs => simp [shifted] at run
          | callBlock t left child right =>
            simp only [shifted] at run
            have bsEq : bs = x :: bs2 := (Prod.mk.inj (Option.some.inj run.symm)).1
            rw [bsEq]
            have bound := extractList_size n loc tag (y :: ys) bs2 (.inr cb) tail
            exact expListSizeHOL_cons_le x bs2 (y :: ys) bound
        | inl indices =>
          simp only [tail] at run
          cases first : extractOneSource n loc tag x with
          | none => simp [first] at run
          | some result1 =>
            obtain ⟨bs1, kind1⟩ := result1
            cases kind1 with
            | inr cb1 =>
              cases cb1 with
              | rCall ticks cargs => simp [first] at run
              | callBlock t left child right =>
                simp only [first] at run
                cases left with
                | nil =>
                  cases right with
                  | nil =>
                    dsimp only at run
                    have bsEq : bs = bs1 ++ bs2 := (Prod.mk.inj (Option.some.inj run.symm)).1
                    rw [bsEq]
                    have bound2 := extractList_size n loc tag (y :: ys) bs2 (.inl indices) tail
                    have bound1 : expListSizeHOL bs1 ≤ expSizeHOL x + 1 :=
                      extractOne_size n loc tag x bs1 (.inr (.callBlock t [] child [])) first
                    rw [expListSizeHOL_append]
                    rw [expListSizeHOL_cons]
                    omega
                  | cons r rs => simp at run
                | cons l ls => simp at run
            | inl vs1 =>
              simp only [first] at run
              split at run
              · have bsEq : bs = bs1 ++ bs2 := (Prod.mk.inj (Option.some.inj run.symm)).1
                rw [bsEq]
                have bound2 := extractList_size n loc tag (y :: ys) bs2 (.inl indices) tail
                have bound1 := extractOne_size n loc tag x bs1 (.inl vs1) first
                rw [expListSizeHOL_append]
                rw [expListSizeHOL_cons]
                omega
              · simp at run
termination_by listBudget args
decreasing_by
  all_goals simp_wf
  all_goals simp_all [listBudget]
  all_goals omega
end

/-- HOL `bvi_to_cb_aux_size_lemma`: extracted bindings are no larger than the
source expression (plus one for a single expression). HOL's `list_size exp_size`
is `expListSizeHOL`: it is generated in the same mutual block as `expSizeHOL`
in `Flapjack/Compiler/Backend/Bvi/GeneratedSize.lean`, and its clauses
(`expListSizeHOL.eq_def`: `[] ↦ 0`, `h :: t ↦ 1 + (expSizeHOL h +
 expListSizeHOL t)`) are exactly HOL's `list_size` clauses. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_aux_size_lemma"]
theorem extract_size_lemma :
    (∀ (n loc tag : Nat) (exp : Exp) (bs : List Exp) (sum : Sum (List Nat) CallBlock),
      extractOneSource n loc tag exp = some (bs, sum) →
        expListSizeHOL bs ≤ expSizeHOL exp + 1) ∧
    (∀ (n loc tag : Nat) (args : List Exp) (bs : List Exp) (sum : Sum (List Nat) CallBlock),
      extractListSource n loc tag args = some (bs, sum) →
        expListSizeHOL bs ≤ expListSizeHOL args) :=
  ⟨fun n loc tag exp bs sum run => extractOne_size n loc tag exp bs sum run,
    fun n loc tag args bs sum run => extractList_size n loc tag args bs sum run⟩

/-- HOL `bvi_to_cb_aux_size`: the list conjunct of the size lemma. HOL's
`list_size exp_size` is `expListSizeHOL`, whose clauses
(`expListSizeHOL.eq_def`) are exactly HOL's `list_size` clauses on the
`expSizeHOL` element measure. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_aux_size"]
theorem extractList_size_lemma (n loc tag : Nat) (args : List Exp) (bs : List Exp)
    (sum : Sum (List Nat) CallBlock)
    (run : extractListSource n loc tag args = some (bs, sum)) :
    expListSizeHOL bs ≤ expListSizeHOL args :=
  extractList_size n loc tag args bs sum run

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
                    change (if BackendCommon.smallEnoughInt
                        (Int.ofNat (vs1.length + vs2.length)) then
                      some (some (bs1 ++ bs2, Sum.inl (vs1 ++ vs2.map (· + bs1.length))))
                      else some none) = some result at run
                    split at run <;>
                      simp_all [shiftVars, BackendCommon.smallEnoughInt] <;>
                      omega
                  | inr cb =>
                    cases cb with
                    | rCall ticks args => simp_all
                    | callBlock t left child right =>
                      cases left <;> cases right <;> simp_all [shiftVars] <;> exact run.symm
termination_by fuel
end

/-- The executable retry always returns the source extraction result. -/
theorem extractListBounded_eq_source (fuel n loc tag : Nat) (xs : List Exp) :
    extractListBounded fuel n loc tag xs = some (extractListSource n loc tag xs) := by
  cases first : extractListFuel fuel n loc tag xs with
  | some value =>
    have equal := extractListFuel_success_eq fuel n loc tag xs value first
    simp [extractListBounded, first, equal]
  | none =>
    have enough : listBudget xs < max fuel (listBudget xs + 1) := by omega
    obtain ⟨result, retry⟩ := extractListFuel_succeeds (max fuel (listBudget xs + 1)) n loc tag xs enough
    have equal := extractListFuel_success_eq _ n loc tag xs result retry
    simp [extractListBounded, first, retry, equal]

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

/-- HOL `bvi_to_cb_size`: block extraction shrinks the expression size. HOL's
`list_size exp_size` is `expListSizeHOL` (same clauses as
`expListSizeHOL.eq_def`) and `exp_size` is `expSizeHOL`. -/
@[hol "cakeml/compiler/backend/bvi_tmcScript.sml" "bvi_to_cb_size"]
theorem toBlock_size (n loc : Nat) (x : Exp) (bs : List Exp) (cb : CallBlock)
    (run : toBlockSource n loc x = some (bs, cb)) : expListSizeHOL bs < expSizeHOL x := by
  cases x with
  | call ticks dest args handler =>
    simp only [toBlockSource] at run
    cases h : callToBlockSource loc ticks dest args handler with
    | none => simp [h] at run
    | some pair =>
      obtain ⟨bs', cb'⟩ := pair
      simp only [h] at run
      have bsEq : bs = args := by
        have pairEq := Option.some.inj run.symm
        exact (Prod.mk.inj pairEq).1.trans
          (callToBlockSource_bindings loc ticks dest args handler bs' cb' h)
      rw [bsEq]
      rw [expSizeHOL.eq_def]
      dsimp only
      simp only [expOptionSizeHOL.eq_def, Flapjack.optionSizeHOL]
      omega
  | op actual args =>
    cases actual with
    | blockOp block =>
      cases block with
      | cons childTag =>
        simp only [toBlockSource] at run
        cases h : extractListSource n loc childTag args with
        | none => simp [h] at run
        | some result =>
          obtain ⟨bindings, kind⟩ := result
          cases kind with
          | inr cb' =>
            simp only [h] at run
            have bsEq : bs = bindings := (Prod.mk.inj (Option.some.inj run.symm)).1
            rw [bsEq]
            have bound := extractList_size n loc childTag args bindings (.inr cb') h
            rw [expSizeHOL.eq_def]
            dsimp only
            omega
          | inl indices => simp [h] at run
      | _ => simp [toBlockSource] at run
    | _ => simp [toBlockSource] at run
  | _ => simp [toBlockSource] at run

end Flapjack.Compiler.Backend.BviTmc
