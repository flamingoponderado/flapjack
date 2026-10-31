import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TmcNames

/-! Absence of TMC's mutable-block primitive before the TMC pass. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BviTmc (noMutcons noMutconsOp)

/-- Replacing a propagated variable by zero cannot introduce mutable-block
allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bvi_let_delete_var_no_mutcons"]
theorem deleteVar_noMutcons (expression : Bvi.Exp) (safe : noMutcons expression) :
    noMutcons (BviLet.deleteVar expression) := by
  cases expression <;> simp_all [BviLet.deleteVar, noMutcons, noMutconsOp, Subtype.forall]

/-- Integer literal lowering never emits mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_int_no_mutcons"]
theorem compileInt_noMutcons (value : Int) : noMutcons (compileInt value) := by
  simp [compileInt, noMutcons, noMutconsOp, Subtype.forall]
  split <;> simp

/-- Every accumulator operator used by tail-recursion rewriting is safe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "to_op_no_mutcons"]
theorem tailrec_toOp_noMutcons (op : BviTailrec.AssocOp) : noMutconsOp (BviTailrec.toOp op) := by
  cases op <;> simp [BviTailrec.toOp, noMutconsOp]

/-- Applying an accumulator operator introduces no mutable allocation of
its own, so safety is exactly safety of both operands. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "apply_op_no_mutcons"]
theorem tailrec_applyOp_noMutcons (op : BviTailrec.AssocOp) (first second : Bvi.Exp) :
    noMutcons (BviTailrec.applyOp op first second) ↔ noMutcons first ∧ noMutcons second := by
  simp [BviTailrec.applyOp, noMutcons, Subtype.forall, tailrec_toOp_noMutcons]

/-- Accumulator identities do not allocate mutable blocks. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "id_from_op_no_mutcons"]
theorem tailrec_identity_noMutcons (op : BviTailrec.AssocOp) : noMutcons (BviTailrec.identity op) := by
  cases op <;> simp [BviTailrec.identity, noMutcons, noMutconsOp, Subtype.forall]

/-- The tail-recursion wrapper adds only variable bindings. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "let_wrap_no_mutcons"]
theorem tailrec_letWrap_noMutcons (arity : Nat) (identity body : Bvi.Exp) :
    noMutcons (BviTailrec.letWrap arity identity body) ↔ noMutcons identity ∧ noMutcons body := by
  simp only [BviTailrec.letWrap, noMutcons, Subtype.forall, List.mem_append, List.mem_map,
    List.mem_singleton, List.mem_range]
  constructor
  · rintro ⟨bindings, bodySafe⟩
    exact ⟨bindings identity (Or.inr rfl), bodySafe⟩
  · rintro ⟨identitySafe, bodySafe⟩
    refine ⟨?_, bodySafe⟩
    intro expression member
    rcases member with ⟨index, _, rfl⟩ | rfl
    · simp [noMutcons]
    · exact identitySafe

/-- Extracting a binary operation preserves safety of both operands. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "get_bin_args_no_mutcons"]
theorem tailrec_getBinArgs_noMutcons (expression first second : Bvi.Exp)
    (found : BviTailrec.getBinArgs expression = some (first, second)) (safe : noMutcons expression) :
    noMutcons first ∧ noMutcons second := by
  cases expression with
  | op op args =>
    cases args with
    | nil => simp [BviTailrec.getBinArgs] at found
    | cons x xs =>
      cases xs with
      | nil => simp [BviTailrec.getBinArgs] at found
      | cons y rest =>
        cases rest with
        | nil =>
          simp [BviTailrec.getBinArgs] at found
          obtain ⟨rfl, rfl⟩ := found
          simp [noMutcons, Subtype.forall] at safe
          exact safe.2
        | cons z rest => simp [BviTailrec.getBinArgs] at found
  | _ => simp [BviTailrec.getBinArgs] at found

/-- An operator-checked binary extraction likewise preserves operand safety. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "opbinargs_no_mutcons"]
theorem tailrec_opBinArgs_noMutcons (op : BviTailrec.AssocOp) (expression first second : Bvi.Exp)
    (found : BviTailrec.opBinArgs op expression = some (first, second)) (safe : noMutcons expression) :
    noMutcons first ∧ noMutcons second := by
  unfold BviTailrec.opBinArgs at found
  split at found
  · exact tailrec_getBinArgs_noMutcons expression first second found safe
  · simp at found

/-- Swapping the operands of an accepted accumulator operation preserves
the absence of mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "try_swap_no_mutcons"]
theorem tailrec_trySwap_noMutcons (loc : Nat) (op : BviTailrec.AssocOp) (expression : Bvi.Exp)
    (safe : noMutcons expression) : noMutcons (BviTailrec.trySwap loc op expression) := by
  unfold BviTailrec.trySwap
  split
  · exact safe
  · cases found : BviTailrec.opBinArgs op expression with
    | none => simpa only [found] using safe
    | some pair =>
      obtain ⟨first, second⟩ := pair
      have operands := tailrec_opBinArgs_noMutcons op expression first second found safe
      dsimp only
      split
      · exact (tailrec_applyOp_noMutcons op second first).mpr ⟨operands.2, operands.1⟩
      · exact safe

/-- A successful tail-recursion candidate check does not introduce mutable
block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "check_op_no_mutcons"]
theorem tailrec_checkOp_noMutcons (ctx : List BviTailrec.ValueType) (op : BviTailrec.AssocOp)
    (loc : Nat) (expression checked : Bvi.Exp)
    (found : BviTailrec.checkOp ctx op loc expression = some checked) (safe : noMutcons expression) :
    noMutcons checked := by
  have swapped := tailrec_trySwap_noMutcons loc op expression safe
  unfold BviTailrec.checkOp at found
  cases operands : BviTailrec.opBinArgs op (BviTailrec.trySwap loc op expression) with
  | none => simp [operands] at found
  | some pair =>
    obtain ⟨first, second⟩ := pair
    have pairSafe := tailrec_opBinArgs_noMutcons op _ first second operands swapped
    rw [operands] at found
    dsimp only at found
    split at found
    · simp only [Option.some.injEq] at found
      subst checked
      exact (tailrec_applyOp_noMutcons op first second).mpr pairSafe
    · simp at found

/-- Extracted call arguments and handler inherit safety from the call. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "args_from_no_mutcons"]
theorem tailrec_argsFrom_noMutcons (expression : Bvi.Exp) (ticks loc : Nat)
    (args : List Bvi.Exp) (handler : Option Bvi.Exp)
    (found : BviTailrec.argsFrom expression = some (ticks, loc, args, handler))
    (safe : noMutcons expression) :
    (∀ e ∈ args, noMutcons e) ∧ (match handler with | none => True | some e => noMutcons e) := by
  cases expression with
  | call ticks' dest args' handler' =>
    cases dest with
    | none => simp [BviTailrec.argsFrom] at found
    | some loc' =>
      simp [BviTailrec.argsFrom] at found
      obtain ⟨rfl, rfl, rfl, rfl⟩ := found
      cases handler' <;> simpa [noMutcons, Subtype.forall] using safe
  | _ => simp [BviTailrec.argsFrom] at found

/-- Building an accumulator worker call preserves safety of its inputs. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "push_call_no_mutcons"]
theorem tailrec_pushCall_noMutcons (next : Nat) (op : BviTailrec.AssocOp) (acc : Nat)
    (value expression : Bvi.Exp) (valueSafe : noMutcons value) (safe : noMutcons expression) :
    noMutcons (BviTailrec.pushCall next op acc value (BviTailrec.argsFrom expression)) := by
  cases found : BviTailrec.argsFrom expression with
  | none => simp [BviTailrec.pushCall, noMutcons]
  | some data =>
    obtain ⟨ticks, loc, args, handler⟩ := data
    obtain ⟨argsSafe, handlerSafe⟩ := tailrec_argsFrom_noMutcons expression ticks loc args handler found safe
    cases handler <;> simp_all [BviTailrec.pushCall, noMutcons, Subtype.forall]
    all_goals
      intro e member
      rcases member with member | rfl
      · exact argsSafe e member
      · exact (tailrec_applyOp_noMutcons op _ _).mpr ⟨by simp [noMutcons], valueSafe⟩

private theorem noMutcons_binary (op : ClosLang.Op) (x y : Bvi.Exp)
    (safe : noMutconsOp op) (hx : noMutcons x) (hy : noMutcons y) :
    noMutcons (.op op [x, y]) := by
  simp [noMutcons, Subtype.forall, safe, hx, hy]

private theorem noMutcons_nullary (op : ClosLang.Op) (safe : noMutconsOp op) :
    noMutcons (.op op []) := by
  simp [noMutcons, Subtype.forall, safe]

/-- Every runtime stub is free of mutable-block allocation. This is the
initial-code portion of the source no-mutcons argument. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "stubs_no_mutcons"]
theorem stubs_noMutcons (start count : Nat) :
    ∀ entry ∈ stubs start count, noMutcons entry.2.2 := by
  intro entry member
  simp [stubs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [allocGlobalCode, copyGlobalsCode, initGlobalsCode, listLengthCode,
      fromListByteCode, toListByteCode, sumListLengthCode, concatByteCode,
      noMutcons, noMutconsOp, Subtype.forall]
  all_goals repeat' first
    | constructor
    | apply noMutcons_binary
    | apply noMutcons_nullary
    | simp [noMutcons, noMutconsOp, Subtype.forall]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
