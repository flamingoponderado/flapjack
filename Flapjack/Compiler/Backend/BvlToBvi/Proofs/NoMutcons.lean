import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TmcNames
import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteCorrespondence

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

/-- Lowering an operation cannot introduce mutable-block allocation when
its already lowered operands do not contain it. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_op_no_mutcons"]
theorem compileOp_noMutcons (op : ClosLang.Op) (args : List Bvi.Exp)
    (safe : ∀ e ∈ args, noMutcons e) : noMutcons (compileOp op args) := by
  have zeroSafe : noMutcons (.op (.intOp (.const 0)) []) := by simp [noMutcons, noMutconsOp, Subtype.forall]
  have lengthSafe (v : Nat) : noMutcons (.call 0 (some listLengthLocation)
      [.var v, .op (.intOp (.const 0)) []] none) := by simp [noMutcons, noMutconsOp, Subtype.forall]
  have argsSafe : ∀ e ∈ (if args.isEmpty then [.op (.intOp (.const 0)) []] else args), noMutcons e := by
    split <;> simp_all
  cases op <;> simp only [compileOp]
  all_goals repeat' first | split | simp [noMutcons, noMutconsOp, Subtype.forall, compileInt_noMutcons]
  all_goals repeat' first
    | exact safe
    | exact zeroSafe
    | exact lengthSafe _
    | exact argsSafe
    | constructor
    | simp_all
  intro e member
  rcases member with member | rfl
  · exact safe e member
  · exact zeroSafe

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

/-- The source rewrite's candidate-dispatch branch preserves the absence of
mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "rewrite_catchall_no_mutcons"]
theorem tailrec_dispatch_noMutcons (ctx : List BviTailrec.ValueType)
    (op : BviTailrec.AssocOp) (loc next acc : Nat) (expression : Bvi.Exp)
    (flag : Bool) (output : Bvi.Exp)
    (result : BviTailrec.sourceDispatch loc next op acc ctx expression = (flag, output))
    (safe : noMutcons expression) : noMutcons output := by
  unfold BviTailrec.sourceDispatch at result
  cases checked : BviTailrec.checkOp ctx op loc expression with
  | none =>
    simp [checked] at result
    obtain ⟨_, rfl⟩ := result
    exact (tailrec_applyOp_noMutcons op _ _).mpr ⟨by simp [noMutcons], safe⟩
  | some candidate =>
    have candidateSafe := tailrec_checkOp_noMutcons ctx op loc expression candidate checked safe
    cases operands : BviTailrec.opBinArgs op candidate with
    | none =>
      simp [checked, operands] at result
      obtain ⟨_, rfl⟩ := result
      exact (tailrec_applyOp_noMutcons op _ _).mpr ⟨by simp [noMutcons], candidateSafe⟩
    | some pair =>
      obtain ⟨value, call⟩ := pair
      have pairSafe := tailrec_opBinArgs_noMutcons op candidate value call operands candidateSafe
      simp [checked, operands] at result
      obtain ⟨_, rfl⟩ := result
      exact tailrec_pushCall_noMutcons next op acc value call pairSafe.1 pairSafe.2

/-- The source-shaped tail-recursion rewrite preserves absence of mutable
allocation. The executed bounded rewrite agrees with this definition. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "rewrite_no_mutcons"]
theorem tailrec_rewrite_noMutcons (loc next : Nat) (op : BviTailrec.AssocOp)
    (acc : Nat) (ctx : List BviTailrec.ValueType) (expression : Bvi.Exp)
    (flag : Bool) (output : Bvi.Exp)
    (result : BviTailrec.rewriteSource loc next op acc ctx expression = (flag, output))
    (safe : noMutcons expression) : noMutcons output := by
  cases expression with
  | var n =>
    simp [BviTailrec.rewriteSource.eq_def] at result
    obtain ⟨_, rfl⟩ := result
    simp [noMutcons]
  | force l n =>
    simp [BviTailrec.rewriteSource.eq_def] at result
    obtain ⟨_, rfl⟩ := result
    simp [noMutcons]
  | ifThenElse cond yes no =>
    have parts : noMutcons cond ∧ noMutcons yes ∧ noMutcons no := by simpa [noMutcons] using safe
    rw [BviTailrec.rewriteSource.eq_def] at result
    dsimp only at result
    generalize hy : BviTailrec.rewriteSource loc next op acc _ yes = y at result
    generalize hn : BviTailrec.rewriteSource loc next op acc _ no = n at result
    obtain ⟨yf, ye⟩ := y
    obtain ⟨nf, ne⟩ := n
    have ys := tailrec_rewrite_noMutcons loc next op acc _ yes yf ye hy parts.2.1
    have ns := tailrec_rewrite_noMutcons loc next op acc _ no nf ne hn parts.2.2
    simp only [Prod.mk.injEq] at result
    obtain ⟨_, rfl⟩ := result
    simp only [noMutcons]
    refine ⟨parts.1, ?_, ?_⟩
    · cases yf <;> simp_all [tailrec_applyOp_noMutcons, noMutcons]
    · cases nf <;> simp_all [tailrec_applyOp_noMutcons, noMutcons]
  | «let» xs body =>
    have parts : (∀ e ∈ xs, noMutcons e) ∧ noMutcons body := by
      simpa [noMutcons, Subtype.forall] using safe
    rw [BviTailrec.rewriteSource.eq_def] at result
    dsimp only at result
    generalize hr : BviTailrec.rewriteSource loc next op (acc + xs.length) _ body = r at result
    obtain ⟨rf, re⟩ := r
    have rs := tailrec_rewrite_noMutcons loc next op (acc + xs.length) _ body rf re hr parts.2
    simp only [Prod.mk.injEq] at result
    obtain ⟨_, rfl⟩ := result
    simpa [noMutcons, Subtype.forall] using And.intro parts.1 rs
  | tick body =>
    rw [BviTailrec.rewriteSource.eq_def] at result
    dsimp only at result
    generalize hr : BviTailrec.rewriteSource loc next op acc ctx body = r at result
    obtain ⟨rf, re⟩ := r
    have rs := tailrec_rewrite_noMutcons loc next op acc ctx body rf re hr (by simpa [noMutcons] using safe)
    simp only [Prod.mk.injEq] at result
    obtain ⟨_, rfl⟩ := result
    simpa [noMutcons] using rs
  | raise body => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
  | call ticks dest args handler => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
  | op actual args => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
  | letCall ticks dest arity args body => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
  | «return» args => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
termination_by sizeOf expression

/-- Both bodies generated by the source expression pass remain free of
mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "tailrec_compile_exp_no_mutcons"]
theorem tailrec_compileExp_noMutcons (loc next arity : Nat) (expression aux opt : Bvi.Exp)
    (result : BviTailrec.compileExpSource loc next arity expression = some (aux, opt))
    (safe : noMutcons expression) : noMutcons aux ∧ noMutcons opt := by
  unfold BviTailrec.compileExpSource at result
  cases checked : BviTailrec.checkExpOriginal loc arity expression with
  | none => simp [checked] at result
  | some op =>
    simp only [checked, Option.some.injEq, Prod.mk.injEq] at result
    obtain ⟨rfl, rfl⟩ := result
    let context : List BviTailrec.ValueType := List.replicate arity .any
    let rewritten := BviTailrec.rewriteSource loc next op arity context expression
    have workerSafe := tailrec_rewrite_noMutcons loc next op arity context expression
      rewritten.1 rewritten.2 (Prod.eta rewritten) safe
    exact ⟨(tailrec_letWrap_noMutcons arity _ _).mpr ⟨tailrec_identity_noMutcons op, workerSafe⟩,
      workerSafe⟩

/-- Tail-recursion compilation preserves the invariant over every function
body in the source-shaped function list. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bvi_tailrec_compile_each_no_mutcons"]
theorem tailrec_compileEach_noMutcons (next : Nat) (program : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (result : List (Nat × Nat × Bvi.Exp))
    (compiled : BviTailrec.compileEachSource next program = (next', result))
    (safe : ∀ entry ∈ program, noMutcons entry.2.2) :
    ∀ entry ∈ result, noMutcons entry.2.2 := by
  induction program generalizing next next' result with
  | nil =>
    simp [BviTailrec.compileEachSource] at compiled
    obtain ⟨_, rfl⟩ := compiled
    simp
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    have bodySafe : noMutcons body := safe (loc, arity, body) (by simp)
    have restSafe : ∀ entry ∈ rest, noMutcons entry.2.2 := by
      intro entry member
      exact safe entry (by simp [member])
    cases decision : BviTailrec.compileExpSource loc next arity body with
    | none =>
      cases comp : BviTailrec.compileEachSource next rest with
      | mk last output =>
        simp [BviTailrec.compileEachSource, decision, comp] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        simpa using And.intro bodySafe (ih next last output comp restSafe)
    | some pair =>
      obtain ⟨aux, opt⟩ := pair
      have generated := tailrec_compileExp_noMutcons loc next arity body aux opt decision bodySafe
      cases comp : BviTailrec.compileEachSource (next + Flapjack.bvlToBviNamespaces) rest with
      | mk last output =>
        simp [BviTailrec.compileEachSource, decision, comp] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        simpa using And.intro generated.1 (And.intro generated.2
          (ih _ last output comp restSafe))

/-- Enabling or disabling the source program pass preserves the invariant. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bvi_tailrec_compile_prog_no_mutcons"]
theorem tailrec_compileProg_noMutcons (enabled : Bool) (next next' : Nat)
    (program result : List (Nat × Nat × Bvi.Exp))
    (compiled : BviTailrec.compileProgSource enabled next program = (next', result))
    (safe : ∀ entry ∈ program, noMutcons entry.2.2) :
    ∀ entry ∈ result, noMutcons entry.2.2 := by
  cases enabled with
  | false =>
    simp [BviTailrec.compileProgSource] at compiled
    obtain ⟨_, rfl⟩ := compiled
    exact safe
  | true =>
    exact tailrec_compileEach_noMutcons next program next' result
      (by simpa [BviTailrec.compileProgSource] using compiled) safe

/-- The production bounded pass has the same preservation property. -/
theorem tailrec_compileProgFuel_noMutcons (fuel : Nat) (enabled : Bool) (next next' : Nat)
    (program result : List (Nat × Nat × Bvi.Exp))
    (compiled : BviTailrec.compileProgFuel fuel enabled next program = some (next', result))
    (safe : ∀ entry ∈ program, noMutcons entry.2.2) :
    ∀ entry ∈ result, noMutcons entry.2.2 := by
  rw [BviTailrec.compileProgFuel_eq_source] at compiled
  exact tailrec_compileProg_noMutcons enabled next next' program result (Option.some.inj compiled) safe

/-- The TMC precondition follows from safety of the tail-recursion input;
the pass itself preserves that safety. -/
theorem tailrec_output_tmc_inputCondition_of_input_noMutcons
    (fuel : Nat) (enabled : Bool) (next last tmcNext : Nat)
    (program output : List (Nat × Nat × Bvi.Exp)) (condition : BviTailrec.inputCondition next program)
    (outside : ∀ name ∈ program.map Prod.fst, bvlNumStubs ≤ name → ¬BviTmc.inWorkerNamespace name)
    (safe : ∀ entry ∈ program, noMutcons entry.2.2)
    (tmcBound : bvlNumStubs ≤ tmcNext) (tmcWorker : BviTmc.inWorkerNamespace tmcNext)
    (run : BviTailrec.compileProgFuel fuel enabled next program = some (last, output)) :
    BviTmc.inputCondition tmcNext output := by
  exact tailrec_output_tmc_inputCondition fuel enabled next last tmcNext program output condition outside
    (tailrec_compileProgFuel_noMutcons fuel enabled next last program output run safe) tmcBound tmcWorker run

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
