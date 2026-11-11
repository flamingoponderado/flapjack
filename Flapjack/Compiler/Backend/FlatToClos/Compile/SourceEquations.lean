module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelInduction

@[expose] public section

/-! Source equations for the executed list-valued flat-to-closure compiler. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.BackendCommon

/-- The executed compiler satisfies the source list equations. This is a
kernel-checked source-comparison witness, not a separate HOL theorem. -/
theorem compile_source_equations :
    (∀ names, compile names [] = []) ∧
    (∀ names x y xs, compile names (x :: y :: xs) = compile names [x] ++ compile names (y :: xs)) ∧
    (∀ names t e, compile names [.raise t e] =
      [.raise t (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile names [e]))]) ∧
    (∀ names t l, compile names [.lit t l] = [compileLit t l]) ∧
    (∀ names t v, compile names [.varLocal t v] = [.var t (Flapjack.holFindi (some v) names)]) ∧
    (∀ names t n es, compile names [.con t n es] =
      [smartCons t (match n with | some (tag, _) => tag | none => 0) (compile names es.reverse)]) ∧
    (∀ names t op es, compile names [.app t op es] =
      match destNop op es with
      | some e => compile names [e]
      | none => [compileOp t op (compile names es.reverse)]) ∧
    (∀ names t v e, compile names [.fn t v e] =
      [.fn t none none 1 (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile (some v :: names) [e]))]) ∧
    (∀ names t x y z, compile names [.if_ t x y z] =
      [.ifThenElse t (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile names [x]))
        (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile names [y]))
        (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile names [z]))]) ∧
    (∀ names t v e body, compile names [.let_ t v e body] =
      [.let t (compile names [e]) (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile (v :: names) [body]))]) ∧
    (∀ names t e rows, compile names [.mat t e rows] = [.op t (.intOp (.const 0)) []]) ∧
    (∀ names t e rows, compile names [.handle t e rows] =
      match destPat rows with
      | some (v, h) => [.handle t (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile names [e]))
          (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile (some v :: names) [h]))]
      | none => compile names [e]) ∧
    (∀ names t funs e, compile names [.letrec t funs e] =
      let newNames := funs.map (fun f => some f.1) ++ names
      [.letrec (funs.map (fun f => joinStrings t f.1)) none none
        (funs.map (fun (_, arg, body) =>
          (1, @Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile (some arg :: newNames) [body]))))
        (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (compile newNames [e]))]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro names; simp [compile, compileExps]
  · intro names x y xs; simp [compile, compileExps]
  · intro names t e; simp [compile, compileExps, compileExp, Flapjack.holHd]
  · intro names t l; simp [compile, compileExps, compileExp]
  · intro names t v; simp [compile, compileExps, compileExp, nameIndex_eq_holFindi]
  · intro names t n es
    simp only [compile, compileExps]
    rw [compileExp.eq_def]
    dsimp only
    simp [compileExps_eq_map]
    rfl
  · intro names t op es
    simp only [compile, compileExps]
    rw [compileExp.eq_def]
    dsimp only
    cases found : destNop op es <;> simp [compileExps_eq_map]
  · intro names t v e; simp [compile, compileExps, compileExp, Flapjack.holHd]
  · intro names t x y z; simp [compile, compileExps, compileExp, Flapjack.holHd]
  · intro names t v e body; simp [compile, compileExps, compileExp, Flapjack.holHd]
  · intro names t e rows; simp [compile, compileExps, compileExp]
  · intro names t e rows
    simp only [compile, compileExps]
    rw [compileExp.eq_def]
    dsimp only
    cases found : destPat rows with
    | none => rfl
    | some pair =>
      rcases pair with ⟨v, h⟩
      simp [Flapjack.holHd]
  · intro names t funs e
    simp [compile, compileExps, compileExp, Flapjack.holHd, compileFuns_eq_source]

/-- The executable top-level traversal satisfies the two source equations. -/
theorem compileDecs_source_equations :
    compileDecs [] = [] ∧
      ∀ expression rest, compileDecs (expression :: rest) =
        compile [] [expression] ++ compileDecs rest := by
  constructor
  · simp [compileDecs, compile, compileExps]
  · intro expression rest
    simp [compileDecs, compile, compileExps]

end Flapjack.Compiler.Backend.FlatToClos
