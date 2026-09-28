(* Direct HOL-EVAL fixture for crep_to_loopTheory.code_rel2_def. *)
load "bossLib";
load "preamble";
load "crep_to_loopProofTheory";
load "crep_arithTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopProofTheory;

(* `EVAL` does not reduce `FLOOKUP (FMAP_MAP2 f m) k` on its own, because
   `FMAP_MAP2` is `FUN_FMAP` underneath.  Rewriting with the library theorem
   `FLOOKUP_FMAP_MAP2` (`finite_mapScript.sml:2344`) exposes the callback
   semantics, and the residual `FLOOKUP` on the concrete finite map then
   reduces under `EVAL`. *)
fun print_map2 label q =
  let
    val th1 = REWRITE_CONV [FLOOKUP_FMAP_MAP2] q
    val th2 = EVAL (rhs (concl th1))
  in
    print (label ^ "=");
    print_term (rconc th2);
    print "\n"
  end;

(* Concrete instance of HOL `code_rel2_def`
   (cakeml/pancake/proofs/crep_to_loopProofScript.sml:3842-3844):

     code_rel2 ctxt s_code t_code <=>
       code_rel ctxt
         (FMAP_MAP2 (\(s,n,p). (n, crep_arith$simp_prog p)) s_code) t_code

   HOL `FMAP_MAP2` preserves the key and stores the callback result, so the
   lambda receives `(key, (n, p))`, discards the key as its first component, and
   returns `(n, simp_prog p)`.  The fixture uses

     s_code = FEMPTY |+ (5, ([1;2], Skip))           (* key 5 is the name slot *)
     s_code = FEMPTY |+ (5, ([1;2], Assign 1 (Crepop Mul [Var 2; Const 2w]))).

   The `Skip` body is fixed by `simp_prog`, while the `Assign`/`Mul` body is
   rewritten to a shift, so its `FMAP_MAP2` row is visibly different. *)

val sk = ``(crepLang$Skip : 8 word crepLang$prog)``;
val assignMul = ``crepLang$Assign (1:num)
  (crepLang$Crepop crepLang$Mul
    [crepLang$Var (2:num); crepLang$Const (2w : 8 word)])``;
val s_code_skip = ``FEMPTY |+ ((5:num), (([1;2] : num list), ^sk))``;
val s_code_mul = ``FEMPTY |+ ((5:num), (([1;2] : num list), ^assignMul))``;

(* `FMAP_MAP2` keeps key 5 and stores `(ns, simp_prog p)`: the key is preserved
   (same key 5), the body is simplified (`Skip` unchanged, `Mul` to a shift),
   and an absent key stays absent.  The distributing lambda is inlined so that
   its `simp_prog` body width is inferred from the source map's value type. *)
print_map2 "code_rel2_skip_map2"
  ``FLOOKUP (FMAP_MAP2 (\(s,n,p). (n, crep_arith$simp_prog p)) ^s_code_skip) 5``;
print_map2 "code_rel2_mul_map2"
  ``FLOOKUP (FMAP_MAP2 (\(s,n,p). (n, crep_arith$simp_prog p)) ^s_code_mul) 5``;
print_map2 "code_rel2_key_absent"
  ``FLOOKUP (FMAP_MAP2 (\(s,n,p). (n, crep_arith$simp_prog p)) ^s_code_skip) 6``;
