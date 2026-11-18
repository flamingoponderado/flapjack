(* Typed statements of the small word_to_stackProof helpers (task 231). *)
load "preamble";
load "word_to_stackProofTheory";
open HolKernel Parse boolLib bossLib preamble word_to_stackProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label q = (print (label ^ "="); print_term q; print "\n");

val _ = show "copy_ret_F_typed" ``copy_ret F is_handle (k,f,f') vs kont =
    let n = num_stack_ret k vs in
    if n = 0 then kont
    else Seq (copy_ret_aux k (if is_handle then f + 3 else f) n)
             (SeqStackFree n kont)``;
val _ = show "LASTN_HD_typed" ``∀ls x. x ≤ LENGTH ls ⇒
    HD (LASTN x ls) = EL (LENGTH ls - x) ls``;
val _ = show "list_rearrange_I_typed" ``list_rearrange I = I``;
val _ = show "EL_REVERSE_REWRITE_typed" ``∀l n k. n < LENGTH l ∧ k < n ⇒
    EL (LENGTH l - n + k) l = EL (n-k -1) (REVERSE l)``;
val _ = show "ALOOKUP_IFF_MEM_typed" ``ALL_DISTINCT (MAP FST l) ⇒
    (ALOOKUP l q = SOME r ⇔ MEM (q,r) l)``;
val _ = show "state_rel_set_var_prime_typed" ``state_rel ac k f f' s t lens extra ∧
    x < k ∧ y = x * 2 ⇒
    state_rel ac k f f' (set_var y v s) (set_var x v t) lens extra``;
val _ = show "with_same_locals_typed" ``s with locals := s.locals = (s:('a,'b,'c) wordSem$state)``;
val _ = show "LAST_add_ret_loc_typed" ``args' ≠ [] ⇒
    LAST (add_ret_loc ret args') = LAST args'``;
val _ = show "MAP_o_THE_FILTER_IS_SOME_typed" ``MAP (f o THE) (FILTER IS_SOME ls) =
    MAP (THE o OPTION_MAP f) (FILTER IS_SOME ls)``;
val _ = show "MAP_OPTION_MAP_FILTER_IS_SOME_typed" ``MAP (OPTION_MAP (f:α->α)) (FILTER IS_SOME ls) =
    FILTER IS_SOME (MAP (OPTION_MAP f) ls)``;
val _ = show "MAP_FILTER_IS_SOME_typed" ``MAP f (FILTER IS_SOME ls) =
    MAP (f o SOME o THE) (FILTER IS_SOME ls)``;
val _ = show "PAIR_MAP_SOME_SWAP_typed" ``(SOME ## SOME) o (f ## g) =
    (OPTION_MAP f ## OPTION_MAP g) o (SOME ## SOME)``;
val _ = show "IS_SOME_o_OPTION_MAP_typed" ``IS_SOME o OPTION_MAP f = IS_SOME``;
val _ = show "IS_SOME_OPTION_MAP2_EQ_typed" ``IS_SOME (OPTION_MAP2 f A B) ⇔
    (IS_SOME A ∧ IS_SOME B)``;
val _ = show "DROP_SUB_typed" ``a ≤ LENGTH ls ∧ b ≤ a ⇒
    DROP (a-b) ls = DROP (a-b) (TAKE a ls) ++ DROP a ls``;
val _ = show "DROP_SUB2_typed" ``∀a ls b. b ≤ a ∧ a = LENGTH ls ⇒
    ∃rest. DROP (a-b) ls = rest ∧ LENGTH rest = b``;
val _ = show "SUB_ADD_EQ_typed" ``a <= b ==> a + (b - a:num) = b``;
val _ = show "EXISTS_PULL_FORALL1_typed" ``((?x. !y. (Abbrev (y = P)) ==> Q x y) ⇔
    (!y. (Abbrev (y = P)) ==> ?x. Q x y))``;
val _ = show "EXISTS_PULL_FORALL2_typed" ``((?x. !y z. P = (y, z) ==> Q x y z) ⇔
    (!y z. P = (y, z) ==> ?x. Q x y z))``;
val _ = show "EXISTS_PULL_FORALL3_typed" ``((?x. !y z a. P = (y, z, a) ==> Q x y z a) ⇔
    (!y z a. P = (y, z, a) ==> ?x. Q x y z a))``;
val _ = show "SUB_SUB_SUB_MAX_typed" ``a - b - (c - b) = a - MAX b c``;
val _ = show "MAX_LE_typed" ``a <= b ==> MAX a b = b``;
val _ = show "EVEN_DIV_2_props_typed" ``a MOD 2 = 0 ∧ b MOD 2 = 0 ⇒
    (a ≠ b ⇒ a DIV 2 ≠ b DIV 2) ∧ (a ≠ 0 ⇒ a DIV 2 ≠ 0)``;
val _ = show "bits_to_word_bit_typed" ``∀bs i. i < dimindex (:'a) ∧ i < LENGTH bs ⇒
    ((bits_to_word bs:'a word) ' i = EL i bs)``;
val _ = show "stack_rel_aux_LENGTH_typed" ``∀k len xs ys. stack_rel_aux k len xs ys ⇒
    LENGTH xs = LENGTH ys``;
val _ = show "stack_rel_aux_LASTN_typed" ``∀k len xs ys n. stack_rel_aux k len xs ys ⇒
    stack_rel_aux k len (LASTN n xs) (LASTN n ys)``;
val _ = show "sub_union_lemma_typed" ``∀x y z. x SUBSET y ⇒ x SUBSET y UNION z``;
val _ = show "evaluate_copy_ret_Seq_prime_typed" ``∀F is_handle k f f' vs k0 t.
    evaluate (copy_ret F is_handle (k,f,f') vs k0,t) =
    let n = num_stack_ret k vs in
    evaluate (Seq (copy_ret_aux k (if is_handle then f + 3 else f) n)
      (SeqStackFree n k0),t)``;
val _ = show "wRegWrite1_thm1_weak_typed" ``∀ac k f f' s t lens m v kont.
    state_rel ac k f f' s t lens 0 ∧ m < f' + k ∧
    (∀n. n ≤ k ⇒ evaluate (kont n, t) = (NONE, set_var n v t)) ⇒
    ∃t'. evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
    state_rel ac k f f' (set_var (2 * m) v s) t' lens 0``;
val _ = show "wRegWrite1_thm2_typed" ``∀ac k f f' s t lens m v v' kont.
    state_rel ac k f f' s t lens 0 ∧ m < f' + k ∧
    (∀n. n ≤ k ⇒ evaluate (kont n, t) = (NONE, set_var 0 v' (set_var n v t))) ⇒
    ∃t'. evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
    state_rel ac k f f' (set_var 0 v' (set_var (2 * m) v s)) t' lens 0 ∧
    LENGTH t'.stack = LENGTH t.stack ∧ t'.stack_space = t.stack_space``;
val _ = show "wRegWrite2_thm1_typed" ``∀ac k f f' s t lens m v kont.
    state_rel ac k f f' s t lens 0 ∧ m < f' + k ∧
    (∀n. n ≤ k + 1 ⇒ evaluate (kont n, t) = (NONE, set_var n v t)) ⇒
    ∃t'. evaluate (wRegWrite2 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
    state_rel ac k f f' (set_var (2 * m) v s) t' lens 0``;
val _ = show "bits_to_word_bitstring_reverse_typed" ``∀xs.
    (bits_to_word xs:'a word) = bitstring$v2w (REVERSE xs)``;
val _ = show "evaluate_PopHandler_clock_typed" ``∀(t:('a,'c,'ffi) stackSem$state) F k f f' clk.
    let prog = PopHandler F (k,f,f') Skip in
    evaluate (prog,t with clock:=clk) =
    (FST (evaluate(prog,t)), SND (evaluate(prog,t)) with clock:=clk)``;
val _ = show "evaluate_PopHandler_seq_typed" ``∀prog (t:('a,'c,'ffi) stackSem$state) F k f f'.
    evaluate (PopHandler F (k,f,f') prog,t) =
    evaluate (Seq (PopHandler F (k,f,f') Skip) prog,t)``;
