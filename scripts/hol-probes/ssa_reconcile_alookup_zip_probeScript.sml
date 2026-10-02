load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val alookup_zip_map_some = prove (``∀ls vs i f.
    ALL_DISTINCT (MAP f ls) ∧
    i < LENGTH ls ∧
    LENGTH vs = LENGTH ls ⇒
    ALOOKUP (ZIP (MAP f ls, vs)) (f (EL i ls)) = SOME (EL i vs)``,
rpt strip_tac >>
  irule ALOOKUP_ALL_DISTINCT_MEM >>
  conj_tac
  >- (`LENGTH (MAP f ls) = LENGTH vs` by simp[LENGTH_MAP] >>
      simp[MAP_ZIP]) >>
  `LENGTH (MAP f ls) = LENGTH ls` by simp[LENGTH_MAP] >>
  simp[MEM_ZIP] >>
  qexists_tac `i` >> simp[EL_MAP]);
val alookup_zip_map_option_lookup_none = prove (``∀ls vs n ns f.
    INJ f (domain ns) UNIV ∧
    n ∈ domain ns ∧
    ¬MEM n ls ∧
    (∀v. MEM v ls ⇒ v ∈ domain ns) ∧
    LENGTH vs = LENGTH ls ⇒
    ALOOKUP (ZIP (MAP f ls, vs)) (f n) = NONE``,
rpt strip_tac >>
  Cases_on `ALOOKUP (ZIP (MAP f ls, vs)) (f n)` >> simp[] >>
  imp_res_tac ALOOKUP_MEM >>
  `LENGTH (MAP f ls) = LENGTH vs` by simp[LENGTH_MAP] >>
  fs[MEM_ZIP] >>
  `f n = f (EL n' ls)` by
    (`EL n' (MAP f ls) = f (EL n' ls)` by (irule EL_MAP >> simp[]) >>
     fs[]) >>
  `MEM (EL n' ls) ls` by (simp[MEM_EL] >> qexists_tac `n'` >> simp[]) >>
  `EL n' ls ∈ domain ns` by (first_x_assum irule >> simp[]) >>
  `EL n' ls = n` by (
    qpat_x_assum `INJ f _ _` mp_tac >>
    simp[INJ_DEF] >> strip_tac >>
    first_x_assum irule >> simp[]) >>
  fs[]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "sz_some_full" alookup_zip_map_some;
val _ = out "sz_none_full" alookup_zip_map_option_lookup_none;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(fst(strip_forall(concl th)) @ free_vars(concl th))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "sz_alookup_zip_map_some_type_ls" "ls" alookup_zip_map_some;
val _ = ty "sz_alookup_zip_map_some_type_vs" "vs" alookup_zip_map_some;
val _ = ty "sz_alookup_zip_map_some_type_i" "i" alookup_zip_map_some;
val _ = ty "sz_alookup_zip_map_some_type_f" "f" alookup_zip_map_some;
val _ = ty "sz_alookup_zip_map_option_lookup_none_type_f" "f" alookup_zip_map_option_lookup_none;
val _ = ty "sz_alookup_zip_map_option_lookup_none_type_ns" "ns" alookup_zip_map_option_lookup_none;
val _ = ty "sz_alookup_zip_map_option_lookup_none_type_n" "n" alookup_zip_map_option_lookup_none;
val _ = ty "sz_alookup_zip_map_option_lookup_none_type_ls" "ls" alookup_zip_map_option_lookup_none;
val _ = ty "sz_alookup_zip_map_option_lookup_none_type_vs" "vs" alookup_zip_map_option_lookup_none;
