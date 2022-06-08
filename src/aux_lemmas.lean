/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom, Eric Rodriguez
-/

import for_mathlib.basic_estimates
import defs

/-!
# Title

This file contains a host of independent lemmas used in main_results.
-/

open_locale big_operators -- this lets me use ∑ and ∏ notation
open filter finset real
open nat (coprime)

open_locale arithmetic_function
open_locale classical
noncomputable theory


lemma tendsto_pow_rec_loglog_at_top {c : ℝ} (hc : 0 < c) :
  filter.tendsto (λ x : ℝ, x^(c/log(log x))) filter.at_top filter.at_top := sorry

lemma weird_floor_sq_tendsto_at_top :
  filter.tendsto (λ x : ℝ, ⌈real.logb 2 x⌉₊^2) filter.at_top filter.at_top := sorry

lemma tendsto_pow_rec_loglog_spec_at_top :
  filter.tendsto (λ x : ℝ, x^((1:ℝ)-8/log(log x))) filter.at_top filter.at_top := sorry

lemma prime_counting_lower_bound_explicit : ∀ᶠ (N : ℕ) in at_top,
   ⌊sqrt N⌋₊ ≤ (filter nat.prime (Icc 1 N)).card :=
begin
  have haux: asymptotics.is_O_with ((1 : ℝ) / 4) log id at_top,
  { refine is_o_log_id_at_top.def' _,  rw one_div_pos, norm_num1, },
  rcases chebyshev_first_all with ⟨c,h0c,hcheb⟩,
  filter_upwards [
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually haux.bound,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually (eventually_gt_at_top ((0:ℝ))),
    tendsto_coe_nat_at_top_at_top.eventually (eventually_ge_at_top ((2:ℝ))),
    tendsto_coe_nat_at_top_at_top.eventually (eventually_ge_at_top ((1/c)^(4:ℝ))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ))]
  with N hlarge hlogN h2N hcN hloglogN,
  have h0N : (0:ℝ) < N := lt_of_lt_of_le zero_lt_two h2N,
  specialize hcheb (N:ℝ) h2N,
  rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg, abs_of_nonneg] at hcheb,
  rw [← prime_counting_eq_card_primes], nth_rewrite 1 ← nat.floor_coe N,
  rw [← @nat.cast_le ℝ _ _ _ _, ← mul_le_mul_right hlogN],
  refine le_trans (le_trans _ hcheb) (chebyshev_first_trivial_bound _),
  rw [← le_div_iff hlogN], refine le_trans (nat.floor_le _) _, refine sqrt_nonneg _,
  rw [le_div_iff hlogN, ← log_le_log, log_mul, sqrt_eq_rpow, log_rpow],
  calc _ ≤ (1/2)*(log N) + (1/4)*(log N) :_
     ... ≤ _ :_,
  rw add_le_add_iff_left, rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hlarge,
  exact hlarge, exact hlogN, exact hloglogN,
  rw [← add_mul, ← log_rpow, log_le_log, ← one_le_div, div_eq_mul_inv, ← rpow_neg, mul_assoc,
     mul_comm (N:ℝ), ← rpow_add_one, ← div_le_iff'], norm_num1,
  rw [← rpow_le_rpow_iff _ _ (zero_lt_four), ← rpow_mul], norm_num1, rw rpow_one, exact hcN,
  exact nat.cast_nonneg N, rw one_div_nonneg, exact le_of_lt h0c,
  refine rpow_nonneg_of_nonneg (nat.cast_nonneg N) _, exact h0c,
  exact ne_of_gt h0N,  exact nat.cast_nonneg N, refine rpow_pos_of_pos h0N _,
  refine rpow_pos_of_pos h0N _, exact mul_pos h0c h0N, exact h0N, exact h0N,
  refine ne_of_gt _, rw sqrt_pos, exact h0N, exact ne_of_gt hlogN, refine mul_pos _ hlogN,
  rw sqrt_pos, exact h0N, exact mul_pos h0c h0N,
  exact le_of_lt (chebyshev_first_pos (N:ℝ) h2N),
  exact nat.cast_nonneg N,
end

theorem sum_bUnion_le_sum_of_nonneg {N : Type*} [ordered_add_comm_monoid N] {f : ℕ → N}
 {s : finset ℕ} {t : ℕ → finset ℕ}
 (hf : ∀ x ∈ s.bUnion t, 0 ≤ f x) :
(s.bUnion t).sum (λ (x : ℕ), f x) ≤ s.sum (λ (x : ℕ), (t x).sum (λ (i : ℕ), f i)) :=
begin
  induction s using finset.induction_on with n s hns hs,
  simp only [le_refl, finset.bUnion_empty, finset.sum_empty, finset.sum_congr],
  have hins : (insert n s).bUnion t = (s.bUnion t) ∪ ((t n)\(s.bUnion t)), {
    ext, split, intro ha, rw mem_bUnion at ha, rcases ha with ⟨m,hm1,hm2⟩,
    rw mem_insert at hm1, rw mem_union, cases hm1 with hm3 hm4,
    rw or_iff_not_imp_left, intro ha2, rw mem_sdiff, rw hm3 at hm2,
    refine ⟨hm2,ha2⟩, left, rw mem_bUnion, use m, refine ⟨hm4,hm2⟩,
    intro ha, rw mem_union at ha, rw mem_bUnion,
    cases ha with ha2 ha3, rw mem_bUnion at ha2, rcases ha2 with ⟨m,hm1,hm2⟩,
    use m, refine ⟨mem_insert_of_mem hm1,hm2⟩, use n, rw mem_sdiff at ha3,
    refine ⟨mem_insert_self _ _,ha3.1⟩,
   },
  have hf' : (∀ x ∈ s.bUnion t, 0 ≤ f x), {
    intros x hx, refine hf x _, rw mem_bUnion at hx, rcases hx with ⟨m,hm1,hm2⟩,
    rw mem_bUnion, use m, refine ⟨mem_insert_of_mem hm1,hm2⟩,
   },
  rw [hins, sum_union, sum_insert hns], rw add_comm (∑ i in t n, f i),
  refine add_le_add (hs hf') _, refine sum_le_sum_of_subset_of_nonneg _ _,
  refine sdiff_subset _ _, intros m hm1 hm2, refine hf m _,
  rw mem_bUnion, use n, refine ⟨mem_insert_self _ _,hm1⟩,
  refine disjoint_sdiff,
end

lemma sum_pow {ι α : Type*} [decidable_eq ι] [decidable_eq α]
  (f : ι → ℝ) {s : finset ι} {B : finset α} :
  (∑ i in s, f i) ^ B.card =
    ∑ g in B.pi (λ _, s), ∏ j in B.attach, f (g _ j.prop) :=
by { rw [←prod_const, prod_sum], refl }

lemma sum_pow' {ι α : Type*} [decidable_eq ι] [decidable_eq α]
  (f : ι → ℝ) {s : finset ι} {B : finset α} :
  (∑ i in s, f i) ^ B.card = ∑ (g : B → s), ∏ (j : B), f (g j) :=
begin
  rw sum_pow,
  simp_rw finset.prod_coe_sort_eq_attach,
  rw eq_comm,
  refine sum_bij (λ f _ i hi, f ⟨_, hi⟩) _ _ _ _,
  { intros f hf,
    rw [finset.mem_pi],
    intros a ha,
    exact (f ⟨a, ha⟩).prop },
  { intros f hf,
    refine prod_congr rfl _,
    rintro ⟨x, hx⟩ _,
    simp },
  { simp only [function.funext_iff, mem_univ, forall_true_left],
    rintro f₁ f₂ h ⟨i, hi⟩,
    ext1,
    exact h _ _  },
  intros f hf,
  refine ⟨λ i, ⟨f _ i.prop, _⟩, mem_univ _, _⟩,
  { rw [finset.mem_pi] at hf,
    apply hf _ i.prop },
  ext i hi,
  refl,
end

lemma something_like_this {ι : Type*} [decidable_eq ι] (f : ι → ℝ) (A B : finset ι)
  (hA : A.card = B.card) :
  ∑ (g : B ≃ A), ∏ (j : B), f (g j) = B.card.factorial * ∏ n in A, f n :=
begin
  rw [sum_congr rfl, sum_const (∏ n in A, f n)],
  { rw [nsmul_eq_mul],
    congr' 2,
    rw [card_univ, fintype.card_equiv],
    { simp [hA] },
    apply fintype.equiv_of_card_eq,
    simp [hA] },
  intros g hg,
  simp only [univ_eq_attach, mem_filter, mem_univ, true_and] at hg,
  rw ←@prod_coe_sort _ _ A,
  refine fintype.prod_equiv g _ _ (λ x, rfl),
end



--  ∑ (g : B → s), ∏ (j : B), f (g j) ≥  ∑ (g : B → s).filter( g injection ), ∏ (j : B), f (g j)
-- (g : B → s).filter( g injection ) = ((A ⊆ s).filter(λ A, A.card = t)).bUnion(λ g, g ≃ A)
--  ∑ (g : B → s).filter( g injection ), ∏ (j : B), f (g j) = ∑ (A ⊆ s).filter(λ A, A.card = t), ∑ (g : B ≃ A), ∏ (j : B), f (g j)
--  ∑ (A ⊆ s).filter(λ A, A.card = t), A.card.factorial * ∏ n in A, f n

lemma my_function_aux {n : ℕ} : ((nat.factorization n).sum (λ p k, {p ^ k}) : multiset ℕ).nodup :=
begin
  rw multiset.nodup_iff_count_le_one,
  intro x,
  rw [finsupp.sum, ←multiset.coe_count_add_monoid_hom, add_monoid_hom.map_sum],
  simp only [nat.support_factorization, multiset.coe_count_add_monoid_hom,
    multiset.count_singleton, sum_boole, nat.cast_id],
  rw finset.card_le_one_iff,
  simp only [mem_filter, list.mem_to_finset, and_imp],
  rintro a b ha rfl hb h,
  apply eq_of_prime_pow_eq _ _ _ h,
  { rw ←nat.prime_iff,
    exact nat.prime_of_mem_factors ha },
  { rw ←nat.prime_iff,
    exact nat.prime_of_mem_factors hb },
  rwa [pos_iff_ne_zero, ←finsupp.mem_support_iff, nat.support_factorization, list.mem_to_finset],
end

def my_function (n : ℕ) : finset ℕ :=
((nat.factorization n).sum (λ p k, {p ^ k}) : multiset ℕ).to_finset

lemma card_my_function {n : ℕ} : (my_function n).card = ω n :=
begin
  rw [my_function, nat.arithmetic_function.card_distinct_factors_apply, multiset.card_to_finset,
    multiset.nodup.dedup, finsupp.sum, add_monoid_hom.map_sum],
  { simpa only [multiset.card_singleton, ←card_eq_sum_ones, nat.support_factorization] },
  apply my_function_aux
end

lemma prod_my_function {n : ℕ} (hn : n ≠ 0) :
  ∏ i in my_function n, i = n :=
begin
  rw [my_function, finset.prod, multiset.map_id', multiset.to_finset_val,
    multiset.nodup.dedup my_function_aux, finsupp.sum, multiset.prod_sum],
  simp only [multiset.prod_singleton],
  exact nat.factorization_prod_pow_eq_self hn,
end

lemma my_function_injective {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
  my_function n = my_function m → n = m :=
λ h, by rw [←prod_my_function hn, h, prod_my_function hm]

lemma rec_sum_le_prod_sum_aux {A : finset ℕ} (t : ℕ) (hA : 0 ∉ A) :
  ∑ i in filter (λ (n : ℕ), ω n = t) A, (1 : ℝ) / i ≤
    ∑ x in powerset_len t (ppowers_in_set A), ∏ (n : ℕ) in x, 1 / n :=
begin
  have : (filter (λ n : ℕ, ω n = t) A).image my_function ⊆ powerset_len t (ppowers_in_set A),
  { intros B,
    simp only [mem_image, mem_filter, exists_prop, forall_exists_index, and_imp, mem_powerset_len],
    rintro n hn rfl rfl,
    rw [card_my_function, eq_self_iff_true, and_true],
    intros m hm,
    simp only [my_function, multiset.mem_to_finset, finsupp.sum, mem_sum,
      multiset.mem_singleton] at hm,
    obtain ⟨a, ha, rfl⟩ := hm,
    rw mem_ppowers_in_set',
    { exact ⟨_, hn, rfl⟩ },
    { exact nat.prime_of_mem_factorization ha },
    rwa finsupp.mem_support_iff at ha },
  simp only [one_div],
  apply (sum_le_sum_of_subset_of_nonneg this _).trans_eq' _,
  { intros i _ _,
    refine prod_nonneg (λ _ _, _),
    simp only [inv_nonneg, nat.cast_nonneg] },
  rw [sum_image, sum_congr rfl],
  { intros x hx,
    simp only [mem_filter] at hx,
    rw [prod_inv_distrib, ←nat.cast_prod, prod_my_function],
    exact ne_of_mem_of_not_mem hx.1 hA },
  simp only [mem_filter, and_imp],
  intros x hx _ y hy _ h,
  exact my_function_injective (ne_of_mem_of_not_mem hx hA) (ne_of_mem_of_not_mem hy hA) h,
end

lemma rec_sum_le_prod_sum {A : finset ℕ} (hA₀ : 0 ∉ A) {I: finset ℕ} (hI : ∀ n ∈ A, ω n ∈ I) :
  (rec_sum A : ℝ) ≤ ∑ t in I, (∑ q in ppowers_in_set A, (1/q : ℝ))^t/(nat.factorial t) :=
begin
  rw rec_sum, push_cast,
  have hA : I.bUnion(λ t, A.filter(λ n : ℕ, ω n = t)) = A, { refine finset.bUnion_filter_eq_of_maps_to hI, },
  nth_rewrite 0 ← hA, refine le_trans (sum_bUnion_le_sum_of_nonneg _) _, intros n hn,
  rw one_div_nonneg, exact nat.cast_nonneg n, refine sum_le_sum _,
  intros t ht, rw [le_div_iff],
  { rw [←card_range t, sum_pow', card_range t, mul_comm],
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset function.injective _) _).trans' _,
    { intros f _ _,
      refine prod_nonneg _,
      intros i hi,
      rw one_div_nonneg,
      exact nat.cast_nonneg _ },
    have : filter function.injective (univ : finset (↥(range t) → ↥(ppowers_in_set A))) =
      (((ppowers_in_set A).powerset).filter(λ (B : finset _), B.card = t)).bUnion (λ B,
         (finset.filter function.injective
          (univ : finset (↥(range t) → ↥(ppowers_in_set A)))).filter
            (λ g, univ.image (λ i, (g i : ℕ)) = B)),
    { rw finset.bUnion_filter_eq_of_maps_to,
      simp only [mem_filter, mem_univ, true_and, univ_eq_attach, mem_powerset],
      intros f hf,
      refine ⟨λ i, _, _⟩,
      { simp only [mem_image, mem_attach, exists_true_left, forall_exists_index],
        rintro y rfl,
        exact (f y).2 },
      rw [card_image_of_inj_on, card_attach, card_range],
      simp only [set.inj_on, mem_coe, mem_attach, forall_true_left],
      intros x₁ x₂ h,
      exact hf (subtype.ext h) },
    rw [this, sum_bUnion],
    swap,
    { rintro B₁ hB₁ B₂ hB₂ h,
      simp only [coe_filter, set.mem_sep_eq, mem_coe, mem_powerset] at hB₁ hB₂,
      change disjoint _ _,
      rw disjoint_left,
      simp only [univ_eq_attach, mem_filter, mem_univ, true_and, not_and, and_imp],
      rintro g hg rfl - rfl,
      apply h rfl },
    have : ∀ x ∈ (ppowers_in_set A).powerset.filter (λ B : finset ℕ, B.card = t),
      ∑ (i : range t → ppowers_in_set A) in
        filter (λ (g : range t → ppowers_in_set A), image (λ i, (g i : ℕ)) univ = x)
          (filter function.injective univ),
            ∏ (j : range t), (1 : ℝ) / ((i j : ℕ) : ℝ) =
      ∑ (i : range t ≃ x), ∏ (j : range t), (1 : ℝ) / (i j : ℕ),
    { intros x hx,
      rw [mem_filter, mem_powerset] at hx,
      refine (sum_bij _ _ _ _ _).symm,
      { intros i _ j,
        exact ⟨i j, hx.1 (i j).prop⟩ },
      { intros i _,
        simp only [mem_filter, univ_eq_attach, mem_univ, true_and, subtype.coe_mk],
        refine ⟨λ j₁ j₂ h, i.injective _, _⟩,
        { simp only [subtype.mk_eq_mk] at h,
          apply subtype.ext h },
        ext j,
        split,
        { simp only [mem_image, mem_attach, exists_true_left, forall_exists_index],
          rintro k rfl,
          exact (i k).prop },
        simp only [mem_image, mem_attach, exists_true_left],
        exact λ hj, ⟨i.symm ⟨_, hj⟩, by simp⟩ },
      { intros i hi,
        refl },
      { intros g₁ g₂ _ _,
        simp only [function.funext_iff, equiv.ext_iff, subtype.ext_iff, imp_self] },
      { intros g hg,
        simp only [mem_filter, mem_univ, true_and, finset.ext_iff, mem_image,
          iff_def, mem_attach, exists_true_left, forall_exists_index, forall_and_distrib,
          forall_apply_eq_imp_iff'] at hg,
        choose f' hf' using hg.2.2,
        refine ⟨⟨λ j, ⟨g j, hg.2.1 _⟩, λ j, f' _ j.prop, _, _⟩, mem_univ _, _⟩,
        { rintro ⟨j, hj⟩,
          apply hg.1,
          ext1,
          dsimp,
          rw hf' },
        { rintro ⟨j, hj⟩,
          ext1,
          dsimp,
          apply hf' },
        ext ⟨j, hj⟩,
        refl } },
    rw sum_congr rfl this,
    have : ∀ x ∈ (ppowers_in_set A).powerset.filter (λ B : finset ℕ, B.card = t),
      ∑ (i : range t ≃ x), ∏ (j : range t), (1 : ℝ) / ((i j : ℕ) : ℝ) =
        t.factorial * ∏ n in x, (1 : ℝ) / n,
    { intros x hx,
      rw [mem_filter] at hx,
      rw [something_like_this (λ (q : ℕ), (1 : ℝ) / q), card_range],
      rw [card_range, hx.2] },
    rw [sum_congr rfl this, ←mul_sum, ←powerset_len_eq_filter],
    apply mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
    exact rec_sum_le_prod_sum_aux _ hA₀ },
  exact_mod_cast nat.factorial_pos t,
end

lemma such_large_N_wow : ∀ᶠ (N : ℕ) in at_top,
  2 * log (log (⌈real.logb 2 N⌉₊ ^ 2)) < 1 / 500 * log (log N) :=
begin
  have haux: asymptotics.is_O_with ((1 : ℝ) / 8000) log id at_top,
  { refine is_o_log_id_at_top.def' _,  rw one_div_pos, norm_num1, },
  filter_upwards [tendsto_coe_nat_at_top_at_top.eventually
    (eventually_ge_at_top ((1:ℝ))),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_gt_at_top ((1:ℝ))),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_ge_at_top (2/log 2)),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_gt_at_top (log 2)),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_gt_at_top (exp (exp (2 * log ((2:ℕ):ℝ)))*log 2)),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_ge_at_top (sqrt 2)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (1500 * log 2 * 2)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually haux.bound] with N h1N h1logN hlogN' hlog2logN hcomplogN
       hsqrtlogN hloglogN hlarge1,
  have h0logN : 0 < log N, { exact lt_trans zero_lt_one h1logN, },
  have h0loglogN : 0 < log(log N), { refine lt_trans _ hloglogN, refine mul_pos _ zero_lt_two,
    refine mul_pos _ (log_pos one_lt_two),  norm_num1, },
  have h2000 : (0:ℝ) < 1500 := by norm_num1,
  have hhelper : (⌈real.logb 2 N⌉₊:ℝ) ≤ (log N)^2, {
     refine le_trans (le_of_lt (nat.ceil_lt_add_one _)) _, refine logb_nonneg one_lt_two h1N,
     rw ← add_halves ((log N)^2), refine add_le_add _ _,
     rw [← log_div_log, div_le_div_iff, sq, mul_assoc, mul_le_mul_left, ← div_le_iff],
     exact hlogN', exact log_pos one_lt_two, exact h0logN, exact log_pos one_lt_two, exact zero_lt_two,
     rw [le_div_iff, one_mul, ← real.sqrt_le_left], exact hsqrtlogN, exact le_of_lt h0logN,
     exact zero_lt_two,
   },
  have hhelper2 : (1:ℝ) < ⌈real.logb 2 N⌉₊, {
    refine lt_of_lt_of_le _ (nat.le_ceil _), rw [← log_div_log, one_lt_div], exact hlog2logN,
    exact log_pos one_lt_two,
  },
  have hhelper3 : exp (exp (2 * log ↑2)) < ⌈real.logb 2 N⌉₊, {
    refine lt_of_lt_of_le _ (nat.le_ceil _), rw [← log_div_log, lt_div_iff (log_pos one_lt_two)],
    exact hcomplogN,
  },
  rw [← rpow_nat_cast, log_rpow, log_mul, mul_add],
  transitivity ((2+1)*log (log (⌈real.logb 2 N⌉₊))), rw [add_mul, one_mul, add_comm, real.add_lt_add_iff_left],
  rw [lt_log_iff_exp_lt, lt_log_iff_exp_lt], exact hhelper3, exact lt_trans zero_lt_one hhelper2,
  exact log_pos hhelper2, rw [mul_comm ((1:ℝ)/500), ← div_eq_mul_one_div, lt_div_iff', ← mul_assoc],
  calc _ ≤ (1500:ℝ)*log(log ((log N)^(2:ℝ))) :_
     ... < _ :_,
  norm_num1,
  rw [mul_le_mul_left, log_le_log, log_le_log], rw ← real.rpow_two at hhelper,
  exact hhelper, exact lt_trans zero_lt_one hhelper2,
  refine rpow_pos_of_pos h0logN _, exact log_pos hhelper2, refine log_pos _,
  refine real.one_lt_rpow h1logN zero_lt_two, norm_num1,
  rw [log_rpow, log_mul, mul_add], nth_rewrite 1 ← add_halves (log(log N)), refine add_lt_add _ _,
  rw lt_div_iff, exact hloglogN, exact zero_lt_two, rw [← lt_div_iff', div_div, div_eq_mul_one_div,
     mul_comm],
  calc _ ≤ ((1:ℝ)/8000)*log(log N) :_
     ... < _ :_,
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hlarge1, exact hlarge1, exact h0loglogN,
  refine log_pos _, refine lt_trans _ hloglogN, refine one_lt_mul _ one_lt_two,
  rw ← div_le_iff', refine le_trans _ (le_of_lt real.log_two_gt_d9), norm_num1, exact h2000,
  rw mul_lt_mul_right, rw one_div_lt_one_div, norm_num1, norm_num1,
  exact mul_pos zero_lt_two h2000, exact h0loglogN, exact h2000, exact two_ne_zero,
  exact ne_of_gt h0loglogN, exact h0logN, norm_num1, norm_cast, exact two_ne_zero,
  exact (ne_of_gt (log_pos hhelper2)), exact lt_trans zero_lt_one hhelper2,
end

lemma explicit_mertens :
  ∀ᶠ N : ℕ in at_top,
    ((∑ q in (finset.range (N + 1)).filter is_prime_pow, 1 / q) : ℝ) ≤ 2 * log (log N) :=
begin
  obtain ⟨b, hb⟩ := prime_power_reciprocal,
  obtain ⟨c, hc₀, hc⟩ := hb.exists_pos,
  filter_upwards [(tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_ge_at_top (c : ℝ)), (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top (b + 1)),
    tendsto_coe_nat_at_top_at_top.eventually hc.bound]
    with N hN₁ hN₂ hN₃,
  dsimp at hN₁ hN₂,
  have hN₄ : 0 < log N := hc₀.trans_le hN₁,
  simp_rw [norm_inv, ←div_eq_mul_inv, ←one_div, norm_eq_abs, abs_of_nonneg hN₄.le,
    nat.floor_coe] at hN₃,
  have : c / log N ≤ 1 := div_le_one_of_le hN₁ hN₄.le,
  have := sub_le_iff_le_add.1 (sub_le_of_abs_sub_le_right (hN₃.trans this)),
  convert this.trans (show log (log N) + b + 1 ≤ 2 * log (log N), by linarith) using 2,
  rw [range_eq_Ico, nat.Ico_succ_right],
  ext n,
  simpa only [mem_filter, and.congr_left_iff, mem_Icc, zero_le', iff_and_self, true_and] using
    λ h _, (is_prime_pow.one_lt h).le,
end

lemma card_factors_le_log {n : ℕ} : Ω n ≤ ⌊real.logb 2 n⌋₊ :=
begin
  by_cases hn : n = 0,
  rw hn, rw nat.arithmetic_function.map_zero, refine nat.zero_le _,
  by_cases hΩ : Ω n = 0,
  rw hΩ, refine nat.zero_le _,  rw nat.le_floor_iff', rw nat.arithmetic_function.card_factors_apply,
  rw ← real.rpow_le_rpow_left_iff one_lt_two,
  calc _ ≤ (n.factors.prod:ℝ) :_
     ... ≤ _ :_,
  norm_cast, refine list.pow_card_le_prod _ _ _, intros p hp,
  rw [nat.mem_factors, nat.prime_def_min_fac] at hp, exact hp.1.1, exact hn,
  rw nat.prod_factors hn, rw real.rpow_logb, exact zero_lt_two, exact ne_of_gt one_lt_two,
  norm_cast, rw pos_iff_ne_zero, exact hn, exact hΩ,
end

lemma nat_cast_diff_issue {x y : ℤ} : (|x-y|:ℝ) = int.nat_abs (x-y) :=
begin
  have h1 := int.nat_abs_eq (x-y),
  calc _ = ((int.nat_abs (x-y):ℤ):ℝ) :_
     ... = _ :_,
  cases h1 with h1p h1n,
  rw ← h1p, rw abs_of_nonneg, push_cast, norm_cast, rw h1p, norm_cast, refine nat.zero_le _,
  rw eq_neg_iff_eq_neg at h1n, rw h1n, rw abs_of_nonpos, push_cast, norm_cast,
  rw eq_neg_iff_eq_neg at h1n, rw h1n, rw [neg_le, neg_zero], norm_cast, refine nat.zero_le _,
  push_cast,
end

lemma this_condition_here {p : ℕ → Prop} [decidable_pred p] {A : finset ℕ} (hA : ∀ a ∈ A, p a)
  {N : ℕ} (hN : A.card ≤ ((range N).filter p).card) (h : ¬(range N).filter p ⊆ A):
  (∃ r < N, r ∉ A ∧ p r ∧ ∃ a ∈ A, r < a) ∨ A ⊂ (range N).filter p :=
begin
  have h₁ : ((range N).filter p \ A).nonempty,
  { rwa sdiff_nonempty },
  rw or_iff_not_imp_right,
  intro h₂,
  have h₂ : (A \ (range N).filter p).nonempty,
  { rw sdiff_nonempty,
    intro h',
    exact h₂ ⟨h', h⟩ },
  obtain ⟨r, hr⟩ := h₁,
  obtain ⟨a, ha⟩ := h₂,
  simp only [mem_sdiff, mem_filter, mem_range] at hr,
  simp only [mem_sdiff, mem_filter, mem_range, not_and', not_lt] at ha,
  exact ⟨r, hr.1.1, hr.2, hr.1.2, a, ha.1, hr.1.1.trans_le (ha.2 (hA _ ha.1))⟩
end

lemma prime_power_recip_downward_bound (A : finset ℕ) (ha : ∀ q ∈ A, is_prime_pow q)
  (N : ℕ) (hN : A.card ≤ ((range N).filter is_prime_pow).card) :
  ∑ q in A, (1 : ℝ) / q ≤ ∑ q in (range N).filter is_prime_pow, 1 / q :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { rw [sum_empty],
    apply sum_nonneg,
    simp },
  let a := A.max' hA,
  let choices : finset (finset ℕ) :=
    ((range (a + 1)).filter is_prime_pow).powerset.filter
      (λ B, B.card ≤ ((range N).filter is_prime_pow).card),
  have hAc : A ∈ choices,
  { simp only [mem_filter, mem_powerset, finset.subset_iff, mem_range, nat.lt_add_one_iff],
    exact ⟨λ b hb, ⟨finset.le_max' _ _ hb, ha _ hb⟩, hN⟩ },
  cases lt_or_le a N with haN haN,
  { refine sum_le_sum_of_subset_of_nonneg (λ a' ha', _) (by simp),
    rw [mem_filter, mem_range],
    exact ⟨haN.trans_le' (le_max' _ _ ha'), ha _ ha'⟩ },
  obtain ⟨B, hB, hB'⟩ := exists_max_image choices (λ B, ∑ q in B, (1 : ℝ) / q) ⟨_, hAc⟩,
  simp only [mem_filter, mem_powerset, and_imp] at hB,
  suffices : (range N).filter is_prime_pow = B,
  { rw this,
    apply hB' _ hAc },
  suffices : (range N).filter is_prime_pow ⊆ B,
  { exact eq_of_subset_of_card_le this hB.2 },
  dsimp at hB',
  by_contra i,
  have : ∀ (a : ℕ), a ∈ B → is_prime_pow a,
  { intros x hx,
    exact (mem_filter.1 (hB.1 hx)).2 },
  obtain ⟨r, hr, hr', hr'', a', ha', hra'⟩ := this_condition_here this hB.2 i,
  { have hr'''  : r ∉ B.erase a' := λ h, hr' (erase_subset _ _ h),
    let B' := cons _ _ hr''',
    have hra : r ≤ a := hra'.le.trans (mem_range_succ_iff.1 (mem_filter.1 (hB.1 ha')).1),
    have hB'' : B' ∈ choices,
    { simp only [mem_filter, mem_powerset, cons_subset, mem_range_succ_iff, hr'', hra, true_and],
      rw [card_cons, card_erase_of_mem ha', nat.sub_add_cancel],
      { exact ⟨(erase_subset _ _).trans hB.1, hB.2⟩ },
      { rw [nat.add_one_le_iff, card_pos],
        exact ⟨_, ha'⟩ } },
    have := hB' B' hB'',
    rw [sum_cons, ←add_sum_erase _ _ ha', add_le_add_iff_right] at this,
    refine hra'.not_le (nat.cast_le.1 (le_of_one_div_le_one_div _ this)),
    rw nat.cast_pos,
    exact hr''.pos },
  obtain ⟨b, hb, hb'⟩ := ssubset_iff_exists_cons_subset.1 h,
  set B' := cons _ _ hb,
  have hB'' : B' ∈ choices,
  { simp only [mem_filter, mem_powerset, card_le_of_subset hb', and_true],
    intros b hb,
    have := hb' hb,
    simp only [mem_filter, mem_range, nat.lt_add_one_iff] at this ⊢,
    exact ⟨this.1.le.trans haN, this.2⟩ },
  have := hB' _ hB'',
  rw [sum_cons, add_le_iff_nonpos_left, one_div_nonpos, ←nat.cast_zero, nat.cast_le,
    le_zero_iff] at this,
  rw [cons_subset, mem_filter] at hb',
  exact hb'.1.2.pos.ne' this,
end

lemma Omega_eq_card_prime_pow_divisors {n : ℕ} (hn : n ≠ 0) :
  Ω n = (n.divisors.filter is_prime_pow).card :=
begin
  revert hn,
  refine nat.rec_on_prime_coprime _ _ _ n,
  { simp },
  { sorry },
  { sorry },
end

lemma rec_pp_sum_close :
  ∀ᶠ (N : ℕ) in at_top, ∀ x y : ℤ, (x ≠ y) → (|(x : ℝ)-y| ≤ N) →
  ∑ q in (finset.range(N+1)).filter(λ n, is_prime_pow n ∧ (n:ℤ) ∣ x ∧ (n:ℤ) ∣ y), (1 : ℝ)/q <
  ((1 : ℝ)/500)*log(log N) :=
begin
  filter_upwards [eventually_gt_at_top 0, such_large_N_wow,
    (weird_floor_sq_tendsto_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
       prime_counting_lower_bound_explicit,
    (weird_floor_sq_tendsto_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
       explicit_mertens],
  intros N hlarge0 hlarge1 hprimes hmertens x y hxy hxyN,
  let m :=  int.nat_abs (x-y),
  let M := Ω m,
  let T := ⌈real.logb 2 N⌉₊^2,
  have hMT : M ≤ ((finset.range(T+1)).filter is_prime_pow).card, {
    calc _ ≤ ⌊real.logb 2 m⌋₊ : card_factors_le_log
       ... ≤ ⌊sqrt T⌋₊ :_
       ... ≤ ((finset.Icc 1 T).filter nat.prime).card : hprimes
       ... ≤ _ :_,
    refine nat.le_floor _, refine le_trans (nat.floor_le _) _, refine real.logb_nonneg one_lt_two _,
    norm_cast, rw nat.one_le_iff_ne_zero, intro hz, rw int.nat_abs_eq_zero at hz,
    rw sub_eq_zero at hz, exact hxy hz,
    calc _ ≤ real.logb 2 N :_
       ... ≤ _ :_,
    rw logb_le_logb, rw nat_cast_diff_issue at hxyN, exact hxyN, exact one_lt_two,
    norm_cast, rw pos_iff_ne_zero, intro hz, rw int.nat_abs_eq_zero at hz,
    rw sub_eq_zero at hz, exact hxy hz, exact_mod_cast hlarge0,
    push_cast, rw sqrt_sq, exact nat.le_ceil (real.logb 2 N),
    refine nat.cast_nonneg _,
    refine card_le_of_subset _, intros p hp, rw [mem_filter, mem_Icc] at hp,
    rw [mem_filter, mem_range, nat.lt_succ_iff], refine ⟨hp.1.2, nat.prime.is_prime_pow hp.2⟩,
   },
  calc _ ≤ ∑ q in (finset.range(N+1)).filter(λ n, is_prime_pow n ∧ n ∣ m ), (1 : ℝ)/q :_
     ... ≤ ∑ q in (finset.range(T+1)).filter is_prime_pow, (1 : ℝ)/q :_
     ... < _ :_,
  refine sum_le_sum_of_subset_of_nonneg _ _, intros q hq, rw mem_filter at hq,
  rw mem_filter, refine ⟨hq.1,hq.2.1,_⟩,
  rw ← int.coe_nat_dvd_left, refine dvd_sub _ _,  rw ← int.dvd_nat_abs, norm_cast,
  rw ← int.coe_nat_dvd_left, exact hq.2.2.1, exact hq.2.2.2, intros q hq1 hq2,
  rw one_div_nonneg, exact nat.cast_nonneg q,
  apply prime_power_recip_downward_bound _ _ _ _,
  { simp only [mem_filter, and_imp, implies_true_iff] {contextual := tt} },
  { apply hMT.trans',
    sorry
     },
  -- refine prime_power_recip_downward_bound,

  -- The idea for the next part is to write an injection from the range of summation of the first
  -- sum to the second, where we write each set as an increasing list q1, q2,... and r1, r2, r3, ...
  -- and map qi to ri.
  -- ∑ (q in A), 1/q ≤ ∑ (q in B), 1/q if there is a function f : A → B (injective) such that
  -- b ≤ f(a).
  -- suppose there is some b such that f(a) < b, let a be minimal such that this holds.
  -- Then a is a prime power that is less than f(b),
  -- so by inductive construction of f, there is some c such that a = f(c), but then c < b
  -- .......................A..A.......A....A....
  -- BBBBBB......................................
  -- use list.take to truncate second list to be of length M
  --  (and then list.take_sublist and list.sublist.sum_le_sum
  -- then list.forall₂.sum_le_sum
  -- have := list.forall₂.sum_le_sum,
  --
  refine lt_of_le_of_lt hmertens _, dsimp, push_cast, exact hlarge1,
end

-- No sorries below this line! (except Bhavik's bit)
-----------------------------------------
------------------------------------------
-----------------------------------------


lemma ppowers_count_eq_prime_count {n : ℕ} (hn : n ≠ 0) :
  (filter (λ (r : ℕ), is_prime_pow r ∧ r.coprime (n / r)) n.divisors).card
    = (filter (λ (p : ℕ), nat.prime p) n.divisors).card :=
begin
  let f := (λ p, p^(n.factorization p)),
  have h₁ : (filter (λ (r : ℕ), is_prime_pow r ∧ r.coprime (n / r)) n.divisors)
    = finset.image f (filter (λ (p : ℕ), nat.prime p) n.divisors), {
      ext, rw [finset.mem_image, mem_filter], split,
      intro ha, rw is_prime_pow_def at ha, rcases ha.2.1 with ⟨p,k,hp,hk⟩,
       rw [← hk.2, nat.mem_divisors] at ha,
      use p, rw [mem_filter, nat.prime_iff, nat.mem_divisors],
      refine ⟨⟨⟨_,hn⟩,hp⟩,_⟩,
      refine dvd_trans (dvd_pow_self p (ne_of_gt hk.1)) ha.1.1, rw ← nat.prime_iff at hp, rw ← hk.2,
      rw coprime_div_iff hp ha.1.1 (ne_of_gt hk.1) ha.2.2,
      intro a, rcases a with ⟨p,hp,hpa⟩, rw ← hpa, rw nat.mem_divisors,
      rw is_prime_pow_def, rw [mem_filter, nat.prime_iff] at hp,
      have h0fac : 0 < n.factorization p, {
        refine nat.prime.factorization_pos_of_dvd _ hn _, rw nat.prime_iff, exact hp.2,
        refine nat.dvd_of_mem_divisors hp.1,
      },
      refine ⟨⟨(nat.pow_factorization_dvd n p),hn⟩,_,_⟩,
      refine ⟨p,(n.factorization p),hp.2,h0fac,_⟩, refl,
      have : n.factorization p = n.factorization p := by refl,
      rw [← factorization_eq_iff] at this, exact this.2,
      rw nat.prime_iff, exact hp.2, refine ne_of_gt h0fac,
     },
  rw h₁, refine finset.card_image_of_inj_on _,
  intros p₁ hp₁ p₂ hp₂ hps, norm_cast at hp₁, rw mem_filter at hp₁, refine eq_of_prime_pow_eq _ _ _ hps,
  rw [← nat.prime_iff], exact hp₁.2,
  rw [← nat.prime_iff], norm_cast at hp₂, rw mem_filter at hp₂, exact hp₂.2,
  refine nat.prime.factorization_pos_of_dvd _ hn _, exact hp₁.2, refine nat.dvd_of_mem_divisors hp₁.1,
end

lemma omega_count_eq_ppowers {n : ℕ} :
  (filter (λ (r : ℕ), is_prime_pow r ∧ r.coprime (n / r)) n.divisors).card = ω n :=
begin
  by_cases hn0 : n = 0,
  {
  rw [hn0, nat.arithmetic_function.card_distinct_factors_zero, card_eq_zero,
     finset.eq_empty_iff_forall_not_mem], intros r hr,
  rw [mem_filter, nat.zero_div, nat.coprime_zero_right] at hr,
  exact is_prime_pow.ne_one hr.2.1 hr.2.2,
  },
  rw [ppowers_count_eq_prime_count hn0,
     nat.arithmetic_function.card_distinct_factors_apply, ← finset.length_to_list],
  refine list.perm.length_eq _, rw list.perm_ext (finset.nodup_to_list _) (list.nodup_dedup _),
  intro q, rw [mem_to_list, list.mem_dedup, nat.mem_factors hn0],  split,
  intro hq,
  rw mem_filter at hq, refine ⟨hq.2,nat.dvd_of_mem_divisors hq.1⟩,
  intro hq, rw [mem_filter, nat.mem_divisors], refine ⟨⟨hq.2,hn0⟩,hq.1⟩,
end

lemma exp_pol_lbound (k : ℕ) (x : ℝ) (h : 0 < x) : x^k < k.factorial * exp(x) :=
begin
  induction k with k hind generalizing x,
  simp only [pow_zero, nat.factorial_zero, nat.cast_one, one_mul, one_lt_exp_iff, h],
  let f := (λ y:ℝ, ((k.succ).factorial : ℝ)* exp(y) - y^(k.succ)),
  have h₁ : differentiable ℝ f, {
    refine differentiable.sub _ _,
    refine differentiable.const_mul differentiable_exp ((k.succ).factorial : ℝ),
    simp only [differentiable.pow, differentiable_id'],
  },
  have h₂ : ∀ t, deriv f t = (k.succ).factorial* exp(t) - (k.succ)*t^k, {
    intro y,
    rw [deriv_sub, deriv_const_mul, real.deriv_exp, deriv_pow, nat.succ_sub_one],
    simp only [differentiable_at.exp, differentiable_at_id'],
    simp only [differentiable_at.mul, differentiable_at_const, differentiable_at.exp, differentiable_at_id'],
    simp only [differentiable_at.pow, differentiable_at_id'],
  },
  rw ← sub_pos, have h' := (le_of_lt h), rw ← set.mem_Ici at h',
  have := (convex_Ici 0).monotone_on_of_deriv_nonneg h₁.continuous.continuous_on
      h₁.differentiable_on _ (set.left_mem_Ici) h' h',
  refine lt_of_lt_of_le _ this, simp only [sub_pos, zero_pow', ne.def, nat.succ_ne_zero,
     not_false_iff, nat.cast_mul, nat.cast_add, nat.cast_one, exp_zero, mul_one], norm_cast,
  exact nat.factorial_pos (k.succ), intros y hy, rw [h₂ y, sub_nonneg],
  simp only [nat.cast_succ, nat.factorial_succ, nat.cast_mul], rw [mul_assoc, mul_le_mul_left],
  refine le_of_lt (hind y _), rw [interior_Ici, set.mem_Ioi] at hy, exact hy, norm_cast,
  exact nat.succ_pos k,
end

lemma factorial_bound (t : ℕ) : ((t:ℝ)* exp (-1)) ^ t ≤ t.factorial :=
begin
  by_cases h0 : 0 < t,
  rw [mul_pow, ← rpow_nat_cast, ← rpow_nat_cast, ← exp_mul, ← neg_eq_neg_one_mul, exp_neg,
       mul_inv_le_iff', rpow_nat_cast],
  refine le_of_lt (exp_pol_lbound t (t:ℝ) _), exact_mod_cast h0, refine exp_pos _,
  rw [not_lt, nat.le_zero_iff] at h0, rw h0,
  simp only [pow_zero, nat.factorial_zero, nat.cast_one],
end

lemma helpful_decreasing_bound {x y : ℝ} {n : ℕ} (h0y : 0 < y) (hn : x ≤ n) (hy : y ≤ x):
  (y/(n*exp(-1)))^n ≤ (y/(x*exp(-1)))^x :=
begin
  have hhelp₆ : 0 < x := lt_of_lt_of_le h0y hy,
  have hhelp₅ : (0:ℝ) < n := lt_of_lt_of_le hhelp₆ hn,
  have hhelp₃ : (0:ℝ) < (n*exp(-1)) := mul_pos hhelp₅ (exp_pos (-1)),
  have hhelp₄ : 0 < x*exp(-1) := mul_pos hhelp₆ (exp_pos (-1)),
  have hhelp₁ : 0 < y/(n*exp(-1)) := div_pos h0y hhelp₃,
  have hhelp₂ : 0 < y/(x*exp(-1)) := div_pos h0y hhelp₄,
  rw [← rpow_nat_cast, ← exp_log hhelp₁, ← exp_mul, ← exp_log hhelp₂, ← exp_mul, exp_le_exp,
       log_div (ne_of_gt h0y) (ne_of_gt hhelp₃), log_div (ne_of_gt h0y) (ne_of_gt hhelp₄),
      sub_mul, sub_mul, log_mul (ne_of_gt hhelp₆) (ne_of_gt (exp_pos (-1))),
      log_mul (ne_of_gt hhelp₅) (ne_of_gt (exp_pos (-1))), add_mul, add_mul, sub_add_eq_sub_sub,
      sub_add_eq_sub_sub, sub_right_comm, ← sub_mul, sub_right_comm, log_exp, sub_neg_eq_add],
  nth_rewrite 1 ← sub_mul, rw [sub_neg_eq_add],
  let f := (λ x : ℝ, (log y + 1)*x - x*log x),
  have h₂ : ∀ t, t ≠ 0 → deriv f t = log y - log t, {
    intros t ht,
    rw [deriv_sub, deriv_const_mul], simp only [deriv_id'', mul_one],
    rw [deriv_mul, deriv_id'', one_mul, real.deriv_log, mul_inv_cancel ht],
    simp only [add_sub_add_right_eq_sub], exact differentiable_at_id',
    rw differentiable_at_log_iff, exact ht, exact differentiable_at_id',
    simp only [differentiable_at.mul, differentiable_at_const, differentiable_at_id'],
    refine differentiable_at.mul _ _, exact differentiable_at_id',
    rw differentiable_at_log_iff, exact ht,
  },
  have h₁ : differentiable_on ℝ f (set.Ici y), {
    refine differentiable_on.sub _ _, refine differentiable_on.const_mul _ _,
    refine differentiable_on_id, refine differentiable_on.mul _ _, refine differentiable_on_id,
    refine differentiable_on.log _ _, refine differentiable_on_id, intros z hz,
    rw set.mem_Ici at hz, exact ne_of_gt (lt_of_lt_of_le h0y hz),
  },
  have hxIci : x ∈ set.Ici y, { rw set.mem_Ici, exact hy, },
  have := (convex_Ici y).antitone_on_of_deriv_nonpos h₁.continuous_on _ _ hxIci,
  have hny : (n:ℝ) ∈ set.Ici y, { rw set.mem_Ici, exact le_trans hy hn, },
  specialize this hny hn, rw [mul_comm (log n), mul_comm (log x)], exact this,
      refine differentiable_on.sub _ _, refine differentiable_on.const_mul _ _,
    refine differentiable_on_id, refine differentiable_on.mul _ _, refine differentiable_on_id,
    refine differentiable_on.log _ _, refine differentiable_on_id, intros z hz,
    rw interior_Ici at hz, rw set.mem_Ioi at hz, exact ne_of_gt (lt_trans h0y hz),
  intros z hz, rw [interior_Ici, set.mem_Ioi] at hz, rw [h₂, sub_nonpos, log_le_log],
  exact le_of_lt hz, exact h0y, exact lt_trans h0y hz,
  exact ne_of_gt (lt_trans h0y hz),
end

lemma sub_le_omega_div {a b : ℕ} (h: b ∣ a) : (ω a:ℝ) - ω b ≤ ω (a/b) :=
begin
  rcases a.eq_zero_or_pos with rfl | ha,
  { simp },
  rcases b.eq_zero_or_pos with rfl | hb,
  { simp [zero_dvd_iff.mp h] },
  rw sub_le_iff_le_add,
  norm_cast,
  simp only [nat.arithmetic_function.card_distinct_factors_apply],
  rw [add_comm, ←list.length_append],
  apply list.subperm.length_le,
  obtain ⟨k, rfl⟩ := h,
  have hk : 0 < k := pos_of_mul_pos_left ha hb.le,
  rw [k.mul_div_cancel_left hb],
  refine (list.nodup_dedup _).subperm _,
  intros x hx,
  rw [list.mem_dedup, nat.mem_factors_mul hb.ne' hk.ne'] at hx,
  rwa [list.mem_append, list.mem_dedup, list.mem_dedup]
end

lemma omega_div_le {a b : ℕ}  (h : b ∣ a) : ω (a/b) ≤ ω a :=
begin
  obtain ⟨k, rfl⟩ := h,
  rcases eq_or_ne k 0 with rfl|hk,
  { simp },
  rcases b.eq_zero_or_pos with rfl|hb,
  { simp },
  simp only [nat.arithmetic_function.card_distinct_factors_apply, k.mul_div_cancel_left hb],
  refine (k.factors.nodup_dedup.subperm $ λ t ht, _).length_le,
  rw [list.mem_dedup, nat.mem_factors_mul hb.ne' hk],
  exact or.inr (list.mem_dedup.mp ht),
end

lemma harmonic_sum_bound_two : ∀ᶠ (N : ℕ) in at_top,
  ∑ n in finset.range(N+1), (1 : ℝ)/n ≤ 2*log N :=
begin
  have hhar := harmonic_series_is_O_with,
  filter_upwards [eventually_ge_at_top 1,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_ge_at_top (euler_mascheroni + 2 * 1)),
    tendsto_coe_nat_at_top_at_top.eventually hhar.bound]
    with N hlarge hlogN hbound,
  clear hhar, rw [norm_eq_abs, norm_eq_abs, ← sub_add_eq_sub_sub, abs_sub_le_iff] at hbound,
  have hbound' := hbound.1, clear hbound,
  rw [sub_le_iff_le_add, summatory] at hbound',
  have h1N : 1 ≤ N + 1, { rw le_add_iff_nonneg_left, exact nat.zero_le N,},
  calc _ = ∑ (n : ℕ) in Icc 1 ⌊(N:ℝ)⌋₊, ((n:ℝ))⁻¹ :_
     ... ≤ _ :_,
  rw ← finset.sum_range_add_sum_Ico _ h1N,
  have hhelp : ∑ n in finset.range(1), (1 : ℝ)/n = 0, { refine sum_eq_zero _,
    intros n hn, rw [mem_range, nat.lt_one_iff] at hn, rw hn,
    simp only [div_zero, nat.cast_zero, eq_self_iff_true],},
  rw [hhelp, zero_add], refine sum_congr _ _, simp only [nat.floor_coe],
  ext, rw [mem_Ico, mem_Icc, nat.lt_succ_iff], intros n hn, rw one_div,
  refine le_trans hbound' _, rw [abs_of_pos, ← one_div, two_mul (log N), ← add_assoc,
  add_rotate, add_assoc, add_le_add_iff_left],
  transitivity (euler_mascheroni+(2*1)), rw [add_le_add_iff_left,
     mul_le_mul_left zero_lt_two, one_div_le, one_div_one], norm_cast,
  exact hlarge, norm_cast, exact lt_of_lt_of_le zero_lt_one hlarge,
  exact zero_lt_one, exact real.nontrivial, exact hlogN, rw inv_pos, norm_cast,
  exact lt_of_lt_of_le zero_lt_one hlarge,
end


lemma div_bound_useful_version {ε : ℝ} (hε1 : 0 < ε) :
  ∀ᶠ (N : ℕ) in at_top, ∀ n : ℕ, (n ≤ N^2) →
  (σ 0 n : ℝ) ≤ N ^ (2*real.log 2 / log (log (N : ℝ)) * (1 + ε)) :=
begin
  let c := ε/2,
  have hc : 0 < c := half_pos hε1,
  have hhelp0 : 1 ≤  2 * log 2 * (1 + ε), { transitivity (2*(log 2)), rw ← div_le_iff',
    refine le_trans _ (le_of_lt real.log_two_gt_d9), norm_num1, exact zero_lt_two,
    nth_rewrite 0 ← mul_one (2*(log 2)), rw [mul_le_mul_left],
    refine le_add_of_nonneg_right (le_of_lt hε1), refine mul_pos zero_lt_two (log_pos one_lt_two), },
  have hhelp : 0 < 2 * log 2 * (1 + ε), { exact lt_of_lt_of_le zero_lt_one hhelp0, },
  have hhelp2 : 0 < (1+ε)/(1+c), { refine div_pos (add_pos zero_lt_one hε1) (add_pos zero_lt_one hc), },
  have haux: asymptotics.is_O_with (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) log id at_top,
  { refine is_o_log_id_at_top.def' _, refine div_pos _ hhelp2, rw [sub_pos, one_lt_div,
      real.add_lt_add_iff_left], exact half_lt_self hε1, exact add_pos zero_lt_one hc, },
  have hdiv := divisor_bound hc, rw filter.eventually_at_top at hdiv,
  rcases hdiv with ⟨M,hdiv⟩,
  filter_upwards[tendsto_coe_nat_at_top_at_top.eventually  (eventually_ge_at_top (1:ℝ)),
    ((tendsto_pow_rec_loglog_at_top hhelp).comp tendsto_coe_nat_at_top_at_top).eventually
      (eventually_ge_at_top (M:ℝ)),
    ((tendsto_pow_rec_loglog_at_top hhelp).comp tendsto_coe_nat_at_top_at_top).eventually
      (eventually_ge_at_top (exp(1))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually haux.bound,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_gt_at_top ((0:ℝ))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top))).eventually (eventually_gt_at_top (0:ℝ))]
    with N h1N hN hN' hlarge h0logN h0loglogN h0logloglogN,
  intros n hn,
  let X := ((N:ℝ)^(2*real.log 2 / log (log (N : ℝ)) * (1 + ε))),
  have hXhelp : X = ((N:ℝ)^(2*real.log 2 * (1 + ε) / log (log (N : ℝ)) )), { rw ← div_mul_eq_mul_div, },
  have hMX : (M:ℝ) ≤ X, { rw hXhelp, exact hN, },
  have heX : exp(1) ≤ X, { rw hXhelp, exact hN', },
  have h1X : 1 < X, { refine lt_of_lt_of_le _ heX, rw one_lt_exp_iff, exact zero_lt_one, },
  have hlogX : 0 < log X := log_pos h1X,
  by_cases hnbig : (n:ℝ) ≤ X,
  transitivity (n:ℝ), norm_cast, exact trivial_divisor_bound, exact hnbig, rw not_le at hnbig,
  have hloglogn' : 0 < log(log n), { refine log_pos _, rw lt_log_iff_exp_lt, refine lt_of_le_of_lt heX hnbig,
       exact lt_trans (lt_trans zero_lt_one h1X) hnbig, },
  have hloglogn : 0 ≤ log(log n) := le_of_lt hloglogn',
  have hnM : (M:ℝ) ≤ n, { refine le_trans hMX (le_of_lt hnbig), },
  refine le_trans (hdiv n _) _, exact_mod_cast hnM,
  transitivity ((N:ℝ)^2)^(log 2 / log (log ↑n) * (1 + c)), refine rpow_le_rpow _ _ _,
  exact nat.cast_nonneg n, norm_cast, exact hn, refine mul_nonneg _ _,
  refine div_nonneg (log_nonneg one_le_two) _, exact hloglogn, refine add_nonneg zero_le_one (le_of_lt hc),
  rw [← rpow_nat_cast, ← rpow_mul], refine rpow_le_rpow_of_exponent_le _ _, exact h1N, norm_cast,
  rw [← mul_div, mul_assoc, mul_le_mul_left zero_lt_two, div_mul, div_mul, div_le_div_left,
      le_div_iff, div_mul], transitivity log(log X), rw [div_le_iff', ← log_rpow, log_le_log,
      log_rpow, mul_rpow, ← div_le_iff], nth_rewrite 0 ← rpow_one (log N),
  rw [← rpow_sub, div_mul_eq_mul_div, div_rpow, ← neg_sub, rpow_neg, ← one_div, div_le_div_iff, one_mul,
     ← log_le_log, log_rpow, log_mul, log_rpow], refine le_trans _ (le_add_of_nonneg_left _),
  rw [log_rpow, ← le_div_iff', ← div_mul_eq_mul_div],
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hlarge, exact hlarge, exact h0loglogN,
  exact h0logloglogN, exact hhelp2, exact h0logN, refine mul_nonneg (le_of_lt hhelp2) (log_nonneg hhelp0),
  exact hhelp, refine ne_of_gt (rpow_pos_of_pos hhelp _), refine ne_of_gt (rpow_pos_of_pos h0logN _),
  exact h0loglogN, refine rpow_pos_of_pos h0loglogN _, refine mul_pos (rpow_pos_of_pos hhelp _) _,
  refine rpow_pos_of_pos h0logN _, refine rpow_pos_of_pos h0logN _, refine rpow_pos_of_pos h0loglogN _,
  exact le_of_lt h0logN, exact le_of_lt hhelp, exact le_of_lt h0loglogN, exact h0logN,
  refine rpow_pos_of_pos h0logN _, rw div_mul_eq_mul_div,
  refine div_nonneg (le_of_lt hhelp) (le_of_lt h0loglogN), exact le_of_lt h0logN,
  exact lt_of_lt_of_le zero_lt_one h1N, exact h0logN, refine rpow_pos_of_pos _ _, exact hlogX,
  exact hlogX, exact hhelp2, rw [log_le_log, log_le_log], exact le_of_lt hnbig,
  refine rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one h1N) _, refine lt_trans _ hnbig,
  refine rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one h1N) _, exact hlogX,
  rw log_nonneg_iff at hloglogn, exact lt_of_lt_of_le zero_lt_one hloglogn, refine log_pos _,
  refine lt_trans h1X hnbig, refine add_pos zero_lt_one hc, exact log_pos one_lt_two,
  refine div_pos hloglogn' (add_pos zero_lt_one hc), refine div_pos h0loglogN (add_pos zero_lt_one hε1),
  exact real.nontrivial, exact le_trans zero_le_one h1N,
end



lemma another_large_N (c C : ℝ) (hc : 0 < c) (hC : 0 < C) : ∀ᶠ (N : ℕ) in at_top,
  1/c/2 ≤ log(log(log N)) ∧ 2^((100:ℝ)/99) ≤ log N ∧ 4*log(log(log N)) ≤ log(log N)
  ∧ log 2 < log(log(log N)) ∧
  (log N) ^ (-((2:ℝ) / 99) / 2) ≤
     C * (1 / (2 * log N ^ ((1:ℝ) / 100))) / log N ^ ((2:ℝ)/⌊(log (log N))/(2*log(log(log N)))⌋₊) ∧
  (1 - 2 / 99) * log (log N) +
  (1 + 5 / log (⌊(log (log N))/(2*log(log(log N)))⌋₊) * log (log N)) ≤ 99 / 100 * log (log N) :=
begin
  have haux: asymptotics.is_O_with ((1:ℝ)/(4)) log id at_top,
  { refine is_o_log_id_at_top.def' _, norm_num1, },
  have haux2: asymptotics.is_O_with ((1:ℝ)/(3960000)) log id at_top,
  { refine is_o_log_id_at_top.def' _, norm_num1, },
  have haux3: asymptotics.is_O_with (1 / ((exp 10000 + 1) * 2)) log id at_top,
  { refine is_o_log_id_at_top.def' _, rw one_div_pos, refine mul_pos _ zero_lt_two,
    refine add_pos (exp_pos _) zero_lt_one, },
  have hhelp : 0 < (1:ℝ)/10000 := by norm_num1,
  filter_upwards [
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually haux.bound,
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually haux2.bound,
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually haux3.bound,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_gt_at_top ((0:ℝ))),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_ge_at_top ((1:ℝ))),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_ge_at_top ((2^((100:ℝ)/99):ℝ))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top))).eventually (eventually_ge_at_top (1/c/2)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top))).eventually (eventually_gt_at_top (log 2)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top (1000:ℝ)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top))).eventually (eventually_gt_at_top (0:ℝ)),
    (((tendsto_rpow_at_top hhelp).comp (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top))).eventually
       (eventually_ge_at_top ((C / 2)⁻¹)) ]
  with N hlarge hlarge2 hlarge3 h0logN h1logN hlogN hlogloglogN' hlogloglogN h0loglogN hloglogN h0logloglogN hlargepow,
  have hhelp2 : exp(10000) ≤ ⌊(log (log N))/(2*log(log(log N)))⌋₊, {
      rw nat.cast_floor_eq_cast_int_floor, refine le_trans _ (le_of_lt (int.sub_one_lt_floor _)),
      rw [le_sub_iff_add_le, le_div_iff, ← mul_assoc, ← le_div_iff', div_eq_mul_one_div, mul_comm],
      rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hlarge3, exact hlarge3, exact h0loglogN,
      exact h0logloglogN, refine mul_pos _ zero_lt_two,
      refine add_pos (exp_pos _) zero_lt_one, exact mul_pos zero_lt_two h0logloglogN,
      refine div_nonneg (le_of_lt h0loglogN) (mul_nonneg zero_le_two (le_of_lt h0logloglogN)),
   },
  have hhelppos : (0:ℝ) < ⌊(log (log N))/(2*log(log(log N)))⌋₊, {
      refine lt_of_lt_of_le (exp_pos _) hhelp2,
   },
  refine ⟨hlogloglogN',hlogN,_,hlogloglogN,_,_⟩,
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos, mul_comm, ← div_eq_mul_one_div,
      le_div_iff'] at hlarge, exact hlarge, exact zero_lt_four, exact h0loglogN, exact h0logloglogN,
  rw [le_div_iff, ← div_eq_mul_one_div], nth_rewrite 1 div_mul_eq_div_div,
  rw [le_div_iff, ← rpow_add, ← rpow_add],
  calc _ ≤ (log N)^(-(((1:ℝ)/10000))) :_
     ... ≤ _ :_,
  refine rpow_le_rpow_of_exponent_le h1logN _, rw [← le_sub_iff_add_le, ← le_sub_iff_add_le'],
  norm_num1, rw [div_le_div_iff, one_mul], norm_cast, rw [nat.le_floor_iff, le_div_iff, ← mul_assoc],
  norm_num1, rw [← le_div_iff', div_eq_mul_one_div, mul_comm],
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hlarge2, exact hlarge2, exact h0loglogN,
  exact h0logloglogN, norm_num1, refine mul_pos zero_lt_two h0logloglogN,
  refine div_nonneg (le_of_lt h0loglogN) _, refine mul_nonneg (zero_le_two) (le_of_lt h0logloglogN),
  exact hhelppos, norm_num1, rw [rpow_neg, inv_le], dsimp at hlargepow, exact hlargepow,
  refine rpow_pos_of_pos h0logN _, refine div_pos hC zero_lt_two, exact le_of_lt h0logN,
  exact h0logN, exact h0logN, refine rpow_pos_of_pos h0logN _, refine rpow_pos_of_pos h0logN _,
  calc _ ≤ ((97:ℝ)/99)*(log(log N)) + (1/1000)*(log(log N)) + (5/10000)*log(log N) :_
     ... ≤ _ :_,
  rw add_assoc, refine add_le_add _ _, norm_num1, refl, refine add_le_add _ _,
  rw [mul_comm, ← div_eq_mul_one_div, le_div_iff, one_mul], exact hloglogN, norm_num1,
  rw [mul_le_mul_right h0loglogN, div_le_div_left, le_log_iff_exp_le], exact hhelp2,
  exact hhelppos, norm_num1, refine log_pos _, refine lt_of_lt_of_le _ hhelp2, rw one_lt_exp_iff,
  norm_num1, norm_num1,
  rw [← add_mul, ← add_mul, mul_le_mul_right h0loglogN], norm_num1,
end

lemma yet_another_large_N : ∀ᶠ (N : ℕ) in at_top,
(2:ℝ) * N ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) < log N ^ -((1:ℝ) / 101) / 6
:=
begin
  have haux: asymptotics.is_O_with ((1:ℝ)/(2+1)) log id at_top,
  { refine is_o_log_id_at_top.def' _, norm_num1, },
  filter_upwards [tendsto_coe_nat_at_top_at_top.eventually  (eventually_gt_at_top ((0:ℝ))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually haux.bound,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_gt_at_top ((0:ℝ))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (log (6 * 2) / (1 - 1 / 101))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top))).eventually (eventually_ge_at_top (-log (2 + -(2 * log 2) * (1 + 1 / 3)))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top))).eventually (eventually_gt_at_top (0:ℝ))]
  with N h0N hlarge h0logN hloglogN hlogloglogN h0loglogN h0logloglogN,
  have hhelp : 0 <  2 + -(2 * log 2) * (1 + 1 / 3), {
    rw [neg_mul, ← sub_eq_add_neg, sub_pos], nth_rewrite 2 ← mul_one (2:ℝ),
    rw [mul_assoc, mul_lt_mul_left zero_lt_two], norm_num1,
    rw [← lt_div_iff, one_div_div], refine lt_trans real.log_two_lt_d9 _, norm_num1,
    norm_num1, exact real.nontrivial,
   },
  rw [lt_div_iff', ← mul_assoc, ← log_lt_log_iff, log_rpow, log_mul, neg_mul, lt_neg, neg_add,
      log_rpow, ← sub_eq_neg_add, lt_sub_iff_add_lt, ← neg_mul, neg_add, ← neg_div, neg_neg,
      ← neg_mul, ← neg_div], nth_rewrite 1 div_mul_eq_mul_div,
  rw [div_add_div_same],
  calc _ < log(log N) :_
     ... ≤ _ :_,
  rw [← lt_sub_iff_add_lt', ← one_sub_mul, ← div_lt_iff'], exact hloglogN, norm_num1,
  rw [← log_le_log, log_mul, log_div, sub_add_eq_add_sub, le_sub_iff_add_le, ← two_mul,
       ← sub_le_iff_le_add'],
  calc _ ≤ 2*log(log(log N)) + log(log(log N)) :_
     ... ≤ _ :_,
  rw [sub_eq_add_neg, add_le_add_iff_left], exact hlogloglogN,
  rw [← add_one_mul, ← le_div_iff', div_eq_mul_one_div, mul_comm],
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hlarge, exact hlarge, exact h0loglogN,
  exact h0logloglogN, norm_num1, exact ne_of_gt hhelp, exact ne_of_gt h0loglogN,
  refine div_ne_zero (ne_of_gt hhelp) (ne_of_gt h0loglogN), exact ne_of_gt h0logN, exact h0loglogN,
  refine mul_pos _ h0logN, refine div_pos hhelp h0loglogN, exact h0N, norm_num1,
  refine ne_of_gt (rpow_pos_of_pos h0N _), exact h0logN, refine mul_pos _ (rpow_pos_of_pos h0N _),
  norm_num1, refine rpow_pos_of_pos h0logN _, norm_num1,
end

lemma yet_another_large_N' : ∀ᶠ (N : ℕ) in at_top,
1/log N + (1 / (2 * log N ^ ((1:ℝ) / 100)))*((501/500)*log(log N)) ≤
      (log N)^(-(1/101 : ℝ))/6 :=
begin
  have haux: asymptotics.is_O_with ((1:ℝ)/ 10100 / 2) log id at_top,
  { refine is_o_log_id_at_top.def' _, norm_num1, },
  filter_upwards [
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually haux.bound,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_gt_at_top ((0:ℝ))),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_ge_at_top (12 ^ ((101:ℝ) / 100))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top))).eventually (eventually_ge_at_top (log (1503 / 250))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ))]
  with N hlarge h0logN hlogN hlogloglogN h0loglogN,
  rw ← add_halves ((log N)^(-(1/101 : ℝ))/6), refine add_le_add _ _,
  rw [div_div, div_le_iff h0logN, div_mul_eq_mul_div, ← rpow_add_one, one_le_div],
  norm_num1,
  have hhelp : (0:ℝ) < 101/100 := by norm_num1,
  rw ← real.rpow_le_rpow_iff _ _ hhelp, rw [← rpow_mul], norm_num1, rw rpow_one, exact hlogN,
  exact le_of_lt h0logN, norm_num1, refine rpow_nonneg_of_nonneg (le_of_lt h0logN) _, norm_num1,
  exact ne_of_gt h0logN,
  rw [div_div, div_mul_eq_mul_div, one_mul, div_le_div_iff, mul_comm (2:ℝ), ← mul_assoc,
    ← mul_assoc, ← rpow_add, mul_le_mul_right zero_lt_two, mul_comm, ← mul_assoc], norm_num1,
  rw [← log_le_log, log_rpow, log_mul],
  calc _ ≤ 2*log(log(log N)) :_
     ... ≤ _ :_,
  rw [two_mul, add_le_add_iff_right], exact hlogloglogN, rw [← le_div_iff', ← div_mul_eq_mul_div],
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hlarge, exact hlarge, exact h0loglogN,
  refine lt_of_lt_of_le _ hlogloglogN, refine log_pos _, norm_num1, exact zero_lt_two,
  norm_num1, exact ne_of_gt h0loglogN, exact h0logN, refine mul_pos _ h0loglogN, norm_num1,
  refine rpow_pos_of_pos h0logN _, exact real.nontrivial, exact h0logN, refine mul_pos zero_lt_two _,
  refine rpow_pos_of_pos h0logN _, norm_num1,
end

lemma and_another_large_N (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1/2) :  ∀ᶠ (N : ℕ) in at_top,
   2 * log (log N) + 1 ≤ (1 + ε ^ 2) ^ ((1 - ε) * log (log N)) :=
begin
  have haux: asymptotics.is_O_with (log (1 + ε ^ 2) * (1 - ε) / 2) log id at_top,
  { refine is_o_log_id_at_top.def' _, refine div_pos _ zero_lt_two,
    refine mul_pos _ _, refine log_pos _, rw lt_add_iff_pos_right, refine sq_pos_of_pos h1,
    rw sub_pos, refine lt_trans h2 one_half_lt_one,},
  filter_upwards [
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually haux.bound,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_gt_at_top ((0:ℝ))),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top (1:ℝ)),
    (tendsto_log_at_top.comp (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top))).eventually (eventually_ge_at_top (log(2+1)))]
  with N hlarge h0logN h1loglogN hlogloglogN,
  have h1 : 0 < 1 + ε^2, { refine lt_trans zero_lt_one _, rw lt_add_iff_pos_right, refine sq_pos_of_pos h1, },
  rw [← exp_log h1, ← exp_mul, ← mul_assoc], nth_rewrite 1 mul_comm _ (log(log N)),
  rw [exp_mul, exp_log h0logN],
  calc _ ≤ ((2:ℝ)+1)*log(log N) :_
     ... ≤ _ :_,
  rw [add_mul, one_mul, add_le_add_iff_left], exact h1loglogN,
  rw [← log_le_log, log_mul, log_rpow],
  calc _ ≤ 2*(log(log(log N))) :_
     ... ≤ _ :_,
  rw [two_mul, add_le_add_iff_right], exact hlogloglogN, rw [← le_div_iff', ← div_mul_eq_mul_div],
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hlarge, exact hlarge,
  exact lt_of_lt_of_le zero_lt_one h1loglogN, refine lt_of_lt_of_le _ hlogloglogN, refine log_pos _,
  norm_num1, exact zero_lt_two, exact h0logN, norm_num1, refine ne_of_gt (lt_of_lt_of_le zero_lt_one h1loglogN),
  refine mul_pos _ _, exact zero_lt_three, exact lt_of_lt_of_le zero_lt_one h1loglogN,
  refine rpow_pos_of_pos h0logN _,
end

lemma prime_pow_not_coprime_prime_pow {a b : ℕ} (ha : is_prime_pow a) (hb : is_prime_pow b) :
   ¬ (coprime a b) →  ∃ (p k l : ℕ), prime p ∧ (k ≠ 0 ∧ l ≠ 0) ∧ p ^ k = a ∧ p ^ l = b :=
begin
  intro hab,
  rcases (is_prime_pow_def a).1 ha with ⟨q,k,hq,hk,hqa⟩,
  rcases (is_prime_pow_def b).1 hb with ⟨r,l,hr,hl,hrb⟩,
  rw pos_iff_ne_zero at hk, rw pos_iff_ne_zero at hl, refine ⟨q,k,l,hq,⟨hk,hl⟩,hqa,_⟩,
  rw ← hrb, by_contra, apply hab, rw [← hqa, ← hrb], refine nat.coprime_pow_primes _ _ _ _ _,
  rw nat.prime_iff, exact hq, rw nat.prime_iff, exact hr, intro hbad, refine h _,
  rw hbad,
end

lemma omega_mul_ppower {a q : ℕ} (hq : is_prime_pow q) : ω (q*a) ≤ 1 + ω a :=
begin
  -- This really needs to be in arithmetic_functions!
  -- Also, there are a lot of basic lemmas about dedup missing, so this is a bodge
  have : (ω q : ℝ) = 1, {
    norm_cast, rw [nat.arithmetic_function.card_distinct_factors_apply, list.length_eq_one],
    rcases hq with ⟨p,k,hp,hk⟩, rw ← hk.2, use p, rw nat.prime.factors_pow,
    rw ← list.perm_singleton,
    rw ← list.nodup.dedup (list.nodup_singleton p),
    rw ← list.to_finset_eq_iff_perm_dedup, rw list.to_finset_repeat_of_ne_zero,
    ext n, rw [list.mem_to_finset, mem_singleton, list.mem_singleton], rw ← pos_iff_ne_zero,
    exact hk.1, rw nat.prime_iff, exact hp,
   },
  have hdiv : a = (q*a)/q, { rw nat.mul_div_cancel_left, exact is_prime_pow.pos hq, },
  rw ← @nat.cast_le ℝ _ _ _ _, push_cast,
  rw [← sub_le_iff_le_add', zero_add, ← this], nth_rewrite 1 hdiv, refine sub_le_omega_div _,
  refine dvd_mul_right _ _,
end


lemma prime_dvd_prime_pow_then {a p : ℕ} (ha : is_prime_pow a) (hp : nat.prime p)
 (hpa : p ∣ a ) : ∃ k : ℕ, k ≠ 0 ∧
  p ^ k = a :=
begin
  rw is_prime_pow_def at ha, rcases ha with ⟨r,k,hr,hk,hkr⟩,
  refine ⟨k,_,_⟩, rw ← pos_iff_ne_zero, exact hk,
  rw ← hkr at hpa,
  have := nat.prime.dvd_of_dvd_pow hp hpa, rw nat.prime_dvd_prime_iff_eq hp at this,
  rw this, exact hkr, rw nat.prime_iff, exact hr,
end

lemma prime_pow_not_coprime_prod_iff {a : ℕ} {D : finset ℕ} (ha : is_prime_pow a)
(hD : ∀ d ∈ D, is_prime_pow d) :
 ¬ coprime a (∏ d in D, d) ↔ ∃ (p : ℕ) (ka kd : ℕ) (d ∈ D), p.prime ∧ ka ≠ 0 ∧ kd ≠ 0 ∧
 p ^ ka = a ∧ p ^ kd = d :=
begin
  split, intro h, rw nat.prime.not_coprime_iff_dvd at h, rcases h with ⟨p,hp,hpa,hpD⟩,
  use p, rw [← finset.prod_to_list, prime.dvd_prod_iff] at hpD,
  rcases hpD with ⟨d,hd1,hd2⟩, rw list.mem_map at hd1, rcases hd1 with ⟨d',hd1⟩,
  have hdD := hd1.1, rw hd1.2 at hdD, rw finset.mem_to_list at hdD,
  rcases (prime_dvd_prime_pow_then ha hp hpa) with ⟨ka,hka,hpka⟩,
  rcases (prime_dvd_prime_pow_then (hD d hdD) hp hd2) with ⟨kd,hkd,hpkd⟩,
  refine ⟨ka,kd,d,hdD,hp,hka,hkd,hpka,hpkd⟩, rw ← nat.prime_iff, exact hp,
  intro h, rcases h with ⟨p,ka,ka,d,hd,hp,hka,hkd,hpka,hpkd⟩,
  rw nat.prime.not_coprime_iff_dvd, refine ⟨p,hp,_,_⟩,
  rw ← hpka, refine dvd_pow_self _ hka, refine dvd_trans _ (dvd_prod_of_mem _ hd),
  rw ← hpkd, refine dvd_pow_self _ hkd,
end

lemma prime_pow_prods_coprime {A B : finset ℕ} (hA : ∀ a ∈ A, is_prime_pow a)
 (hB : ∀ b ∈ B, is_prime_pow b) : coprime (∏ a in A, a) (∏ b in B, b) ↔
 ∀ a ∈ A, ∀ b ∈ B, coprime a b :=
begin
  split, intros h a ha b hb,
  by_contra, rw nat.prime.not_coprime_iff_dvd at h, rcases h with ⟨r,hr,h2⟩,
  have : ¬ ∃ (p : ℕ), nat.prime p ∧ p ∣ ∏ a in A, a ∧ p ∣ ∏ b in B, b, {
    intro hn, rw ← nat.prime.not_coprime_iff_dvd at hn, exact hn h,
  },
  refine this _, refine ⟨r,hr,dvd_trans h2.1 (finset.dvd_prod_of_mem _ ha),
     dvd_trans h2.2 (finset.dvd_prod_of_mem _ hb)⟩,
  intro h, refine nat.coprime_prod_left _,intros a ha,
  refine nat.coprime_prod_right _, intros b hb, refine h a ha b hb,
end

theorem weighted_ph {s : finset ℕ}
{f : ℕ → ℚ} {w : ℕ → ℚ} {b : ℚ} (h0b : 0 < b)
(hw : ∀ (a : ℕ), a ∈ s → 0 ≤ w a) (hb : b ≤ s.sum (λ (x : ℕ), ((w x) * (f x)))) :
∃ (y : ℕ) (H : y ∈ s), b ≤ (s.sum (λ (x : ℕ), w x))*f y
:=
begin
  have hsne : s.nonempty, { rw nonempty_iff_ne_empty, intro he, rw [he, sum_empty] at hb,
    rw ← not_le at h0b, exact h0b hb, },
  by_contra, rw [not_exists] at h, rw ← not_lt at hb, refine hb _,
  have hmax := exists_max_image s f hsne,
  rcases hmax with ⟨y,hys,hy⟩, specialize h y, rw not_exists at h, specialize h hys,
  rw not_le at h, refine lt_of_le_of_lt _ h, rw sum_mul, refine finset.sum_le_sum _,
  intros n hn, refine mul_le_mul_of_nonneg_left _ _, refine hy n hn,
  refine hw n hn,
end

lemma prime_pow_not_coprime_iff {a b : ℕ} (ha : is_prime_pow a) (hb : is_prime_pow b) :
 ¬ coprime a b ↔ ∃ (p : ℕ) (ka kb : ℕ), p.prime ∧ ka ≠ 0 ∧ kb ≠ 0 ∧
 p ^ ka = a ∧ p ^ kb = b :=
 begin
  split, intro hab,
  rw is_prime_pow_def at ha, rw is_prime_pow_def at hb,
  rcases ha with ⟨p,k,hp,hk,hpa⟩, rcases hb with ⟨r,l,hr,hl,hrb⟩,
  rw ← nat.prime_iff at hp, rw ← nat.prime_iff at hr,
  by_cases hpr : p = r,
  refine ⟨p,k,l,hp,_,_,hpa,_⟩,
  rw ← pos_iff_ne_zero, exact hk, rw ← pos_iff_ne_zero, exact hl, rw hpr,
  exact hrb, exfalso, refine hab _, rw [← hpa, ← hrb],
  refine nat.coprime_pow_primes _ _ hp hr hpr,
  intro he, rcases he with ⟨p,k,l,hp,hk,hl,hpa,hpb⟩,
  rw nat.prime.not_coprime_iff_dvd, refine ⟨p,hp,_,_⟩,
  rw ← hpa, refine dvd_pow_self _ hk,
  rw ← hpb, refine dvd_pow_self _ hl,
 end

lemma eq_iff_ppowers_dvd (a b  : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a = b ↔ (∀ q ∣ a, is_prime_pow q → coprime q (a/q)
 → q ∣ b) ∧ (∀ q ∣ b, is_prime_pow q → coprime q (b/q) → q ∣ a) :=
begin
  split, intro hab, split, intros q hq hqa1 hqa2, rw hab at hq, exact hq,
  intros q hq hqb1 hqb2, rw ← hab at hq, exact hq,
  intro hcomp, refine nat.eq_of_factorization_eq ha hb _,
  intro p,
  let q := p^(a.factorization p),
  let r := p^(b.factorization p),
  by_cases hfac0 : (a.factorization p = 0 ∨ b.factorization p = 0),
  cases hfac0 with hfac1 hfac2,
  by_cases hfac3 : b.factorization p = 0,
  rw [hfac1, hfac3],
  have hr' := hcomp.2 r,
  have hp : nat.prime p, {
    refine @nat.prime_of_mem_factorization b _ _,
     rw finsupp.mem_support_iff, exact hfac3,
   },
  have hr'' : r ∣ b ∧ r.coprime(b/r), {
     rw factorization_eq_iff, exact hp, exact hfac3, },
  have hrpp : is_prime_pow r, {
    refine is_prime_pow.pow (nat.prime.is_prime_pow hp) _, exact hfac3,
  },
  specialize hr' hr''.1 hrpp hr''.2, rw nat.prime.pow_dvd_iff_le_factorization hp at hr',
  rw hfac1 at hr', exfalso, apply hfac3, rw nat.le_zero_iff at hr', exact hr', exact ha,
  by_cases hfac3 : a.factorization p = 0,
  rw [hfac2, hfac3],
  have hr' := hcomp.1 q,
  have hp : nat.prime p, {
    refine @nat.prime_of_mem_factorization a _ _,
     rw finsupp.mem_support_iff, exact hfac3,
   },
  have hr'' : q ∣ a ∧ q.coprime(a/q), {
     rw factorization_eq_iff, exact hp, exact hfac3, },
  have hrpp : is_prime_pow q, {
    refine is_prime_pow.pow (nat.prime.is_prime_pow hp) _, exact hfac3,
  },
  specialize hr' hr''.1 hrpp hr''.2, rw nat.prime.pow_dvd_iff_le_factorization hp at hr',
  rw hfac2 at hr', exfalso, apply hfac3, rw nat.le_zero_iff at hr', exact hr', exact hb,
  rw not_or_distrib at hfac0,
  have hp : nat.prime p, {
    refine @nat.prime_of_mem_factorization a _ _,
     rw finsupp.mem_support_iff, exact hfac0.1,
   },
  have hq' : q ∣ a ∧ q.coprime(a/q), {
     rw factorization_eq_iff, exact hp, exact hfac0.1, },
  have hqpp : is_prime_pow q, {
    refine is_prime_pow.pow (nat.prime.is_prime_pow hp) _, exact hfac0.1,
  },
  have hr' : r ∣ b ∧ r.coprime(b/r), {
     rw factorization_eq_iff, exact hp, exact hfac0.2, },
  have hrpp : is_prime_pow r, {
    refine is_prime_pow.pow (nat.prime.is_prime_pow hp) _, exact hfac0.2,
  },
  have hcompq := hcomp.1 q hq'.1 hqpp hq'.2,
  have hcompr := hcomp.2 r hr'.1 hrpp hr'.2,
  rw nat.prime.pow_dvd_iff_le_factorization hp at hcompq,
  rw nat.prime.pow_dvd_iff_le_factorization hp at hcompr,
  rw le_antisymm_iff, refine ⟨hcompq, hcompr⟩,
  exact ha, exact hb,
end

theorem is_prime_pow_dvd_prod {n : ℕ} {D : finset ℕ}
 (hD : ∀ a b ∈ D, a ≠ b → coprime a b) (hn : is_prime_pow n) :
n ∣ ∏ d in D, d ↔ ∃ d ∈ D, n ∣ d :=
begin
  induction D using finset.induction_on with q D hqD hDind,
  simp only [nat.dvd_one, exists_false, finset.prod_empty, iff_false],
  split, intro hn1, exfalso, exact (is_prime_pow.ne_one hn) hn1,
  intro hne, exfalso, rcases hne with ⟨d,hd1,hd2⟩, exact (not_mem_empty d) hd1,
  split, intro h, rw prod_insert hqD at h,
  have hnec : (∀ (a : ℕ), a ∈ D → ∀ (b : ℕ), b ∈ D → a ≠ b → a.coprime b), {
    intros a ha b hb hab,refine hD a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab,
  },
  specialize hDind hnec, rw nat.coprime.is_prime_pow_dvd_mul _ hn at h,
  cases h with h1 h2, use q, refine ⟨mem_insert_self _ _, h1⟩, rw hDind at h2,
  rcases h2 with ⟨d,hd1,hd2⟩, use d, refine ⟨mem_insert_of_mem hd1,hd2⟩,
  refine nat.coprime_prod_right _, intros d hd,
  refine hD q (mem_insert_self _ _) d (mem_insert_of_mem hd) _, intro hne, rw hne at hqD,
  exact hqD hd,
  intro h, rcases h with ⟨d,hd1,hd2⟩, refine dvd_trans hd2 _,
  refine dvd_prod_of_mem _ hd1,
end

lemma prime_pow_dvd_prime_pow {a b : ℕ} (ha : is_prime_pow a) (hb : is_prime_pow b) :
   a ∣ b ↔  ∃ (p k l : ℕ), prime p ∧ 0 < k ∧ k ≤ l ∧ p ^ k = a ∧ p ^ l = b :=
begin
  split, intro hab,
  rw is_prime_pow_def at hb, rcases hb with ⟨r,l,hr,hl,hrb⟩,
  rw ← hrb at hab, rw ← nat.prime_iff at hr, rw nat.dvd_prime_pow hr at hab,
  rcases hab with ⟨k,hkl,h⟩,
  use r, use k, use l, rw nat.prime_iff at hr,
  refine ⟨hr,_,hkl,_,hrb⟩, rw pos_iff_ne_zero, intro hz,
  rw [hz, pow_zero] at h, refine is_prime_pow.ne_one ha h,
  refine eq.symm h,
  intro he, rcases he with ⟨p,k,l,hp,hk,hkl,hpa,hpb⟩,
  rw [← hpa, ← hpb, pow_dvd_pow_iff], exact hkl,
  exact prime.ne_zero hp, exact prime.not_unit hp,
end

lemma prime_pow_dvd_prod_prime_pow {a : ℕ} {D : finset ℕ} (ha : is_prime_pow a)
 (hD1 : ∀ a b ∈ D, a ≠ b → coprime a b) (hD2 : ∀ d ∈ D, is_prime_pow d) :
a ∣ (∏ d in D, d) → coprime a ((∏ d in D, d)/a) → a ∈ D :=
begin
  intros haD hacop,
  by_cases hprod0 : ∏ (d : ℕ) in D, d = 0,
  rw [hprod0, nat.zero_div, nat.coprime_zero_right] at hacop,
  exfalso, refine is_prime_pow.ne_one ha hacop,
  have haD' := haD, rw is_prime_pow_dvd_prod hD1 ha at haD,
  rcases haD with ⟨d,hd1,hd2⟩,
  have : a = d, {
    have hdpp : is_prime_pow d := hD2 d hd1,
    rw prime_pow_dvd_prime_pow ha (hD2 d hd1) at hd2,
    rcases hd2 with ⟨p,k,l,hp,h0k,hkl,hpa,hpd⟩, rw [← hpa, ← hpd],
    have hnec1 : k = (∏ (d : ℕ) in D, d).factorization p, {
      rw ← nat.prime_iff at hp, rw ← hpa at haD', rw pos_iff_ne_zero at h0k,
      rw ← hpa at hacop,
      refine coprime_div_iff hp haD' h0k hacop,
     },
    have hnec2 : l ≤ (∏ (d : ℕ) in D, d).factorization p, {
      rw ← nat.prime_iff at hp,
      rw ← nat.prime.pow_dvd_iff_le_factorization hp _, rw hpd,
      refine dvd_prod_of_mem _ hd1, exact hprod0,
    },
    have hnec3 : k = l, { rw ← has_le.le.le_iff_eq, exact hkl,
        rw hnec1, exact hnec2,},
    rw hnec3,
   },
  rw this, exact hd1,
end

lemma prod_of_subset_le_prod_of_ge_one'
  {s : finset ℕ} {f : ℕ → ℝ} : ∀ t : finset ℕ, (t ⊆ s) → (∀ i ∈ s, 0 ≤ f i)
  → (∀ i ∈ s, i ∉ t → 1 ≤ f i) →  ∏ i in t, f i ≤ ∏ i in s, f i :=
begin
  induction s using finset.induction_on with n s hns hsind,
  intros t ht hs hf, rw finset.subset_empty.mp ht, simp only [le_refl, finset.prod_empty],
  intros t ht hs hf, rw prod_insert hns,
  by_cases htn : n ∈ t,
  let t' := erase t n,
  have htt' : insert n t' = t, { refine insert_erase htn, },
  rw [← htt', prod_insert (finset.not_mem_erase _ _)], refine mul_le_mul_of_nonneg_left _ _,
  refine hsind t' _ _ _, refine subset_trans (finset.erase_subset_erase _ ht) _,
  refine erase_insert_subset _ _, intros a ha, refine hs a _, refine mem_insert_of_mem ha,
  intros a ha1 ha2, refine hf a (mem_insert_of_mem ha1) _, intro hna, apply ha2,
  rw mem_erase, refine ⟨_,hna⟩, intro hna2, apply hns, rw hna2 at ha1, exact ha1,
  refine hs n (ht htn),
  refine le_trans (hsind t _ _ _) _, rw [subset_insert_iff, erase_eq_of_not_mem htn] at ht,
  exact ht, intros i hi, refine hs i (mem_insert_of_mem hi),
  intros i hi1 hi2, refine hf i (mem_insert_of_mem hi1) hi2,
  refine le_mul_of_one_le_left _ _, refine prod_nonneg _, intros i hi,
  refine hs i (mem_insert_of_mem hi), refine hf n (mem_insert_self _ _) htn,
end

lemma prod_of_subset_le_prod_of_ge_one
  {s t : finset ℕ} {f : ℕ → ℝ} (h : t ⊆ s) (hs : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
begin
  refine prod_of_subset_le_prod_of_ge_one' t h hs hf,
end

lemma sum_le_sum_of_inj' {A : finset ℕ} {f1 f2 : ℕ → ℝ} (g : ℕ → ℕ) :
∀ B : finset ℕ, (∀ b ∈ B, 0 ≤ f2 b ) →
(∀ a ∈ A, g a ∈ B) → (∀ a1 a2 ∈ A, (g a1 = g a2) → a1 = a2) → (∀ a ∈ A, f2 (g a) = f1 a) →
A.sum (λ (i : ℕ), f1 i) ≤ B.sum (λ (i : ℕ), f2 i) :=
begin
  induction A using finset.induction_on with n A hnA hA,
  intros B hf2 hgB hginj hgf, simp only [finset.sum_empty], refine sum_nonneg hf2,
  intros B hf2 hgB hginj hgf, rw sum_insert hnA,
  let B' := erase B (g n),
  have hBB' : insert (g n) B' = B, { refine insert_erase (hgB n _), refine mem_insert_self _ _, },
  rw ← hBB', rw sum_insert (finset.not_mem_erase _ _), refine add_le_add _ _,
  rw hgf n (mem_insert_self _ _), refine hA B' _ _ _ _,
  intros b hb, refine hf2 b (mem_of_mem_erase hb),
  intros a ha, rw mem_erase, refine ⟨_,_⟩,
  intro hne, refine hnA _, rw ← hginj a (mem_insert_of_mem ha) n (mem_insert_self _ _) hne,
  exact ha, refine hgB a (mem_insert_of_mem ha), intros a1 ha1 a2 ha2 hgai,
  refine hginj a1 (mem_insert_of_mem ha1) a2 (mem_insert_of_mem ha2) hgai,
  intros a ha,  refine hgf a (mem_insert_of_mem ha),
end

lemma sum_le_sum_of_inj {A B : finset ℕ} {f1 f2 : ℕ → ℝ} (g : ℕ → ℕ) (hf2 : ∀ b ∈ B, 0 ≤ f2 b )
(hgB : ∀ a ∈ A, g a ∈ B) (hginj : ∀ a1 a2 ∈ A, (g a1 = g a2) → a1 = a2) (hgf : ∀ a ∈ A, f2 (g a) = f1 a) :
A.sum (λ (i : ℕ), f1 i) ≤ B.sum (λ (i : ℕ), f2 i) :=
begin
 refine sum_le_sum_of_inj' g B hf2 hgB hginj hgf,
end

theorem card_bUnion_lt_card_mul_real {s : finset ℤ} {f : ℤ → finset ℕ} (m : ℝ)
  (h : ∀ (a : ℤ), a ∈ s → ((f a).card : ℝ) < m) :
 (s.nonempty) → ((s.bUnion f).card : ℝ) < s.card * m :=
begin
  induction s using finset.induction_on with n s hns hs,
  intro he, exfalso, refine finset.not_nonempty_empty he,
  intro he,
  have hins : (insert n s).bUnion f = (s.bUnion f) ∪ ((f n)\(s.bUnion f)), {
    ext, split, intro ha, rw mem_bUnion at ha, rcases ha with ⟨m,hm1,hm2⟩,
    rw mem_insert at hm1, rw mem_union, cases hm1 with hm3 hm4,
    rw or_iff_not_imp_left, intro ha2, rw mem_sdiff, rw hm3 at hm2,
    refine ⟨hm2,ha2⟩, left, rw mem_bUnion, use m, refine ⟨hm4,hm2⟩,
    intro ha, rw mem_union at ha, rw mem_bUnion,
    cases ha with ha2 ha3, rw mem_bUnion at ha2, rcases ha2 with ⟨m,hm1,hm2⟩,
    use m, refine ⟨mem_insert_of_mem hm1,hm2⟩, use n, rw mem_sdiff at ha3,
    refine ⟨mem_insert_self _ _,ha3.1⟩,
   },
  have hf' : ∀ (a : ℤ), a ∈ s → ((f a).card : ℝ) < m, {
    intros n hn, refine h n (mem_insert_of_mem hn),
   },
  rw [hins, finset.card_disjoint_union, card_insert_of_not_mem hns],
  push_cast, rw [add_mul, one_mul],
  by_cases hsne : s.nonempty,
  refine add_lt_add _ _, exact hs hf' hsne,
  refine lt_of_le_of_lt _ (h n _), norm_cast, refine card_le_of_subset (sdiff_subset _ _),
  refine mem_insert_self _ _, rw finset.not_nonempty_iff_eq_empty at hsne,
  rw hsne, simp only [finset.card_empty, finset.bUnion_empty, finset.sdiff_empty,
    nat.cast_zero, zero_mul, zero_add],
  refine h n (mem_insert_self _ _), refine disjoint_sdiff,
end



lemma prod_le_max_size {ι N : Type*} [ordered_comm_semiring N]
  {s : finset ι} {f : ι → N} (hs : ∀ i ∈ s, 0 ≤ f i) (M : N) (hf : ∀ i ∈ s, f i ≤ M) :
  ∏ i in s, f i ≤ M^s.card :=
begin
  calc _ ≤ ∏ i in s, M :_
     ... = _ : _,
  refine prod_le_prod hs hf, refine finset.prod_const _,
end

lemma sum_add_sum {A B : finset ℕ} {f : ℕ → ℝ} :
A.sum (λ (i : ℕ), f i) + B.sum (λ (i : ℕ), f i) = (A∪B).sum (λ (i : ℕ), f i) +
(A∩B).sum (λ (i : ℕ), f i) :=
begin
  let B' := B\(A∩B),
  have hBunion : B = B'∪(A∩B), { refine eq.symm _, refine sdiff_union_of_subset _,
     refine inter_subset_right _ _, },
  have hABunion: A∪B=A∪B', {
    ext, split, intro ha, rw mem_union, rw mem_union at ha,
    rw or_iff_not_imp_left, intro hna, rw mem_sdiff,
    cases ha with ha1 ha2, exfalso, exact hna ha1, refine ⟨ha2,_⟩, intro hai,
    apply hna, rw mem_inter at hai, exact hai.1, intro ha, rw mem_union,
    rw mem_union at ha, cases ha with ha1 ha2, left, exact ha1, rw mem_sdiff at ha2,
    right, exact ha2.1,
   },
  nth_rewrite 0 hBunion, rw [sum_union, ← add_assoc, hABunion, sum_union],
  rw finset.disjoint_left, intros a ha haB', rw mem_sdiff at haB', apply haB'.2,
  rw mem_inter, refine ⟨ha,haB'.1⟩, refine sdiff_disjoint,
end

lemma sum_add_sum_add_sum {A B C : finset ℕ} {f : ℕ → ℝ} :
A.sum (λ (i : ℕ), f i) + B.sum (λ (i : ℕ), f i) + C.sum (λ (i : ℕ), f i) =
(A∪B∪C).sum (λ (i : ℕ), f i) + (A∩B).sum (λ (i : ℕ), f i) + (A∩C).sum (λ (i : ℕ), f i)
+ (B∩C).sum (λ (i : ℕ), f i) - (A∩B∩C).sum (λ (i : ℕ), f i)
 :=
begin
  rw sum_add_sum, rw [add_right_comm], rw @sum_add_sum (A∪B) C _,
  convert_to ∑ (i : ℕ) in A ∪ B ∪ C, f i + (∑ (i : ℕ) in A ∩ B, f i + ∑ (i : ℕ) in (A ∪ B) ∩ C, f i) =
      ∑ (i : ℕ) in A ∪ B ∪ C, f i + (∑ (i : ℕ) in A ∩ B, f i + (∑ (i : ℕ) in A ∩ C, f i +
       ∑ (i : ℕ) in B ∩ C, f i - ∑ (i : ℕ) in A ∩ B ∩ C, f i)) using 0, { ring_nf, },
  refine congr_arg (has_add.add _) _, refine congr_arg (has_add.add _) _,
  rw @sum_add_sum (A∩C) (B∩C) _,
  have : (A∩C)∩(B∩C) = A∩B∩C, {
    rw [inter_comm B C, ← inter_assoc, inter_assoc A C C, inter_self, inter_assoc, inter_comm C B,
        ← inter_assoc],
   },
  rw [this, ← add_sub, sub_self, add_zero, inter_distrib_right],
end

lemma rec_sum_le_three { A B C : finset ℕ } : rec_sum (A∪B∪C) ≤ rec_sum A + rec_sum B + rec_sum C :=
begin
  let B' := B\A,
  let C' := C\(A∪B'),
  have hunion : A∪B∪C ⊆ A∪B'∪C', {
    intros n hn, rw [mem_union, mem_union],
    rw [mem_union] at hn, rw or_iff_not_imp_left, intro hn2,
    rw mem_sdiff, cases hn with hab hc, exfalso, apply hn2,
    rw mem_union at hab, rw or_iff_not_imp_left, intro hna,
    rw mem_sdiff, refine ⟨_,hna⟩,  cases hab with hab1 hab2,
    exfalso, exact hna hab1, exact hab2, refine ⟨hc,_⟩, intro hn,
    apply hn2, rw ← mem_union, exact hn,
   },
  refine le_trans (rec_sum_mono hunion) _,
  rw [rec_sum_disjoint, rec_sum_disjoint], refine add_le_add _ _,
  rw add_le_add_iff_left, refine rec_sum_mono (sdiff_subset _ _),
  refine rec_sum_mono (sdiff_subset _ _),
  refine disjoint_sdiff, refine disjoint_sdiff,
end

lemma two_in_Icc {a b x y: ℤ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : (|x-y|:ℝ) ≤ b-a :=
begin
  rw abs_le, rw mem_Icc at hx, rw mem_Icc at hy, norm_cast, refine ⟨_,_⟩,
  rw [neg_le, neg_sub], refine sub_le_sub hy.2 hx.1,
  refine sub_le_sub hx.2 hy.1,
end

lemma two_in_Icc' {a b x y: ℤ} (I : finset ℤ) (hI : I = Icc a b) (hx : x ∈ I) (hy : y ∈ I) :
  (|x-y|:ℝ) ≤ b-a :=
begin
  refine two_in_Icc _ _, rw ← hI, exact hx, rw ← hI, exact hy,
end

lemma sum_le_card_mul_real {A : finset ℕ} {M : ℝ} {f : ℕ → ℝ} (h : ∀ n ∈ A, f n ≤ M) :
A.sum f ≤ (A.card) * M :=
begin
  rw ← nsmul_eq_mul, refine finset.sum_le_card_nsmul _ _ _ h,
end

lemma dvd_iff_ppowers_dvd (d n : ℕ) : d ∣ n ↔ ∀ q ∣ d, is_prime_pow q → q ∣ n :=
begin
  split, intros hdn q hqd hq, exact dvd_trans hqd hdn,
  intro h, rw nat.dvd_iff_prime_pow_dvd_dvd, intros p k hp hpkd,
  specialize h (p^k) hpkd,
  by_cases hk0 : k = 0, rw [hk0, pow_zero], exact one_dvd n,
  refine h _, rw is_prime_pow_pow_iff, exact nat.prime.is_prime_pow hp, exact hk0,
end

lemma dvd_iff_ppowers_dvd' (d n : ℕ) (hd : d ≠ 0): d ∣ n ↔ ∀ q ∣ d, (is_prime_pow q  ∧
  coprime q (d/q)) → q ∣ n :=
begin
  split, intros hdn q hqd hq, exact dvd_trans hqd hdn,
  intro h, rw dvd_iff_ppowers_dvd, intros q hqd hq,
   rw is_prime_pow_def at hq,
  rcases hq with ⟨p,k,hp,h0k,hpq⟩, let r := p ^(d.factorization p),
  have : k ≤ d.factorization p, {
     rw ← nat.prime.pow_dvd_iff_le_factorization, rw hpq,
  exact hqd, rw nat.prime_iff, exact hp, exact hd,
  },
  refine @nat.dvd_trans _ r _ _ _,
  rw ← hpq, refine pow_dvd_pow _ _, exact this,
  refine h r (nat.pow_factorization_dvd d p) _, refine ⟨_,_⟩,
  rw is_prime_pow, refine ⟨p,d.factorization p,hp,_,_⟩,
  exact lt_of_lt_of_le h0k this, refl,
  have htemp : d.factorization p = d.factorization p, { refl, },
  rw ← factorization_eq_iff at htemp, exact htemp.2, rw nat.prime_iff, exact hp,
  rw ← pos_iff_ne_zero, exact lt_of_lt_of_le h0k this,
end


lemma rec_sum_le_card_div {A : finset ℕ} {M : ℝ} (hM : 0 < M) (h : ∀ n ∈ A, M ≤ (n:ℝ)) :
 (rec_sum A : ℝ) ≤ A.card / M :=
 begin
  rw [rec_sum, div_eq_mul_one_div], push_cast, refine sum_le_card_mul_real _,
  intros n hn, rw one_div_le_one_div, exact h n hn,
  exact lt_of_lt_of_le hM (h n hn), exact hM,
 end


lemma nat_gcd_prod_le_diff {a b c : ℤ} (hab : a ≠ b) (hac : a ≠ c):
  nat.gcd (int.nat_abs a) (int.nat_abs (b*c)) ≤ (int.nat_abs (a-b))*(int.nat_abs (a-c)) :=
begin
  refine nat.le_of_dvd _ _, rw pos_iff_ne_zero, intro hz,
  rw [mul_eq_zero, int.nat_abs_eq_zero, int.nat_abs_eq_zero, sub_eq_zero, sub_eq_zero] at hz,
  cases hz with hz1 hz2, exact hab hz1, exact hac hz2,
  rw int.nat_abs_mul, refine dvd_trans (nat.gcd_mul_dvd_mul_gcd  _ _ _) _,
  refine mul_dvd_mul _ _,
  rw ← int.coe_nat_dvd_left, refine dvd_sub _ _,  rw ← int.dvd_nat_abs, norm_cast,
  refine nat.gcd_dvd_left _ _, rw ← int.dvd_nat_abs, norm_cast, refine nat.gcd_dvd_right _ _,
  rw ← int.coe_nat_dvd_left, refine dvd_sub _ _,  rw ← int.dvd_nat_abs, norm_cast,
  refine nat.gcd_dvd_left _ _, rw ← int.dvd_nat_abs, norm_cast, refine nat.gcd_dvd_right _ _,
end

lemma triv_ε_estimate (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1/2) : (1-2*ε) ≤ (1-ε)*((1-ε)/(1+ε^2)) :=
begin
  rw [mul_div, le_div_iff],
  convert_to -2*ε^3+1-2*ε+ε^2 ≤ 1-2*ε+ε^2 using 0, { ring_nf, },
  rw [add_le_add_iff_right, sub_le_sub_iff_right, add_le_iff_nonpos_left],
  refine mul_nonpos_of_nonpos_of_nonneg _ _, rw [neg_le, neg_zero], exact zero_le_two,
  refine pow_nonneg _ _, exact le_of_lt hε1, refine lt_of_lt_of_le zero_lt_one _,
  refine le_add_of_nonneg_right (sq_nonneg ε),
end

lemma help_ε_estimate (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1/2) : log (1 - ε) * (1 - ε) ≤ -ε / 2 :=
begin
  have h1ε : 0 < 1 - ε, { rw sub_pos, refine lt_trans hε2 one_half_lt_one, },
  calc _ ≤ (1-ε-1)*(1-ε) : _
     ... = -ε*(1-ε) :_
     ... ≤ _ :_,
  rw mul_le_mul_right, refine log_le_sub_one_of_pos h1ε, exact h1ε,
  simp only [neg_mul, mul_eq_mul_left_iff, true_or, eq_self_iff_true, neg_inj, sub_sub_cancel_left,
     sub_left_inj],
  rw [neg_div, neg_mul, neg_le_neg_iff, div_eq_mul_one_div, mul_le_mul_left, le_sub],
  norm_num1, exact le_of_lt hε2, exact hε1,
end

lemma divisor_function_eq_card_divisors {n : ℕ} : (σ 0 n) = (n.divisors).card :=
begin
  rw [nat.arithmetic_function.sigma_apply, card_eq_sum_ones], refine sum_congr _ _, refl,
  intros x hx, rw pow_zero,
end

lemma tendsto_coe_log_pow_at_top (c : ℝ) (hc : 0 < c) :
  tendsto (λ (x : ℕ), (log x)^c) at_top at_top :=
(tendsto_rpow_at_top hc).comp (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top)

lemma one_lt_four : (1 : ℝ) < 4 :=
begin
  norm_num,
end

lemma floor_sub_ceil {x y z : ℝ} : (⌊z+x⌋:ℝ) - ⌈z-y⌉ ≤ x+y :=
begin
  calc (⌊z+x⌋:ℝ) - ⌈z-y⌉ ≤ z + x - ⌈z-y⌉ :_
      ...  ≤ z + x - (z-y) :_
      ... = x+y :_,
  rw [sub_le_sub_iff_right], refine int.floor_le _,
  rw [sub_le_sub_iff_left], refine int.le_ceil _,
  ring_nf,
end

lemma useful_identity (i:ℕ) (h : (1:ℝ) < i) : (1:ℝ) + 1 / (i - 1) = |(1 - (i)⁻¹)⁻¹| :=
begin
  rw [abs_eq_self.mpr, ← one_div, ← one_div, one_add_div, sub_add, sub_self,
    sub_zero, one_sub_div, one_div, inv_div],
  exact ne_of_gt (lt_trans zero_lt_one h),
  apply ne_of_gt, rw sub_pos, exact h,
  rw [inv_nonneg, sub_nonneg, inv_le, inv_one], exact le_of_lt h,
  exact lt_trans zero_lt_one h, exact zero_lt_one,
end

lemma useful_exp_estimate : ((35 : ℝ)/100) ≤ (1-2*(2/99))*real.exp(-1) :=
begin
  norm_num1, rw [exp_neg, ← one_div, ← div_eq_mul_one_div, le_div_iff', ← le_div_iff],
  apply le_trans (le_of_lt real.exp_one_lt_d9), norm_num1, norm_num1, exact exp_pos 1,
end

lemma rec_qsum_lower_bound (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1/2) :
  ∀ᶠ (N : ℕ) in at_top, ∀ A : finset ℕ,
  ((log N)^(-ε/2) ≤ rec_sum A )
  → (∀ n ∈ A, ((1 - ε)*log(log N) ≤ ω n ) ∧ ( (ω n : ℝ) ≤ 2*(log (log N))))
  → (1 - 2*ε)*real.exp(-1)*log(log N)  ≤ ∑ q in ppowers_in_set A, (1/q : ℝ)
:=
begin
  filter_upwards [eventually_ge_at_top 0, and_another_large_N ε hε1 hε2,
      (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top 0),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
        (eventually_ge_at_top (1 : ℝ))],
  intros N hN hlarge0 hlarge1 hlarge2 A hrecA hreg,
  dsimp at hlarge1 hlarge2,
  have htemp0 : 0 < 1- ε, { rw sub_pos, exact lt_trans hε2 one_half_lt_one, },
  have htemp : 0 < (1-ε)*log(log N), { refine mul_pos htemp0 hlarge1, },
  have h0A : 0 ∉ A, { intro hbad, specialize hreg 0 hbad,
    rw nat.arithmetic_function.card_distinct_factors_zero at hreg,
    rw ← not_lt at hreg, exact hreg.1 htemp, },
  have hrecpos : (0:ℝ) < ∑ (q : ℕ) in ppowers_in_set A, 1 / q, {
    apply sum_pos, intros q hq, rw one_div_pos, norm_cast, rw pos_iff_ne_zero,
    intro hz, rw hz at hq, exact zero_not_mem_ppowers_in_set hq, refine ppowers_in_set_nonempty _,
    have hAne : A.nonempty, {
      rw nonempty_iff_ne_empty, intro he, rw [he, rec_sum_empty, ← not_lt] at hrecA,
      apply hrecA, norm_cast, refine rpow_pos_of_pos _ _, exact lt_of_lt_of_le zero_lt_one hlarge2,
    },
    rcases hAne with ⟨a,ha⟩, refine ⟨a,ha,_⟩, rw nat.two_le_iff, refine ⟨_,_⟩,
    intro ha0, rw ha0 at ha, specialize hreg 0 ha, rw ← not_lt at hreg, refine hreg.1 _,
    rw nat.arithmetic_function.card_distinct_factors_zero, norm_cast, exact htemp,
    intro ha1, rw ha1 at ha, specialize hreg 1 ha, rw ← not_lt at hreg, refine hreg.1 _,
    rw (nat.arithmetic_function.card_distinct_factors_eq_card_factors_iff_squarefree _).mpr _,
    rw nat.arithmetic_function.card_factors_one, norm_cast, exact htemp,
    exact one_ne_zero, exact squarefree_one,
  },
  have htemp1 : 0 < (1 - ε) / (1 + ε ^ 2) * (exp (-1) * log (log N)), {
   refine mul_pos _ _, refine div_pos _ _,
   rw [sub_pos], exact lt_trans hε2 one_half_lt_one,
   refine lt_trans zero_lt_one _, refine lt_add_of_pos_right _ _, exact sq_pos_of_pos hε1,
   refine mul_pos (exp_pos (-1)) hlarge1,
  },
  by_cases hdone : (1 - ε)*log(log N) < ∑ q in ppowers_in_set A, (1/q : ℝ),
  refine le_trans _ (le_of_lt hdone), rw [mul_le_mul_right],
  calc _ ≤ exp(-1) :_
     ... ≤ (1:ℝ)/2 :_
     ... ≤ _ :_,
  refine decidable.mul_le_of_le_one_left _ _, exact le_of_lt (exp_pos (-1)), rw sub_le_self_iff,
  refine le_of_lt (mul_pos zero_lt_two hε1), refine le_trans (le_of_lt exp_neg_one_lt_d9) _, norm_num1,
  nth_rewrite 2 ← add_halves' (1:ℝ), rw [← add_sub, le_add_iff_nonneg_right, sub_nonneg],
  exact le_of_lt hε2, exact hlarge1,
  calc _ ≤ (1-ε)*((1-ε)/(1+ε^2))*real.exp(-1)*log(log N) :_
     ... ≤ _ :_,
  rw [mul_le_mul_right, mul_le_mul_right], exact triv_ε_estimate ε hε1 hε2, exact exp_pos (-1),
  exact hlarge1, rw [mul_assoc, mul_assoc, ← le_div_iff],
  rw ← rpow_le_rpow_iff _ _ htemp, nth_rewrite 0 ← exp_log htemp0, rw [← exp_mul, ← mul_assoc,
    mul_comm _ (log(log N)), exp_mul, exp_log],
  calc _ ≤ (log N)^(-ε/2) :_
     ... ≤ _ :_,
  apply rpow_le_rpow_of_exponent_le, exact hlarge2, exact help_ε_estimate ε hε1 hε2,
  refine le_trans hrecA _,
  let I := (finset.range(⌊2*(log (log N))⌋₊+1)).filter( λ n : ℕ,
     (1 - ε)*log(log N) ≤ n),
  calc _ ≤ ∑ t in I, (∑ q in ppowers_in_set A, (1/q : ℝ))^t/(nat.factorial t) :_
     ... ≤ ∑ t in I, ((∑ q in ppowers_in_set A, (1/q : ℝ)) / (t*exp(-1)))^t :_
     ... ≤ _ :_,
  refine rec_sum_le_prod_sum h0A _, intros n hn, specialize hreg n hn,
  rw [mem_filter, mem_range], refine ⟨_,hreg.1⟩, rw nat.lt_succ_iff,
  refine nat.le_floor hreg.2, refine sum_le_sum _, intros t ht,
  rw [div_pow, div_le_div_left], exact factorial_bound t, apply pow_pos,
  exact hrecpos, norm_cast, exact nat.factorial_pos t,
  apply pow_pos, refine mul_pos _ (exp_pos (-1)), norm_cast, rw pos_iff_ne_zero,
  intro hz, rw [hz, mem_filter, ← not_lt] at ht, refine ht.2 _, norm_cast, exact htemp,
  calc _ ≤ (I.card : ℝ) * ((∑ (q : ℕ) in ppowers_in_set A, 1 / q) /
        ((1 - ε) * (exp (-1) * log (log N)))) ^ ((1 - ε) * log (log N)) :_
     ... ≤ (1+ε^2)^(((1 - ε) * log (log N))) * ((∑ (q : ℕ) in ppowers_in_set A, 1 / q) /
        ((1 - ε) * (exp (-1) * log (log N)))) ^ ((1 - ε) * log (log N)) :_
     ... = _ :_,
  refine sum_le_card_mul_real _, intros n hn, rw [mul_comm (exp(-1)), ← mul_assoc],
  refine helpful_decreasing_bound _ _ _, exact hrecpos, rw mem_filter at hn, exact hn.2,
  rw not_lt at hdone, exact hdone, rw mul_le_mul_right,
  calc _ ≤ ((finset.range(⌊2*(log (log N))⌋₊+1)).card :ℝ) :_
     ... = (⌊2*(log (log N))⌋₊:ℝ)+1 :_
     ... ≤ 2*(log (log N))+1 :_
     ... ≤ _ :_,
  norm_cast, refine finset.card_filter_le _ _, norm_cast, refine finset.card_range _,
  rw add_le_add_iff_right, refine nat.floor_le _, exact le_of_lt (mul_pos zero_lt_two hlarge1),
  exact hlarge0, apply rpow_pos_of_pos, refine div_pos hrecpos _,
  rw [← mul_assoc, mul_comm (1-ε), mul_assoc], refine mul_pos (exp_pos (-1)) htemp,
  rw [← mul_rpow], refine congr_fun (congr_arg rpow _) _,
  rw [mul_comm ((1-ε)/(1+ε^2)), mul_div, mul_div, div_div_eq_mul_div, div_eq_div_iff], ring_nf,
  refine ne_of_gt _, rw [← mul_assoc, mul_comm (1-ε), mul_assoc], refine mul_pos (exp_pos (-1)) htemp,
  refine ne_of_gt _, rw [mul_assoc], refine mul_pos (exp_pos (-1)) _, rw mul_comm, exact htemp,
  refine le_trans zero_le_one _, refine le_add_of_nonneg_right _, exact sq_nonneg ε,
  refine le_of_lt (div_pos hrecpos _),
  rw [← mul_assoc, mul_comm (1-ε), mul_assoc], refine mul_pos (exp_pos (-1)) htemp,
  exact lt_of_lt_of_le zero_lt_one hlarge2, rw [sub_nonneg], exact le_of_lt (lt_trans hε2 one_half_lt_one),
  refine le_of_lt (div_pos hrecpos _), exact htemp1, exact htemp1,
end

lemma useful_rec_aux1 : ∃ C : ℝ, (0 < C) ∧ ∀ N k : ℕ, (1 ≤ k) → ∏ p in (finset.range(N+1)).filter(λ n, nat.prime n ),
    ((1:ℝ) + k/(p*(p-1))) ≤ C^k :=
begin
  have haux : ∃ C : ℝ, (0 < C) ∧ ∀ N : ℕ, ∏ p in (finset.range(N+1)).filter(λ n, nat.prime n ),
    ((1:ℝ) + 1/(p*(p-1))) ≤ C, {
    have ht : ∀ (n : ℕ), log (1 + 1 / (n * (n - 1))) ≤ 2*(1/n^(2:ℝ)),
    { intro i,
            by_cases hi2 : i = 0,
        rw hi2, simp only [div_zero, le_refl, add_zero, neg_zero',
         real.log_one, zero_sub, nat.cast_zero, zero_mul,
         mul_neg, real.rpow_two, zero_pow'],
        rw [zero_pow', div_zero, mul_zero],
        exact ne_of_gt zero_lt_two,
        by_cases hi3 : i = 1,
        rw hi3, simp only [div_zero, one_pow, zero_le_one, add_zero,
        real.log_one, zero_le_bit0, real.rpow_two, nat.cast_one,
         div_one, mul_zero, sub_self], norm_num1,
        have h3 : 2 ≤ i, {
        have : i.pred.succ = i, { apply nat.succ_pred_eq_of_pos,
          exact nat.pos_of_ne_zero hi2, },
        rw ← this, apply nat.succ_lt_succ, apply nat.pos_of_ne_zero,
        intro hf, rw hf at this, apply hi3, rw nat.one_succ_zero,
        exact eq.symm this, },
        apply @le_trans _ _ _ ((1:ℝ)+1/(i*(i-1))-1) _,
        apply log_le_sub_one_of_pos,  refine add_pos zero_lt_one _,
        apply div_pos, exact zero_lt_one, apply mul_pos, norm_cast,
        exact nat.pos_of_ne_zero hi2, norm_cast, rw sub_pos, norm_cast,
        apply lt_of_lt_of_le one_lt_two h3,
        rw [add_tsub_cancel_left, mul_div, mul_one, div_le_div_iff, one_mul, mul_sub,
          mul_one, mul_sub, ← sq, le_sub, rpow_two, ← sub_one_mul, sq,
           ← mul_assoc, mul_le_mul_right],
        norm_num1, rw one_mul, norm_cast, exact h3, norm_cast, exact nat.pos_of_ne_zero hi2,
        apply mul_pos, norm_cast, apply lt_of_lt_of_le zero_lt_two h3,
        rw sub_pos, norm_cast, apply lt_of_lt_of_le one_lt_two h3,
        rw [rpow_two, sq_pos_iff], norm_cast, exact hi2, },
     let C :=  tsum (λ (n: ℕ), (2:ℝ) *(1/ (n ^ ((2:ℝ))))),
     refine ⟨real.exp(C),real.exp_pos C,_⟩,
     have hsum : summable (λ (b : ℕ), log (1 + 1 / (b * (b - 1)))), {
       have : ∃ (T : ℝ), is_lub (set.range (λ (s : finset ℕ),
         ∑ (a : ℕ) in s, log (1 + 1 / (a * (a - 1))))) T, {
           apply exists_is_lub, use 0, rw set.mem_range,
           use ∅, exact sum_empty,
           rw bdd_above, use C, rw mem_upper_bounds, intros x hx,
           rw set.mem_range at hx, cases hx with y hy, rw ← hy,
           apply @le_trans _ _ _ (∑ n in y,  (2:ℝ)*(1/ (n ^ ((2:ℝ))))) _,
           apply sum_le_sum, intros i hi,
           exact ht i,
           apply sum_le_tsum, intros b hb, apply mul_nonneg, exact zero_le_two,
           apply div_nonneg, exact zero_le_one, rw rpow_two,
           exact sq_nonneg (b:ℝ), rw ← summable_mul_left_iff,
           rw summable_one_div_nat_rpow, exact one_lt_two,
           exact ne_of_gt zero_lt_two,
           },
      cases this with T hlub,
      have h2 : has_sum (λ (b : ℕ), log (1 + 1 / (↑b * (↑b - 1)))) T, {
        apply has_sum_of_is_lub_of_nonneg, intro b,
        apply log_nonneg, apply le_add_of_nonneg_right, apply div_nonneg, exact zero_le_one,
        rw mul_comm, exact my_mul_thing, exact hlub,
        },
    refine has_sum.summable h2,
    },
     intro N, rw [← log_le_log, log_exp, log_prod],
     apply @le_trans _ _ _ (tsum (λ (n:ℕ), log (1 + 1 / (n * (n - 1))))) _,
     apply sum_le_tsum, intros b hb, apply log_nonneg,
     apply le_add_of_nonneg_right, apply div_nonneg, exact zero_le_one,
     rw mul_comm, exact my_mul_thing, exact hsum,
 apply tsum_le_tsum, exact ht, exact hsum,  rw ← summable_mul_left_iff,
        rw summable_one_div_nat_rpow, exact one_lt_two,
        exact ne_of_gt zero_lt_two, intros x hx,
        apply ne_of_gt, apply add_pos, exact zero_lt_one,
        apply div_pos, exact zero_lt_one, rw mem_filter at hx,
         apply mul_pos, apply lt_of_le_of_lt zero_le_one, norm_cast,
    exact nat.prime.one_lt hx.2, rw sub_pos, norm_cast,
    exact nat.prime.one_lt hx.2, apply prod_pos,
    intros i hi, apply add_pos, exact zero_lt_one,
        apply div_pos, exact zero_lt_one, rw mem_filter at hi,
         apply mul_pos, apply lt_of_le_of_lt zero_le_one, norm_cast,
    exact nat.prime.one_lt hi.2, rw sub_pos, norm_cast,
    exact nat.prime.one_lt hi.2, exact exp_pos C,
    },
  rcases haux with ⟨C,hC,hN⟩, refine ⟨C,hC,_⟩, intros N k hk,
  specialize hN N,
  rw [← @real.rpow_le_rpow_iff _ _ k, rpow_nat_cast, rpow_nat_cast] at hN,
  apply le_trans _ hN, rw ← prod_pow, refine finset.prod_le_prod _ _,
  intros i hi, apply le_trans zero_le_one, apply le_add_of_nonneg_right,
  apply div_nonneg, norm_cast, apply le_trans zero_le_one hk, apply mul_nonneg,
  exact nat.cast_nonneg i, rw mem_filter at hi, rw sub_nonneg, norm_cast,
  exact le_of_lt (nat.prime.one_lt hi.2), intros i hi, rw mem_filter at hi,
  rw ← mul_one_div, apply one_add_mul_le_pow, rw le_div_iff, apply le_trans _ zero_le_one,
  apply mul_nonpos_of_nonpos_of_nonneg, rw neg_nonpos, exact zero_le_two,
  apply mul_nonneg, exact nat.cast_nonneg i,
  rw sub_nonneg, norm_cast, exact le_of_lt (nat.prime.one_lt hi.2),
  apply mul_pos, apply lt_of_le_of_lt zero_le_one, norm_cast,
  exact nat.prime.one_lt hi.2, rw sub_pos, norm_cast,
  exact nat.prime.one_lt hi.2, apply finset.prod_nonneg,
  intros i hi, apply le_trans zero_le_one, apply le_add_of_nonneg_right,
  apply div_nonneg, norm_cast, exact zero_le_one, apply mul_nonneg,
  exact nat.cast_nonneg i, rw mem_filter at hi, rw sub_nonneg, norm_cast,
  exact le_of_lt (nat.prime.one_lt hi.2), exact le_of_lt hC, norm_cast,
  exact lt_of_lt_of_le zero_lt_one hk,
end

lemma useful_rec_aux3 :  ∃ C : ℝ, (0 < C) ∧ ∀ y : ℝ, ∀ N : ℕ, (1 < y) → (y < N) → ∏ p in
  (finset.range(N+1)).filter(λ n, nat.prime n ∧ y < n ), ((1:ℝ) + 1/(p-1)) ≤ C * |log(N)|/|log(y)| :=
begin
  rcases weak_mertens_third_upper_all with ⟨u,hu,hupp⟩,
  rcases weak_mertens_third_lower_all with ⟨l,hl,hlow⟩,
  refine ⟨u/l, div_pos hu hl,_⟩,
  intros y N hy hyN,
  have haux2 : ∏ p in (finset.range(N+1)).filter(λ n, nat.prime n ∧ y < n ), ((1:ℝ) + 1/(p-1))
    = (∏ p in (finset.range(N+1)).filter(λ n, nat.prime n ), ((1:ℝ) + 1/(p-1)))
    / ∏ p in  (finset.range(N+1)).filter(λ n, nat.prime n ∧ (n:ℝ) ≤ y ), ((1:ℝ) + 1/(p-1)), {
    have : (finset.range(N+1)).filter(λ n, nat.prime n ) \
      (finset.range(N+1)).filter(λ n, nat.prime n ∧ (n:ℝ) ≤ y )
      = (finset.range(N+1)).filter(λ n, nat.prime n ∧ y < n ), {
        ext, split, intro ha, rw finset.mem_filter,
        rw [finset.mem_sdiff, finset.mem_filter, finset.mem_filter, not_and_distrib] at ha,
        refine ⟨ha.1.1, ha.1.2,_⟩,
        cases ha.2 with hn1 hn2, exfalso, exact hn1 ha.1.1,
        rw not_and_distrib at hn2,
        cases hn2 with hn3 hn4, exfalso, exact hn3 ha.1.2,
        exact lt_of_not_ge hn4,
        intro ha, rw finset.mem_filter at ha,
        rw [finset.mem_sdiff, finset.mem_filter],
        refine ⟨⟨ha.1,ha.2.1⟩,_⟩, intro ha2,
        rw [finset.mem_filter, ← not_lt] at ha2, exact ha2.2.2 ha.2.2,
       },
      rw [eq_div_iff, ← this], apply prod_sdiff,
      intros n hn, rw finset.mem_filter, rw finset.mem_filter at hn,
      refine ⟨hn.1,hn.2.1⟩, refine ne_of_gt (prod_pos _),
      intros i hi, refine lt_of_lt_of_le zero_lt_one _,
      rw le_add_iff_nonneg_right, refine div_nonneg zero_le_one _,
      rw [le_sub, sub_zero], rw finset.mem_filter at hi,
      exact_mod_cast le_of_lt (nat.prime.one_lt hi.2.1),
  },
  rw haux2, clear haux2,
  have hNaux : (2:ℝ) ≤ N, { norm_cast, rw nat.succ_le_iff, exact_mod_cast lt_trans hy hyN,},
  specialize hupp N hNaux, simp_rw [norm_eq_abs] at hupp,
  specialize hlow y (le_of_lt hy),  simp_rw [norm_eq_abs] at hlow,
  rw partial_euler_product at hupp, rw [mul_comm, mul_div, div_div],
  apply div_le_div, exact mul_nonneg (abs_nonneg (log N)) (le_of_lt hu),
  rw mul_comm, refine le_trans _ hupp, rw abs_prod,
  apply @le_trans _ _ _
        ( ∏ (x : ℕ) in filter nat.prime (Icc 1 ⌊(N:ℝ)⌋₊), ((1:ℝ)+1/(x-1))) _,
  apply prod_of_subset_le_prod_of_ge_one, intros n hn,
  rw [finset.mem_filter, finset.mem_Icc, nat.floor_coe],
  rw [finset.mem_filter, finset.mem_range, nat.lt_succ_iff] at hn,
  refine ⟨_,hn.2⟩, refine ⟨le_of_lt (nat.prime.one_lt hn.2),hn.1⟩,
  intros i hi, refine add_nonneg zero_le_one (div_nonneg zero_le_one _),
  rw [le_sub, sub_zero], rw finset.mem_filter at hi,
  exact_mod_cast le_of_lt (nat.prime.one_lt hi.2),
  intros i hi hi2, apply le_add_of_nonneg_right, refine div_nonneg zero_le_one _,
  rw [le_sub, sub_zero], rw finset.mem_filter at hi,
  exact_mod_cast le_of_lt (nat.prime.one_lt hi.2),
  apply prod_le_prod, intros i hi,
  refine add_nonneg zero_le_one (div_nonneg zero_le_one _),
  rw [le_sub, sub_zero], rw finset.mem_filter at hi,
  exact_mod_cast le_of_lt (nat.prime.one_lt hi.2),
  intros i hi, rw finset.mem_filter at hi,
  have : (1:ℝ) < i, { exact_mod_cast nat.prime.one_lt hi.2, },
  apply le_of_eq, exact useful_identity i this,
  apply mul_pos, exact hl, apply abs_pos_of_pos, exact log_pos hy,
  apply le_trans hlow,
  rw [partial_euler_product, abs_prod],
  apply @le_trans _ _ _ (∏ (x : ℕ) in filter nat.prime (Icc 1 ⌊y⌋₊), ((1:ℝ)+1/(x-1))) _,
  apply prod_le_prod, intros i hi, exact abs_nonneg _,
  intros i hi,
  rw finset.mem_filter at hi,
  have h1i : (1:ℝ) < i, { exact_mod_cast nat.prime.one_lt hi.2, },
  apply ge_of_eq, exact useful_identity i h1i,
  apply prod_of_subset_le_prod_of_ge_one,
  intros x hx, rw finset.mem_filter, rw finset.mem_filter at hx,
  rw finset.mem_range, rw finset.mem_Icc at hx,
  have : (x: ℝ) ≤ y, { rw ← nat.le_floor_iff, exact hx.1.2, exact le_trans zero_le_one (le_of_lt hy), },
  refine ⟨_,hx.2,this⟩, rw nat.lt_succ_iff,
  exact_mod_cast le_trans this (le_of_lt hyN),
  intros i hi, apply add_nonneg, exact zero_le_one,
  apply mul_nonneg, exact zero_le_one, rw [inv_nonneg, sub_nonneg],
  rw finset.mem_filter at hi, exact_mod_cast (le_of_lt (nat.prime.one_lt hi.2.1)),
  intros i hi1 hi2, rw le_add_iff_nonneg_right, apply div_nonneg,
  exact zero_le_one, rw sub_nonneg, rw finset.mem_filter at hi1,
  exact_mod_cast (le_of_lt (nat.prime.one_lt hi1.2.1)),
end

lemma useful_rec_aux2 :  ∃ C : ℝ, (0 < C) ∧ ∀ y : ℝ, ∀ N k : ℕ, (1 ≤ k) → (1 < y) →
  (y < N) → ∏ p in
  (finset.range(N+1)).filter(λ n, nat.prime n ∧ y < n ),
    ((1:ℝ) + k/(p-1)) ≤ (C * |log(N)|/|log(y)|)^k :=
begin
  rcases useful_rec_aux3 with ⟨C,hC,hN⟩, refine ⟨C,hC,_⟩, intros y N k hk hy hyN,
  specialize hN y N hy hyN,
  apply @le_trans _ _ _ (( ∏ p in (finset.range(N+1)).filter(λ n, nat.prime n ∧ y < n ),
    ((1:ℝ) + 1/(p-1)) )^k) _,
  rw ← prod_pow, apply prod_le_prod, intros i hi, apply add_nonneg, exact zero_le_one,
  refine div_nonneg (nat.cast_nonneg k) _,
  rw [sub_nonneg], rw finset.mem_filter at hi,
  exact_mod_cast (le_of_lt (nat.prime.one_lt hi.2.1)),
  intros i hi,  rw ← mul_one_div,
  apply one_add_mul_le_pow,  apply @le_trans _ _ _ (0:ℝ) _,
  simp only [right.neg_nonpos_iff, zero_le_one, zero_le_bit0],
  refine div_nonneg zero_le_one _, rw [sub_nonneg], rw finset.mem_filter at hi,
  exact_mod_cast (le_of_lt (nat.prime.one_lt hi.2.1)),
   refine pow_le_pow_of_le_left _ hN _,
  apply prod_nonneg, intros i hi, apply add_nonneg, exact zero_le_one,
  refine div_nonneg zero_le_one _, rw [sub_nonneg], rw finset.mem_filter at hi,
  exact_mod_cast (le_of_lt (nat.prime.one_lt hi.2.1)),
end



lemma nat.coprime_symmetric : symmetric coprime := λ n m h, h.symm

-- lemma symmetric.on {α β : Type*} {f : α → β} {r : β → β → Prop} (hr : symmetric r) :
--   symmetric (r on f) :=
-- begin
--   exact symmetric.comap hr f,
-- end

lemma is_multiplicative.prod {ι : Type*} (g : ι → ℕ) {f : nat.arithmetic_function ℝ}
  (hf : f.is_multiplicative) (s : finset ι) (hs : (s : set ι).pairwise (coprime on g)):
  ∏ i in s, f (g i) = f (∏ i in s, g i) :=
begin
  induction s using finset.cons_induction with a s has ih hs,
  { simp [hf] },
  rw [cons_eq_insert, coe_insert, set.pairwise_insert_of_symmetric (nat.coprime_symmetric.comap g)] at hs,
  rw [prod_cons, prod_cons, ih hs.1, hf.map_mul_of_coprime],
  exact nat.coprime_prod_right (λ i hi, hs.2 _ hi (hi.ne_of_not_mem has).symm),
end

-- lemma prod_sum' {α β δ : Type*} [decidable_eq α] [comm_semiring β] [decidable_eq δ]
--   {s : finset α} {t : α → finset δ} {f : δ → β} :
--   ∏ a in s, ∑ b in t a, f b =
--     ∑ p in s.pi t, ∏ x in s.attach, f (p x.1 x.2) :=
-- begin

--   -- rw prod_sum,
-- end

lemma my_sum_lemma {α β γ : Type*} [ordered_add_comm_monoid γ] {s : finset α} {t : finset β}
  (f : α → γ) (g : β → γ) (r : Π i ∈ s, β) (r_inj : ∀ a₁ a₂ ha₁ ha₂, r a₁ ha₁ = r a₂ ha₂ → a₁ = a₂)
  (hg : ∀ i ∈ t, 0 ≤ g i) (rt : ∀ a ha, r a ha ∈ t) (fr : ∀ a ha, g (r a ha) = f a) :
  ∑ i in s, f i ≤ ∑ j in t, g j :=
begin
  have : ∑ i in s.attach, f i = ∑ i in s.attach, g (r i i.prop),
  { simp_rw [fr] },
  rw [←sum_attach, this, ←sum_image],
  { refine sum_le_sum_of_subset_of_nonneg _ (λ _ q _, hg _ q),
    simp only [finset.subset_iff, subtype.coe_mk, mem_image, mem_attach, exists_true_left,
      subtype.exists, bex_imp_distrib],
    rintro _ _ _ rfl,
    exact rt _ _ },
  exact λ _ _ _ _ h, subtype.ext (r_inj _ _ _ _ h),
end

lemma prod_one_add {D : finset ℕ}
  (f : nat.arithmetic_function ℝ) (hf' : f.is_multiplicative) (hf'' : ∀ i, 0 ≤ f i):
  ∑ d in D, f d ≤
    ∏ p in D.bUnion (λ n, n.factors.to_finset),
      (1 + ∑ q in (ppowers_in_set D).filter (λ q, p ∣ q), f q) :=
begin
  simp only [add_comm (1 : ℝ)],
  simp_rw [prod_add, prod_const_one, mul_one],
  change ∑ d in D, f d ≤
    ∑ x in finset.powerset _,
      ∏ t in _,
        ∑ i in filter (λ q, t ∣ q) _, f i,
  -- sorry
  simp_rw [prod_sum],
  dsimp,
  rw sum_sigma',
  dsimp,
  refine my_sum_lemma _ _ _ _ _ _ _,
  { intros d hd,
    exact ⟨(D.bUnion (λ n, n.factors.to_finset)).filter (λ z, z ∣ d),
           λ p hp, p ^ d.factorization p⟩ },
  { intros d₁ d₂ hd₁ hd₂ h,
    dsimp at h,
    simp only [eq_self_iff_true, heq_iff_eq, true_and] at h,
    sorry },
  { intros i hi,
    apply prod_nonneg,
    intros j hj,
    apply hf'' },
  { intros d hd,
    dsimp,

    simp only [mem_sigma, mem_powerset_self, finset.mem_pi, mem_bUnion, list.mem_to_finset,
      exists_prop, mem_filter, forall_exists_index, and_imp, true_and],
    sorry
     },
  { intros d hd,
    dsimp,
    -- rw prod_attach,
    -- refine (@prod_attach _ _ _ _ _).trans _,
    sorry },

  -- have := sum_le_sum_of_subset_of_nonneg,
  -- simp only [subtype.val_eq_coe],

  -- simp only [prod_attach],

  -- have : ∀ x ∈ (D.bUnion (λ (n : ℕ), filter nat.prime n.divisors)).powerset,
  --   ∏ (a : ℕ) in D.bUnion (λ (n : ℕ), filter nat.prime n.divisors) \ x,
  --     (filter (λ q, a ∣ q) (ppowers_in_set D)).sum ⇑f = f sorry,
  -- { intros x hx,
  --   simp only [mem_powerset] at hx,

  -- },
  -- rw sum_powerset,
  -- rw finset.prod_power
  -- refine finset.induction_on D _ _,
  -- { simp },
  -- intros a s has ih,

end

lemma useful_rec_aux4 (y : ℝ) (k N : ℕ) (D : finset ℕ)
  (hD : ∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) :
  ∑ d in D, (k : ℝ) ^ ω d / d ≤
    (∏ p in (finset.range (N+1)).filter nat.prime, (1 + k / (p * (p - 1)))) *
    (∏ p in (finset.range (N+1)).filter (λ n, nat.prime n ∧ y < n), (1 + k * (p - 1)⁻¹)) :=
begin
  have h₁ : ∑ d in D, (k : ℝ) ^ ω d / d ≤  ∏ p in D.bUnion (λ n, n.factors.to_finset),
     (1 + ∑ q in (ppowers_in_set D).filter (λ q, p ∣ q), k/q),
  { let f : nat.arithmetic_function ℝ := ⟨λ d, (k : ℝ) ^ ω d / d, by simp⟩,
    have hf' : f.is_multiplicative := sorry,
    have hf'' : ∀ i, 0 ≤ f i := sorry,
    refine (prod_one_add f hf' hf'').trans_eq _,
    sorry },
  have : D.bUnion (λ n, n.factors.to_finset) ⊆ (finset.range (N+1)).filter nat.prime,
  { sorry },
  apply h₁.trans _,
  refine ((prod_of_subset_le_prod_of_one_le this _ _).trans _),
  { sorry },
  { sorry },
  sorry,
end

lemma useful_rec_bound : ∃ C : ℝ, (0 < C) ∧ ∀ y : ℝ, ∀ k N : ℕ, ∀ D : finset ℕ,
  ((1 < y) → (y < N) → (1 ≤ k) → (∀ q : ℕ, q ∈ ppowers_in_set D → (y < q) ∧ q ≤ N) →
  ∑ d in D, (k:ℝ)^(ω d) / d ≤ (C* |log(N)|/|log(y)|)^k) :=
begin
 rcases useful_rec_aux1 with ⟨C_1,hC_1,hprod1⟩,
 rcases useful_rec_aux2 with ⟨C_2,hC_2,hprod2⟩,
 refine ⟨C_1*C_2, mul_pos hC_1 hC_2, _⟩,
 intros y k N D hy hyN hk hq, specialize hprod1 N k hk, specialize hprod2 y N k hk hy hyN,
 obtain h := useful_rec_aux4,
 specialize h y k N D hq,
 apply le_trans h, rw [mul_assoc, ← mul_div, mul_pow],
 apply mul_le_mul hprod1 hprod2, apply prod_nonneg,
 intros i hi, apply le_trans zero_le_one, apply le_add_of_nonneg_right,
 apply div_nonneg, norm_cast, exact le_trans zero_le_one hk,
 rw finset.mem_filter at hi, rw sub_nonneg, exact_mod_cast (le_of_lt (nat.prime.one_lt hi.2.1)),
 exact pow_nonneg (le_of_lt hC_1) k,
end

lemma find_good_d_aux1 : ∀ᶠ (N : ℕ) in at_top, ∀ M u y : ℝ, ∀ q : ℕ, ∀ A ⊆ finset.range(N+1),
 (0 < M) → (M ≤ N) → (0 ≤ u) →
 ∀ d ∈ (finset.range(N+1)).filter( λ d, (∀ r : ℕ, is_prime_pow r → r ∣ d →
  coprime r (d/r) → y < r ∧ r ≤ N) ∧ M*u < q*d ∧ q*d ≤ N),
   ((∑ n in  (local_part A q).filter(λ n, (q*d)∣n
     ∧ coprime (q*d) (n/(q*d)) ), (q:ℚ)/n) : ℝ) ≤ 2*(log N)/d :=
begin
  filter_upwards [eventually_ge_at_top 0, harmonic_sum_bound_two],
  intros N hN hharmonic M u y q A hA hM hMN hu d hd,
  let X := (local_part A q).filter(λ n, (q*d)∣n ∧ coprime (q*d) (n/(q*d)) ),
  have hDnotzero : d ≠ 0, {
   intro hzd, rw finset.mem_filter at hd,
   obtain hd' := hd.2.2.1,rw hzd at hd', push_cast at hd', rw mul_zero at hd',
   apply (lt_iff_not_ge (M*u) 0).mp hd', apply mul_nonneg, exact le_of_lt hM,
   exact hu,
  },
  have hrectrivialaux : ((∑ n in X, (q:ℚ)/n)) ≤
    ∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), (q/n), {
      apply sum_le_sum_of_subset_of_nonneg, intros x hx,
      rw finset.mem_filter at hx, rw mem_filter,
      refine ⟨hA (mem_of_mem_filter x hx.1),hx.2.1⟩,
      intros i hi1 hi2, apply div_nonneg, exact nat.cast_nonneg q,
      exact nat.cast_nonneg i,
  },
  have hrectrivial' : ((∑ n in X, (q:ℚ)/n):ℝ) ≤
    ∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), (q/n), {
      calc _ = ((((∑ n in X, (q:ℚ)/n)):ℚ):ℝ) :_
        ... ≤ ((∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), (q/n):ℚ):ℝ) :_
        ... ≤ _ :_,
      rw rat.cast_sum, push_cast, exact_mod_cast hrectrivialaux,
      rw rat.cast_sum, push_cast,
  },
  apply le_trans hrectrivial',
  have hrectrivial'' : ∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), ((q : ℝ)/n)
      ≤ (1/d)*∑ m in (finset.range(N+1)).filter(λ x, q*d*x ≤ N), (1/m), {
      let g := (λ n : ℕ, n/(q*d)),
      rw mul_sum, refine sum_le_sum_of_inj g _ _ _ _,
      intros n hn, apply mul_nonneg, rw one_div_nonneg, exact nat.cast_nonneg d,
      rw one_div_nonneg, exact nat.cast_nonneg n, intros n hn,
      rw [mem_filter, mem_range] at hn,
      rw [mem_filter, mem_range, nat.mul_div_cancel_left', ← nat.lt_succ_iff],
      refine ⟨_,hn.1⟩, refine lt_of_le_of_lt _ hn.1,
      refine nat.div_le_self' _ _, exact hn.2, intros a ha b hb hab,
      rw nat.div_left_inj at hab, exact hab, rw mem_filter at ha, exact ha.2,
      rw mem_filter at hb, exact hb.2, intros n hn,
      have : (g n : ℝ) = (n:ℝ)/(q*d), {
        rw [nat.cast_div, nat.cast_mul], rw mem_filter at hn, exact hn.2,
        rw mem_filter at hd, intro hz, rw ← not_le at hd, apply hd.2.2.1,
        rw nat.cast_mul at hz, rw hz, refine mul_nonneg (le_of_lt hM) hu,
        },
      rw [this, one_div_mul_one_div, mul_div, one_div_div, mul_comm (q:ℝ), mul_div_mul_left],
      norm_cast, exact hDnotzero,
  },
  refine le_trans hrectrivial'' _, rw le_div_iff, rw mul_comm, rw ← mul_assoc, rw mul_one_div_cancel,
  rw one_mul,
  have hrectrivial''' : ∑ m in (finset.range(N+1)).filter(λ x, q*d*x ≤ N), ((1 : ℝ)/m)
      ≤  ∑ n in finset.range(N+1), (1 : ℝ)/n, {
        apply sum_le_sum_of_subset_of_nonneg, refine filter_subset _ _,
        intros i hi1 hi2, rw one_div_nonneg, exact nat.cast_nonneg i,
  },
  apply le_trans hrectrivial''' hharmonic, norm_cast, exact hDnotzero, norm_cast,
  rw pos_iff_ne_zero, exact hDnotzero,
end

lemma find_good_d_aux2 : ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ k : ℕ,
  ∀ A ⊆ finset.range(N+1), (0 < M) →
  (M ≤ N) → (1 ≤ k)
  → (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n) : ℝ) < (log N)^((1:ℝ)/k)) →
  ∀ q ∈ ppowers_in_set A,  ∀ n ∈ local_part A q,
  ∃ d ∈ (finset.range(N+1)).filter( λ d, (∀ r : ℕ, is_prime_pow r → r ∣ d → coprime r (d/r) →
     real.exp((log N)^((1:ℝ) - 2/k)) < r ∧ r ≤ N) ∧ M*real.exp(-(log N)^((1:ℝ) - 1/k)) < q*d ∧ q*d ≤ N),
 (q*d ∣ n) ∧ coprime (q*d) (n/(q*d)) :=
begin
  filter_upwards [eventually_gt_at_top 1],
  intros N hlargeN M k A hA hM hMN hk hAreg q hq n hn,
  have hN : 0 < N, { exact lt_trans zero_lt_one hlargeN, },
    let Q := n.divisors.filter(λ r, is_prime_pow r ∧ coprime r (n/r) ∧
       r ≠ q ∧ real.exp((log N)^((1:ℝ) - 2/k)) < r),
    let d := ∏ r in Q, r,
    have hnz : n ≠ 0, {
        intro hnz2,
        specialize hAreg 0, rw [local_part, hnz2] at hn,
        obtain htemp := hAreg (mem_of_mem_filter 0 hn),
        rw lt_iff_not_ge at hM, apply hM, exact_mod_cast htemp.1,
      },
    have hnN : n ≤ N, {
      rw [← nat.lt_succ_iff, ← finset.mem_range],
     exact hA (mem_of_mem_filter n hn), },
    have hqdcop : coprime q d, {
      by_contra, rw [local_part,mem_filter] at hn,
      rw prime_pow_not_coprime_prod_iff at h,
      rcases h with ⟨p,kq,kd,d,hd,h⟩, rw mem_filter at hd,
      apply hd.2.2.2.1, rw [← h.2.2.2.1, ← h.2.2.2.2], refine congr_arg (pow p) _,
      calc kd = n.factorization p : _
           ... = kq :_,
      apply coprime_div_iff, exact h.1, rw h.2.2.2.2,
      exact nat.dvd_of_mem_divisors hd.1, exact h.2.2.1, rw h.2.2.2.2,
      exact hd.2.2.1, refine eq.symm _,  apply coprime_div_iff, exact h.1, rw h.2.2.2.1,
      exact hn.2.1, exact h.2.1, rw h.2.2.2.1, exact hn.2.2,
      rw [ppowers_in_set,mem_bUnion] at hq, rcases hq with ⟨a,ha,hq⟩,
      rw mem_filter at hq, exact hq.2.1, intros d hd, rw mem_filter at hd,
      exact hd.2.1,
     },
    have hQcoprime : ∀ (a : ℕ), a ∈ n.divisors.filter(λ r, is_prime_pow r ∧ coprime r (n/r))
     → ∀ (b : ℕ), b ∈ n.divisors.filter(λ r, is_prime_pow r ∧ coprime r (n/r)) → a ≠ b
     → a.coprime b, {
      intros a ha b hb hab, rw mem_filter at ha,
      rw mem_filter at hb, by_contra,
      rw prime_pow_not_coprime_iff at h, apply hab,
      rcases h with ⟨p,ka,kb,h⟩,
      rw [← h.2.2.2.1, ← h.2.2.2.2], refine congr_arg (pow p) _,
      calc ka = n.factorization p : _
           ... = kb :_,
      apply coprime_div_iff, exact h.1, rw h.2.2.2.1,
      exact nat.dvd_of_mem_divisors ha.1, exact h.2.1, rw h.2.2.2.1,
      exact ha.2.2, refine eq.symm _, apply coprime_div_iff, exact h.1,
      rw h.2.2.2.2, exact nat.dvd_of_mem_divisors hb.1, exact h.2.2.1,
      rw h.2.2.2.2, exact hb.2.2, exact ha.2.1, exact hb.2.1,
    },
    have hqd : q*d ∣ n, { rw dvd_iff_ppowers_dvd, intros r hr1 hr2,
      rw nat.coprime.is_prime_pow_dvd_mul at hr1,
      cases hr1 with hr11 hr12, rw [local_part, mem_filter] at hn,
      exact dvd_trans hr11 hn.2.1, rw is_prime_pow_dvd_prod at hr12,
      rcases hr12 with ⟨t,ht,hr12⟩, rw mem_filter at ht,
      exact dvd_trans hr12 (nat.dvd_of_mem_divisors ht.1),
      intros a ha b hb hab, refine hQcoprime _ _ _ _ hab,
      rw mem_filter, rw mem_filter at ha, refine ⟨ha.1,ha.2.1,ha.2.2.1,⟩,
      rw mem_filter, rw mem_filter at hb, refine ⟨hb.1,hb.2.1,hb.2.2.1,⟩,
      exact hr2, exact hqdcop, exact hr2,
      },
    have hdupp : q*d ≤ N, { refine le_trans (nat.le_of_dvd _ hqd) hnN,
      have : (0:ℝ) < n, { refine lt_of_lt_of_le hM _,
        exact (hAreg n (mem_of_mem_filter n hn)).1, },
      exact_mod_cast this,
    },
        let Q' := n.divisors.filter(λ r, is_prime_pow r ∧ coprime r (n/r) ∧
       r ≠ q ∧ (r:ℝ) ≤ real.exp((log N)^((1:ℝ) - 2/k))),
    have hQ'dcop : coprime q (∏ r in Q', r), {
      by_contra, rw [local_part,mem_filter] at hn,
      rw prime_pow_not_coprime_prod_iff at h,
      rcases h with ⟨p,kq,kd,d,hd,h⟩, rw mem_filter at hd,
      apply hd.2.2.2.1, rw [← h.2.2.2.1, ← h.2.2.2.2], refine congr_arg (pow p) _,
      calc kd = n.factorization p : _
           ... = kq :_,
      apply coprime_div_iff, exact h.1, rw h.2.2.2.2,
      exact nat.dvd_of_mem_divisors hd.1, exact h.2.2.1, rw h.2.2.2.2,
      exact hd.2.2.1, refine eq.symm _,  apply coprime_div_iff, exact h.1, rw h.2.2.2.1,
      exact hn.2.1, exact h.2.1, rw h.2.2.2.1, exact hn.2.2,
      rw [ppowers_in_set,mem_bUnion] at hq, rcases hq with ⟨a,ha,hq⟩,
      rw mem_filter at hq, exact hq.2.1, intros d hd, rw mem_filter at hd,
      exact hd.2.1,
     },
    have hQ'qd : coprime (q*d) (∏ r in Q', r), {
      apply nat.coprime.symm,
      apply nat.coprime.mul_right, exact nat.coprime.symm hQ'dcop,
      rw prime_pow_prods_coprime, intros a ha b hb, refine hQcoprime _ _ _ _ _,
      rw mem_filter, rw mem_filter at ha, refine ⟨ha.1,ha.2.1,ha.2.2.1⟩,
      rw mem_filter, rw mem_filter at hb, refine ⟨hb.1,hb.2.1,hb.2.2.1⟩,
      intro hab, rw [hab, mem_filter] at ha, rw mem_filter at hb,
      rw lt_iff_not_ge at hb, exact hb.2.2.2.2 ha.2.2.2.2,
      intros a ha, rw mem_filter at ha, exact ha.2.1,
      intros a ha, rw mem_filter at ha, exact ha.2.1,
    },
    have hnqd : n = (∏ r in Q', r)*q*d, {
      rw eq_iff_ppowers_dvd, split,
      intros r hr1 hr2 hr3,
      by_cases hrq : r = q,
      rw [mul_comm _ q, mul_assoc], rw hrq, refine dvd_mul_right q _,
      by_cases hrsize : (r:ℝ) ≤ real.exp((log N)^((1:ℝ) - 2/k)),
      apply @nat.dvd_trans _ (∏ r in Q', r) _ _ _, apply dvd_prod_of_mem,
      rw mem_filter, refine ⟨_,hr2,hr3,hrq,hrsize⟩,
      rw nat.mem_divisors, refine ⟨hr1,hnz⟩, rw mul_assoc,
      refine dvd_mul_right _ _, apply @nat.dvd_trans _ d _ _ _,
      apply dvd_prod_of_mem, rw mem_filter, rw ← lt_iff_not_ge at hrsize,
      refine ⟨_,hr2,hr3,hrq,hrsize⟩, rw nat.mem_divisors, refine ⟨hr1,hnz⟩,
      refine dvd_mul_left _ _,
      intros r hr1 hr2 hr3, rw [mul_assoc, nat.coprime.is_prime_pow_dvd_mul,
       nat.coprime.is_prime_pow_dvd_mul] at hr1,
      cases hr1 with hw1 hw2,
      rw is_prime_pow_dvd_prod at hw1, rcases hw1 with ⟨t,ht,hw1⟩,
      apply dvd_trans hw1, rw mem_filter at ht, exact nat.dvd_of_mem_divisors ht.1,
      intros a ha b hb hab, refine hQcoprime _ _ _ _ hab,
      rw mem_filter, rw mem_filter at ha, refine ⟨ha.1,ha.2.1,ha.2.2.1⟩,
      rw mem_filter, rw mem_filter at hb, refine ⟨hb.1,hb.2.1,hb.2.2.1⟩,
      exact hr2, cases hw2 with hw3 hw4, rw [local_part, mem_filter] at hn,
      exact dvd_trans hw3 hn.2.1,
      refine dvd_trans hw4 (dvd_trans (dvd_mul_left _ _) hqd), exact hqdcop,
      exact hr2, exact nat.coprime.symm hQ'qd, exact hr2, exact hnz,
      rw mul_assoc, refine mul_ne_zero _ _, rw prod_ne_zero_iff,
      intros r hr, rw mem_filter at hr, intro hbad,
      have := is_prime_pow.pos hr.2.1, rw pos_iff_ne_zero at this, exact this hbad,
      intro hbad, apply hnz,  rw [hbad, zero_dvd_iff] at hqd, exact hqd,
     },
    use d, split, rw mem_filter, split, rw [mem_range, nat.lt_succ_iff],
    refine le_trans _ hdupp, apply nat.le_mul_of_pos_left,
    rw pos_iff_ne_zero, by_contra, rw h at hq,
    exact zero_not_mem_ppowers_in_set hq, split, intros r hr1 hr2 hr3,
    have hrQ : r ∈ Q, {
      refine prime_pow_dvd_prod_prime_pow hr1 _ _ hr2 hr3,
      intros a ha b hb hab, by_contra, rw mem_filter at ha, rw mem_filter at hb,
      have h' := prime_pow_not_coprime_prime_pow _ _ h,
      rcases h' with ⟨p,k,l,hp,hkl,hpa,hpb⟩,
      have hafac : n.factorization p = k, {
        rw [← factorization_eq_iff, hpa], refine ⟨nat.dvd_of_mem_divisors ha.1,ha.2.2.1⟩,
        rw nat.prime_iff, exact hp, exact hkl.1,
      },
      have hbfac : n.factorization p = l, {
        rw [← factorization_eq_iff, hpb], refine ⟨nat.dvd_of_mem_divisors hb.1,hb.2.2.1⟩,
        rw nat.prime_iff, exact hp, exact hkl.2,
      },
      apply hab, rw [← hpa, ← hpb, ← hafac, ← hbfac], exact ha.2.1, exact hb.2.1,
      intros t ht, rw mem_filter at ht, exact ht.2.1,
    },
    rw mem_filter at hrQ, refine ⟨hrQ.2.2.2.2,_⟩,
    exact le_trans ( nat.divisor_le hrQ.1) hnN, refine ⟨_,hdupp⟩,
    apply @lt_of_le_of_lt _ _ _ ((n:ℝ)*real.exp(-(log N)^((1:ℝ) - 1/k))) _,
    rw mul_le_mul_right,
    exact (hAreg n (mem_of_mem_filter n hn)).1, exact exp_pos _,
    rw hnqd, push_cast, rw mul_assoc (Q'.prod coe) (q:ℝ),
    rw mul_comm _ ((q:ℝ)*(Q.prod coe)), rw mul_assoc, apply mul_lt_of_lt_one_right,
    norm_cast,
    rw pos_iff_ne_zero, intro hzero, rw [hzero, zero_dvd_iff] at hqd,
    exact hnz hqd, rw [exp_neg, ← one_div, mul_one_div, div_lt_one],
    calc (Q'.prod coe) ≤ (real.exp((log N)^((1:ℝ) - 2/k)))^(Q'.card) : _
     ... < (real.exp((log N)^((1:ℝ) - 2/k)))^((log N)^((1:ℝ)/k)) : _
     ... = exp (log ↑N ^ ((1:ℝ) - 1 / ↑k)): _,
    apply prod_le_max_size, intros i hi, exact nat.cast_nonneg i,
    intros i hi, rw mem_filter at hi, exact hi.2.2.2.2,
    rw ← rpow_nat_cast, apply rpow_lt_rpow_of_exponent_lt, rw one_lt_exp_iff,
    apply rpow_pos_of_pos, apply log_pos, norm_cast, exact hlargeN,
    calc (Q'.card : ℝ) ≤ (n.divisors.filter(λ r, is_prime_pow r ∧ coprime r (n/r))).card : _
     ... = (ω n : ℝ) : _
     ... < (log N)^((1:ℝ)/k) : _,
    norm_cast, apply finset.card_le_of_subset, intros r hr, rw mem_filter at hr,
    rw mem_filter, refine ⟨hr.1,hr.2.1,hr.2.2.1⟩, norm_cast,
    exact omega_count_eq_ppowers, rw local_part at hn,
    specialize hAreg n (finset.mem_of_mem_filter n hn), exact hAreg.2,
    rw [← exp_mul, ← rpow_add, sub_add, div_sub_div_same], norm_num1, refl,
    apply log_pos, norm_cast, exact hlargeN, refine exp_pos _,
    refine ⟨hqd,_⟩, rw [hnqd, mul_assoc, nat.mul_div_cancel], exact hQ'qd,
    rw pos_iff_ne_zero, intro hzero, rw [hzero, zero_dvd_iff] at hqd,
    exact hnz hqd,
end

-- Lemma 5.4
lemma find_good_d : ∃ c C : ℝ, (0 < c) ∧ (0 < C) ∧ ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ k : ℕ,
  ∀ A ⊆ finset.range(N+1), (0 < M) → (M ≤ N) → (1 < k) →
  ((k:ℝ) ≤ c* log(log N))  → (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n) : ℝ) < (log N)^((1:ℝ)/k)) →
  (∀ q ∈ ppowers_in_set A,  (1/(log N) ≤ rec_sum_local A q) →
  (∃ d : ℕ,  ( M*real.exp(-(log N)^((1:ℝ) - 1/k)) < q*d ) ∧
  ( (ω d : ℝ) < (5/log k) * log(log N) ) ∧  ( C*(rec_sum_local A q) / (log N)^((2:ℝ)/k) ≤
      ∑ n in (local_part A q).filter(λ n, (q*d ∣ n) ∧
  (coprime (q*d) (n/(q*d)))), (q*d/n : ℝ)  ) ) )
  :=
begin
  rcases useful_rec_bound with ⟨C1,hC1,hrec1⟩,
  let C2 := max C1 2,
  let c := (1/2)/(log(C2)),
  have hc : 0 < c, { apply div_pos, apply half_pos, exact zero_lt_one,
    apply log_pos, refine lt_of_lt_of_le one_lt_two _,
    exact le_max_right C1 2, },
  let C := 1/(C1*2),
  have hC : 0 < C, { rw one_div_pos, exact mul_pos hC1 zero_lt_two,},
  have hC' : C1 = 1 / (C * 2), { rw [div_mul, mul_div_cancel, one_div_one_div], exact ne_of_gt zero_lt_two, },
  have hC2 : 1 < C2 := lt_of_lt_of_le one_lt_two (le_max_right C1 2),
  refine ⟨c,C,hc,hC,_⟩,
  filter_upwards [find_good_d_aux1, find_good_d_aux2,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually  (eventually_gt_at_top (1 : ℝ)),
    eventually_gt_at_top 0,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually  (eventually_ge_at_top (16 : ℝ))
    ],
  intros N haux1 haux2 hlarge hlarge' hlarge'' M k A hAN hzM hMN h1k hkN hAreg q hq hsumq,
  dsimp at hlarge,
  have hlarge1 : 0 < log N, { exact lt_trans zero_lt_one hlarge, },
  have hlarge2 : 4 * log N ^ (-((3:ℝ) / 2) + 1) ≤ 1, {
    norm_num1, rw [rpow_neg, ← one_div, mul_one_div, div_le_one],
    calc (4:ℝ) = (16)^((1:ℝ)/2) : _
         ... ≤ (log N)^((1:ℝ)/2) : _,
    rw ← sqrt_eq_rpow,
    have : (16:ℝ) = 4^2, { norm_num, },
    rw [this, sqrt_sq], exact le_of_lt zero_lt_four, apply rpow_le_rpow,
    norm_num1, exact hlarge'', exact le_of_lt one_half_pos,
    apply rpow_pos_of_pos, exact hlarge1, exact le_of_lt hlarge1,
   },
  let y := real.exp((log N)^((1:ℝ) - 2/k)),
  let u := real.exp(-(log N)^((1:ℝ) - 1/k)),
  have h1y : 1 < y, { rw one_lt_exp_iff, refine rpow_pos_of_pos hlarge1 _, },
  have hyN : y < N, { rw ← @exp_log (N:ℝ), rw exp_lt_exp,
    nth_rewrite 1 ← rpow_one (log N), apply rpow_lt_rpow_of_exponent_lt,
    exact hlarge, apply sub_lt_self, refine div_pos zero_lt_two _,
    refine lt_trans zero_lt_one _, exact_mod_cast h1k, exact_mod_cast hlarge',},
  have h0k : (0:ℝ) < k, { exact_mod_cast lt_trans zero_lt_one h1k, },
  let D := (finset.range(N+1)).filter( λ d, (∀ r : ℕ, is_prime_pow r → r ∣ d → coprime r (d/r) →
     y < r ∧ r ≤ N) ∧ M*u < q*d ∧ q*d ≤ N),
  specialize haux2 M k A hAN hzM hMN (le_of_lt h1k) hAreg q hq,
  specialize haux1 M u y q A hAN hzM hMN (le_of_lt (real.exp_pos _)),
  let new_local := (λ d : ℕ, (local_part A q).filter(λ n, (q*d)∣n
     ∧ coprime (q*d) (n/(q*d)) )),
  have hlocal2 : local_part A q ⊆ D.bUnion (λ d, new_local d),
  { intros n hn, rw finset.mem_bUnion, specialize haux2 n hn,
    rcases haux2 with ⟨d,hd,hlocal⟩, refine ⟨d,hd,_⟩, rw finset.mem_filter,
    refine ⟨hn,hlocal⟩, },
  have hrecbound : rec_sum_local A q ≤ ∑ d in D, ∑ n in new_local d, (q:ℚ)/n,
  { rw rec_sum_local,
    apply @le_trans _ _ _ (∑ (n : ℕ) in D.bUnion (λ d, new_local d), (q:ℚ) / n) _,
    refine sum_le_sum_of_subset_of_nonneg hlocal2 _,
    intros i hi1 hi2, apply div_nonneg, exact nat.cast_nonneg q, exact nat.cast_nonneg i,
    refine sum_bUnion_le_sum_of_nonneg _,
    intros x hx, exact div_nonneg (nat.cast_nonneg q) (nat.cast_nonneg x),
  },
  have hDnotzero : ∀ d ∈ D, d ≠ 0, {
   intros i hi hzi, rw finset.mem_filter at hi,
   obtain hi' := hi.2.2.1,rw hzi at hi', push_cast at hi', rw mul_zero at hi',
   apply (lt_iff_not_ge (M*u) 0).mp hi', apply mul_nonneg, exact le_of_lt hzM,
   exact le_of_lt (real.exp_pos _),
  },
  set ω0 := (5/log k) * log(log N) with hω0,
  let D1 := D.filter(λ d, ω0 ≤ (ω d : ℝ)),
  have hrec2 := hrec1,
  specialize hrec1 y k N D1 h1y hyN (le_of_lt h1k),
  have hbound1 : ((∑ d in D1, ∑ n in new_local d, (q : ℚ)/n):ℝ) ≤ (rec_sum_local A q)/2, {
    calc ((∑ d in D1, ∑ n in new_local d, (q : ℚ)/n):ℝ) ≤ ∑ d in D1, 2*(log N)/d : _
         ... = 2*(log N)*∑ d in D1, 1/d : _
         ... ≤ 2*(log N)*∑ d in D1, k^(-ω0)*(k^(ω d)/d) : _
         ... = 2*(log N)*k^(-ω0)*∑ d in D1, (k^(ω d)/d) : _
         ... ≤ 2*(log N)*k^(-ω0)*(C1*|log N|/|log y|)^k : _
         ... = 2*((log N)^(-2:ℝ))*C1^k : _
         ... ≤ 2*((log N)^(-2:ℝ))*C2^k : _
         ... ≤ 2*(log N)^(-2:ℝ)*((log N)^(log(C2)*c)) : _
         ... = 2*(log N)^(-(3/2:ℝ)) : _
         ... ≤ (1/log N)/2 : _
         ... ≤ ((rec_sum_local A q)/2 : ℝ) : _,
    apply finset.sum_le_sum, intros d hd, apply haux1, rw mem_filter at hd,
    exact hd.1,
    rw mul_sum, refine sum_congr _ _, refl, intros x hx, rw div_eq_mul_one_div,
    rw mul_le_mul_left, apply finset.sum_le_sum, intros i hi,
    nth_rewrite 1 div_eq_mul_one_div, rw ← mul_assoc, apply le_mul_of_one_le_left,
    rw one_div_nonneg, exact nat.cast_nonneg i, rw [← rpow_nat_cast, ← rpow_add],
    apply one_le_rpow, exact_mod_cast (le_of_lt h1k), rw [← sub_eq_neg_add, sub_nonneg],
    rw finset.mem_filter at hi, exact hi.2, exact h0k, exact mul_pos zero_lt_two hlarge1,
    nth_rewrite 1 mul_assoc,
    refine congr_arg (has_mul.mul (2*(log N))) _, rw mul_sum,
    rw mul_le_mul_left, apply hrec1, intros r hr, rw [ppowers_in_set, mem_bUnion] at hr,
    rcases hr with ⟨a,ha,hr⟩, rw [mem_filter, mem_filter] at ha, rw mem_filter at hr,
    refine ha.1.2.1 _ hr.2.1 (nat.dvd_of_mem_divisors hr.1) hr.2.2,
    refine mul_pos (mul_pos zero_lt_two hlarge1) (rpow_pos_of_pos h0k _),
    rw [← @exp_log k, ← exp_mul, neg_eq_neg_one_mul, hω0,
     ← mul_assoc, mul_comm (log k) (-1), ← mul_assoc, mul_assoc (-1) (log k),
     mul_div_cancel', ← neg_eq_neg_one_mul, mul_comm (-5) (log(log N)), exp_mul,
     exp_log, abs_eq_self.mpr, abs_eq_self.mpr, log_exp],
     nth_rewrite 2 ← rpow_one (log N),
     rw [mul_div_assoc, ← rpow_sub, ← sub_add, sub_self, zero_add, mul_pow],
     nth_rewrite 1 ← rpow_nat_cast, rw [← rpow_mul, div_mul_cancel, ← mul_assoc],
     nth_rewrite 0 ← rpow_one (log N),
     rw [mul_assoc (2:ℝ), ← rpow_add, mul_comm _ ((log N)^(2:ℝ)),
     ← mul_assoc, ← mul_assoc, ← mul_comm (2:ℝ) ((log N)^(2:ℝ)), mul_assoc (2:ℝ),
     ← rpow_add], norm_num1, refl, exact hlarge1, exact hlarge1,
     exact ne_of_gt h0k, exact le_of_lt hlarge1, exact hlarge1, apply log_nonneg,
     apply one_le_exp, apply rpow_nonneg_of_nonneg, exact le_of_lt hlarge1,
     exact le_of_lt hlarge1, exact hlarge1, apply ne_of_gt, apply log_pos,
     exact_mod_cast h1k, exact h0k,
     rw [mul_le_mul_left], refine pow_le_pow_of_le_left (le_of_lt hC1) (le_max_left C1 2) _,
     refine mul_pos zero_lt_two _, refine rpow_pos_of_pos hlarge1 _,
     rw [mul_le_mul_left, ← log_le_log, log_pow, log_rpow, mul_comm, mul_assoc,
        mul_le_mul_left], exact hkN, exact log_pos hC2, exact hlarge1,
        apply pow_pos, exact (lt_trans zero_lt_one hC2), apply rpow_pos_of_pos hlarge1,
        refine mul_pos zero_lt_two (rpow_pos_of_pos hlarge1 _),
     rw [mul_assoc, ← rpow_add, mul_comm (log C2), div_mul_cancel], norm_num1,
     refl, exact ne_of_gt (log_pos hC2), exact hlarge1,
     rw [le_div_iff, le_div_iff],
     convert_to 4*((log N)^(-((3:ℝ)/2))*(log N)) ≤ 1 using 0, { ring_nf, },
     rw ← rpow_add_one, exact hlarge2, exact ne_of_gt hlarge1, exact hlarge1,
     exact zero_lt_two, rw div_le_div_right, exact hsumq, exact zero_lt_two,
     },
  let D2 := D.filter(λ d, (ω d : ℝ) < ω0),
  specialize hrec2 y 1 N D2 h1y hyN (le_refl 1),
  have hbound2 : (rec_sum_local A q)/2 ≤ ∑ d in D2, ∑ n in new_local d, q/n, {
    calc  (rec_sum_local A q)/2 =  (rec_sum_local A q) -  (rec_sum_local A q)/2 : _
          ... ≤ ∑ d in D, ∑ n in new_local d, (q:ℚ)/n - ∑ d in D1, ∑ n in new_local d, (q:ℚ)/n : _
          ... = ∑ d in D2, ∑ n in new_local d, q/n : _,
    refine eq.symm (sub_self_div_two (rec_sum_local A q)),
    apply sub_le_sub, exact hrecbound, exact_mod_cast hbound1,
    have : D = D1 ∪ D2, {
      ext, split, intro ha, rw mem_union,
      by_cases ha2 :  ω0 ≤ (ω a : ℝ), left, rw mem_filter, refine ⟨ha,ha2⟩,
      rw not_le at ha2, right, rw mem_filter, refine ⟨ha,ha2⟩,
      intro ha, rw mem_union at ha, cases ha with h1 h2,
      exact mem_of_mem_filter a h1, exact mem_of_mem_filter a h2,
     },
    rw this, rw sum_union, simp only [add_tsub_cancel_left, eq_self_iff_true],
    rw disjoint_filter, intros x hx1 hx2, rw not_lt, exact hx2,
  },
  have hbound3 : (rec_sum_local A q)/2 ≤ ∑ d in D2, (1/d)*(∑ n in new_local d, (q*d)/n), {
    apply le_trans hbound2, apply sum_le_sum, intros d hd, rw mul_sum, apply sum_le_sum,
    intros n hn, apply le_of_eq, rw [← mul_div, ← mul_assoc, mul_comm (1/(d:ℚ)) q,
      mul_assoc, mul_comm (1/(d:ℚ)), ← div_mul_eq_div_mul_one_div, div_mul_left,
      mul_one_div], norm_cast,  rw mem_filter at hd, exact hDnotzero d hd.1,
  },

  have hDsumpos : 0 < ∑ d in D2, ((1 : ℚ)/d), {
    apply sum_pos, intros i hi, apply div_pos, exact zero_lt_one, norm_cast,
    rw pos_iff_ne_zero, apply hDnotzero,
    have : D2 ⊆ D, { refine finset.filter_subset _ _, },
    exact this hi,  rw finset.nonempty_iff_ne_empty, intro hempty,
    have hempty2 : ∑ d in D2, ((1:ℚ)/d)*(∑ n in new_local d, (q*d)/n) = 0, {
     rw hempty, exact finset.sum_empty,
    },
    rw hempty2 at hbound3, apply (lt_iff_not_ge 0 ((rec_sum_local A q)/2)).mp,
    apply div_pos,
    have : (0 : ℝ) < rec_sum_local A q, {
     refine lt_of_lt_of_le _ hsumq, apply div_pos, exact zero_lt_one, exact hlarge1,
    },
    exact_mod_cast this, exact zero_lt_two, exact hbound3,
  },
  have hfound0 : ∃ x ∈ D2, (rec_sum_local A q)/2 ≤
     (∑ d in D2, (1/d))*∑ n in new_local x, (q*x)/n, {
    have : 0 < (rec_sum_local A q : ℝ), {
      refine lt_of_lt_of_le _ hsumq, rw one_div_pos, exact hlarge1,
    },
    refine weighted_ph _ _ hbound3, refine div_pos _ zero_lt_two,
    exact_mod_cast this,
    intros d hd, rw one_div_nonneg,
    exact nat.cast_nonneg d,
  },
  have hfound : ∃ d ∈ D2, (rec_sum_local A q)/(2*∑ d in D2, (1/d)) ≤
     ∑ n in new_local d, (q*d)/n, {
      rcases hfound0 with ⟨x,hx1,hx2⟩, refine ⟨x,hx1,_⟩,
      rw [div_le_iff, mul_comm, mul_assoc, ← div_le_iff'], exact hx2, exact zero_lt_two,
      refine mul_pos zero_lt_two hDsumpos,
  },
  have hfound1 : ∃ d ∈ D2, (rec_sum_local A q : ℝ)/(2*∑ d in D2, (1/d)) ≤
     ∑ n in new_local d, (q*d)/n, {
       rcases hfound with ⟨d,hd1,hd2⟩, refine ⟨d,hd1,_⟩,
       calc _ = (rec_sum_local A q : ℝ)/(((2*∑ d in D2, (1/d)):ℚ):ℝ) :_
          ... ≤ ((∑ n in new_local d, (q*d)/n : ℚ):ℝ) :_
          ... = _ :_,
       rw [rat.cast_mul, rat.cast_sum], push_cast,
       exact_mod_cast hd2, rw rat.cast_sum, push_cast,
  },
  have hbound4 : ∑ d in D2, ((1 : ℝ)/d) ≤ (log N)^((2:ℝ)/k) / (C*2), {
    calc  ∑ d in D2, ((1 : ℝ)/d) = ∑ d in D2, 1^(ω d)/d : _
          ... ≤ (C1*|log N|/|log y|)^1 : _
          ... = C1*(log N)^((2:ℝ)/k) : _
          ... = (log N)^((2:ℝ)/k) / (C*2) :_,
    apply sum_congr, refl, intros x hx, rw one_pow,
    rw nat.cast_one at hrec2,
    apply hrec2, intros r hr, rw [ppowers_in_set, mem_bUnion] at hr,
    rcases hr with ⟨a,ha,hr⟩, rw [mem_filter, mem_filter] at ha, rw mem_filter at hr,
    refine ha.1.2.1 _ hr.2.1 (nat.dvd_of_mem_divisors hr.1) hr.2.2,
    rw [pow_one, abs_eq_self.mpr, abs_eq_self.mpr, log_exp],
    nth_rewrite 0 ← rpow_one (log N),
    rw [mul_div_assoc, ← rpow_sub, ← sub_add, sub_self, zero_add],
    exact hlarge1, apply log_nonneg, exact le_of_lt h1y, exact le_of_lt hlarge1,
    rw mul_comm C1, nth_rewrite 1 ← mul_one_div, rw hC',
  },
  rcases hfound1 with ⟨d,hd,hfound1⟩,
  use d, rw finset.mem_filter at hd, rw finset.mem_filter at hd,
  refine ⟨hd.1.2.2.1,hd.2,_⟩, apply le_trans _ hfound1, rw div_le_div_iff,
  rw mul_comm C, rw mul_assoc, rw mul_le_mul_left, rw ← mul_assoc, rw mul_comm,
  rw ← le_div_iff, exact hbound4, apply mul_pos hC zero_lt_two,
  apply lt_of_lt_of_le _ hsumq, apply div_pos, exact zero_lt_one, exact hlarge1,
  apply rpow_pos_of_pos hlarge1, refine mul_pos zero_lt_two _,
  rw [← @rat.cast_pos ℝ _ _, rat.cast_sum] at hDsumpos, push_cast at hDsumpos,
  exact hDsumpos,
end


-- Lemma 6.1
lemma find_good_x :  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  (0 < M) → (M ≤ N) → (0 ∉ A) →
  (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
  (∀ (t : ℝ) (I : finset ℤ) (q ∈ ppowers_in_set A),
  I = finset.Icc ⌈t - (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) / 2⌉ ⌊t + (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) / 2⌋ →
  (((1 : ℝ)/(2*(log N)^((1 : ℝ)/100))) ≤ rec_sum_local (A.filter (λ n, ∃ x ∈ I, (n:ℤ) ∣ x)) q)
  → (∃ xq ∈ I, ((q:ℤ) ∣ xq) ∧ (((35 : ℝ)/100)*log(log N)) ≤
     ∑ r in (ppowers_in_set A).filter(λ n, (n:ℤ) ∣ xq), 1/r ))
  :=
begin
  obtain hgoodd := find_good_d,
  rcases hgoodd with ⟨c,C,hc,hC,hgoodd⟩,
  have heasy1 : 0 < ((2:ℝ)/99) := by norm_num1,
  have heasy2 : ((2:ℝ)/99) < 1/2 := by norm_num1,
  obtain hlargerecbound := rec_qsum_lower_bound ((2:ℝ)/99) heasy1 heasy2,
  filter_upwards [hgoodd, hlargerecbound, another_large_N c C hc hC],
  clear hgoodd hlargerecbound,
  intros N hgooddN hlargerecbound hlargegroup M A hA h0M hMN h0A hMA hreg t I q hq hI hqlocal,
  have hlarge4 : 4*log(log(log N)) ≤ log(log N) := hlargegroup.2.2.1,
  have hlarge5 : 1/c/2 ≤ log(log(log N)) := hlargegroup.1,
  have hlarge6 : 2^((100:ℝ)/99) ≤ log N := hlargegroup.2.1,
  have hlarge7 : log 2 < log(log(log N)) := hlargegroup.2.2.2.1,
  have hlarge0 : 0 < log(log(log N)), { refine lt_trans _ hlarge7, refine log_pos one_lt_two, },
  have hlarge1 : 0 < log(log N), { refine lt_of_lt_of_le _ hlarge4, refine mul_pos zero_lt_four hlarge0, },
  have hlarge3 : 1 ≤ log N, { refine le_trans _ hlarge6, refine one_le_rpow one_le_two _, norm_num1, },
  have hlarge2 : 0 < log(N), { exact lt_of_lt_of_le zero_lt_one hlarge3, },
  let A_I := A.filter (λ n : ℕ, ∃ x ∈ I, (n:ℤ) ∣ x),
  let k := ⌊(log (log N))/(2*log(log(log N)))⌋₊,
  have h1k : 1 < k, {
    apply nat.lt_of_succ_lt_succ,
    have : (2:ℝ) < k + 1, {
      calc (2:ℝ) ≤ (log (log N))/(2*log(log(log N))) :_
           ... < k + 1 :_,
      rw [le_div_iff, ← mul_assoc], norm_num1, exact hlarge4,
      exact mul_pos zero_lt_two hlarge0, refine nat.lt_floor_add_one _,
    },
    exact_mod_cast this,
  },
  have hkc : (k:ℝ) ≤ c* log(log N), {
    calc (k:ℝ) ≤ (log (log N))/(2*log(log(log N))) :_
        ... ≤ c* log(log N) :_,
    refine nat.floor_le _, refine div_nonneg (le_of_lt hlarge1) _,
    refine mul_nonneg zero_le_two (le_of_lt hlarge0),
    rw [mul_comm c, div_eq_mul_one_div, mul_le_mul_left, one_div_le, ← div_le_iff'],
    exact hlarge5, exact zero_lt_two, exact mul_pos zero_lt_two hlarge0,
    exact hc, exact hlarge1,
  },
  have hlogNk : 2*log (log N) < log N ^ ((1:ℝ) / k), {
    calc 2*log(log N) = 2*log(N)^(log(log(log N))/log(log N)) : _
         ... < (log N)^((2*log(log(log N)))/(log (log N))) :_
         ... ≤ (log N)^((1:ℝ)/k) :_,
    nth_rewrite 1 ← exp_log hlarge2, rw [← exp_mul, mul_div,
      mul_comm (log(log N)), mul_div_cancel, exp_log], exact hlarge1,
    exact ne_of_gt hlarge1, rw [← lt_div_iff, ← rpow_sub, ← mul_div],
    nth_rewrite 1 ← one_mul (log (log (log N)) / log (log N)), rw [← sub_mul], norm_num1,
    rw [one_mul, ← log_lt_log_iff, log_rpow, div_mul_cancel],
    exact hlarge7, exact ne_of_gt hlarge1, exact hlarge2, exact zero_lt_two,
    apply rpow_pos_of_pos, exact hlarge2, exact hlarge2, apply rpow_pos_of_pos, exact hlarge2,
    apply rpow_le_rpow_of_exponent_le, exact hlarge3, rw [le_one_div, one_div_div],
    refine nat.floor_le _, refine div_nonneg (le_of_lt hlarge1) _,
    refine mul_nonneg zero_le_two (le_of_lt hlarge0), refine div_pos _ hlarge1,
    refine mul_pos zero_lt_two hlarge0, norm_cast, exact lt_trans zero_lt_one h1k,
  },
  have hlogNk2 : (log N) ^ (-((2:ℝ) / 99) / 2) ≤ C * (1 / (2 * log N ^ ((1:ℝ) / 100))) / log N ^ ((2:ℝ)/k), {
    exact hlargegroup.2.2.2.2.1,
  },
  have hNlogk : (1 - 2 / 99) * log (log N) + (1 + 5 / log k * log (log N)) ≤ 99 / 100 * log (log N), {
    exact hlargegroup.2.2.2.2.2,
  },
  have hA_I : A_I ⊆ finset.range(N+1), { apply subset_trans _ hA, apply finset.filter_subset,},
  have hA_I' : (∀ n ∈ A_I, M ≤ (n : ℝ) ∧ ((ω n) : ℝ) < (log N)^((1:ℝ)/k)), {
    intros n hn, refine ⟨hMA n (mem_of_mem_filter n hn),_⟩,
    rw arith_regular at hreg, specialize hreg n (mem_of_mem_filter n hn),
    refine lt_of_le_of_lt hreg.2 _, exact hlogNk,
   },
  have hqA_I : q ∈ ppowers_in_set A_I, {
    have : (local_part A_I q).nonempty, {
      rw finset.nonempty_iff_ne_empty, intro hem,
      rw [rec_sum_local, hem, sum_empty, ← not_lt] at hqlocal, apply hqlocal, norm_cast,
      rw one_div_pos, refine mul_pos zero_lt_two _, apply rpow_pos_of_pos,
      exact hlarge2,
     },
    obtain ⟨n,hn⟩ := this, rw [local_part, mem_filter] at hn,
    rw [ppowers_in_set, mem_bUnion], refine ⟨n,hn.1,_⟩, rw mem_filter,
    rw [ppowers_in_set, mem_bUnion] at hq, rcases hq with ⟨b,hb,hq⟩, rw mem_filter at hq,
    refine ⟨_,hq.2.1,hn.2.2⟩, rw nat.mem_divisors, refine ⟨hn.2.1,_⟩,
    intro hnz, rw hnz at hn, apply h0A, exact mem_of_mem_filter 0 hn.1,
   },
  have hqlocal2 :  (1/(log N) ≤ rec_sum_local A_I q), {
    refine le_trans _ hqlocal, rw [one_div_le_one_div, ← le_div_iff],
    nth_rewrite 0 ← rpow_one (log N), rw [← rpow_sub], norm_num1,
    have : (0:ℝ) < 100/99, { norm_num1, },
    rw [← real.rpow_le_rpow_iff _ _ this, ← rpow_mul], norm_num1, rw rpow_one, exact hlarge6,
    exact le_of_lt hlarge2, exact zero_le_two, apply rpow_nonneg_of_nonneg,
    exact le_of_lt hlarge2, exact hlarge2, apply rpow_pos_of_pos, exact hlarge2, exact hlarge2,
    refine mul_pos zero_lt_two _, apply rpow_pos_of_pos, exact hlarge2,
   },
  specialize hgooddN M k A_I hA_I h0M hMN h1k hkc hA_I' q hqA_I hqlocal2,
  rcases hgooddN with ⟨d,hgood1,hgood2,hgood3⟩,
  let A_I' := A_I.filter(λ n : ℕ, (q*d) ∣ n ),
  let A_I'' := (finset.range(N+1)).filter(λ m : ℕ, ∃ n ∈ A_I', m*(q*d)=n ∧ coprime m (q*d) ),
  have hsum : (((35 : ℝ)/100)*log(log N)) ≤ ∑ r in (ppowers_in_set A_I''), 1/r, {
    calc _ ≤ (1-2*(2/99))*real.exp(-1)*log(log N) :_
        ... ≤  ∑ r in (ppowers_in_set A_I''), 1/r :_,
    rw mul_le_mul_right, exact useful_exp_estimate, exact hlarge1,
    refine hlargerecbound A_I'' _ _,
    calc _ ≤ C * (1 / (2 * log N ^ ((1:ℝ) / 100))) / (log N)^((2:ℝ) /k) : hlogNk2
       ... ≤ C * (rec_sum_local A_I q) / (log N)^((2:ℝ) /k) :_
       ... ≤ ∑ (n : ℕ) in filter (λ (n : ℕ), q * d ∣ n ∧ (q * d).coprime (n / (q * d))) (local_part A_I q),
         (q:ℝ) * d / n : hgood3
       ... ≤ _ :_,
       refine div_le_div_of_le_of_nonneg _ _, rw mul_le_mul_left,
       exact hqlocal, exact hC,
       apply rpow_nonneg_of_nonneg, exact le_of_lt hlarge2,
       rw rec_sum,
       let g := (λ n : ℕ, n/(q*d) ), push_cast,
       refine sum_le_sum_of_inj g _ _ _ _, intros b hb, rw one_div_nonneg, exact nat.cast_nonneg b,
       intros a ha, rw mem_filter, rw [mem_filter, local_part] at ha,
       refine ⟨_,a,_,_⟩,
       rw mem_range, refine lt_of_le_of_lt (nat.div_le_self a (q*d)) _,
       rw ← mem_range, exact hA_I (mem_of_mem_filter a ha.1),
       rw mem_filter, rw mem_filter at ha, refine ⟨ha.1.1,ha.2.1⟩,
       rw [nat.div_mul_cancel, nat.coprime_comm], refine ⟨_,ha.2.2⟩, refl, exact ha.2.1,
       intros a ha b hb hab, have := congr_arg (has_mul.mul (q*d)) hab,
       rw [nat.mul_div_cancel', nat.mul_div_cancel'] at this, exact this, rw mem_filter at hb,
       exact hb.2.1, rw mem_filter at ha, exact ha.2.1,
       intros a ha, rw mem_filter at ha, rw [nat.cast_div, one_div_div, nat.cast_mul],
       exact ha.2.1, norm_cast, intro hzero, rw hzero at ha,
       have : a = 0 := nat.eq_zero_of_zero_dvd ha.2.1, rw [this, local_part] at ha,
       apply h0A, exact mem_of_mem_filter 0 (mem_of_mem_filter 0 ha.1),
       intros n hn, rw mem_filter at hn, rcases hn.2 with ⟨m,hm1,hm2⟩,
       have : m / (q*d) = n, { apply nat.div_eq_of_eq_mul_right,
         rw pos_iff_ne_zero, intro hzero, rw [hzero, mul_zero] at hm2, apply h0A, rw ← hm2.1 at hm1,
         exact mem_of_mem_filter 0 (mem_of_mem_filter 0 hm1), rw mul_comm at hm2, refine eq.symm hm2.1,
         },
        rw ← this, rw arith_regular at hreg, specialize hreg m (mem_of_mem_filter m (mem_of_mem_filter m hm1)),
        refine ⟨_,_⟩,
        calc _ ≤ (ω m: ℝ) - (1+(5/log k)*log(log N) ) :_
           ... ≤ (ω m : ℝ) - ω (q*d) : _
           ... ≤ _ :_,
       rw le_sub_iff_add_le, refine le_trans _ hreg.1, exact hNlogk, apply sub_le_sub_left,
       calc _ ≤ 1 + (ω d:ℝ) :_
           ...≤ _ :_,
       have htemp : ω (q*d) ≤ 1 + ω d, { refine omega_mul_ppower _,
         rw mem_ppowers_in_set at hq, exact hq.1, },
       exact_mod_cast htemp, apply add_le_add_left, exact le_of_lt hgood2,
       refine sub_le_omega_div _, rw mem_filter at hm1, exact hm1.2, refine le_trans _ hreg.2, norm_cast,
       refine omega_div_le _, rw mem_filter at hm1, exact hm1.2,
   },
  clear hlargerecbound,
  let I' := I.filter(λ x : ℤ, ∃ n ∈ A_I', (n:ℤ) ∣ x),
  have hI'ne : I'.nonempty, {
    rw filter_nonempty_iff,
    have haux : A_I'.nonempty, {
      rw finset.nonempty_iff_ne_empty, intro hem,
      have haux3 : A_I'' = ∅, {
        rw ← finset.not_nonempty_iff_eq_empty, intro h,
        rw filter_nonempty_iff at h, rcases h with ⟨a,ha1,n,hn1,hn2⟩,
        rw eq_empty_iff_forall_not_mem at hem, specialize hem n hn1, exact hem,
       },
      have hem2 : ppowers_in_set A_I'' = ∅, {
        rw haux3, exact ppowers_in_set_empty,
      },
      rw [hem2, sum_empty, ← not_lt] at hsum, apply hsum, refine mul_pos _ hlarge1, norm_num1,
    },
    obtain ⟨n,hn⟩ := haux,
    have haux2 := hn, rw mem_filter at hn, rw mem_filter at hn,
    rcases hn.1.2 with ⟨x,hx1,hx2⟩, refine ⟨x,hx1,n,haux2,hx2⟩,
   },
  obtain ⟨x, hx⟩ := hI'ne,
  have hI'single : ∀ y ∈ I', x=y, {
    by_contra, rw not_forall at h, rcases h with ⟨y,hy⟩, rw not_imp at hy,
    have hdx : ((q*d):ℤ) ∣ x, {
      rw mem_filter at hx, rcases hx.2 with ⟨m,hm1,hm2⟩,
      rw mem_filter at hm1, refine dvd_trans _ hm2, exact_mod_cast hm1.2,
     },
    have hdy : ((q*d):ℤ) ∣ y, {
      rw mem_filter at hy, rcases hy.1.2 with ⟨m,hm1,hm2⟩,
      rw mem_filter at hm1, refine dvd_trans _ hm2, exact_mod_cast hm1.2,
     },
    let z := |x-y|,
    have hdz : ((q*d):ℤ) ∣ z, {
      rw dvd_abs, exact dvd_sub hdx hdy,
    },
    have hzs : (z:ℝ) ≤ (M*(N : ℝ)^(-(2 : ℝ)/log(log N))), {
      let b := ⌊t + (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) / 2⌋,
      let a := ⌈t - (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) / 2⌉,
      calc (z:ℝ) ≤ b - a :_
           ... ≤ (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) :_,
      have hIx : x ∈ Icc a b, { rw ← hI, exact mem_of_mem_filter x hx, },
      have hIy : y ∈ Icc a b, { rw ← hI, exact mem_of_mem_filter y hy.1, },
      push_cast, refine two_in_Icc hIx hIy,
      apply le_trans floor_sub_ceil, rw add_halves',
    },
    rw lt_iff_not_ge at hgood1, apply hgood1,
    calc (q:ℝ)*d ≤ z : _
         ... ≤ (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) : _
         ... ≤ M * exp (-(log N) ^ ((1:ℝ) - 1 / k)) :_,
    norm_cast, refine int.le_of_dvd _ hdz, rw abs_pos, rw sub_ne_zero, exact hy.2,
    exact hzs, rw mul_le_mul_left,
    nth_rewrite 0 ← exp_log (lt_of_lt_of_le h0M hMN),
    rw [← exp_mul, exp_le_exp, mul_div, mul_comm, le_neg, neg_eq_neg_one_mul, ← mul_div,
     ← mul_assoc, ← neg_eq_neg_one_mul, neg_neg, sub_eq_neg_add, rpow_add_one],
    nth_rewrite 1 div_eq_mul_one_div,
    rw [← mul_assoc, mul_comm, mul_comm (2:ℝ), mul_assoc, mul_le_mul_left,
      ← div_eq_mul_one_div, rpow_neg, ← one_div, div_le_div_iff, one_mul],
    calc log(log N) ≤ 2*log(log N) : _
         ... ≤ (log N)^((1:ℝ)/k) : _
         ... ≤ 2*(log N)^((1:ℝ)/k) :_,
    nth_rewrite 0 ← one_mul (log(log N)), rw mul_le_mul_right, exact one_le_two,
    exact hlarge1, exact le_of_lt hlogNk, nth_rewrite 0 ← one_mul ((log N)^((1:ℝ)/k)),
    rw mul_le_mul_right, exact one_le_two, apply rpow_pos_of_pos, exact hlarge2,
    apply rpow_pos_of_pos, exact hlarge2, exact hlarge1,
    exact le_of_lt hlarge2, exact hlarge2, exact ne_of_gt hlarge2, exact h0M,
   },
  refine ⟨x, mem_of_mem_filter x hx,_,_⟩,
  rw mem_filter at hx, rcases hx.2 with ⟨n,hn1,hn2⟩, refine dvd_trans _ hn2,
  rw mem_filter at hn1, norm_cast, refine dvd_trans _ hn1.2, exact dvd_mul_right q d,
  have hpp : ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter(λ n : ℕ, (n:ℤ) ∣ x), {
    intros r hr, rw [ppowers_in_set, mem_bUnion] at hr,
    rcases hr with ⟨a,ha,hr⟩, rw mem_filter at hr, rw mem_filter,
    rw mem_filter at ha, rcases ha.2 with ⟨m,hm1,hm2⟩,
    have hm1' := hm1,
    rw mem_filter at hm1, rw mem_filter at hm1, rcases hm1.1.2 with ⟨y,hy1,hy2⟩,
    have hyI' : y ∈ I', {
      rw mem_filter, refine ⟨hy1,m,hm1',hy2⟩,
     },
    have hyx : x = y := by exact hI'single y hyI',
    rw [hyx, ppowers_in_set, mem_bUnion], refine ⟨_,_⟩,
    refine ⟨m,hm1.1.1,_⟩, rw mem_filter, refine ⟨_,hr.2.1,_⟩,
    rw nat.mem_divisors, refine ⟨_,_⟩,  rw ← hm2.1,
    exact dvd_trans (nat.dvd_of_mem_divisors hr.1) (dvd_mul_right a (q*d)),
    intro h0m, rw h0m at hm1, exact h0A hm1.1.1,
    rw [← hm2.1, mul_comm, nat.mul_div_assoc], refine nat.coprime.mul_right _ hr.2.2,
    exact nat.coprime.coprime_dvd_left (nat.dvd_of_mem_divisors hr.1) hm2.2,
    exact nat.dvd_of_mem_divisors hr.1, refine dvd_trans _ hy2, norm_cast,
    refine dvd_trans (nat.dvd_of_mem_divisors hr.1) _, rw ← hm2.1,
    exact dvd_mul_right a (q*d),
  },
  apply le_trans hsum, refine sum_le_sum_of_subset_of_nonneg hpp _,
  intros i hi1 hi2, rw one_div_nonneg, exact nat.cast_nonneg i,
end
