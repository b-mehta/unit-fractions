/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import for_mathlib.basic_estimates
import defs
import aux_lemmas
import fourier
import main_results
import algebra.indicator_function

/-!
# Title

This file contains a formal proof of the headline results of
 https://arxiv.org/pdf/2112.03726.pdf.
-/

open_locale big_operators
open filter finset real
open nat (coprime)

open_locale arithmetic_function
open_locale classical
noncomputable theory

lemma another_weird_tendsto_at_top_aux (c : ℝ) (hc : 1 < c) :
  tendsto (λ x, c ^ x / log x) at_top at_top :=
((tendsto_exp_mul_div_rpow_at_top 1 _ (log_pos hc)).at_top_mul_at_top
  (tendsto_mul_add_div_pow_log_at_top 1 0 1 zero_lt_one)).congr' $
by filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx using
  by simp [rpow_def_of_pos (zero_le_one.trans_lt hc), div_mul_div_cancel _ hx.ne']

lemma the_thing : 1 < exp 2 / 2 :=
begin
  rw [one_lt_div, ←log_lt_iff_lt_exp zero_lt_two],
  { exact log_two_lt_d9.trans_le (by norm_num) },
  exact zero_lt_two
end

lemma another_weird_tendsto_at_top :
  tendsto (λ x : ℝ, x / (2 ^ (1 / 2 * log x + 1) * log (1 / 2 * log x))) at_top at_top :=
(tendsto.const_mul_at_top (show (0 : ℝ) < 1 / 2, by norm_num)
  ((another_weird_tendsto_at_top_aux (exp 2 / 2) the_thing).comp
    (tendsto_log_at_top.const_mul_at_top (show (0 : ℝ) < 1 / 2, by norm_num)))).congr' $
begin
  filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx,
  dsimp,
  rw [div_rpow (exp_pos _).le zero_le_two, div_div, div_mul_div_comm, one_mul,
    rpow_add_one two_ne_zero, rpow_def_of_pos (exp_pos _), log_exp, ←mul_assoc,
    mul_one_div_cancel (two_ne_zero : (2 : ℝ) ≠ 0), one_mul, exp_log hx, ←mul_assoc,
    mul_comm (2 : ℝ)],
end

lemma omega_eq_sum (N : ℕ) {n : ℕ} (hn : n ∈ Icc 1 N) :
  ω n = ∑ p in (((Icc 1 N).filter (λ p, nat.prime p)).filter (λ p, p ∣ n)), 1 :=
begin
  rw [card_distinct_factors_apply', ←card_eq_sum_ones,
    nat.prime_divisors_eq_to_filter_divisors_prime],
  rw mem_Icc at hn,
  congr' 1,
  ext p,
  simp only [mem_filter, nat.mem_divisors, ne.def, mem_Icc, and_assoc],
  split,
  { rintro ⟨hp₁, hp₂, hp₃⟩,
    refine ⟨hp₃.one_lt.le, _, hp₃, hp₁⟩,
    exact (nat.le_of_dvd (pos_iff_ne_zero.2 hp₂) hp₁).trans hn.2 },
  { rintro ⟨hp₁, hp₂, hp₃, hp₄⟩,
    refine ⟨hp₄, _, hp₃⟩,
    rw nat.succ_le_iff at hn,
    exact hn.1.ne' }
end

lemma count_multiples'' {m n : ℕ} (hm : 1 ≤ m) :
  (((finset.Icc 1 n).filter (λ k, m ∣ k)).card : ℝ) = (n / m : ℝ) - int.fract (n / m) :=
begin
  rw [count_multiples hm, int.self_sub_fract, ←nat.cast_floor_eq_cast_int_floor,
    nat.floor_div_eq_div],
  exact div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)
end

lemma count_multiples''' {m n : ℕ} (hm : 1 ≤ m) :
  (((finset.Icc 1 n).filter (λ k, m ∣ k)).card : ℝ) ≤ (n / m : ℝ) :=
begin
  rw [count_multiples'' hm, sub_le_self_iff],
  apply int.fract_nonneg,
end

lemma sum_prime_counting : ∃ (C : ℝ), ∀ᶠ (N : ℕ) in at_top,
   (N : ℝ) * log (log N) - C * N ≤ ∑ x in Icc 1 N, (ω x : ℝ) :=
begin
  obtain ⟨c, hc⟩ := (prime_reciprocal.trans (is_o_log_inv_one one_ne_zero).is_O).bound,
  use -meissel_mertens + c + 1,
  filter_upwards [tendsto_coe_nat_at_top_at_top hc] with N hN,
  dsimp at hN,
  simp only [prime_summatory, nat.floor_coe, abs_one, mul_one, norm_eq_abs] at hN,
  have : ∀ x ∈ Icc 1 N, (ω x : ℝ) = ∑ p in ((Icc 1 N).filter nat.prime), ite (p ∣ x) 1 0,
  { intros x hx,
    rw [omega_eq_sum _ hx, nat.cast_sum, nat.cast_one, sum_filter] },
  rw [sum_congr rfl this, sum_comm],
  simp only [←sum_filter],
  have : ∀ x ∈ (Icc 1 N).filter nat.prime,
    ∑ (a : ℕ) in filter (has_dvd.dvd x) (Icc 1 N), (1 : ℝ) = (N / x : ℝ) - int.fract (N / x),
  { intros x hx,
    rw [←count_multiples'', card_eq_sum_ones, nat.cast_sum, nat.cast_one],
    rw [mem_filter, mem_Icc] at hx,
    exact hx.1.1 },
  rw [sum_congr rfl this, sum_sub_distrib],
  simp only [div_eq_mul_inv (N : ℝ), ←mul_sum],
  have h₁ : (N : ℝ) * (log (log N) + meissel_mertens - c) ≤
    N * ∑ (x : ℕ) in filter nat.prime (Icc 1 N), (↑x)⁻¹,
  { apply mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
    exact sub_le_of_abs_sub_le_left hN },
  have h₂ : ∑ x in filter nat.prime (Icc 1 N), int.fract ((N : ℝ) * (↑x)⁻¹) ≤ N,
  { refine (finset.sum_le_card_nsmul _ _ 1 _).trans _,
    { intros x hx,
      exact (int.fract_lt_one _).le },
    simp only [nat.smul_one_eq_coe, nat.cast_le],
    exact (card_le_of_subset (filter_subset _ _)).trans (by simp) },
  refine (sub_le_sub h₁ h₂).trans' (le_of_eq _),
  ring,
end

lemma range_eq_insert_Icc {n : ℕ} (hn : 1 ≤ n) : range n = insert 0 (Icc 1 (n - 1)) :=
begin
  rw [Icc_succ_left, Ioc_insert_left (nat.zero_le _), ←nat.Ico_succ_right, nat.succ_eq_add_one,
    nat.sub_add_cancel hn, range_eq_Ico],
end

lemma prime_recip_lazy :
  ∃ c, ∀ᶠ N : ℕ in at_top, ∑ p in (Icc 1 N).filter nat.prime, (p : ℝ)⁻¹ ≤ log (log N) + c :=
begin
  obtain ⟨c, hc⟩ := (prime_reciprocal.trans (is_o_log_inv_one one_ne_zero).is_O).bound,
  use meissel_mertens + c,
  filter_upwards [tendsto_coe_nat_at_top_at_top hc] with N hN,
  dsimp at hN,
  simp only [prime_summatory, nat.floor_coe, abs_one, mul_one, norm_eq_abs, abs_sub_le_iff,
    sub_le_iff_le_add', add_assoc] at hN,
  exact hN.1
end

lemma sum_prime_counting_sq : ∃ (C : ℝ), ∀ᶠ (N : ℕ) in at_top,
   ∑ x in Icc 1 N, (ω x : ℝ) ^ 2 ≤ N * log (log N) ^ 2 + C * N * log (log N) :=
begin
  obtain ⟨c, hc⟩ := prime_recip_lazy,
  use ((2 * c + 1) + 1),
  filter_upwards [hc, tendsto_log_log_coe_at_top.eventually_ge_at_top (c ^ 2 + c)] with N hN hN',
  have : ∀ x ∈ Icc 1 N, (ω x : ℝ) ^ 2 = (∑ p in (Icc 1 N).filter nat.prime, ite (p ∣ x) 1 0) ^ 2,
  { intros x hx,
    rw [omega_eq_sum _ hx, nat.cast_sum, nat.cast_one, sum_filter] },
  rw [sum_congr rfl this],
  simp_rw [sq, sum_mul, mul_sum, boole_mul, ←ite_and, @sum_comm _ _ _ _ (Icc _ _), ←sq],
  have : ∀ p ∈ (Icc 1 N).filter nat.prime,
    ∑ q in (Icc 1 N).filter nat.prime, ∑ n in Icc 1 N, ite (p ∣ n ∧ q ∣ n) (1 : ℝ) 0 ≤
    ∑ n in Icc 1 N, ite (p ∣ n) 1 0 +
      ∑ q in (Icc 1 N).filter nat.prime, ∑ n in Icc 1 N, ite (p * q ∣ n) 1 0,
  { intros p hp,
    rw [←sum_filter_add_sum_filter_not _ (λ q, p = q), sum_filter, sum_ite_eq, if_pos hp],
    simp only [and_self, add_le_add_iff_left],
    refine (sum_le_sum _).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) _),
    { intros q hq,
      simp only [mem_filter, mem_Icc, ←ne.def] at hp hq,
      refine sum_le_sum (λ n hn, _),
      by_cases p ∣ n ∧ q ∣ n,
      { rw [if_pos h, if_pos (nat.prime.dvd_mul_of_dvd_ne hq.2 hp.2 hq.1.2 h.1 h.2)] },
      rw if_neg h,
      split_ifs,
      { exact zero_le_one },
      { refl } },
    { intros i _ _,
      simp only [sum_boole, nat.cast_nonneg] } },
  refine (sum_le_sum this).trans _,
  rw [sum_add_distrib],
  simp only [sum_boole],
  have h₁ : ∑ x in (Icc 1 N).filter nat.prime, ((filter ((∣) x) (Icc 1 N)).card : ℝ) ≤
    N * ∑ x in (Icc 1 N).filter nat.prime, x⁻¹,
  { simp only [mul_sum, ←div_eq_mul_inv],
    refine sum_le_sum (λ x hx, _),
    simp only [mem_filter, mem_Icc] at hx,
    apply count_multiples''' hx.1.1 },
  have h₂ : ∑ p in filter nat.prime (Icc 1 N), ∑ q in filter nat.prime (Icc 1 N),
    ((filter (has_dvd.dvd (p * q)) (Icc 1 N)).card : ℝ) ≤
    N * (∑ p in (Icc 1 N).filter nat.prime, p⁻¹) ^ 2,
  { simp only [sq, mul_sum, sum_mul, ←mul_inv, ←div_eq_mul_inv (N : ℝ), ←nat.cast_mul],
    refine sum_le_sum (λ p hp, (sum_le_sum (λ q hq, _))),
    simp only [mem_filter, mem_Icc] at hp hq,
    apply count_multiples''' (one_le_mul hp.1.1 hq.1.1) },
  refine (add_le_add h₁ h₂).trans _,
  rw [mul_comm (2 * c + 1 + 1), mul_assoc, ←mul_add, ←mul_add],
  refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
  refine (add_le_add hN (pow_le_pow_of_le_left _ hN 2)).trans _,
  { exact sum_nonneg (by simp) },
  rw [add_sq],
  linarith only [hN'],
end

-- I think this is false because the LHS set includes 0
-- but does changing to
-- ((filter (λ i, x ∣ i) (Icc 1 N)).card : ℝ) make anything afterwards more annoying?
-- same for the three above
lemma count_divisors {x N : ℕ} (hx : x ≠ 0) :
  ((filter (λ i, x ∣ i) (Icc 1 N)).card : ℝ) = (N / x : ℝ) - int.fract (N / x) :=
begin
  rw count_multiples'',
  exact hx.bot_lt,
end

lemma count_divisors' {x N : ℕ} (hx : x ≠ 0) (hN : N ≠ 0):
  ((filter (λ i, x ∣ i) (range(N))).card : ℝ) = (N / x : ℝ) - (1/x - 1 + int.fract ((N-1) / x)) :=
begin
  have hN' : 1 ≤ N := hN.bot_lt,
  rw [range_eq_insert_Icc hN', filter_insert, if_pos (dvd_zero _), card_insert_of_not_mem,
    nat.cast_add_one, count_divisors hx, nat.cast_sub hN', nat.cast_one, sub_div],
  { ring },
  simp,
end

lemma is_multiplicative_one {R : Type*} [ring R] :
  (1 : nat.arithmetic_function R).is_multiplicative :=
begin
  refine ⟨nat.arithmetic_function.one_one, _⟩,
  intros m n hmn,
  change ite _ _ _ = ite _ _ _ * ite _ _ _,
  simp only [boole_mul, ←ite_and, nat.mul_eq_one_iff],
end

lemma ite_div (p : Prop) [decidable p] {x y z : ℝ} :
  ite p x y / z = ite p (x / z) (y / z) :=
apply_ite (λ i, i / z) _ _ _

lemma moebius_rec_sum {N : ℕ} (hN : N ≠ 0) :
  ∑ (x : ℕ) in N.divisors, (μ x : ℝ) / x = ∏ p in filter nat.prime N.divisors, (1 - p⁻¹) :=
begin
  let f' : nat.arithmetic_function ℝ := ⟨λ x, (μ x : ℝ) / x, by simp⟩,
  have hf' : f'.is_multiplicative,
  { refine ⟨_, λ m n hmn, _⟩,
    { simp only [f', zero_hom.coe_mk, nat.arithmetic_function.moebius_apply_of_squarefree,
        squarefree_one, nat.arithmetic_function.card_factors_one, pow_zero, int.cast_one,
        nat.cast_one, div_one] },
    simp only [zero_hom.coe_mk, nat.cast_mul, int.cast_mul, mul_div_mul_comm,
      nat.arithmetic_function.is_multiplicative_moebius.map_mul_of_coprime hmn] },
  let f : nat.arithmetic_function ℝ := f' * ζ,
  have hf : f.is_multiplicative := hf'.mul nat.arithmetic_function.is_multiplicative_zeta.nat_cast,
  change ∑ x : ℕ in N.divisors, f' x = _,
  rw ←nat.arithmetic_function.coe_mul_zeta_apply,
  change f N = _,
  rw ←nat.prime_divisors_eq_to_filter_divisors_prime,
  revert hN N,
  refine nat.rec_on_pos_prime_pos_coprime _ _ _ _,
  { intros p k hp hk hpk,
    rw [nat.prime_pow_prime_divisor hk.ne' hp, prod_singleton,
      nat.arithmetic_function.coe_mul_zeta_apply, nat.sum_divisors_prime_pow hp],
    simp only [zero_hom.coe_mk, nat.cast_pow, sum_range_succ', pow_zero,
      nat.arithmetic_function.moebius_apply_one, int.cast_one, div_one],
    simp_rw [nat.arithmetic_function.moebius_apply_prime_pow hp (nat.succ_ne_zero _),
      int.cast_ite, int.cast_neg, int.cast_zero, int.cast_one, nat.succ_inj',
      ite_div, zero_div, sum_ite_eq', neg_div, pow_one, one_div, mem_range, if_pos hk,
      neg_add_eq_sub] },
  { intro h,
    cases h rfl },
  { intro _,
    simp only [nat.factors_one, list.to_finset_nil, prod_empty, hf.map_one] },
  { intros a b ha hb hab aih bih k,
    rw [hf.map_mul_of_coprime hab, nat.factors_mul_to_finset_of_coprime hab, prod_union, aih, bih],
    { linarith },
    { linarith },
    rw list.disjoint_to_finset_iff_disjoint,
    apply nat.coprime_factors_disjoint hab
    },
end

lemma prod_sdiff'' {ι α : Type*} [comm_group_with_zero α] (f : ι → α) (s t : finset ι) (h : t ⊆ s)
  (ht : ∀ i ∈ t, f i ≠ 0) :
  ∏ i in s \ t, f i = (∏ i in s, f i) / ∏ i in t, f i :=
begin
  rw [eq_div_iff_mul_eq, prod_sdiff h],
  rwa prod_ne_zero_iff,
end

lemma filter_sdiff {ι : Type*} (p : ι → Prop) [decidable_eq ι] [decidable_pred p] (s t : finset ι) :
  (s \ t).filter p = s.filter p \ t.filter p :=
begin
  ext x,
  simp only [mem_sdiff, mem_filter],
  tauto,
end

lemma product_of_primes_factors {s : finset ℕ} (hs : ∀ p ∈ s, nat.prime p) :
  (∏ p in s, p).factors = s.sort (≤) :=
begin
  refine (list.eq_of_perm_of_sorted (nat.factors_unique _ _) _ (nat.factors_sorted _)).symm,
  { rw [prod_eq_multiset_prod, multiset.map_id', ←multiset.coe_prod, finset.sort_eq] },
  { simpa only [mem_sort] },
  exact sort_sorted _ _,
end

lemma product_of_primes_factors_to_finset {s : finset ℕ} (hs : ∀ p ∈ s, nat.prime p) :
  (∏ p in s, p).factors.to_finset = s :=
by rw [product_of_primes_factors hs, sort_to_finset]

lemma mem_factors_prod {A : finset ℕ} (h : ∀ n ∈ A, n ≠ 0) {p : ℕ} :
p ∈ (∏ a in A, a).factors ↔ ∃ a ∈ A, p ∈ (a:ℕ).factors :=
begin
  induction A using finset.induction_on with n A hnA hA,
  simp only [prod_empty, nat.factors_one, list.not_mem_nil, not_mem_empty, exists_false_left,
     exists_false],
  rw [prod_insert hnA, nat.mem_factors_mul], split, intro h',
  cases h' with h₁ h₂, use n, refine ⟨mem_insert_self _ _,h₁⟩,
  rw hA at h₂, rcases h₂ with ⟨b,hb₁,hb₂⟩, use b, refine ⟨_,hb₂⟩,
  refine mem_insert_of_mem hb₁, intros n hn, refine h n _,
  refine mem_insert_of_mem hn, intro h', rcases h' with ⟨a,ha₁,ha₂⟩,
  rw mem_insert at ha₁, cases ha₁, rw ha₁ at ha₂, left, exact ha₂,
  right, rw hA, use a, refine ⟨ha₁,ha₂⟩, intros n hn, refine h n _,
  refine mem_insert_of_mem hn, refine h n _, refine mem_insert_self _ _,
  rw prod_ne_zero_iff, intros n hn, refine h n _,
  refine mem_insert_of_mem hn,
end

lemma prod_primes_squarefree {A : finset ℕ} (h : ∀ n ∈ A, nat.prime n) :
 squarefree ∏ p in A, p :=
begin
  unfreezingI { induction A using finset.induction_on with p A hpA hA },
  simp only [prod_empty, squarefree_one],
  rw prod_insert hpA, rw nat.squarefree_mul,
  refine ⟨prime.squarefree _,_⟩, rw ← nat.prime_iff, refine h p _, refine mem_insert_self _ _,
  refine hA _, intros n hn, refine h n _, refine mem_insert_of_mem hn,
  refine nat.coprime_prod_right _, intros q hq, rw nat.coprime_primes, intro hbad,
  rw hbad at hpA, exact hpA hq, refine h p _, refine mem_insert_self _ _,
  refine h q _, refine mem_insert_of_mem hq,
end

lemma sieve_lemma_prec (N : ℕ) (y z : ℝ) (hy : 1 ≤ y) (hzN : z < N) :
   (((finset.range(N)).filter (λ n, ∀ p : ℕ, prime p → p ∣ n → ((p : ℝ) < y) ∨ z < p)).card : ℝ) ≤
   ((partial_euler_product ⌊y⌋₊)/(partial_euler_product ⌊z⌋₊)) * N + 2^(z+1) :=
begin
  by_cases hN0 : N = 0,
  rw [hN0, range_zero, filter_empty], norm_cast, rw [mul_zero, zero_add],
  simp only [card_empty, nat.cast_zero], refine rpow_nonneg_of_nonneg _ _,
  exact zero_le_two,
  cases lt_or_le z y,
  { calc _ ≤ (N:ℝ) :_
       ... ≤ _ :_,
    norm_cast,
    have : N = (finset.range(N)).card, { rw card_range, },
    nth_rewrite 1 this, refine finset.card_filter_le _ _,
    rw ← add_zero (N:ℝ), refine add_le_add _ _, rw add_zero, refine le_mul_of_one_le_left _ _,
    exact nat.cast_nonneg N, rw [one_le_div, partial_euler_product, partial_euler_product],
    refine prod_of_subset_le_prod_of_one_le _ _ _, intros p hp,
    rw [mem_filter, mem_Icc], rw [mem_filter, mem_Icc] at hp, refine ⟨⟨hp.1.1,_⟩,hp.2⟩,
    refine le_trans hp.1.2 _,
    by_cases h0z : 1 ≤ z,
    rw nat.le_floor_iff, refine le_trans _ (le_of_lt h), refine nat.floor_le _,
    exact le_trans zero_le_one h0z,  exact le_trans zero_le_one hy,
    rw [not_le, ← nat.floor_eq_zero] at h0z, rw h0z, exact zero_le ⌊y⌋₊,
    intros p hp, rw [inv_nonneg, sub_nonneg, inv_le_one_iff], right,
    norm_cast, rw mem_filter at hp, refine le_of_lt (nat.prime.one_lt hp.2),
    intros p hp1 hp2, refine one_le_inv _ _, rw [sub_pos, inv_lt_one_iff], right,
    norm_cast, rw mem_filter at hp1, exact nat.prime.one_lt hp1.2,
    refine sub_le_self _ _, rw [inv_nonneg], exact nat.cast_nonneg p,
    refine lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound,
    refine rpow_nonneg_of_nonneg _ _, exact zero_le_two,
  },
  let P := ∏ p in ((finset.range N).filter (λ p, nat.prime p ∧ (y ≤ p) ∧ ((p:ℝ) ≤ z))), p,
  have hP : P ≠ 0,
  { rw prod_ne_zero_iff,
    intros x hx,
    simp only [mem_filter, mem_range] at hx,
    exact hx.2.1.pos.ne' },
  have h₁ : ((finset.range(N)).filter (λ n, ∀ p : ℕ, prime p → p ∣ n →
       ((p : ℝ) < y) ∨ (z < p))).card = ((finset.range(N)).filter (λ n, coprime n P)).card,
  { congr' 1,
    apply filter_congr,
    simp only [mem_range, nat.coprime_prod, mem_filter, and_imp, ←nat.prime_iff],
    intros n hn,
    split,
    { intros h p pn hp hy hz,
      rw [nat.coprime_comm, hp.coprime_iff_not_dvd],
      intro t,
      cases h p hp t with h' h',
      { exact h'.not_le hy },
      { exact h'.not_le hz } },
    { intros h p hp pn,
      by_contra' h',
      rw [hp.dvd_iff_not_coprime, ←nat.coprime_comm] at pn,
      exact pn (h p (nat.cast_lt.1 (h'.2.trans_lt hzN)) hp h'.1 h'.2) } },
  have : ∀ n, ∑ (i : ℕ) in (nat.gcd n P).divisors, (μ i : ℝ) = ite (nat.gcd n P = 1) 1 0,
  { intro n,
    rw ←int.cast_sum,
    rw ←nat.arithmetic_function.coe_mul_zeta_apply,
    rw nat.arithmetic_function.moebius_mul_coe_zeta,
    change coe (ite _ _ _) = _,
    split_ifs; simp only [int.cast_one, int.cast_zero] },
  rw h₁,
  rw ←sum_boole,
  simp only [nat.coprime],
  simp_rw [←this],
  have hgcddiv : ∀ x : ℕ, (x.gcd P).divisors = (P.divisors).filter (λ d, d ∣ x), -- x ≠ 0
  { intros x,
    ext m,
    simp only [nat.mem_divisors, mem_filter, nat.dvd_gcd_iff, hP, nat.gcd_eq_zero_iff, ne.def,
      and_false, not_false_iff, and_true, and_comm (m ∣ P) (m ∣ x)] },
  simp_rw [hgcddiv, sum_filter],
  rw sum_comm,
  simp_rw [←mul_boole _ (μ _ : ℝ), ←mul_sum],
  simp_rw [sum_boole],
  have : ∑ x in P.divisors, (μ x : ℝ) * ((filter (λ i, x ∣ i) (finset.range(N))).card : ℝ) =
      ∑ x in P.divisors, (μ x : ℝ) * ((N / x : ℝ) - (1/x - 1 + int.fract ((N-1) / x))),
  { rw sum_congr rfl,
    intros x hx,
    rw count_divisors',
    rw nat.mem_divisors at hx,
    exact ne_zero_of_dvd_ne_zero hx.2 hx.1, exact hN0,
    },
  simp_rw [this, mul_sub],
  rw sum_sub_distrib,
  simp_rw [mul_div_assoc', mul_comm _ (N : ℝ), mul_div_assoc],
  rw ←mul_sum,
  have hP_divisors : P.divisors.filter nat.prime =
    (range N).filter (λ p, nat.prime p ∧ y ≤ p ∧ (p : ℝ) ≤ z),
  { rw [←nat.prime_divisors_eq_to_filter_divisors_prime, product_of_primes_factors_to_finset],
    simp only [mem_filter, implies_true_iff] {contextual := tt} },
  have hP_divisors' :
    filter nat.prime (Icc 1 ⌊z⌋₊ \ Icc 1 ⌊y⌋₊) ⊆ P.divisors.filter nat.prime,
  {
    rw [hP_divisors, Icc_sdiff_Icc_left], intros n hn,
    simp only [mem_filter, mem_Ioc, mem_range, and_assoc],
    rw [mem_filter, mem_Ioc, nat.le_floor_iff, nat.floor_lt'] at hn,
    refine ⟨_,hn.2,_,hn.1.2⟩,
    exact_mod_cast lt_of_le_of_lt hn.1.2 hzN, refine le_of_lt _, exact hn.1.1,
    exact nat.prime.ne_zero hn.2,
    refine le_trans _ h, refine le_trans zero_le_one hy,
    rw nat.le_floor_iff, refine le_trans _ h, refine nat.floor_le _,
    exact le_trans zero_le_one hy,
    refine le_trans _ h, refine le_trans zero_le_one hy, rw nat.le_floor_iff,
    exact_mod_cast hy, exact le_trans zero_le_one hy,
  },
  have hPsum : ∑ (x : ℕ) in P.divisors, (μ x : ℝ) / x ≤
    (partial_euler_product ⌊y⌋₊) / (partial_euler_product ⌊z⌋₊),
  { rw [moebius_rec_sum hP, partial_euler_product, partial_euler_product, prod_inv_distrib,
      prod_inv_distrib, inv_div_inv, ←prod_sdiff'', ←filter_sdiff],
    refine prod_le_prod_of_subset_of_le_one _ _ _,
    { convert hP_divisors' },
    intros p hp, rw [sub_nonneg, inv_le_one_iff], right, norm_cast, rw mem_filter at hp,
    refine le_of_lt (nat.prime.one_lt hp.2), intros p hp1 hp2, refine sub_le_self _ _,
    rw inv_nonneg, exact nat.cast_nonneg p, intros p hp,
    rw [mem_filter, mem_Icc], rw [mem_filter, mem_Icc] at hp, refine ⟨⟨hp.1.1,_⟩,hp.2⟩,
    refine le_trans hp.1.2 _,
    rw nat.le_floor_iff, refine le_trans _ h, refine nat.floor_le _,
    exact le_trans zero_le_one hy,
    refine le_trans _ h, refine le_trans zero_le_one hy,
    intros p hp, refine ne_of_gt _, rw [sub_pos, inv_lt_one_iff],
    right, norm_cast, rw mem_filter at hp,
    refine nat.prime.one_lt hp.2,
  },
  rw [sub_eq_add_neg],
  refine add_le_add _ _,
  refine mul_le_mul_of_nonneg_left hPsum _,
  exact nat.cast_nonneg N, refine le_trans (le_abs_self _) _,
  rw [abs_neg], refine le_trans (abs_sum_le_sum_abs _ _) _,
  calc _ ≤ (2:ℝ)*(σ 0 P : ℝ) :_
     ... ≤ _ :_,
  rw nat.arithmetic_function.sigma_zero_apply,
  refine le_trans (finset.sum_le_card_nsmul _ _ 2 _) _,
  intros d hd, rw [abs_mul], rw ← one_mul (2:ℝ), refine mul_le_mul _ _ _ _,
  by_cases hdsq : squarefree d,
  rw [nat.arithmetic_function.moebius_apply_of_squarefree hdsq], norm_cast,
  rw [abs_pow, abs_neg, abs_one, one_pow],
  rw nat.arithmetic_function.moebius_eq_zero_of_not_squarefree hdsq, norm_cast,
  exact zero_le_one,
  rw [← add_sub_right_comm, ← add_sub], refine le_trans (abs_add _ _) _,
  transitivity (1:ℝ)+1, refine add_le_add _ _,
  rw [abs_of_nonneg, one_div_le], norm_num1, norm_cast, rw nat.succ_le_iff,
  exact nat.pos_of_mem_divisors hd, exact_mod_cast nat.pos_of_mem_divisors hd,
  exact zero_lt_one, rw one_div_nonneg, exact nat.cast_nonneg d,
  rw [abs_of_nonpos, neg_sub], refine sub_le_self _ _, refine int.fract_nonneg _,
  rw sub_nonpos, refine le_of_lt (int.fract_lt_one _), norm_num1,
  refine abs_nonneg _, exact zero_le_one,
  simp only [nsmul_eq_mul], rw mul_comm,
  have hPsq : squarefree P, { refine prod_primes_squarefree _,
    intros p hp, rw mem_filter at hp, exact hp.2.1, },
  rw divisor_count_eq_pow_iff_squarefree.2 hPsq, rw nat.cast_pow, norm_num1,
  rw [← rpow_nat_cast, mul_comm, ← rpow_add_one],
  refine rpow_le_rpow_of_exponent_le one_le_two _,
  rw [nat.arithmetic_function.card_distinct_factors_apply, ← list.card_to_finset],
  transitivity ((Icc 0 ⌊z⌋₊).card : ℝ),
  norm_cast,
  transitivity (insert 0 P.factors.to_finset).card, rw finset.card_insert_of_not_mem,
  rw list.mem_to_finset, intro hbad, refine nat.not_prime_zero _,
  exact nat.prime_of_mem_factors hbad,
  refine finset.card_le_of_subset _, intros p hp,
  rw mem_insert at hp, cases hp with hp₁ hp₂, rw hp₁,
  simp only [left_mem_Icc, zero_le'],
  rw [list.mem_to_finset, mem_factors_prod] at hp₂,
  rcases hp₂ with ⟨q,hq1,hq2⟩, rw mem_filter at hq1,
  rw [nat.factors_prime hq1.2.1, list.mem_singleton] at hq2, rw [hq2, mem_Icc],
  refine ⟨zero_le q,_⟩, rw nat.le_floor_iff, exact hq1.2.2.2,
  refine le_trans _ h, exact le_trans zero_le_one hy,
  intros n hn, rw mem_filter at hn, exact nat.prime.ne_zero hn.2.1,
  rw [nat.card_Icc, nat.cast_sub], push_cast, rw sub_zero,
  rw add_le_add_iff_right, refine nat.floor_le _,
  refine le_trans _ h, exact le_trans zero_le_one hy,
  exact zero_le (⌊z⌋₊ + 1), refine ne_of_gt zero_lt_two,
end

lemma sieve_lemma_prec' : ∃ C c : ℝ, (0 < C) ∧ (0 < c) ∧
  ∀ᶠ (N : ℕ) in at_top, ∀ y z : ℝ, (2 ≤ y) → (1 < z) → (z ≤ c*log N) →
   (((finset.range(N)).filter(λ n, ∀ p : ℕ, prime p → p ∣ n →
       ((p : ℝ) < y) ∨ (z < p))).card : ℝ) ≤ C*(log y/log z)*N :=
begin
  rcases weak_mertens_third_lower_all with ⟨C₁,hC₁,hml⟩,
  rcases weak_mertens_third_upper_all with ⟨C₂,hC₂,hmu⟩,
  let C := 1 / C₁ * C₂ * 2,
  let c := (1:ℝ)/2,
  have h0C : 0 < C, { refine mul_pos _ zero_lt_two,
    refine mul_pos _ hC₂, rw one_div_pos, exact hC₁, },
  use C, use c, refine ⟨h0C,one_half_pos,_⟩,
  filter_upwards [tendsto_coe_nat_at_top_at_top.eventually (eventually_gt_at_top (0:ℝ)),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually (eventually_gt_at_top (1*2:ℝ)),
    (another_weird_tendsto_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
       (eventually_ge_at_top (1 / (C / 2 * log 2)))
    ]
    with N h0N hlogN hweirdN,
  intros y z h2y h1z hzN,
  have h0logN : 0 < log N, { refine lt_trans _ hlogN, norm_num1, },
  have hzN' : z < N,
  { apply hzN.trans_lt ((log_lt_self h0N).trans_le' _),
    refine mul_le_of_le_one_left h0logN.le _,
    change (1 : ℝ) / 2 ≤ 1,
    refine half_le_self zero_le_one },
  refine le_trans (sieve_lemma_prec N y z (h2y.trans' (by norm_num1)) hzN') _,
  rw [← add_halves C, add_mul, add_mul], refine add_le_add _ _,
  rw [mul_le_mul_right h0N, mul_div, div_le_div_iff],
  specialize hmu y, specialize hml z (le_of_lt h1z),
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hml,
  rw [norm_eq_abs, abs_of_pos, norm_eq_abs, abs_of_pos] at hmu,
  transitivity (C₂*log(y)*log z), refine mul_le_mul_of_nonneg_right (hmu _) _, exact h2y,
  exact log_nonneg (le_of_lt h1z), transitivity (C₂*log(y)*partial_euler_product ⌊z⌋₊/C₁),
  rw [le_div_iff hC₁, mul_assoc _ _ C₁], refine mul_le_mul_of_nonneg_left _ _,
  rw mul_comm, exact hml, refine mul_nonneg (le_of_lt hC₂) (log_nonneg _),
  refine le_trans one_le_two h2y, rw [div_eq_mul_one_div, mul_comm _ (1/C₁), ← mul_assoc,
    mul_le_mul_right, ← mul_assoc],
  transitivity ((1/C₁)*C₂*(log y)), rw mul_le_mul_left, refine mul_pos _ hC₂,
  rw one_div_pos, exact hC₁, rw [mul_le_mul_right, le_div_iff], exact zero_lt_two,
  refine log_pos _, exact lt_of_lt_of_le one_lt_two h2y,
  exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound, refine log_pos _,
  exact lt_of_lt_of_le one_lt_two h2y,
  exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound,
  exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound, exact log_pos h1z,
  exact lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound, exact log_pos h1z,
  transitivity ((C / 2 * (log 2))*N / log z),
  transitivity (2:ℝ)^(((1:ℝ)/2)*log N+1),
  refine rpow_le_rpow_of_exponent_le one_le_two _, rw add_le_add_iff_right, exact hzN,
  rw le_div_iff, transitivity ((2:ℝ)^(((1:ℝ)/2)*log N+1))*(log(((1:ℝ)/2)*log N)),
  rw mul_le_mul_left, rw log_le_log, exact hzN, exact lt_trans zero_lt_one h1z,
  exact mul_pos (one_half_pos) h0logN, refine rpow_pos_of_pos zero_lt_two _,
  rw [← one_le_div, ← mul_div, ← div_le_iff'], exact hweirdN,
  refine mul_pos _ _, exact div_pos h0C zero_lt_two,
  exact log_pos one_lt_two, refine mul_pos _ _, refine rpow_pos_of_pos zero_lt_two _,
  refine log_pos _, rw [mul_comm, ← div_eq_mul_one_div, lt_div_iff], exact hlogN,
  exact zero_lt_two, exact log_pos h1z, rw [mul_assoc, ← mul_div, mul_assoc,
    mul_le_mul_left, mul_comm _ (N:ℝ), ← mul_div, mul_comm, mul_le_mul_right,
    div_le_div_right, log_le_log], exact h2y, exact zero_lt_two,
  exact lt_of_lt_of_le zero_lt_two h2y, exact log_pos h1z, exact h0N,
  exact div_pos h0C zero_lt_two,
end

lemma plogp_tail_bound (a : ℝ) (ha : 0 < a): ∃ c : ℝ, (0 < c) ∧ ∀ᶠ (N : ℕ) in at_top, ∀ z : ℝ,
  (0 ≤ log(log (⌊z⌋₊))) →
  ∑ (x : ℕ) in filter nat.prime (Icc N ⌊z⌋₊), (a / (log(x/4)*x)) ≤ c*(log(log (⌊z⌋₊)))/log(N/4) :=
begin
  have hmertens := explicit_mertens,
  rw eventually_at_top at hmertens,
  rcases hmertens with ⟨c₁,hmertens⟩,
  let c := a*2,
  use c, refine ⟨mul_pos ha zero_lt_two,_⟩,
  filter_upwards [eventually_gt_at_top 4,
    tendsto_coe_nat_at_top_at_top.eventually (eventually_ge_at_top c₁),
    tendsto_coe_nat_at_top_at_top.eventually (eventually_gt_at_top (exp(1)))]
    with N h4N hcN heN,
  have h0N : (0:ℝ) < N, { norm_cast, exact lt_trans zero_lt_four h4N, },
  have hlogN : 0 < log(N/4), {  refine log_pos _,
    rw one_lt_div, exact_mod_cast h4N, exact zero_lt_four, },
  intros z hz',
  by_cases hz : (N:ℝ) ≤ z,
  have hexpz : exp 1 < ⌊z⌋₊, {
    rw ← nat.le_floor_iff' at hz, refine lt_of_lt_of_le heN _, exact_mod_cast hz,
    refine ne_of_gt _, exact_mod_cast h0N,
   },
  calc _ ≤ ∑ (x : ℕ) in filter nat.prime (Icc N ⌊z⌋₊), (a/log(N/4)) * (1/x) :_
     ... ≤ _ :_,
  refine sum_le_sum _, intros p hp, rw [mem_filter, mem_Icc] at hp,
  rw [div_mul, div_le_div_left ha, ← div_mul, div_one, mul_le_mul_right, log_le_log,
     div_le_div_right], exact_mod_cast hp.1.1, exact zero_lt_four,
  refine div_pos h0N zero_lt_four, refine div_pos _ zero_lt_four, exact_mod_cast (nat.prime.pos hp.2),
  exact_mod_cast (nat.prime.pos hp.2), refine mul_pos _ _, refine log_pos _,
  rw one_lt_div, norm_cast, refine lt_of_lt_of_le h4N hp.1.1, exact zero_lt_four,
  exact_mod_cast (nat.prime.pos hp.2), refine div_pos hlogN _, rw one_div_pos,
  exact_mod_cast (nat.prime.pos hp.2), rw [← mul_sum, div_mul_eq_mul_div, div_le_div_right hlogN,
    ← le_div_iff' ha],
  transitivity ((∑ q in (finset.range (⌊z⌋₊ + 1)).filter is_prime_pow, 1 / q) : ℝ),
  refine sum_le_sum_of_subset_of_nonneg _ _, intros q hq,
  rw [mem_filter, mem_range], rw [mem_filter, mem_Icc, nat.prime_iff] at hq,
  rw nat.lt_succ_iff, refine ⟨hq.1.2,prime.is_prime_pow hq.2⟩,
  intros n hn1 hn2, rw one_div_nonneg, exact nat.cast_nonneg n,
  refine le_trans (hmertens ⌊z⌋₊ _) _, rw ← nat.le_floor_iff' at hz,
  refine le_trans hcN _, exact_mod_cast hz, refine ne_of_gt _,
  exact_mod_cast h0N, rw [le_div_iff ha, mul_comm _ a, ← mul_assoc, mul_le_mul_right],
  refine log_pos _, rw [← exp_lt_exp, exp_log], exact hexpz,
  refine lt_trans _ hexpz, exact exp_pos 1,
  have : Icc N ⌊z⌋₊ = ∅, { refine finset.Icc_eq_empty _, rw nat.le_floor_iff', exact hz,
    refine ne_of_gt _, exact_mod_cast h0N, },
  rw [this, filter_empty, sum_empty], refine div_nonneg _ _, refine mul_nonneg _ _,
  refine mul_nonneg _ zero_le_two, exact le_of_lt ha, exact hz',
  refine log_nonneg _, rw le_div_iff, norm_cast, rw one_mul,
  exact le_of_lt h4N, exact zero_lt_four,
end

lemma filter_div_aux (a b c d: ℝ) (hb : 0 < b) (hc : 0 < c) : ∃ y z w : ℝ,
 (2 ≤ y) ∧ (16 ≤ w) ∧ (0 < z) ∧ (1 < z) ∧ (4*y + 4 ≤ z) ∧ (a ≤ y) ∧ (d ≤ y) ∧ (log w / log z ≤ b) ∧
 (∑ (x : ℕ) in filter nat.prime (Icc ⌈w⌉₊ ⌊z⌋₊), (log y / (log (x/4) * x)) ≤ c) :=
begin
  let y := max (2:ℝ) (max a d),
  have hlogy : 0 < log y, { refine log_pos _, exact lt_of_lt_of_le one_lt_two (le_max_left _ _), },
  rcases plogp_tail_bound (log y) hlogy with ⟨C₁,h0C₁,htail⟩,
  rw eventually_at_top at htail, rcases htail with ⟨C₂',htail'⟩,
  let C₂ := max 1 C₂',
  have haux: asymptotics.is_O_with (1 / (C₁ * (1 / c * (2 * (1 / b))))) at_top (λ (x : ℝ), (log x))
     (λ (x : ℝ), x^((1:ℝ))), {
    refine asymptotics.is_o.def' _ _, refine is_o_log_rpow_at_top _, exact zero_lt_one,
    rw one_div_pos, refine mul_pos h0C₁ _, refine mul_pos _ _, rw one_div_pos, exact hc,
    refine mul_pos zero_lt_two _, rw one_div_pos, exact hb,
    },
  have haux' := tendsto_log_at_top.eventually haux.bound,
  rw eventually_at_top at haux', rcases haux' with ⟨C₃,haux'⟩,
  let z := max (exp (log 4 * 2 / b)) (max C₃ (max (3:ℝ) (max
     (4*y + 4)
     (max (exp (exp (log (16 / 4) * c / C₁)) + 1) (exp (exp (log (C₂ / 4) * c / C₁)) + 1))))),
  let w := 4*exp (C₁ * log (log ⌊z⌋₊) / c),
  have hz₁ : exp (log 4 * 2 / b) ≤ z, { refine le_max_left _ _, },
  have hz₂ : C₃ ≤ z, { refine le_trans (le_max_left _ _) (le_max_right _ _), },
  have hz₄' : 3 ≤ z, { refine le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _) ), },
  have hz₄ : 2 < z, { refine lt_of_lt_of_le _ hz₄', norm_num1, },
  have hz₅ : exp(1) < z, { refine lt_of_lt_of_le _ hz₄',
    refine lt_trans real.exp_one_lt_d9 _, norm_num1, },
  have hz₆ : (4*y + 4) ≤ z, { refine le_trans (le_max_left _ _)
   (le_trans (le_max_right _ _) ((le_trans (le_max_right _ _) (le_max_right _ _) ))), },
  have hzfloor : z - 1 ≤ ⌊z⌋₊, { rw sub_le_iff_le_add, refine le_of_lt (nat.lt_floor_add_one _), },
  have hz₃ : 1 ≤ z := le_trans one_le_two (le_of_lt hz₄),
  have hz₀ : 0 < z := lt_of_lt_of_le zero_lt_one hz₃,
  have hz₈' : exp (exp (log (16 / 4) * c / C₁)) + 1 ≤ z, { refine le_trans (le_max_left _ _)
   (le_trans (le_max_right _ _) ((le_trans (le_max_right _ _)
      ((le_trans (le_max_right _ _) (le_max_right _ _) ))))), },
  have hz₉' : exp (exp (log (C₂ / 4) * c / C₁)) + 1 ≤ z, { refine le_trans (le_max_right _ _)
   (le_trans (le_max_right _ _) ((le_trans (le_max_right _ _)
      ((le_trans (le_max_right _ _) (le_max_right _ _) ))))), },
  have hz₈ : log (16 / 4) * c / C₁ ≤ log (log ⌊z⌋₊), {
    rw [← exp_le_exp, exp_log, ← exp_le_exp, exp_log], refine le_trans _ hzfloor,
    rw le_sub_iff_add_le, exact hz₈', norm_cast, rw nat.floor_pos, exact hz₃,
    refine log_pos _, refine lt_of_lt_of_le _ hzfloor, rw lt_sub_iff_add_lt,
    exact hz₄,
   },
  have hz₉ : log (C₂ / 4) * c / C₁ ≤ log (log ⌊z⌋₊), {
    rw [← exp_le_exp, exp_log, ← exp_le_exp, exp_log], refine le_trans _ hzfloor,
    rw le_sub_iff_add_le, exact hz₉', norm_cast, rw nat.floor_pos, exact hz₃,
    refine log_pos _, refine lt_of_lt_of_le _ hzfloor, rw lt_sub_iff_add_lt,
    exact hz₄,
   },
  have hz₇ : (0 ≤ log(log (⌊z⌋₊))), { refine le_trans _ hz₈, refine div_nonneg _ _,
    refine mul_nonneg _ _, refine log_nonneg _, norm_num1, exact le_of_lt hc,
    exact le_of_lt h0C₁, },
  have hzw : (exp (log w / b)) ≤ z, {
    rw [← log_le_log, log_exp, div_le_iff, log_mul, log_exp, ← add_halves (log z*b)],
    refine add_le_add _ _, rw [le_div_iff, ← div_le_iff, ← exp_le_exp, exp_log],
    exact hz₁, exact hz₀, exact hb, exact zero_lt_two,
    rw [le_div_iff, div_eq_mul_one_div, ← div_le_iff, div_eq_mul_one_div, mul_assoc,
      mul_assoc, mul_comm C₁, mul_assoc, mul_comm], specialize haux' z hz₂,
    rw [← le_div_iff', div_eq_mul_one_div, mul_comm],
    transitivity log(log z), rw [log_le_log, log_le_log], refine nat.floor_le _,
    exact le_of_lt hz₀, norm_cast, rw nat.floor_pos, exact hz₃, exact hz₀, refine log_pos _,
    norm_cast, rw ← nat.succ_lt_succ_iff, rw ← @nat.cast_lt ℝ _ _ _ _,
    refine lt_trans _ (nat.lt_succ_floor _), norm_num1, exact hz₄, refine log_pos _,
    exact lt_trans one_lt_two hz₄, rw [norm_eq_abs, norm_eq_abs, rpow_one, abs_of_pos,
      abs_of_pos] at haux', exact haux', refine log_pos (lt_trans one_lt_two hz₄),
    refine log_pos _, rw [← exp_lt_exp, exp_log], exact hz₅, exact hz₀,
    refine mul_pos h0C₁ _, refine mul_pos _ _, rw one_div_pos, exact hc,
    refine mul_pos zero_lt_two _, rw one_div_pos, exact hb, exact hb, exact zero_lt_two,
    exact four_ne_zero, refine exp_ne_zero _, exact hb, refine exp_pos _, exact hz₀,
  },
  have h16w : 16 ≤ w, {
    rw [← div_le_iff', ← log_le_log, log_exp, le_div_iff, ← div_le_iff'], exact hz₈,
    exact h0C₁, exact hc, norm_num1, refine exp_pos _, exact zero_lt_four,
  },
  have hC₂w : (C₂ :ℝ) ≤ w, {
    rw [← div_le_iff', ← log_le_log, log_exp, le_div_iff, ← div_le_iff'], exact hz₉,
    exact h0C₁, exact hc, refine div_pos _ _, norm_cast, refine lt_of_lt_of_le zero_lt_one _,
    refine le_max_left _ _, norm_num1, refine exp_pos _,
    exact zero_lt_four,
  },
  have h0w' : (1:ℝ) < ⌈w⌉₊ / 4, { rw lt_div_iff, refine lt_of_lt_of_le _ (nat.le_ceil _),
    refine lt_of_lt_of_le _ h16w, norm_num1, exact zero_lt_four, },
  refine ⟨y,z,w,le_max_left _ _,h16w, hz₀, (lt_trans one_lt_two hz₄), hz₆, le_trans (le_max_left _ _) (le_max_right _ _),
     le_trans (le_max_right _ _) (le_max_right _ _),_,_⟩,
  rw [div_le_iff, ← div_le_iff' hb, ← exp_le_exp, exp_log], exact hzw, exact hz₀,
  refine log_pos _, refine lt_trans one_lt_two hz₄,
  have h₁ : C₂' ≤ ⌈w⌉₊, {
    rw ← @nat.cast_le ℝ _ _ _ _, refine le_trans _ (nat.le_ceil _),
    refine le_trans _ hC₂w, norm_cast, refine le_max_right _ _,
   },
  refine le_trans (htail' ⌈w⌉₊ h₁ z hz₇) _,
  rw [div_le_iff, ← div_le_iff' hc, ← exp_le_exp, exp_log],
  rw le_div_iff, refine le_trans _ (nat.le_ceil _), rw mul_comm _ (4:ℝ),
  exact zero_lt_four,  exact lt_trans zero_lt_one h0w', exact log_pos h0w',
end

lemma filter_div  (D : ℝ) (hD : 0 < D) : ∃ y z : ℝ,
(1 ≤ y) ∧ (4*y + 4 ≤ z) ∧ (0<z) ∧ (2 / (1 / (5 * D * 2) * D) ≤ y) ∧ ((2 / (1 / (5 * D * 2))) ≤ y) ∧
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ range(N),
   (((A).filter (λ n, ¬ ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧
      (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z))).card : ℝ) ≤ N/(5*D)
    :=
begin
  rcases sieve_lemma_prec' with ⟨C,c,h0C,h0c,hsieve⟩,
  have haux1 : 0 < (1 / (10 * D))/C, { refine div_pos _ h0C, rw one_div_pos, refine mul_pos _ hD, norm_num1, },
  have haux2 : 0 < (1 / (20 * D))/C, { refine div_pos _ h0C, rw one_div_pos, refine mul_pos _ hD, norm_num1, },
  rw filter.eventually_at_top at hsieve,
  rcases hsieve with ⟨T,hsieve⟩,
  rcases (filter_div_aux (2 / (1 / (5 * D * 2) * D)) _ _ ((2 / (1 / (5 * D * 2)))) haux1 haux2)
     with ⟨y,z,w,h2y,h16w,h0z,h1z,hyz,hDy,hDy',hwzD',hzsum⟩,
  have hwzD : C * (log w / log z) ≤ 1 / (10 * D), { rw ← le_div_iff', exact hwzD', exact h0C, },
  have h2w : 2 ≤ w, { refine le_trans _ h16w, norm_num1, },
  have h1y : 1 ≤ y := le_trans one_le_two h2y,
  have h0zc : (0:ℝ) < ⌊z⌋₊, { norm_cast, rw ← nat.succ_lt_succ_iff, rw ← @nat.cast_lt ℝ _ _ _ _, push_cast,
    rw zero_add, refine lt_trans _ (nat.lt_floor_add_one _), refine lt_of_lt_of_le _ hyz,
    transitivity (4+(4:ℝ)*1), norm_num1,
    rw [add_comm _ (4:ℝ), real.add_lt_add_iff_left, mul_lt_mul_left zero_lt_four],
    exact lt_of_lt_of_le one_lt_two h2y, exact real.nontrivial,
  },
  refine ⟨y,z,h1y,hyz,h0z,hDy,hDy',_⟩,
  filter_upwards [tendsto_coe_nat_at_top_at_top.eventually (eventually_gt_at_top (0:ℝ)),
    tendsto_coe_nat_at_top_at_top.eventually (eventually_ge_at_top ((T:ℝ)*⌊z⌋₊)),
    tendsto_coe_nat_at_top_at_top.eventually (eventually_ge_at_top
       ((∑ (x : ℕ) in filter nat.prime (Icc ⌈w⌉₊ ⌊z⌋₊), C * (log y / log (x/4) * 1)) * (20 * D))),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually (eventually_ge_at_top
       ((4:ℝ) * ⌊z⌋₊ / c + log ⌊z⌋₊)),
     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually (eventually_ge_at_top
       (z/c)),
       eventually_ge_at_top T]
    with N h0N hTzN hweirdN hlogN1 hlogN2 hlarge,
  intros A hA, transitivity (((finset.range(N)).filter (λ n, ¬ ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧
      (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z))).card : ℝ),
  norm_cast, refine card_le_of_subset _, refine filter_subset_filter _ hA,
  have hz' : z ≤ c*log N, { rw ← div_le_iff', exact hlogN2, exact h0c, },
  let X := ((finset.range(N)).filter(λ n, ∀ p : ℕ, prime p → p ∣ n →
                     ((p : ℝ) < w) ∨ (z < p))),
  let Y := (λ m, (finset.range(N)).filter(λ n, m ∣ n ∧ ∀ p : ℕ, prime p → p ∣ n →
                     ((p : ℝ) < y) ∨ (m < 4*p))),
  have hXbound : (X.card : ℝ) ≤ C*(log w/log z)*N := hsieve N hlarge w z h2w h1z hz',
  have hYlocbound : ∀ m : ℕ, (16 ≤ m) → ((m:ℝ)/4 ≤ c*log ⌈(N:ℝ)/m⌉₊) → (T ≤ ⌈(N:ℝ)/m⌉₊) →
      ((Y m).card : ℝ) ≤ C*(log y/log ((m:ℝ)/4))*(N/m + 1), {
    intros m h16m hm hTm,
    have h0m : 0 < m, { refine lt_of_lt_of_le _ h16m, norm_num1, },
    transitivity (((finset.range(⌈(N:ℝ)/m⌉₊)).filter(λ n, ∀ p : ℕ, prime p → p ∣ n →
                     ((p : ℝ) < y) ∨ (((m:ℝ)/4 < p)))).card : ℝ),
    norm_cast, refine finset.card_le_card_of_inj_on (λ i, i / m) _ _,
    intros n hn, rw [mem_filter, mem_range], rw [mem_filter, mem_range] at hn,
    refine ⟨_,_⟩, rw nat.lt_ceil, rw nat.cast_div hn.2.1,
    rw div_lt_div_right, norm_cast, exact hn.1, exact_mod_cast h0m, norm_cast,
    intro hbad, rw hbad at h0m, exact nat.lt_asymm h0m h0m,
    intros p hp hpnm, rw [div_lt_iff, mul_comm _ (4:ℝ)], norm_cast,
    refine hn.2.2 p hp _, refine dvd_trans hpnm (nat.div_dvd_of_dvd hn.2.1), exact zero_lt_four,
    intros a ha b hb hab, rw mem_filter at ha, rw mem_filter at hb,
    rw [nat.div_eq_iff_eq_mul_right h0m ha.2.1, nat.mul_div_cancel_left' hb.2.1] at hab, exact hab,
    have h1m' : 1 < ((m:ℝ)/4), { rw one_lt_div, norm_cast,
       refine lt_of_lt_of_le _ h16m, norm_num1, exact zero_lt_four, },
    refine le_trans (hsieve ⌈(N:ℝ)/m⌉₊ hTm y ((m:ℝ)/4) h2y h1m' hm) _,
    rw mul_le_mul_left, refine le_of_lt (nat.ceil_lt_add_one _), refine div_nonneg (nat.cast_nonneg N) (nat.cast_nonneg m),
    refine mul_pos h0C (div_pos (log_pos _) (log_pos _)), exact lt_of_lt_of_le one_lt_two h2y,
    have h14 : (1:ℝ) < 4*1 := by norm_num1, refine lt_of_lt_of_le h14 _,
    rw [mul_one, le_div_iff], norm_num1, norm_cast, exact h16m, exact zero_lt_four,
  },
  let Y' := ((finset.Icc ⌈w⌉₊ ⌊z⌋₊).filter(λ r:ℕ, nat.prime r)).bUnion (λ p, Y p),
  have hcover : (finset.range(N)).filter (λ n, ¬ ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧
      (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z)) ⊆ X ∪ Y', {
        intros n hn, rw [mem_filter, not_exists] at hn,
        rw [mem_union, or_iff_not_imp_left, mem_filter, mem_bUnion], intro hn',
        rw [not_and_distrib, or_iff_not_imp_left, not_not] at hn', specialize hn' hn.1,
        rw [not_forall] at hn', rcases hn' with ⟨p,hp⟩, rw [not_imp, not_imp,
           decidable.not_or_iff_and_not, not_lt, not_lt] at hp,
        refine ⟨p,_,_⟩,
        rw [mem_filter, mem_Icc], rw ← nat.prime_iff at hp, refine ⟨⟨_,_⟩,hp.1⟩, rw nat.ceil_le, exact hp.2.2.1,
        rw nat.le_floor_iff', exact hp.2.2.2, rw ← pos_iff_ne_zero, exact nat.prime.pos hp.1,
        rw mem_filter, refine ⟨hn.1,hp.2.1,_⟩, intros q hq hqn,
        have hn'' := hn.2 q, rw not_exists at hn'', specialize hn'' p,
        rw [not_and_distrib, or_iff_not_imp_left, not_not] at hn'', specialize hn'' hqn,
        rw [not_and_distrib, or_iff_not_imp_left, not_not] at hn'', specialize hn'' hp.2.1,
        rw [not_and_distrib] at hn'', cases hn'' with hn''1 hn''2,
        rw ← not_le, left, exact hn''1, right, rw [not_and_distrib, or_iff_not_imp_right, not_not] at hn''2,
        specialize hn''2 hp.2.2.2, rw not_le at hn''2, exact hn''2,
       },
  calc _ ≤ ((X∪Y').card :ℝ) :_
     ... ≤ (X.card : ℝ) + (Y'.card : ℝ) :_
     ... ≤ C*(log w/log z)*N + (Y'.card : ℝ) :_
     ... ≤ C*(log w/log z)*N + ∑ p in (finset.Icc ⌈w⌉₊ ⌊z⌋₊).filter(λ r:ℕ, nat.prime r), ((Y p).card) :_
     ... ≤ C*(log w/log z)*N + ∑ p in (finset.Icc ⌈w⌉₊ ⌊z⌋₊).filter(λ r:ℕ, nat.prime r), C*(log y/log (p/4))*(N/p + 1) :_
     ... ≤ (N:ℝ)/(10*D) + (N:ℝ)/(10*D) :_
     ... ≤ _ :_,
  norm_cast, refine card_le_of_subset hcover,
  norm_cast, refine card_union_le _ _, rw add_le_add_iff_right, exact hXbound,
  rw add_le_add_iff_left, norm_cast, exact finset.card_bUnion_le, rw add_le_add_iff_left,
  refine sum_le_sum _, intros p hp, rw [mem_filter, mem_Icc] at hp,
  have h16p : 16 ≤ p, { refine le_trans _ hp.1.1, rw ← @nat.cast_le ℝ _ _ _ _,
     refine le_trans _ (nat.le_ceil _), norm_cast, exact h16w,},
  refine hYlocbound p h16p _ _,
  transitivity ((4:ℝ)*⌊z⌋₊), norm_cast, rw [div_le_iff, mul_comm _ (4:ℝ)], push_cast, rw [← mul_assoc], norm_cast,
  transitivity (1*⌊z⌋₊), rw one_mul, exact hp.1.2, rw mul_le_mul_right, norm_num1, exact_mod_cast h0zc, exact zero_lt_four,
  rw ← div_le_iff', transitivity log((N:ℝ)/p), transitivity log((N:ℝ)/⌊z⌋₊), rw [log_div, le_sub_iff_add_le],
  exact hlogN1, exact ne_of_gt h0N, exact ne_of_gt h0zc, rw [log_le_log, div_le_div_left], exact_mod_cast hp.1.2,
  exact h0N,  exact h0zc, norm_cast, exact nat.prime.pos hp.2, exact div_pos h0N h0zc,
  refine div_pos h0N _, exact_mod_cast (nat.prime.pos hp.2), rw log_le_log, refine nat.le_ceil _,
  refine div_pos h0N _, exact_mod_cast (nat.prime.pos hp.2), refine lt_of_lt_of_le _ (nat.le_ceil _),
  refine div_pos h0N _, exact_mod_cast (nat.prime.pos hp.2), exact h0c, rw ← @nat.cast_le ℝ _ _ _ _,
  refine le_trans _ (nat.le_ceil _), rw le_div_iff,
  by_cases h0T : (0:ℝ) < T,
  transitivity ((T:ℝ)*⌊z⌋₊), rw mul_le_mul_left h0T, exact_mod_cast hp.1.2, exact hTzN,
  transitivity (0:ℝ), rw mul_nonpos_iff, right, rw not_lt at h0T,
  refine ⟨h0T, le_of_lt _⟩, exact_mod_cast (nat.prime.pos hp.2), exact nat.cast_nonneg N,
  exact_mod_cast (nat.prime.pos hp.2),
  refine add_le_add _ _, rw [div_eq_mul_one_div (N:ℝ), mul_comm (N:ℝ), mul_le_mul_right h0N],
  exact hwzD, simp_rw [mul_assoc, mul_add],
  calc _ ≤ (N:ℝ)/(20*D) + (N:ℝ)/(20*D) :_
     ... ≤ _ :_,
  rw sum_add_distrib, refine add_le_add _ _, simp_rw [← mul_div_mul_comm, mul_comm _ (N:ℝ), ← mul_div,
     ← mul_assoc], rw [← mul_sum, mul_comm C, mul_assoc, div_eq_mul_one_div (N:ℝ), mul_le_mul_left h0N,
      ← le_div_iff' h0C], exact hzsum, rw le_div_iff, exact hweirdN, refine mul_pos _ hD, norm_num1,
  rw [← two_mul, ← le_div_iff', div_div, mul_comm _ (2:ℝ), ← mul_assoc], norm_num1, refl,
  norm_num1,
  rw [← two_mul, ← le_div_iff', div_div, mul_comm _ (2:ℝ), ← mul_assoc], norm_num1, refl,
  norm_num1,
end


lemma turan_primes_estimate : ∃ (C : ℝ), ∀ᶠ (N : ℕ) in at_top,
  (∑ n in (Icc 1 N), ((ω n : ℝ) - log(log N))^2
  ≤  C * N * log(log N)  ) :=
begin
  rcases sum_prime_counting with ⟨C1,hsum⟩,
  rcases sum_prime_counting_sq with ⟨C2,hsumsq⟩,
  let C := (C2+2*C1),
  use C,
  filter_upwards [hsum, hsumsq,
       (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ))]
   with N hlargesum hlargesumsq hlargeN,
  have hcardIcc : (Icc 1 N).card = N, {
    rw nat.card_Icc, simp only [nat.add_succ_sub_one, add_zero],
   },
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_const, nsmul_eq_mul, hcardIcc],
  calc _ ≤ ∑ (x : ℕ) in Icc 1 N, (ω x:ℝ) ^ 2 - 2*(-(C1*N)+N*log(log N))*log(log N) + N * log (log N) ^ 2 :_
     ... ≤ C2*N*log(log N) + N*(log(log N))^2- 2*(-(C1*N)+N*log(log N))*log(log N) + N * log (log N) ^ 2 :_
     ... = _ :_,
  rw [add_le_add_iff_right, sub_le_sub_iff_left, mul_le_mul_right, mul_le_mul_left zero_lt_two],
  rw neg_add_eq_sub, exact hlargesum, exact real.nontrivial, exact hlargeN,
  rw [add_le_add_iff_right, sub_le_sub_iff_right, add_comm], exact hlargesumsq, ring_nf,
  rw [mul_assoc (2*C1), mul_comm _ C2, ← add_mul, ← mul_assoc],
end



lemma filter_regular  (D : ℝ) (hD : 0 < D) : ∀ᶠ (N : ℕ) in at_top,
  ∀ A ⊆ range(N),
   ((A.filter(λ n:ℕ, n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)))).card : ℝ)
   ≤ N/D :=
begin
  rcases turan_primes_estimate with ⟨C,hturan⟩,
  have h100 : (0:ℝ) < 1/100 := by norm_num1,
  filter_upwards [hturan,
       (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ)),
       (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top (
    C / (1 / 100) / (1 / D * (1 / 100)))),
       (tendsto_coe_nat_at_top_at_top).eventually (eventually_gt_at_top (0:ℝ))]
    with N hNturan hlargeN hlargeN2 hlargeN3,
  clear hturan,
  intros A hA,
  by_contra, rw not_le at h, rw ← not_lt at hNturan, refine hNturan _, clear hNturan,
  let A' := A.filter(λ n:ℕ, n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N))),
  calc _ ≤ ((N:ℝ)/D)*((1/100)*log(log N))^2 :_
     ... < (A'.card : ℝ)*((1/100)*log(log N))^2 :_
     ... ≤ (∑ n in A', ((ω n : ℝ) - log(log N))^2) :_
     ... ≤ _ :_,
  rw [mul_comm C, div_eq_mul_one_div (N:ℝ), mul_assoc, mul_assoc, mul_le_mul_left, sq,
      ← mul_assoc, ← mul_assoc, mul_le_mul_right, ← div_le_iff, ← mul_assoc,
     ← div_le_iff'], exact hlargeN2,
  refine mul_pos _ _, rw one_div_pos, exact hD, exact h100, exact h100, exact hlargeN,
  exact hlargeN3,
  rw mul_lt_mul_right, exact h, refine sq_pos_of_pos _, refine mul_pos _ hlargeN,
  norm_num1, rw [← nsmul_eq_mul], refine finset.card_nsmul_le_sum _ _ _ _,
  clear h, intros n hn,
  rw [mem_filter, not_and_distrib] at hn,
  rw [sq_le_sq, le_abs, abs_of_pos], cases hn.2.2 with hn1 hn2,
  right, rw [neg_sub, le_sub, ← one_sub_mul], rw not_le at hn1, norm_num1,
  exact le_of_lt hn1, left, rw [le_sub_iff_add_le, add_comm, ← one_add_mul],
  rw not_le at hn2, refine le_trans _ (le_of_lt hn2), rw mul_le_mul_right, norm_num1,
  exact hlargeN, refine mul_pos _ hlargeN, norm_num1,
  refine sum_le_sum_of_subset_of_nonneg _ _,
  intros m hm, rw mem_Icc, refine ⟨_,_⟩,
  rw [nat.succ_le_iff, pos_iff_ne_zero], intro hbad,
  rw [hbad, mem_filter] at hm, refine hm.2.1 _, refl,
  have htempy := hA ((filter_subset _ _) hm),
  rw mem_range at htempy, exact le_of_lt htempy,
  intros n hn1 hn2, refine sq_nonneg _,
end

lemma log_helper (y : ℝ) (h : 0 < y) (h'' : y ≤ 1/2) : -2*y ≤ log(1-y) :=
begin
 have h' : y < 1 := lt_of_le_of_lt h'' one_half_lt_one,
 rw [neg_mul, neg_le, ← log_inv],
 refine le_trans (real.log_le_sub_one_of_pos _) _, rw [inv_pos, sub_pos], exact h',
 rw [sub_le_iff_le_add, ← one_div, div_le_iff, add_mul, one_mul, mul_sub, mul_one, mul_assoc,
    ← sq],
 convert_to 1 ≤ 1+(y-2*y^2) using 0, { ring_nf, },
 nth_rewrite 0 ← add_zero (1:ℝ), refine add_le_add _ _, refl, rw sub_nonneg,
 nth_rewrite 1 ← one_mul y, rw sq, rw ← mul_assoc, rw mul_le_mul_right,
 rw ← le_div_iff', exact h'', exact zero_lt_two, exact h, rw sub_pos, exact h',
end

lemma nat_floor_real_le_floor {M : ℝ} {N : ℕ} (h : M ≤ N) : ⌊M⌋₊ ≤ ⌊N⌋₊ :=
begin
  have : ⌊N⌋₊ = ⌊(N:ℝ)⌋₊, { rw nat.floor_eq_iff, refine ⟨_,_⟩, norm_cast,
    rw nat.floor_coe, rw nat.floor_coe, norm_cast, exact lt_add_one N, exact nat.zero_le N,},
  rw this, rw nat.floor_coe, refine nat.floor_le_of_le h,
end

lemma diff_mertens_sum : ∃ c : ℝ, ∀ᶠ (N : ℕ) in at_top,
  ∑ q in (range N).filter (λ r, is_prime_pow r ∧ (N:ℝ)^((1:ℝ)-8/(log(log N))) < r), (q : ℝ)⁻¹
  ≤ c/log(log N) :=
begin
  have haux: asymptotics.is_O_with ((1: ℝ)/8) at_top (λ (x : ℝ), (log x))
     (λ (x : ℝ), x^((1:ℝ))), {
    refine asymptotics.is_o.def' _ _, refine is_o_log_rpow_at_top _,
    norm_num1, norm_num1,
    },
  rcases prime_power_reciprocal with ⟨b,hppr'⟩,
  have hppr := asymptotics.is_O.exists_pos hppr',
  clear hppr', rcases hppr with ⟨c,h0c,hppr⟩, rw asymptotics.is_O_with_iff at hppr,
  let C := c/2 + 16,
  use C,
  filter_upwards [tendsto_coe_nat_at_top_at_top.eventually (eventually_gt_at_top (0:ℝ)),
    tendsto_coe_nat_at_top_at_top.eventually hppr,
     (tendsto_pow_rec_loglog_spec_at_top.comp tendsto_coe_nat_at_top_at_top).eventually hppr,
     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually (eventually_gt_at_top (0:ℝ)),
       (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ)),
       (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (8:ℝ)),
       (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top ((8:ℝ)*2)),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually haux.bound]
    with N h0N hlarge1 hlarge2 hlogN hloglogN h8loglogN h16loglogN hlarge5,
  let M := (N:ℝ)^((1:ℝ)-8/log(log N)),
  have hlarge4 : log (log N) * 4 ≤ (1/2)*log N, {
    dsimp at hlarge5, simp_rw [norm_eq_abs, rpow_one] at hlarge5,
    rw abs_of_pos at hlarge5, rw abs_of_pos at hlarge5, rw [← le_div_iff, mul_comm, ← div_eq_mul_one_div,
      div_div], norm_num1, rw [div_eq_mul_one_div, mul_comm], exact hlarge5, exact zero_lt_four,
      exact hlogN, exact hloglogN,
   },
  clear hlarge5,
  have hlarge3 : log (log N) * 4 ≤ log N, { refine hlarge4.trans _,
    rw [mul_comm, ← div_eq_mul_one_div], refine half_le_self _, exact le_of_lt hlogN, },
  clear hppr,
  simp_rw [norm_eq_abs, abs_le] at hlarge1, simp_rw [norm_eq_abs, abs_le] at hlarge2,
  have hl1 := hlarge1.2, have hl2 := hlarge2.1, clear hlarge1 hlarge2,
  dsimp at hl2, rw [log_rpow h0N, log_mul _ (ne_of_gt hlogN)] at hl2,
  calc _ ≤ ∑ (q : ℕ) in filter is_prime_pow (Icc 1 ⌊N⌋₊), (q:ℝ)⁻¹ -
             ∑ (q : ℕ) in filter is_prime_pow (Icc 1 ⌊M⌋₊), (q:ℝ)⁻¹ :_
     ... ≤  c * |(log ↑N)⁻¹|+(log (log N) + b) - ∑ (q : ℕ) in filter is_prime_pow (Icc 1 ⌊M⌋₊), (q:ℝ)⁻¹ :_
     ... ≤  c * |(log ↑N)⁻¹|+(log (log N) + b) - ((log (1 - 8 / log (log N)) + log (log N) + b -
             (c * |((1 - 8 / log (log N)) * log N)⁻¹|))) :_
     ... ≤ _ :_,
  rw [le_sub_iff_add_le, ← sum_union], refine sum_le_sum_of_subset_of_nonneg _ _,
  intros q hq, rw [mem_filter, mem_Icc], rw [mem_union, mem_filter, mem_filter] at hq,
  cases hq with hq1 hq2, rw nat.le_floor_iff, rw mem_range at hq1,
  refine ⟨⟨_,_⟩,hq1.2.1⟩, exact le_of_lt (is_prime_pow.one_lt hq1.2.1), norm_cast,
  exact le_of_lt hq1.1, refine le_of_lt _, exact_mod_cast h0N, rw [mem_Icc] at hq2,
  refine ⟨⟨hq2.1.1,_⟩,hq2.2⟩, refine (hq2.1.2).trans _, refine nat_floor_real_le_floor _,
  rw [← rpow_one (N:ℝ)], refine real.rpow_le_rpow_of_exponent_le _ _, norm_cast,
  rw [nat.one_le_iff_ne_zero, ← pos_iff_ne_zero], exact_mod_cast h0N, refine sub_le_self _ _,
  refine div_nonneg _ _, norm_num1, exact le_of_lt hloglogN,
  intros n hn1 hn2, rw inv_nonneg, exact nat.cast_nonneg n,
  rw finset.disjoint_left, intros q hq, rw mem_filter at hq, intro hbad,
  rw [mem_filter, mem_Icc] at hbad, rw ← not_le at hq, refine hq.2.2 _,
  rw nat.le_floor_iff at hbad, exact hbad.1.2,
  refine rpow_nonneg_of_nonneg _ _, exact le_of_lt h0N,
  rw nat.floor_coe at hl1,
  rw [sub_le_sub_iff_right, ← sub_le_iff_le_add], exact hl1,
  rw [sub_le_sub_iff_left], rw [neg_le, neg_sub] at hl2, rw sub_le, exact hl2,
  ring_nf,
  calc _ ≤ (c/log(log N))/2 - log(1-8/log(log N)) :_
     ... ≤ _ :_,
  rw [sub_le_sub_iff_right, div_div, mul_comm _ c, div_eq_mul_one_div c, mul_le_mul_left],
  calc _ ≤ (1/(log(log N)*4)) + (1/(log(log N)*4)) :_
     ... = _ :_,
  refine add_le_add _ _, rw [abs_of_pos, one_div, inv_le_inv], exact hlarge3, exact hlogN,
  refine mul_pos hloglogN zero_lt_four, rw inv_pos, exact hlogN,
  rw [abs_of_pos, one_div, inv_le_inv], refine le_trans hlarge4 _, rw mul_le_mul_right,
  rw [le_sub, sub_half, div_le_div_iff, one_mul], exact h16loglogN, exact hloglogN,
  exact zero_lt_two, exact hlogN, refine mul_pos _ hlogN, rw [sub_pos, div_lt_one],
  exact h8loglogN, exact hloglogN, refine mul_pos hloglogN _, exact zero_lt_four,
  rw inv_pos, refine mul_pos _ hlogN, rw [sub_pos, div_lt_one],
  exact h8loglogN, exact hloglogN, rw [div_add_div_same, div_eq_div_iff], ring_nf,
  refine ne_of_gt _, refine mul_pos hloglogN zero_lt_four,
  refine ne_of_gt _, refine mul_pos hloglogN zero_lt_two, exact h0c,
  rw [mul_comm, ← one_div, div_div, ← div_eq_mul_one_div, mul_comm _ (2:ℝ), ← div_div, sub_le,
      div_sub_div_same, div_le_iff, mul_comm],
  have hloghelper := log_helper (8/log(log N)) _ _,
  rw [mul_div, div_le_iff'] at hloghelper, norm_num1 at hloghelper,
  have hhelper2 : c/2 - C = -16, { rw [sub_add_eq_sub_sub, sub_self, zero_sub], },
  rw hhelper2, exact hloghelper, exact hloglogN, refine div_pos _ hloglogN, norm_num1,
  rw [div_le_div_iff, one_mul], exact h16loglogN, exact hloglogN, exact zero_lt_two,
  exact hloglogN,
  refine ne_of_gt _, rw [sub_pos, div_lt_one hloglogN], exact h8loglogN,
end

lemma filter_smooth (D : ℝ) (hD : 0 < D) : ∀ᶠ (N : ℕ) in at_top,
∀ A ⊆ range(N),
   ((A.filter(λ n, ∃ q : ℕ, is_prime_pow q ∧ (N:ℝ)^((1:ℝ)-8/(log(log N))) < q ∧ q ∣ n)).card : ℝ)
   ≤ N/D :=
begin
  rcases diff_mertens_sum with ⟨c,hdiff⟩,
  filter_upwards [hdiff,
      tendsto_coe_nat_at_top_at_top.eventually  (eventually_gt_at_top (0:ℝ)),
      tendsto_coe_nat_at_top_at_top.eventually  (eventually_ge_at_top (D*2)),
      (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
        (eventually_ge_at_top (0:ℝ)),
       (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top (c / (1 / (2 * D)))),
       (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_gt_at_top (0:ℝ))
  ]
  with N hdiff' hlarge1 hlarge2 hlarge3 hlarge4 hlarge5,
  clear hdiff,
  intros A hA,
  let A' := erase A 0,
  have hlocal : ∀ q ∈ (range N), (1 ≤ q) → (A'.filter(λ n, q ∣ n)).card ≤ N / q, {
    intros q hq h1q,
    calc _ ≤ ((finset.Icc 1 N).filter (λ n, q ∣ n)).card :_
       ... = _ : count_multiples _,
    refine card_le_of_subset _, refine filter_subset_filter _ _, intros n hn,
    rw mem_Icc, obtain hnN := hA ((erase_subset 0 A) hn), rw mem_range at hnN, refine ⟨_,le_of_lt hnN⟩,
    rw nat.one_le_iff_ne_zero, intro hbad, rw hbad at hn, exact (not_mem_erase 0 A) hn, exact h1q,
  },
  have hlocal' : ∀ q ∈ (range N), (1 ≤ q) → ((A'.filter(λ n, q ∣ n)).card : ℝ) ≤ N / q, {
    intros q hq h1q, refine le_trans _ nat.cast_div_le, exact_mod_cast hlocal q hq h1q,
  },
  calc _ ≤
   ((A'.filter(λ n, ∃ q : ℕ, is_prime_pow q ∧ (N:ℝ)^((1:ℝ)-8/(log(log N))) < q ∧ q ∣ n)).card : ℝ) + 1 :_
   ... ≤ ∑ q in ((range N).filter(λ r:ℕ, is_prime_pow r ∧ (N:ℝ)^((1:ℝ)-8/(log(log N))) < r)),
           ((A'.filter(λ n, q ∣ n)).card : ℝ) + 1 :_
   ... ≤ (N:ℝ)*(∑ q in ((range N).filter(λ r:ℕ, is_prime_pow r ∧ (N:ℝ)^((1:ℝ)-8/(log(log N))) < r)), (1:ℝ)/q) + 1 :_
   ... ≤ (N:ℝ)/(2*D) + 1 :_
   ... ≤ _ :_,
  norm_cast, rw filter_erase, refine le_trans (card_le_of_subset
     (finset.insert_erase_subset 0 _)) _, refine finset.card_insert_le _ _,
  rw add_le_add_iff_right,
  have hdecomp : A'.filter(λ n, ∃ q : ℕ, is_prime_pow q ∧ (N:ℝ)^((1:ℝ)-8/(log(log N))) < q ∧ q ∣ n)
    ⊆ ((range N).filter(λ r:ℕ, is_prime_pow r ∧ (N:ℝ)^((1:ℝ)-8/(log(log N))) < r)).bUnion
            (λ q, A'.filter(λ n, q ∣ n)),
    { intros n hn, rw mem_filter at hn, rw [mem_bUnion], rcases hn.2 with ⟨q,hq,hq2⟩,
      refine ⟨q,_,_⟩, rw mem_filter, refine ⟨_,hq,hq2.1⟩, rw mem_range,
      refine lt_of_le_of_lt (nat.le_of_dvd _ hq2.2) _, rw pos_iff_ne_zero,
      intro hbad, rw hbad at hn, exact (not_mem_erase 0 A) hn.1, rw ← mem_range,
      exact hA ((erase_subset 0 A) hn.1), rw mem_filter, refine ⟨hn.1,hq2.2⟩,
      },
  norm_cast,
  refine le_trans (card_le_of_subset hdecomp) _, exact_mod_cast finset.card_bUnion_le,
  rw [add_le_add_iff_right, mul_sum], refine finset.sum_le_sum _,
  intros q hq, rw ← div_eq_mul_one_div, rw mem_filter at hq, refine hlocal' q _ _,
  exact hq.1, exact le_of_lt (is_prime_pow.one_lt hq.2.1),
  rw [add_le_add_iff_right, div_eq_mul_one_div (N:ℝ), mul_le_mul_left],
  calc _ = ∑ (q : ℕ) in filter (λ (r : ℕ), is_prime_pow r ∧ (N:ℝ) ^ ((1:ℝ) - 8 / log (log N)) < r) (range N), (q:ℝ)⁻¹ :_
     ... ≤ c/log(log N) : hdiff'
     ... ≤ _ :_,
  simp_rw one_div, rw div_le_iff, nth_rewrite 0 mul_comm, rw ← div_le_iff,
  exact hlarge4, rw one_div_pos, exact mul_pos zero_lt_two hD, exact hlarge5,
  exact hlarge1, rw [mul_comm, ← div_div, ← le_sub_iff_add_le', sub_half, div_div,
     one_le_div], exact hlarge2, refine mul_pos hD zero_lt_two,
end

lemma nat_le_cast_real_sub {m n : ℕ} : (n:ℝ)-(m:ℝ) ≤ (n-m:ℕ) :=
begin
  by_cases h : m < n,
  rw nat.cast_sub (le_of_lt h), rw not_lt at h, rw nat.sub_eq_zero_of_le h,
  norm_cast, rw sub_nonpos, exact_mod_cast h,
end

lemma final_large_N (D:ℝ) (hD : 0 < D) : ∃ y z : ℝ,
(1 ≤ y) ∧ (4*y + 4 ≤ z) ∧ (0 < z) ∧
∀ᶠ N : ℕ in at_top, ((0:ℝ)< N) ∧
 (N : ℝ)^(1 - (1 : ℝ)/(log(log N))) + 1 < N/(5*D) ∧ (∀ A ⊆ range(N),
   (((A.filter(λ n, ∃ q : ℕ, is_prime_pow q ∧ (N:ℝ)^((1:ℝ)-8/(log(log N))) < q ∧ q ∣ n)).card : ℝ)
   ≤ N/(5*D))) ∧  (∀ A ⊆ range(N),
   ((A.filter(λ n:ℕ, n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)))).card : ℝ)
   ≤ N/(5*D)) ∧ (∀ A ⊆ range(N),
   ((A.filter(λ n, ¬ ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧
      (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z))).card : ℝ) ≤ N/(5*D))
  ∧ z ≤ (log N) ^ ((1:ℝ) / 500) ∧
   (2 / y + log N ^ -((1:ℝ)/ 200)) * N ≤ N / (5 * D) :=
begin
  rcases (filter_div D hD) with ⟨y,z,h1y,hyz,h0z,hChelp,hChelp',hfilterdiv⟩,
  refine ⟨y,z,h1y,hyz,h0z,_⟩,
  have h5D : 0 < 5*D, { refine mul_pos _ hD, norm_num1, },
  have h1pos : (0:ℝ) < 1 := by norm_num1,
  filter_upwards [eventually_gt_at_top 0, (filter_smooth (5*D) h5D),filter_regular (5*D) h5D,
     hfilterdiv,
     tendsto_coe_nat_at_top_at_top.eventually  (eventually_gt_at_top (2*(5*D))),
    ((tendsto_pow_rec_log_log_at_top h1pos).comp tendsto_coe_nat_at_top_at_top).eventually
        (eventually_ge_at_top (5 * D * 2)),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
        (eventually_ge_at_top (z^(500:ℝ))),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
        (eventually_gt_at_top (0:ℝ)),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
        (eventually_ge_at_top ((1 / (1 / (5 * D) / 2)) ^ (200:ℝ))) ]
    with N hlarge hsmooth hregular hdiv hlarge2 hlarge3 hlarge4 hlarge5 hlarge6,
  dsimp at hlarge3 hlarge4 hlarge5 hlarge6,
  refine ⟨_,_,hsmooth,hregular,hdiv,_,_⟩, exact_mod_cast hlarge,
  calc _ < (N : ℝ)^(1 - (1 : ℝ)/(log(log N))) + ((N/(5*D)))/2 :_
     ... ≤ _ :_,
  rw [real.add_lt_add_iff_left, lt_div_iff, lt_div_iff, one_mul], exact hlarge2,
  refine mul_pos _ hD, norm_num1, exact zero_lt_two,
  rw [← le_sub_iff_add_le, sub_half, sub_eq_add_neg, add_comm, rpow_add_one, mul_comm, div_div],
  nth_rewrite 1 div_eq_mul_one_div, rw [mul_le_mul_left, rpow_neg, ← one_div, one_div_le_one_div],
  exact hlarge3, refine rpow_pos_of_pos _ _, exact_mod_cast hlarge,
  refine mul_pos _ zero_lt_two, refine mul_pos _ hD, norm_num1, refine le_of_lt _,
  exact_mod_cast hlarge, exact_mod_cast hlarge, refine ne_of_gt _, exact_mod_cast hlarge,
  have h500 : (0:ℝ) < 500 := by norm_num1,
  rw [← real.rpow_le_rpow_iff _ _ h500, ← rpow_mul, one_div_mul_cancel,
       rpow_one], exact hlarge4, exact ne_of_gt h500, exact (le_of_lt hlarge5), exact le_of_lt h0z,
  refine rpow_nonneg_of_nonneg _ _,
  exact (le_of_lt hlarge5), nth_rewrite 2 div_eq_mul_one_div, rw [mul_comm, mul_le_mul_left],
  calc _ ≤ (1/(5*D))/2 + (1/(5*D))/2 :_
     ... = _ :_,
  refine add_le_add _ _, rw [div_div, div_le_iff, ← div_le_iff'], exact hChelp',
  rw one_div_pos, refine mul_pos (mul_pos _ hD) zero_lt_two,
  norm_num1, exact lt_of_lt_of_le zero_lt_one h1y,
  rw [rpow_neg, ← one_div, one_div_le],
  have h200 : (0:ℝ) < 200 := by norm_num1,
  rw [← real.rpow_le_rpow_iff _ _ h200, ← rpow_mul, one_div_mul_cancel, rpow_one],
  exact hlarge6, exact ne_of_gt h200, exact (le_of_lt hlarge5), rw one_div_nonneg,
  refine div_nonneg _ zero_le_two, rw one_div_nonneg, refine mul_nonneg _ (le_of_lt hD), norm_num1,
  refine rpow_nonneg_of_nonneg (le_of_lt hlarge5) _, refine rpow_pos_of_pos hlarge5 _,
  refine div_pos _ zero_lt_two, rw one_div_pos, refine mul_pos _ hD, norm_num1,
  exact le_of_lt hlarge5, rw add_halves, exact_mod_cast hlarge,
end

theorem unit_fractions_upper_density' (D : ℝ) (hD : 0 < D) : ∃ y z : ℝ,
(1 ≤ y) ∧ (0 ≤ z) ∧
∀ A : set ℕ, (upper_density A > 1 / D) → ∃ d ∈ finset.Icc ⌈y⌉₊ ⌊z⌋₊,
  ∃ (S : finset ℕ), (S : set ℕ) ⊆ A ∧ ∑ n in S, (1 / n : ℚ) = 1/d :=
begin
  rcases (final_large_N D hD) with ⟨y,z,h1y,hyz,h0z,hfinal⟩,
  refine ⟨y,z,h1y,(le_of_lt h0z),_⟩, intros A hA,
  have hlargeN := filter.frequently.and_eventually (frequently_nat_of hA) hfinal,
  clear hfinal,
  rw filter.frequently_iff_forall_eventually_exists_and at hlargeN,
  specialize hlargeN technical_prop,
  rcases hlargeN with ⟨N,hlargeN,htech⟩,
  dsimp at hlargeN,
  have hzN := hlargeN.2.2.2.2.2.2.1,
  have hyN := hlargeN.2.2.2.2.2.2.2,
  let A' := filter (λ (n : ℕ), n ∈ A) (range N),
  have hA'card : (N:ℝ)/D < A'.card, {
    rw [div_eq_mul_one_div, ← lt_div_iff'], exact hlargeN.1, exact hlargeN.2.1,
   },
  let M := (N:ℝ)^((1:ℝ)-8/(log(log N))),
  let A0 := A'.filter(λ n : ℕ, (n:ℝ) < (N : ℝ)^(1 - (1 : ℝ)/(log(log N)))),
  have hA0card : (A0.card : ℝ) < N/(5*D), {
    calc _ ≤ ((finset.range(⌈(N : ℝ)^(1 - (1 : ℝ)/(log(log N)))⌉₊)).card : ℝ) :_
       ... < _ :_,
    norm_cast, refine finset.card_le_of_subset _, intros n hn,
    rw mem_filter at hn, rw [mem_range, nat.lt_ceil], exact hn.2, rw finset.card_range,
    refine lt_trans (nat.ceil_lt_add_one _) hlargeN.2.2.1,
    refine rpow_nonneg_of_nonneg (le_of_lt hlargeN.2.1) _,
   },
  let A1 := A'.filter(λ n, ∃ q : ℕ, is_prime_pow q ∧ M < q ∧ q ∣ n),
  have hA1card : (A1.card : ℝ) ≤ N/(5*D), {
    refine hlargeN.2.2.2.1 A' _, refine filter_subset _ _,
  },
  let A2 := A'.filter(λ n, n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N))),
  have hA2card : (A2.card : ℝ) ≤ N/(5*D), {
    refine hlargeN.2.2.2.2.1 A' _, refine filter_subset _ _,
  },
  let A3 := A'.filter(λ n, ¬ ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧ (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z) ),
  have hA3card : (A3.card : ℝ)  ≤ N/(5*D), {
    refine hlargeN.2.2.2.2.2.1 A' _, refine filter_subset _ _,
  },
  let A'' := A'\(A0∪A1∪A2∪A3),
  have hA''card : (N:ℝ)/(5*D) ≤ A''.card, {
    calc _ ≤ (A'.card : ℝ) - (N/(5*D)+N/(5*D)+N/(5*D)+N/(5*D)) :_
       ... ≤ (A'.card : ℝ) - (A0∪A1∪A2∪A3).card :_
       ... ≤ _ :_,
    rw [le_sub_iff_add_le, ← add_div, ← add_div, ← add_div, ← add_div, ← two_mul, add_assoc,
          ← two_mul, ← add_mul, ← one_add_mul], norm_num1, rw mul_div_mul_left,
    exact le_of_lt hA'card, norm_num1, rw sub_le_sub_iff_left,
    calc _ ≤ ((A0.card + A1.card + A2.card + A3.card : ℕ):ℝ) :_
       ... ≤ _ :_,
    norm_cast, refine le_trans (card_union_le _ _) _, rw add_le_add_iff_right,
    refine le_trans (card_union_le _ _) _, rw add_le_add_iff_right,
    refine card_union_le _ _, push_cast,
    refine add_le_add _ hA3card, refine add_le_add _ hA2card, refine add_le_add _ hA1card,
    exact le_of_lt hA0card, refine le_trans nat_le_cast_real_sub _, norm_cast,
    refine le_card_sdiff _ _,
   },
  clear hA'card hA0card hA1card hA2card hA3card,
  have h0A'' : 0 ∉ A'', {
    intro hz, rw [mem_sdiff, not_mem_union, not_mem_union, not_mem_union] at hz,
    nth_rewrite 1 mem_filter at hz, refine hz.2.1.1.1 ⟨hz.1,_⟩,
    refine rpow_pos_of_pos hlargeN.2.1 _,
   },
  have hA''N : ∀ n ∈ A'', n < N, {
    intros n hn, rw [mem_sdiff, mem_filter, mem_range] at hn, exact hn.1.1,
  },
  have hstep : ∃ S ⊆ A'', ∃ d : ℕ, (y ≤ d) ∧ ((d : ℝ) ≤ z) ∧ rec_sum S = 1/d, {
    refine htech A'' _ y z h1y hyz hzN h0A'' _ _ _ _ _,
    intros n hn, rw mem_range, refine lt_of_lt_of_le (hA''N n hn) (nat.le_succ N),
    intros n hn, rw [mem_sdiff, not_mem_union, not_mem_union, not_mem_union] at hn,
    nth_rewrite 1 mem_filter at hn, rw ← not_lt, intro hbad, refine hn.2.1.1.1 ⟨hn.1,hbad⟩,
    calc _ ≤ (A''.card:ℝ)/N :_
       ... ≤ _ :_,
    rw le_div_iff hlargeN.2.1, refine le_trans hyN hA''card,
    rw [card_eq_sum_ones, rec_sum], push_cast, rw sum_div, refine sum_le_sum _,
    intros n hn, rw [zero_add, one_div_le_one_div], norm_cast, exact le_of_lt (hA''N n hn),
    exact hlargeN.2.1, norm_cast, rw pos_iff_ne_zero, intro hz, rw hz at hn, exact h0A'' hn,
    intros n hn, rw [mem_sdiff, not_mem_union, not_mem_union, not_mem_union] at hn,
    nth_rewrite 4 mem_filter at hn, rw [not_and, not_not] at hn, exact hn.2.2 hn.1,
    intros n hn, rw is_smooth, intros q hq hqn,
    rw [mem_sdiff, not_mem_union, not_mem_union, not_mem_union] at hn,
    nth_rewrite 2 mem_filter at hn, rw not_and at hn, rw ← not_lt, intro hbad,
    refine hn.2.1.1.2 hn.1 _, refine ⟨q,hq,hbad,hqn⟩,
    rw arith_regular, intros n hn, rw [mem_sdiff, not_mem_union, not_mem_union, not_mem_union] at hn,
    nth_rewrite 3 mem_filter at hn, rw [not_and, not_and, not_not] at hn,
    refine hn.2.1.2 hn.1 _, intro hbad, refine hn.2.1.1.1 _,
    rw [hbad, mem_filter], rw hbad at hn, refine ⟨hn.1,_⟩, norm_cast,
    refine rpow_pos_of_pos _ _, exact hlargeN.2.1,
  },
  clear htech,
  rcases hstep with ⟨S,hS,d,hyd,hdz,hrecd⟩, refine ⟨d,_,S,_,_⟩,
  rw mem_Icc, refine ⟨_,_⟩, rw ← nat.ceil_le at hyd, exact hyd,
  rw ← nat.le_floor_iff at hdz, exact hdz, exact le_of_lt h0z,
  intros s hs, rw finset.mem_coe at hs, have := hS hs,
  rw [mem_sdiff, mem_filter] at this, exact this.1.2,
  rw rec_sum at hrecd, exact hrecd,
end


theorem unit_fractions_upper_density (A : set ℕ) (hA : upper_density A > 0):
   ∃ (S : finset ℕ), (S : set ℕ) ⊆ A ∧ ∑ n in S, (1 / n : ℚ) = 1 :=
begin
  let D := 2/ upper_density A,
  have hD : 0 < D := div_pos zero_lt_two hA,
  have hDA : 1/D < upper_density A, { rw one_div_div, refine half_lt_self hA, },
  rcases (unit_fractions_upper_density' D hD) with ⟨y,z,h1y,h0z,hupp⟩,
  let M := ∑ d in finset.Icc ⌈y⌉₊ ⌊z⌋₊, d,
  let good_set : finset (finset ℕ) → Prop :=
    λ S, (∀ s ∈ S, (s : set ℕ) ⊆ A) ∧ (S : set (finset ℕ)).pairwise_disjoint id ∧
      ∀ s, ∃ (d : ℕ), s ∈ S → y ≤ d ∧ (d : ℝ) ≤ z ∧ rec_sum s = 1 / d,
  let P : ℕ → Prop := λ k, ∃ S : finset (finset ℕ), S.card = k ∧ good_set S,
  let k : ℕ := nat.find_greatest P (M+1),
  have P0 : P 0 := ⟨∅, by simp [good_set]⟩,
  have Pk : P k := nat.find_greatest_spec (nat.zero_le _) P0,
  obtain ⟨S, hk, hS₁, hS₂, hS₃⟩ := Pk,
  choose d' hd'₁ hd'₂ hd'₃ using hS₃,
  let t : ℕ → ℕ := λ d, (S.filter (λ s, d' s = d)).card,
  by_cases h : ∃ d : ℕ, 0 < d ∧ d ≤ t d,
  { obtain ⟨d, d_pos, ht⟩ := h,
    obtain ⟨T', hT', hd₂⟩ := finset.exists_smaller_set _ _ ht,
    have hT'S := hT'.trans (finset.filter_subset _ _),
    refine ⟨T'.bUnion id, _, _⟩,
    have hfinstep : T'.bUnion id ⊆  S.bUnion id :=
       by refine (finset.bUnion_subset_bUnion_of_subset_left _ hT'S),
    rw ← finset.coe_subset at hfinstep,
    refine hfinstep.trans _, intros n hn,
    rw [finset.coe_bUnion, set.mem_Union] at hn,
    rcases hn with ⟨i,hi⟩, rw set.mem_Union at hi, rcases hi with ⟨hiS,hni⟩,
    dsimp at hni, refine hS₁ i _ hni, rw ← finset.mem_coe, exact hiS,
    rw [sum_bUnion (hS₂.subset hT'S), finset.sum_congr rfl, finset.sum_const, hd₂,
        nsmul_eq_mul, mul_div_cancel'],
    { rw nat.cast_ne_zero, exact d_pos.ne' },
    intros i hi,
    rw [← rec_sum], dsimp, rw [hd'₃ _ (hT'S hi), (finset.mem_filter.1 (hT' hi)).2],
    },
  push_neg at h,
  exfalso,
  let A' := A \ S.bUnion id,
  have hAS : disjoint A' (S.bUnion id) := (set.disjoint_diff).symm,
  have hDA' : 1/D < upper_density A', {
    have : upper_density A = upper_density A' := upper_density_preserved,
    rw ← this, exact hDA },
  specialize hupp A' hDA', rcases hupp with ⟨d,hd,S',hS'⟩,
  have hd' : y ≤ d ∧ (d : ℝ) ≤ z, {
    rw mem_Icc at hd, refine ⟨_,_⟩,
    refine le_trans (nat.le_ceil _) _, norm_cast, exact hd.1,
    refine le_trans _ (nat.floor_le _), norm_cast, exact hd.2, exact h0z,
   },
  have h1d : 1 ≤ d, {
    have : (1:ℝ) ≤ d := le_trans h1y hd'.1,
    exact_mod_cast this,
  },
  have hS'' : ∀ s ∈ S, disjoint S' s, {
    intros s hs, rw ←finset.disjoint_coe,
    refine set.disjoint_of_subset_left hS'.1 _,
    refine set.disjoint_of_subset_right _ hAS,
    rw finset.coe_bUnion, refine set.subset_bUnion_of_mem hs,
  },
  have hS'A : (S':set ℕ) ⊆ A, {
    refine subset_trans hS'.1 (set.diff_subset _ _),
   },
  have hS''' : S' ∉ S,
  { intro t,
    exact (nonempty_of_rec_sum_recip h1d hS'.2).ne_empty (disjoint_self.1 (hS'' _ t)) },
  have : P (k+1),
  { refine ⟨insert S' S, _, _⟩,
    { rw [finset.card_insert_of_not_mem hS''', hk] },
    refine ⟨_, _, _⟩,
    {  intros s hs, rw mem_insert at hs,
       cases hs with hs1 hs2, rw hs1, exact hS'A, exact hS₁ s hs2,  },
    { simpa [set.pairwise_disjoint_insert, hS₂] using λ s hs _, hS'' _ hs },
    intros s,
    rcases eq_or_ne s S' with rfl | hs,
    { exact ⟨d, λ _, ⟨hd'.1, hd'.2, hS'.2⟩⟩ },
    refine ⟨d' s, λ i, _⟩,
    have : s ∈ S := finset.mem_of_mem_insert_of_ne i hs,
    exact ⟨hd'₁ _ this, hd'₂ _ this, hd'₃ _ this⟩ },
  have hk_bound : k+1 ≤ M+1,
  { rw [← hk, add_le_add_iff_right],
    have hSdecomp : (finset.Icc ⌈y⌉₊ ⌊z⌋₊).bUnion(λ d, S.filter (λ (s : finset ℕ), d' s = d)) = S,
    { refine finset.bUnion_filter_eq_of_maps_to _,
      intros n hn, rw [mem_Icc, nat.ceil_le, nat.le_floor_iff],
      refine ⟨hd'₁ n hn,hd'₂ n hn⟩, exact h0z,
       },
    rw ← hSdecomp, refine le_trans (finset.card_bUnion_le) _, refine finset.sum_le_sum _,
    intros d' hd', refine le_of_lt (h d' _), rw [mem_Icc, nat.ceil_le] at hd',
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_trans h1y hd'.1)),
   },
  have : k + 1 ≤ k := nat.le_find_greatest hk_bound this,
  simpa using this,
end

lemma rec_sum_sdiff {A B : finset ℕ} :
   (rec_sum A:ℝ) - rec_sum B ≤ rec_sum (A\B) :=
sorry

lemma rec_sum_union {A B : finset ℕ} :
   (rec_sum (A∪B) : ℝ) ≤ rec_sum A + rec_sum B :=
sorry

lemma rec_sum_bUnion {I : finset ℕ} (f : ℕ → finset ℕ) :
  (rec_sum (I.bUnion (λ i:ℕ, f i)):ℝ) ≤ ∑ i in I, rec_sum (f i) := sorry

lemma this_particular_tends_to :
  tendsto (λ x : ℝ, x^(log(log(log x))/log(log x)) ) at_top at_top := sorry

lemma Ioc_subset_Ioc_union_Ioc {a b c : ℕ} :
  Ioc a c ⊆ Ioc a b ∪ Ioc b c :=
by { rw [←coe_subset, coe_union, coe_Ioc, coe_Ioc, coe_Ioc], exact set.Ioc_subset_Ioc_union_Ioc }

lemma bUnion_range_Ioc (N : ℕ) (f : ℕ → ℕ) :
   Ioc (f N) (f 0)  ⊆ (range(N)).bUnion(λ i:ℕ, Ioc (f (i+1)) (f (i))) :=
begin
  induction N, simp only [range_zero, bUnion_empty, Ioc_self], refl,
  rw [range_succ, finset.bUnion_insert],
  have :  Ioc (f (N_n + 1)) (f 0)  ⊆ (Ioc (f (N_n + 1)) (f N_n)  ∪ Ioc (f N_n) (f 0) ), {
    refine Ioc_subset_Ioc_union_Ioc,
   },
  refine subset_trans this _, refine finset.union_subset_union _ N_ih, refl,
end

lemma the_last_large_N : ∀ C : ℝ, (0 < C) → ∀ᶠ (N : ℕ) in at_top,
log N ^ ((3:ℝ) / 4) ≤ log N * (log(log(log N))/log(log N)) ∧
(⌈log (log (log N) / log (log (log N))) *(2 * log (log N))⌉₊:ℝ) *
  (2 * ((log N)^((1:ℝ) / 500)) + C*(1/(log(log N))^2)*log N) < (2+2*C)*(log(log(log N))/log(log N)) * log N := sorry

lemma this_fun_increasing : ∃ C : ℝ, ∀ N M : ℕ, (C ≤ N) ∧ (N ≤ M) →
  log N/(log(log N))^2 ≤ log M/(log(log M))^2 := sorry

lemma harmonic_sum_bound_two' : ∀ᶠ (N : ℝ) in at_top,
  ∑ n in finset.range(⌈N⌉₊), (1 : ℝ)/n ≤ 2*log N := sorry

lemma harmonic_filter_div : ∃ C : ℝ, (0 < C) ∧
 ∀ᶠ (N : ℕ) in at_top, ∑ n in (Icc (⌈(N:ℝ)^(log(log(log N))/log(log N))⌉₊) N).filter(λ n,
    ¬ ∃ d : ℕ, d ∣ n ∧ (4 ≤ d) ∧ ((d : ℝ) ≤ (log N)^((1:ℝ)/1000))), (1:ℝ)/n
    ≤ C*log N/(log(log N)) := sorry

lemma harmonic_filter_reg : ∃ C : ℝ, (0 < C) ∧
 ∀ᶠ (N : ℕ) in at_top, ∑ n in (Icc (⌈(N:ℝ)^(log(log(log N))/log(log N))⌉₊) N).filter(λ n, n ≠ 0 ∧
   ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ (3/2) * log (log N))), (1:ℝ)/n
    ≤ C*log N/(log(log N)) := sorry

lemma harmonic_filter_smooth : ∃ C : ℝ, (0 < C) ∧
 ∀ᶠ (N : ℕ) in at_top, ∑ m in (Icc (⌈(N:ℝ)^(1-1/log(log N))⌉₊) N).filter(λ n:ℕ, ∃ q : ℕ,
   is_prime_pow q ∧ ((N:ℝ)^(1-8/log(log N)) < q ∧ q ∣ n)), (1:ℝ)/m
    ≤ C*log N/(log(log N))^2 := sorry

 theorem unit_fractions_upper_log_density :
∃ C : ℝ, ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ Icc 1 N,
     C*(log (log (log N)) / log (log N))* log N ≤ ∑ n in A, 1 / n →
       ∃ S ⊆ A, ∑ n in S, (1 / n : ℚ) = 1 :=
begin
  rcases harmonic_filter_div with ⟨C₁,h0C₁,hdiv⟩,
  rcases harmonic_filter_reg with ⟨C₂,h0C₂,hreg⟩,
  rcases harmonic_filter_smooth with ⟨C₃,h0C₃,hsmooth⟩,
  rw eventually_at_top at hdiv, rcases hdiv with ⟨C₁',hdiv⟩,
  rw eventually_at_top at hreg, rcases hreg with ⟨C₂',hreg⟩,
  rw eventually_at_top at hsmooth, rcases hsmooth with ⟨C₃',hsmooth⟩,
  let C := 2+2*C₃+C₁+C₂+2,
  use C,
  have hcoraux := corollary_one,
  rw eventually_at_top at hcoraux, rcases hcoraux with ⟨C₀,hcor⟩,
  rcases this_fun_increasing with ⟨Cinc, hinc⟩,
  filter_upwards [eventually_gt_at_top 1,
    tendsto_log_coe_at_top.eventually_gt_at_top (0:ℝ),
    tendsto_log_log_coe_at_top.eventually_gt_at_top (0:ℝ),
    tendsto_log_log_coe_at_top.eventually_gt_at_top (1:ℝ),
    (tendsto_log_at_top.comp tendsto_log_log_coe_at_top).eventually_ge_at_top (1:ℝ),
    (this_particular_tends_to.comp tendsto_coe_nat_at_top_at_top).eventually
       (eventually_ge_at_top (C₀:ℝ)),
    (tendsto_coe_nat_at_top_at_top).eventually
       (eventually_ge_at_top (C₁':ℝ)),
    (tendsto_coe_nat_at_top_at_top).eventually
       (eventually_ge_at_top (C₂':ℝ)),
    (this_particular_tends_to.comp tendsto_coe_nat_at_top_at_top).eventually
       (eventually_ge_at_top (C₃':ℝ)),
     (this_particular_tends_to.comp tendsto_coe_nat_at_top_at_top).eventually
       (eventually_ge_at_top (Cinc:ℝ)),
   (this_particular_tends_to.comp tendsto_coe_nat_at_top_at_top).eventually
       (eventually_gt_at_top (1:ℝ)),
    (this_particular_tends_to.comp tendsto_coe_nat_at_top_at_top).eventually
       (eventually_ge_at_top (exp(exp(1)))),
    (the_last_large_N (C₃) h0C₃),
    (this_particular_tends_to.comp tendsto_coe_nat_at_top_at_top).eventually
      harmonic_sum_bound_two']
    with N hN h0logN h0loglogN h1loglogN h1log₃N hlargeN hdivth hregth hsmoothth hincth
       hlargeN₂ hlargeN₃ hlargeN₄ hharmonic,
  let ε := log(log(log N))/log(log N),
  let ε' := 1/log(log N),
  have h0ε : 0 < ε, { refine div_pos _ h0loglogN, refine log_pos h1loglogN, },
  have h01ε : 0 < 1/ε, { rw one_div_pos, exact h0ε, },
  have hε1 : ε < 1, { rw [div_lt_one h0loglogN, log_lt_log_iff h0loglogN,
     log_lt_log_iff h0logN], refine lt_of_le_of_lt (log_le_sub_one_of_pos _) _,
     norm_cast, exact lt_trans zero_lt_one hN, exact sub_one_lt (N:ℝ),
     norm_cast, exact lt_trans zero_lt_one hN, exact h0logN,},
  intros A hAN hrecA,
  let A' := A.filter(λ n : ℕ, (N:ℝ)^ε ≤ n),
  have hrecA' : (2+2*C₃+C₁+C₂)*ε*log N ≤ rec_sum A', {
    have hAtemp : A' ∪ (A\A') = A, { refine union_sdiff_of_subset _, refine filter_subset _ _, },
    by_contra, rw [not_le, rec_sum] at h, rw ← not_lt at hrecA, refine hrecA _,
    push_cast at h, rw [← hAtemp, sum_union],
    have hotherrec : ∑ n in (A\A'), (1:ℝ) / n ≤ 2*ε*log N, {
      calc _ ≤ ∑ n in range(⌈(N:ℝ)^ε⌉₊), (1:ℝ) / n :_
         ... ≤ _ :_,
      refine sum_le_sum_of_subset_of_nonneg _ _, intros n hn, rw mem_range,
      rw [mem_sdiff, mem_filter, not_and, not_le] at hn, rw nat.lt_ceil, exact hn.2 hn.1,
      intros n hn1 hn2, rw one_div_nonneg, exact nat.cast_nonneg n,
      rw [mul_assoc, ← log_rpow], exact hharmonic, norm_cast,
      exact lt_trans zero_lt_one hN,
     },
    have hnum : C = 2+2*C₃+C₁+C₂+2 := by refl,
    rw [hnum, add_mul, add_mul], refine add_lt_add_of_lt_of_le _ hotherrec, exact h,
    exact disjoint_sdiff,
   },
  clear hharmonic,
  let Y := A'.filter(λ n, n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧
      (ω n : ℝ) ≤ (3/2) * log (log N))),
  let X := A'.filter(λ n, ¬ ∃ d : ℕ, d ∣ n ∧ (4 ≤ d) ∧
     ((d : ℝ) ≤ (log N)^((1:ℝ)/1000))),
  have hA'Icc : A' ⊆ Icc ⌈(N:ℝ) ^ ε⌉₊ N, {
    intros n hn, rw mem_Icc, rw mem_filter at hn,
    have hn' := hAN hn.1, rw mem_Icc at hn', refine ⟨_,hn'.2⟩,
    rw nat.ceil_le, exact hn.2,
   },
  have hrecX : (rec_sum X : ℝ) ≤ C₁*ε' * (log N), {
    rw rec_sum, push_cast, specialize hdiv N, rw [mul_assoc, mul_comm ε', ← div_eq_mul_one_div,
      ← mul_div_assoc],
    refine le_trans _ (hdiv _), refine sum_le_sum_of_subset_of_nonneg _ _,
    refine finset.filter_subset_filter _ hA'Icc,
    intros n hn1 hn2, rw one_div_nonneg, exact nat.cast_nonneg n, rw ge_iff_le,
    rw ← @nat.cast_le ℝ _ _ _ _, exact hdivth,
   },
  have hε₁ : ε' ≤ ε, { rw div_le_div_right, exact h1log₃N, exact h0loglogN, },
  have hrecX' : (rec_sum X : ℝ) ≤ C₁*ε * (log N), {
    refine le_trans hrecX _, rw mul_le_mul_right h0logN, rw mul_le_mul_left h0C₁, exact hε₁,
   },
  have hrecY : (rec_sum Y : ℝ) ≤ C₂*ε' * (log N), {
    rw rec_sum, push_cast, specialize hreg N, rw [mul_assoc, mul_comm ε', ← div_eq_mul_one_div,
      ← mul_div_assoc],
    refine le_trans _ (hreg _), refine sum_le_sum_of_subset_of_nonneg _ _,
    refine finset.filter_subset_filter _ hA'Icc,
    intros n hn1 hn2, rw one_div_nonneg, exact nat.cast_nonneg n, rw ge_iff_le,
    rw ← @nat.cast_le ℝ _ _ _ _, exact hregth,
   },
  have hrecY' : (rec_sum Y : ℝ) ≤ C₂*ε * (log N), {
    refine le_trans hrecY _, rw mul_le_mul_right h0logN, rw mul_le_mul_left h0C₂, exact hε₁,
   },
  let A'' := A'\(X∪Y),
  have hrecA'' : (2+2*C₃)*ε*log N ≤ rec_sum A'', {
     refine le_trans _ rec_sum_sdiff, rw le_sub_iff_add_le, refine le_trans _ hrecA',
     rw [add_assoc (2+2*C₃)], nth_rewrite 2 (add_mul (_ : ℝ)), nth_rewrite 2 (add_mul (_ : ℝ)),
     rw add_le_add_iff_left,
     refine le_trans (rec_sum_union) _, rw [add_mul, add_mul],
     refine add_le_add hrecX' hrecY',
   },
  let δ := 1 - 1/log(log N),
  have h0δ : 0 < δ, { rw [sub_pos, one_div_lt, one_div_one], exact h1loglogN, exact h0loglogN, exact zero_lt_one, },
  have hδ1 : δ ≤ 1, { refine sub_le_self _ _, rw one_div_nonneg, exact le_of_lt h0loglogN, },
  let Nf := (λ i : ℕ, (N:ℝ)^(δ^i)),
  let Af := (λ i : ℕ, Ioc ⌊Nf (i+1)⌋₊ ⌊Nf i⌋₊ ∩ A''),
  let Nf' := (λ i : ℕ, ⌊Nf i⌋₊),
  let ε'' := 1/(log(log N))^2,
  have hgoodi : ∃ i:ℕ, 2*(log N)^((1:ℝ)/500) + C₃*ε''*(log N) ≤ rec_sum (Af i), {
    by_contra,
    let I := range(⌈log(1/ε)*(2*log(log N))⌉₊),
    have hIA : A'' = I.bUnion( λ i, Af i), { rw ← finset.bUnion_inter, refine eq.symm _,
      rw finset.inter_eq_right_iff_subset, intros n hn,
      have := bUnion_range_Ioc ⌈log(1/ε)*(2*log(log N))⌉₊ Nf', refine this _, rw mem_Ioc,
      rw [mem_sdiff, mem_filter] at hn,
      refine ⟨_,_⟩, rw nat.floor_lt, refine lt_of_lt_of_le _ hn.1.2,
      refine rpow_lt_rpow_of_exponent_lt _ _, exact_mod_cast hN,
      calc _ ≤ δ ^ (log(1/ε)*(2*log(log N))) :_
         ... < _ :_,
      rw ← rpow_nat_cast, refine rpow_le_rpow_of_exponent_ge h0δ hδ1 _,
      refine nat.le_ceil _, rw [← exp_log h0δ, ← exp_mul, ← mul_assoc, mul_comm (log δ),
        mul_assoc, exp_mul, exp_log h01ε, one_div, ← rpow_neg_one, ← rpow_mul],
      nth_rewrite 1 ← rpow_one ε,
      refine rpow_lt_rpow_of_exponent_gt h0ε hε1 _,
      rw [← mul_assoc, neg_one_mul, ← div_lt_iff, lt_neg],
      refine lt_of_le_of_lt (real.log_le_sub_one_of_pos h0δ) _,
      rw [← sub_add_eq_sub_sub, add_comm, sub_add_eq_sub_sub, sub_self, zero_sub,
        lt_neg, neg_neg, one_div_lt_one_div],
      nth_rewrite 0 ← one_mul (log(log N)), refine mul_lt_mul _ _ _ _, exact one_lt_two,
      refl, exact h0loglogN, exact zero_le_two, refine mul_pos zero_lt_two h0loglogN,
      exact h0loglogN, refine mul_pos zero_lt_two h0loglogN, exact le_of_lt h0ε,
      refine rpow_nonneg_of_nonneg _ _, exact nat.cast_nonneg N,
      have hnntemp := hAN hn.1.1, rw mem_Icc at hnntemp,
      have htemp : Nf' 0 = N, {
        have htemp' : Nf 0 = (N:ℝ)^(δ^0), { refl, },
        have htemp'' : Nf' 0 = ⌊Nf 0⌋₊, { refl, },
        rw [htemp'', htemp', pow_zero, rpow_one, nat.floor_coe],
       },
      rw htemp, exact hnntemp.2,
     },
    rw ← not_lt at hrecA'', refine hrecA'' _, rw not_exists at h, rw hIA,
    refine lt_of_le_of_lt (rec_sum_bUnion Af) _,
    refine lt_of_le_of_lt
       (finset.sum_le_card_nsmul _ _ (2*(log N)^((1:ℝ)/500) + (C₃)*ε''*(log N)) _) _,
    intros x hx, specialize h x, rw not_le at h, exact le_of_lt h,
    rw [card_range, one_div_div, nsmul_eq_mul], exact hlargeN₄.2,
  },
  rcases hgoodi with ⟨i,hi⟩,
  let A₀ := Af i,
  let N₀ := ⌊Nf i⌋₊,
  have hNN₀ : (N:ℝ)^ε ≤ N₀, {
    by_contra,
    have : Af i = ∅, { rw finset.eq_empty_iff_forall_not_mem,
     intros n hn, rw [mem_inter, mem_sdiff, mem_Ioc, mem_filter] at hn,
     refine h _, refine le_trans hn.2.1.2 _, exact_mod_cast hn.1.2, },
    rw [this, ← not_lt, rec_sum_empty] at hi, refine hi _, norm_cast, refine add_pos _ _,
    refine mul_pos _ _, norm_num1, refine rpow_pos_of_pos h0logN _,
    refine mul_pos _ h0logN, refine mul_pos h0C₃ _, rw one_div_pos, refine sq_pos_of_pos h0loglogN,
   },
  have h1N₀' : 1 ≤ Nf i, { refine one_le_rpow _ _, exact_mod_cast le_of_lt hN,
    refine pow_nonneg _ _, exact le_of_lt h0δ, },
  have h1N₀ : 1 ≤ N₀, {
    rw ← @nat.cast_le ℝ _ _ _ _, refine le_trans _ hNN₀, norm_cast, exact (le_of_lt hlargeN₂),
   },
  have hN₀large₂ : 0 < log(N₀), { refine log_pos _,
    refine lt_of_lt_of_le _ hNN₀, exact hlargeN₂, },
  have hN₀large : 1 ≤ log(log N₀), { rw [← exp_le_exp, exp_log, ← exp_le_exp, exp_log],
    refine le_trans _ hNN₀, exact hlargeN₃, norm_cast, exact lt_of_lt_of_le zero_lt_one h1N₀,
    exact hN₀large₂, },
  have hN₀N : (N₀ : ℝ) ≤ N, { rw ← rpow_one N, refine le_trans (nat.floor_le _) _,
    refine rpow_nonneg_of_nonneg _ _, exact nat.cast_nonneg N,
    refine rpow_le_rpow_of_exponent_le _ _, exact_mod_cast le_of_lt hN,
    refine pow_le_one _ _ _, exact le_of_lt h0δ, exact hδ1, },
  have hlogNN₀': 3 / 2 * log (log N) ≤ 2 * log (log N₀), {
    rw [← div_le_iff', mul_comm, mul_div_assoc], norm_num1, rw [mul_comm, ← log_rpow, log_le_log,
      ← exp_le_exp, exp_log],
      { refine le_trans _ hNN₀, have : (0:ℝ) < N, { norm_cast, exact lt_trans zero_lt_one hN, },
         rw [← exp_log this, ← exp_mul, exp_le_exp, exp_log this], exact hlargeN₄.1 },
    norm_cast, exact lt_of_lt_of_le zero_lt_one h1N₀, refine rpow_pos_of_pos _ _, exact h0logN,
    exact hN₀large₂, exact h0logN, exact zero_lt_two,
   },
  have hlogNN₀: log N ≤ (log N₀)^(2:ℝ), { rw [← log_le_log, log_rpow],
    refine le_trans _ hlogNN₀', nth_rewrite 0 ← one_mul (log(log N)), rw mul_le_mul_right h0loglogN,
    norm_num1, exact hN₀large₂, exact h0logN, refine rpow_pos_of_pos _ _, exact hN₀large₂},
  let M := (N₀:ℝ)^((1:ℝ)-8/(log(log N₀))),
  let Z := A₀.filter(λ n, ∃ q : ℕ, is_prime_pow q ∧ M < q ∧ q ∣ n),
  let A₁ := A₀ \ Z,
  have hloc : log N₀/(log(log N₀))^2 ≤ ε'' * log N, {
    rw [mul_comm, ← div_eq_mul_one_div], refine hinc N₀ N ⟨_,_⟩,
    refine le_trans hincth hNN₀, exact_mod_cast hN₀N,
   },
  have hA₀large : ∀ n ∈ A₀, (N₀ : ℝ) ^ (1 - (1 : ℝ) / log (log N₀)) ≤ n, {
    intros n hn,
    have := (inter_subset_left _ _) hn,
    rw mem_Ioc at this, rw nat.floor_lt at this, refine le_trans _ (le_of_lt this.1),
    transitivity ((Nf i)^ (1 - (1 : ℝ) / log (log N₀))),
    refine rpow_le_rpow _ _ _, norm_cast, exact le_trans zero_le_one h1N₀,
    refine nat.floor_le _, refine rpow_nonneg_of_nonneg _ _, exact nat.cast_nonneg N,
    rw [sub_nonneg, one_div_le, one_div_one], exact hN₀large,
    exact lt_of_lt_of_le zero_lt_one hN₀large, exact zero_lt_one,
    rw ← rpow_mul, refine rpow_le_rpow_of_exponent_le _ _, norm_cast,
    exact le_of_lt hN, rw [← rpow_nat_cast, ← rpow_nat_cast], push_cast,
    rw [rpow_add_one, mul_le_mul_left, sub_le_sub_iff_left, one_div_le_one_div, log_le_log,
     log_le_log], exact hN₀N, norm_cast, exact lt_of_lt_of_le zero_lt_one h1N₀, norm_cast,
    exact lt_trans zero_lt_one hN, exact hN₀large₂, exact h0logN, exact h0loglogN,
    exact lt_of_lt_of_le zero_lt_one hN₀large, refine rpow_pos_of_pos h0δ _,
    exact ne_of_gt h0δ, exact nat.cast_nonneg N, refine rpow_nonneg_of_nonneg _ _,
    exact nat.cast_nonneg N,
  },
  have hA₁large : ∀ n ∈ A₁, (N₀ : ℝ) ^ (1 - (1 : ℝ) / log (log N₀)) ≤ n, {
    intros n hn, refine hA₀large n _, refine (sdiff_subset _ _) hn,
   },
  have hA₀' : A₀ ⊆ Icc ⌈(N₀:ℝ) ^ (1 - 1 / log (log N₀))⌉₊ N₀, {
    intros n hn, rw mem_Icc, have hn' := hn,
    rw [mem_inter, mem_Ioc] at hn, refine ⟨_,hn.1.2⟩, rw nat.ceil_le, exact hA₀large n hn',
   },
  have hrecZ : (rec_sum Z : ℝ) ≤ C₃*ε''* (log N), {
    rw rec_sum, push_cast, transitivity (C₃*log N₀/(log(log N₀))^2), specialize hsmooth N₀,
    refine le_trans _ (hsmooth _), refine sum_le_sum_of_subset_of_nonneg _ _,
    refine finset.filter_subset_filter _ hA₀',
    intros n hn1 hn2, rw one_div_nonneg, exact nat.cast_nonneg n, rw ge_iff_le,
    rw ← @nat.cast_le ℝ _ _ _ _, refine le_trans hsmoothth hNN₀,
    rw [mul_assoc, mul_div_assoc, mul_le_mul_left h0C₃], exact hloc,
  },
  have hrecA₁ : 2*(log N₀)^((1:ℝ)/500) ≤ rec_sum A₁, {
    transitivity 2*(log N)^((1:ℝ)/500),
    rw mul_le_mul_left zero_lt_two, refine rpow_le_rpow _ _ _, refine log_nonneg _,
    exact_mod_cast h1N₀, rw log_le_log, exact hN₀N, norm_cast, rw nat.floor_pos,
    exact h1N₀', exact_mod_cast lt_trans zero_lt_one hN, norm_num1, exact real.nontrivial,
    refine le_trans _ rec_sum_sdiff, rw le_sub_iff_add_le, refine le_trans _ hi,
    rw add_le_add_iff_left, exact hrecZ,
   },
  have hN₀ : C₀ ≤ N₀, {
    rw ← @nat.cast_le ℝ _ _ _ _, refine le_trans _ hNN₀, exact hlargeN,
   },
  have hA₁N₀ : A₁ ⊆ range(N₀ + 1), {
    intros n hn, rw [mem_range, nat.lt_succ_iff],
    have hn' := (inter_subset_left _ _) ((sdiff_subset _ _) hn),
    rw mem_Ioc at hn', exact hn'.2,
   },
  have hA₁div : ∀ n ∈ A₁, ∃ p : ℕ, p ∣ n ∧ 4 ≤ p ∧ (p : ℝ) ≤ log N₀ ^ (1/500 : ℝ), {
    intros n hn, rw [mem_sdiff, mem_inter, mem_sdiff, not_mem_union] at hn,
    have hn' := hn.1.2.2.1, rw [mem_filter, not_and, not_not] at hn',
    rcases (hn' hn.1.2.1) with ⟨d, hd⟩, refine ⟨d,hd.1,hd.2.1,_⟩,
    refine le_trans hd.2.2 _, have : (0:ℝ) < 1000 := by norm_num1,
    rw ← rpow_le_rpow_iff _ _ this, rw [← rpow_mul, ← rpow_mul], norm_num1,
    rw rpow_one, exact hlogNN₀, exact le_of_lt hN₀large₂, exact le_of_lt h0logN,
    refine rpow_nonneg_of_nonneg _ _, exact le_of_lt h0logN,
    refine rpow_nonneg_of_nonneg _ _, exact le_of_lt hN₀large₂,
   },
  have hA₁smooth : ∀ n ∈ A₁, is_smooth (M) n, {
    intros n hn, rw is_smooth, intros q hq₁ hq₂, rw [mem_sdiff] at hn,
    have hn' := hn.2, rw [mem_filter, not_and] at hn',
    have := hn' hn.1, rw ← not_lt, intro hbad, refine this ⟨q,hq₁,hbad,hq₂⟩,
   },
  have hA₁reg : arith_regular N₀ A₁, {
    rw arith_regular, intros n hn, rw [mem_sdiff, mem_inter, mem_sdiff, not_mem_union] at hn,
    have hn' := hn.1.2.2.2, rw [mem_filter, not_and, not_and, not_not] at hn',
    have hn'' := hn' hn.1.2.1 _, refine ⟨_,_⟩,
    refine le_trans _ hn''.1, rw [mul_le_mul_left, log_le_log, log_le_log], exact hN₀N,
    norm_cast, exact lt_of_lt_of_le zero_lt_one h1N₀, norm_cast, exact lt_trans zero_lt_one hN,
    exact hN₀large₂, exact h0logN, norm_num1, refine le_trans hn''.2 hlogNN₀',
    intro hbad, rw hbad at hn,
    have htemp' := hAN ((filter_subset _ _) hn.1.2.1),
    rw [mem_Icc, ← not_lt] at htemp', exact htemp'.1 zero_lt_one,
   },
  specialize hcor N₀ hN₀ A₁ hA₁N₀ hA₁large hrecA₁ hA₁div hA₁smooth hA₁reg,
  rcases hcor with ⟨S,hS₁,hS₂⟩,
  rw rec_sum at hS₂, refine ⟨S,_,hS₂⟩,
  refine subset_trans hS₁ (subset_trans (sdiff_subset _ _) _),
  refine subset_trans (inter_subset_right _ _) _,
  refine subset_trans (sdiff_subset _ _) (filter_subset _ _),
end

