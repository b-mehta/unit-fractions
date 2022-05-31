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

lemma omega_eq_sum (N : ℕ) {n : ℕ} (hn : n ∈ range(N)) :
   ω n = ∑ p in (((range(N)).filter(λ p, nat.prime p)).filter(λ p, p ∣ n)), 1 := sorry

lemma sum_prime_counting : ∃ (C : ℝ), ∀ᶠ (N : ℕ) in at_top,
   (N:ℝ)*log(log N) -C*N ≤ ∑ (x : ℕ) in (range N), (ω x : ℝ) :=
begin
  let C := 2,
  use C,
  filter_upwards [eventually_ge_at_top 0]
    with N hN,
  calc _ ≤ ∑ (x : ℕ) in (range N),
       ( ∑ p in (((range(N)).filter(λ p, nat.prime p)).filter(λ p, p ∣ x)), 1 : ℝ) :_
     ... = _ :_,

  sorry,
  refine sum_congr _ _, refl, intros n hn, norm_cast, rw ← omega_eq_sum N hn,
end

lemma sum_prime_counting_sq : ∃ (C : ℝ), ∀ᶠ (N : ℕ) in at_top,
   ∑ (x : ℕ) in (range N), (ω x : ℝ)^2 ≤ N*(log(log N))^2 + C*N*log(log N):= sorry

lemma tendsto_pow_rec_loglog_spec_at_top :
  filter.tendsto (λ x : ℝ, x^((1:ℝ)-8/log(log x))) filter.at_top filter.at_top := sorry

lemma sieve_lemma_prec (N : ℕ) (y z : ℝ) :
   (((finset.range(N)).filter(λ n, ∀ p : ℕ, prime p → p ∣ n →
       ((p : ℝ) < y) ∨ (z < p))).card : ℝ) ≤
   ((partial_euler_product ⌊z⌋₊)/(partial_euler_product ⌊y⌋₊))*N + 2^(z+1) :=
sorry

lemma sieve_lemma_prec' : ∃ C c : ℝ, (0 < C) ∧ (0 < c) ∧
  ∀ᶠ (N : ℕ) in at_top, ∀ y z : ℝ, (2 ≤ y) → (z ≤ c*log N) →
   (((finset.range(N)).filter(λ n, ∀ p : ℕ, prime p → p ∣ n →
       ((p : ℝ) < y) ∨ (z < p))).card : ℝ) ≤ C*(log y/log z)*N :=
sorry

lemma filter_div_aux (a b c d: ℝ) (hb : 0 < b) (hc : 0 < c) : ∃ y z w : ℝ,
 (2 ≤ y) ∧ (16 ≤ w) ∧ (0 < z) ∧ (4*y + 4 ≤ z) ∧ (a ≤ y) ∧ (d ≤ y) ∧ (log w / log z ≤ b) ∧
 (∑ (x : ℕ) in filter nat.prime (Icc ⌈w⌉₊ ⌊z⌋₊), (log y / (log (x/4) * x)) ≤ c) := sorry

 #exit

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
     with ⟨y,z,w,h2y,h16w,h0z,hyz,hDy,hDy',hwzD',hzsum⟩,
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
  have hXbound : (X.card : ℝ) ≤ C*(log w/log z)*N := hsieve N hlarge w z h2w hz',
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
    refine le_trans (hsieve ⌈(N:ℝ)/m⌉₊ hTm y ((m:ℝ)/4) h2y hm) _,
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

-- No sorries below this point!


lemma turan_primes_estimate : ∃ (C : ℝ), ∀ᶠ (N : ℕ) in at_top,
  (∑ n in finset.range(N), ((ω n : ℝ) - log(log N))^2
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
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_const, nsmul_eq_mul, card_range],
  calc _ ≤ ∑ (x : ℕ) in range N, (ω x:ℝ) ^ 2 - 2*(-(C1*N)+N*log(log N))*log(log N) + N * log (log N) ^ 2 :_
     ... ≤ C2*N*log(log N) + N*(log(log N))^2- 2*(-(C1*N)+N*log(log N))*log(log N) + N * log (log N) ^ 2 :_
     ... = _ :_,
  rw [add_le_add_iff_right, sub_le_sub_iff_left, mul_le_mul_right, mul_le_mul_left zero_lt_two],
  rw neg_add_eq_sub, exact hlargesum, exact real.nontrivial, exact hlargeN,
  rw [add_le_add_iff_right, sub_le_sub_iff_right, add_comm], exact hlargesumsq, ring_nf,
  rw [mul_assoc (2*C1), mul_comm _ C2, ← add_mul, ← mul_assoc],
end

lemma filter_regular  (D : ℝ) (hD : 0 < D) : ∀ᶠ (N : ℕ) in at_top,
  ∀ A ⊆ range(N),
   ((A.filter(λ n:ℕ, ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)))).card : ℝ)
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
  let A' := A.filter(λ n:ℕ, ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N))),
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
  rw [mem_filter, not_and_distrib] at hn, refine sq_le_sq _,
  rw [le_abs, abs_of_pos], cases hn.2 with hn1 hn2,
  right, rw [neg_sub, le_sub, ← one_sub_mul], rw not_le at hn1, norm_num1,
  exact le_of_lt hn1, left, rw [le_sub_iff_add_le, add_comm, ← one_add_mul],
  rw not_le at hn2, refine le_trans _ (le_of_lt hn2), rw mul_le_mul_right, norm_num1,
  exact hlargeN, refine mul_pos _ hlargeN, norm_num1,
  refine sum_le_sum_of_subset_of_nonneg _ _, refine subset_trans (filter_subset _ _) hA,
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
  have haux: asymptotics.is_O_with ((1: ℝ)/8) (λ (x : ℝ), (log x))
     (λ (x : ℝ), x^((1:ℝ))) at_top, {
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
   ((A.filter(λ n:ℕ, ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)))).card : ℝ)
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
    ((tendsto_pow_rec_loglog_at_top h1pos).comp tendsto_coe_nat_at_top_at_top).eventually
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
∀ A : set ℕ, (upper_density A > 1/D) →  ∃ d ∈ finset.Icc ⌈y⌉₊ ⌊z⌋₊,
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
  let A2 := A'.filter(λ n, ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N))),
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
    nth_rewrite 3 mem_filter at hn, rw [not_and, not_not] at hn, exact hn.2.1.2 hn.1,
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
  let D := 2/(upper_density A),
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
    rw ← this, exact hDA,
   },
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
    intros s hs, rw finset.disjoint_iff_disjoint_coe,
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



-- Lemma 1
lemma sieve_lemma_one  : ∃ C : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ y z : ℝ, (3 ≤ y) → (y < z) → (z ≤ log N) →
   (((finset.range(2*N)).filter(λ n, N ≤ n ∧ ∀ p : ℕ, prime p → p ∣ n →
       ((p : ℝ) < y) ∨ (z < p))).card : ℝ) ≤
   C * (log y / log z) * N
    :=
sorry

theorem unit_fractions_upper_log_density :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range (N+1),
    25 * log (log (log N)) * log N / log (log N) ≤ ∑ n in A, (1 / n : ℝ) →
      ∃ S ⊆ A, ∑ n in S, (1 / n : ℝ) = 1 :=
sorry

