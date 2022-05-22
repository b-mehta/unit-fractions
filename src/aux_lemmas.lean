/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import for_mathlib.basic_estimates
import defs

/-!
# Title

This file should contain a formal proof of https://arxiv.org/pdf/2112.03726.pdf, but for now it
contains associated results useful for that paper.
-/

open_locale big_operators -- this lets me use ∑ and ∏ notation
open filter finset real
open nat (coprime)

open_locale arithmetic_function
open_locale classical
noncomputable theory



lemma useful_exp_estimate : ((35 : ℝ)/100) ≤ (1-2*(2/99))*real.exp(-1) :=
begin
  norm_num1, rw [exp_neg, ← one_div, ← div_eq_mul_one_div, le_div_iff', ← le_div_iff],
  apply le_trans (le_of_lt real.exp_one_lt_d9), norm_num1, norm_num1, exact exp_pos 1,
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

lemma two_in_Icc {a b x y: ℤ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : (|x-y|:ℝ) ≤ b-a :=
sorry

lemma omega_div {a b : ℕ} (h: b ∣ a) : (ω a:ℝ)- ω b ≤ ω (a/b) := sorry

lemma omega_div_le {a b : ℕ} : ω (a/b) ≤ ω a := sorry

lemma omega_mul_ppower {a q : ℕ} (hq : is_prime_pow q) : ω (q*a) ≤ 1 + ω a := sorry


lemma sum_le_sum_of_inj {A B : finset ℕ} {f1 f2 : ℕ → ℝ} (g : ℕ → ℕ) (hf2 : ∀ b ∈ B, 0 ≤ f2 b )
(hgB : ∀ a ∈ A, g a ∈ B) (hginj : ∀ a1 a2 ∈ A, (g a1 = g a2) → a1 = a2) (hgf : ∀ a ∈ A, f2 (g a) = f1 a) :
A.sum (λ (i : ℕ), f1 i) ≤ B.sum (λ (i : ℕ), f2 i) := sorry

lemma dvd_iff_ppowers_dvd (d n : ℕ) : d ∣ n ↔ ∀ q ∣ d, is_prime_pow q → q ∣ n := sorry

lemma eq_iff_ppowers_dvd (a b  : ℕ) : a = b ↔ (∀ q ∣ a, is_prime_pow q → coprime q (a/q)
 → q ∣ b) ∧ (∀ q ∣ b, is_prime_pow q → coprime q (b/q) → q ∣ a) := sorry

theorem is_prime_pow_dvd_prod {n : ℕ} {D : finset ℕ}
 (hD : ∀ a b ∈ D, a ≠ b → coprime a b) (hn : is_prime_pow n) :
n ∣ ∏ d in D, d ↔ ∃ d ∈ D, n ∣ d := sorry

lemma prime_pow_not_coprime_iff {a b : ℕ} (ha : is_prime_pow a) (hb : is_prime_pow b) :
 ¬ coprime a b ↔ ∃ (p : ℕ) (ka kb : ℕ), p.prime ∧ ka ≠ 0 ∧ kb ≠ 0 ∧
 p ^ ka = a ∧ p ^ kb = b := sorry

lemma prime_pow_not_coprime_prod_iff {a : ℕ} {D : finset ℕ} (ha : is_prime_pow a)
(hD : ∀ d ∈ D, is_prime_pow d) :
 ¬ coprime a (∏ d in D, d) ↔ ∃ (p : ℕ) (ka kd : ℕ) (d ∈ D), p.prime ∧ ka ≠ 0 ∧ kd ≠ 0 ∧
 p ^ ka = a ∧ p ^ kd = d := sorry

 lemma prime_pow_dvd_prod_prime_pow {a : ℕ} {D : finset ℕ} (ha : is_prime_pow a)
(hD : ∀ d ∈ D, is_prime_pow d) :
a ∣ (∏ d in D, d) → coprime a ((∏ d in D, d)/a) → a ∈ D := sorry

lemma prime_pow_prods_coprime {A B : finset ℕ} (hA : ∀ a ∈ A, is_prime_pow a)
 (hB : ∀ b ∈ B, is_prime_pow b) : coprime (∏ a in A, a) (∏ b in B, b) ↔
 ∀ a ∈ A, ∀ b ∈ B, coprime a b := sorry

lemma prod_le_max_size {ι N : Type*} [ordered_comm_semiring N]
  {s : finset ι} {f : ι → N} (hs : ∀ i ∈ s, 0 ≤ f i) (M : N) (hf : ∀ i ∈ s, f i ≤ M) :
  ∏ i in s, f i ≤ M^s.card :=
sorry

lemma omega_count_eq_ppowers {n : ℕ} :
  (filter (λ (r : ℕ), is_prime_pow r ∧ r.coprime (n / r)) n.divisors).card = ω n := sorry

lemma prod_of_subset_le_prod_of_ge_one {ι N : Type*} [ordered_comm_semiring N]
  {s t : finset ι} {f : ι → N} (h : t ⊆ s) (hs : ∀ i ∈ t, 0 ≤ f i) (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
sorry


lemma useful_identity (i:ℕ) (h : (1:ℝ) < i) : (1:ℝ) + 1 / (i - 1) = |(1 - (i)⁻¹)⁻¹| :=
begin
  rw [abs_eq_self.mpr, ← one_div, ← one_div, one_add_div, sub_add, sub_self,
    sub_zero, one_sub_div, one_div, inv_div],
  exact ne_of_gt (lt_trans zero_lt_one h),
  apply ne_of_gt, rw sub_pos, exact h,
  rw [inv_nonneg, sub_nonneg, inv_le, inv_one], exact le_of_lt h,
  exact lt_trans zero_lt_one h, exact zero_lt_one,
end

theorem sum_bUnion_le_sum_of_nonneg
{f : ℕ → ℚ} {s : finset ℕ} {t : ℕ → finset ℕ}
 (hf : ∀ x ∈ s.bUnion t, 0 ≤ f x) :
(s.bUnion t).sum (λ (x : ℕ), f x) ≤ s.sum (λ (x : ℕ), (t x).sum (λ (i : ℕ), f i)) :=
sorry

theorem weighted_ph {α M: Type*} {s : finset α}
{f : α → M} {w : α → M} {b : M} [ordered_comm_semiring M]
(hw : ∀ (a : α), a ∈ s → 0 ≤ w a) (hf : ∀ (a : α), a ∈ s → 0 ≤ f a)
(hb : b ≤ s.sum (λ (x : α), ((w x) * (f x)))) :
∃ (y : α) (H : y ∈ s), b ≤ (s.sum (λ (x : α), w x))*f y
:= sorry

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
  rw finset.mem_filter at hi, exact_mod_cast (le_of_lt (nat.prime.one_lt hi.2)),
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

lemma prod_one_add {D : finset ℕ} {k : ℝ}
  (f : nat.arithmetic_function ℝ) (hf' : f.is_multiplicative) :
  ∑ d in D, f d ≤
    ∏ p in D.bUnion (λ n, (nat.divisors n).filter nat.prime),
      (1 + ∑ q in (ppowers_in_set D).filter (λ q, p ∣ q), f q) :=
begin
  simp only [add_comm (1 : ℝ)],
  simp_rw [prod_add, prod_const_one, mul_one],
  change ∑ d in D, f d ≤
    ∑ x in finset.powerset _,
      ∏ t in _,
        ∑ i in _, f i,
  sorry
  -- simp_rw [prod_sum],

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

lemma useful_rec_aux4 : ∀ y : ℝ, ∀ k N : ℕ, ∀ D : finset ℕ,
 (∀ q : ℕ, q ∈ ppowers_in_set D → (y < q) ∧ q ≤ N) →
  ∑ d in D, (k:ℝ)^(ω d) / d ≤
  ( ∏ p in (finset.range(N+1)).filter(λ n, nat.prime n ),
    ((1:ℝ) + k/(p*(p-1)))) *
  (∏ p in  (finset.range(N+1)).filter(λ n, nat.prime n ∧ y < n ),
    ((1:ℝ) + k/(p-1))) :=
begin
  sorry
  -- have : ∑ d in D, (k : ℝ) ^ ω d / d ≤ ∏ q in ppowers_in_set D, (1 + k / q),
  -- {

  -- },
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
  filter_upwards [eventually_ge_at_top 0],
  intros N hN M u y q A hA hM hMN hu d hd,
  let X := (local_part A q).filter(λ n, (q*d)∣n ∧ coprime (q*d) (n/(q*d)) ),
  -- For the below, could use the aysmptotic for the sum, but that's overkill, is just
  -- the integral test upper bound in mathlib?
  have hDnotzero : d ≠ 0, {
   intro hzd, rw finset.mem_filter at hd,
   obtain hd' := hd.2.2.1,rw hzd at hd', push_cast at hd', rw mul_zero at hd',
   apply (lt_iff_not_ge (M*u) 0).mp hd', apply mul_nonneg, exact le_of_lt hM,
   exact hu,
  },
  have hharmonic : ∑ n in finset.range(N+1), (1 : ℝ)/n ≤ 2*log N,
  { sorry, },
  have hrectrivialaux : ((∑ n in X, (q:ℚ)/n)) ≤
    ∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), (q/n), {
      apply sum_le_sum_of_subset_of_nonneg, intros x hx,
      rw finset.mem_filter at hx, rw mem_filter,
      refine ⟨hA (mem_of_mem_filter x hx.1),hx.2.1⟩,
      intros i hi1 hi2, apply div_nonneg, exact nat.cast_nonneg q,
      exact nat.cast_nonneg i,
  },
    -- The next is the previous hypothesis with an annoying casting issue
  have hrectrivial' : ((∑ n in X, (q:ℚ)/n):ℝ) ≤
    ∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), (q/n), {
      sorry,
  },
  apply le_trans hrectrivial',
  have hrectrivial'' : ∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), ((q : ℝ)/n)
      = (1/d)*∑ m in (finset.range(N+1)).filter(λ x, q*d*x ≤ N), (1/m), {
        sorry,
  },
  rw hrectrivial'', rw le_div_iff, rw mul_comm, rw ← mul_assoc, rw mul_one_div_cancel,
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
  (M ≤ N) → ((N : ℝ) ≤ M^(2 : ℝ)) → (1 ≤ k)
  → (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n) : ℝ) < (log N)^((1:ℝ)/k)) →
  ∀ q ∈ ppowers_in_set A,  ∀ n ∈ local_part A q,
  ∃ d ∈ (finset.range(N+1)).filter( λ d, (∀ r : ℕ, is_prime_pow r → r ∣ d → coprime r (d/r) →
     real.exp((log N)^((1:ℝ) - 2/k)) < r ∧ r ≤ N) ∧ M*real.exp(-(log N)^((1:ℝ) - 1/k)) < q*d ∧ q*d ≤ N),
 (q*d ∣ n) ∧ coprime (q*d) (n/(q*d)) :=
begin
  filter_upwards [eventually_gt_at_top 1],
  intros N hlargeN M k A hA hM hMN hNM hk hAreg q hq n hn,
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
      exact hr2, exact nat.coprime.symm hQ'qd, exact hr2,
     },
    use d, split, rw mem_filter, split, rw [mem_range, nat.lt_succ_iff],
    refine le_trans _ hdupp, apply nat.le_mul_of_pos_left,
    rw pos_iff_ne_zero, by_contra, rw h at hq,
    exact zero_not_mem_ppowers_in_set hq, split, intros r hr1 hr2 hr3,
    have hrQ : r ∈ Q, {
      refine prime_pow_dvd_prod_prime_pow hr1 _ hr2 hr3, intros t ht,
      rw mem_filter at ht, exact ht.2.1,
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
  ∀ A ⊆ finset.range(N+1), (0 < M) → (M ≤ N) → ((N : ℝ) ≤ M^(2 : ℝ)) → (1 < k) →
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
  intros N haux1 haux2 hlarge hlarge' hlarge'' M k A hAN hzM hMN hNM h1k hkN hAreg q hq hsumq,
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
  specialize haux2 M k A hAN hzM hMN hNM (le_of_lt h1k) hAreg q hq,
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
    refine weighted_ph _ _ hbound3, intros d hd, rw one_div_nonneg,
    exact nat.cast_nonneg d, intros d hd, apply sum_nonneg, intros n hn,
    apply div_nonneg, exact mul_nonneg (nat.cast_nonneg q) (nat.cast_nonneg d),
    exact nat.cast_nonneg n,
  },
  have hfound : ∃ d ∈ D2, (rec_sum_local A q)/(2*∑ d in D2, (1/d)) ≤
     ∑ n in new_local d, (q*d)/n, {
      rcases hfound0 with ⟨x,hx1,hx2⟩, refine ⟨x,hx1,_⟩,
      rw [div_le_iff, mul_comm, mul_assoc, ← div_le_iff'], exact hx2, exact zero_lt_two,
      refine mul_pos zero_lt_two hDsumpos,
  },
  have hfound1 : ∃ d ∈ D2, (rec_sum_local A q : ℝ)/(2*∑ d in D2, (1/d)) ≤
     ∑ n in new_local d, (q*d)/n, {
       -- This is identical to hfound, modulo trivial casting issues
       sorry,
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
  -- The remaining goal is identical to hDsumpos, modulo trivial casting issues
  sorry,
end


-- Lemma 4
lemma rec_qsum_lower_bound (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1/2) :
  ∀ᶠ (N : ℕ) in at_top, ∀ A : finset ℕ,
  ((log N)^(-ε/2) ≤ rec_sum A )
  → (∀ n ∈ A, ((1 - ε)*log(log N) ≤ ω n ) ∧ ( (ω n : ℝ) ≤ 2*(log (log N))))
  → (1 - 2*ε)*real.exp(-1)*log(log N)  ≤ ∑ q in ppowers_in_set A, (1/q : ℝ)
:=
sorry


-- Lemma 6.1
lemma find_good_x :  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  (0 < M) → (M ≤ N) → ((N : ℝ) ≤ M^(2 : ℝ)) → (0 ∉ A) →
  (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
  (∀ (t : ℝ) (I : finset ℤ) (q ∈ ppowers_in_set A),
  I = finset.Icc ⌈t - (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) / 2⌉ ⌊t + (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) / 2⌋ →
  (((1 : ℝ)/(2*(log N)^((1 : ℝ)/100))) < rec_sum_local (A.filter (λ n, ∃ x ∈ I, (n:ℤ) ∣ x)) q)
  → (∃ xq ∈ I, ((q:ℤ) ∣ xq) ∧ (((35 : ℝ)/100)*log(log N)) ≤
     ∑ r in (ppowers_in_set A).filter(λ n, (n:ℤ) ∣ xq), 1/r ))
  :=
begin
  obtain hgoodd := find_good_d,
  rcases hgoodd with ⟨c,C,hc,hC,hgoodd⟩,
  have heasy1 : 0 < ((2:ℝ)/99) := by norm_num1,
  have heasy2 : ((2:ℝ)/99) < 1/2 := by norm_num1,
  obtain hlargerecbound := rec_qsum_lower_bound ((2:ℝ)/99) heasy1 heasy2,
  -- Work out the right filter later
  filter_upwards [hgoodd, hlargerecbound],
  clear hgoodd hlargerecbound,
  intros N hgooddN hlargerecbound M A hA h0M hMN hNM h0A hMA hreg t I q hq hI hqlocal,
  have hlarge0 : 0 < log(log(log N)), { sorry, },
  have hlarge1 : 0 < log(log N), { sorry, },
  have hlarge2 : 0 < log(N), { sorry, },
  have hlarge3 : 1 ≤ log N, { sorry, },
  have hlarge4 : 4*log(log(log N)) ≤ log(log N), { sorry, },
  have hlarge5 : 1/c/2 ≤ log(log(log N)), { sorry, },
  have hlarge6 : 2^((100:ℝ)/99) ≤ log N, { sorry, },
  have hlarge7 : log 2 < log(log(log N)), { sorry, },
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
    sorry,
  },
  have hNlogk : (1 - 2 / 99) * log (log N) + (1 + 5 / log k * log (log N)) ≤ 99 / 100 * log (log N), {
    sorry,
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
      rw [rec_sum_local, hem, sum_empty, ← not_le] at hqlocal, apply hqlocal, norm_cast,
      rw one_div_nonneg, refine mul_nonneg zero_le_two _, apply rpow_nonneg_of_nonneg,
      exact le_of_lt hlarge2,
     },
    obtain ⟨n,hn⟩ := this, rw [local_part, mem_filter] at hn,
    rw [ppowers_in_set, mem_bUnion], refine ⟨n,hn.1,_⟩, rw mem_filter,
    rw [ppowers_in_set, mem_bUnion] at hq, rcases hq with ⟨b,hb,hq⟩, rw mem_filter at hq,
    refine ⟨_,hq.2.1,hn.2.2⟩, rw nat.mem_divisors, refine ⟨hn.2.1,_⟩,
    intro hnz, rw hnz at hn, apply h0A, exact mem_of_mem_filter 0 hn.1,
   },
  have hqlocal2 :  (1/(log N) ≤ rec_sum_local A_I q), {
    refine le_trans _ (le_of_lt hqlocal), rw [one_div_le_one_div, ← le_div_iff],
    nth_rewrite 0 ← rpow_one (log N), rw [← rpow_sub], norm_num1,
    have : (0:ℝ) < 100/99, { norm_num1, },
    rw [← real.rpow_le_rpow_iff _ _ this, ← rpow_mul], norm_num1, rw rpow_one, exact hlarge6,
    exact le_of_lt hlarge2, exact zero_le_two, apply rpow_nonneg_of_nonneg,
    exact le_of_lt hlarge2, exact hlarge2, apply rpow_pos_of_pos, exact hlarge2, exact hlarge2,
    refine mul_pos zero_lt_two _, apply rpow_pos_of_pos, exact hlarge2,
   },
  specialize hgooddN M k A_I hA_I h0M hMN hNM h1k hkc hA_I' q hqA_I hqlocal2,
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
       exact le_of_lt hqlocal, exact hC,
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
       refine omega_div _, rw mem_filter at hm1, exact hm1.2, refine le_trans _ hreg.2, norm_cast,
       exact omega_div_le,
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

