/-
Copyright (c) 2021 Thomas Bloom, Alex Kontorovich, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bloom, Alex Kontorovich, Bhavik Mehta
-/

import analysis.special_functions.integrals
import analysis.special_functions.pow
import number_theory.arithmetic_function
import number_theory.von_mangoldt
import number_theory.primorial
import measure_theory.function.floor
import measure_theory.integral.integral_eq_improper
import data.complex.exponential_bounds
import analysis.p_series
import topology.algebra.order.floor
import number_theory.prime_counting
import analysis.special_functions.log.base
import for_mathlib.misc
import for_mathlib.integral_rpow
import tactic.equiv_rw

noncomputable theory

open_locale big_operators nnreal filter topological_space arithmetic_function

open filter asymptotics real set

section to_mathlib

end to_mathlib

lemma tendsto_log_coe_at_top : tendsto (λ x : ℕ, log (x : ℝ)) at_top at_top :=
tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top
lemma tendsto_log_log_coe_at_top : tendsto (λ x : ℕ, log (log (x : ℝ))) at_top at_top :=
tendsto_log_at_top.comp tendsto_log_coe_at_top
lemma tendsto_log_log_log_coe_at_top : tendsto (λ x : ℕ, log (log (log (x : ℝ)))) at_top at_top :=
tendsto_log_at_top.comp tendsto_log_log_coe_at_top

variables {M : Type*} [add_comm_monoid M] (a : ℕ → M)

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ n ≤ x, a(n).
-/
def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
∑ n in finset.Icc k ⌊x⌋₊, a n

lemma summatory_nat (k n : ℕ) :
  summatory a k n = ∑ i in finset.Icc k n, a i :=
by simp only [summatory, nat.floor_coe]

lemma summatory_eq_floor {k : ℕ} (x : ℝ) :
  summatory a k x = summatory a k ⌊x⌋₊ :=
by rw [summatory, summatory, nat.floor_coe]

lemma summatory_eq_of_Ico {n k : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a k x = summatory a k n :=
by rw [summatory_eq_floor, nat.floor_eq_on_Ico' _ _ hx]

lemma summatory_eq_of_lt_one {k : ℕ} {x : ℝ} (hk : k ≠ 0) (hx : x < k) :
  summatory a k x = 0 :=
begin
  rw [summatory, finset.Icc_eq_empty_of_lt, finset.sum_empty],
  rwa [nat.floor_lt' hk],
end

lemma summatory_zero_eq_of_lt {x : ℝ} (hx : x < 1) :
  summatory a 0 x = a 0 :=
by rw [summatory_eq_floor, nat.floor_eq_zero.2 hx, summatory_nat, finset.Icc_self,
  finset.sum_singleton]

@[simp] lemma summatory_zero {k : ℕ} (hk : k ≠ 0) : summatory a k 0 = 0 :=
summatory_eq_of_lt_one _ hk (by rwa [nat.cast_pos, pos_iff_ne_zero])

@[simp] lemma summatory_self {k : ℕ} : summatory a k k = a k :=
by simp [summatory]

@[simp] lemma summatory_one : summatory a 1 1 = a 1 :=
by simp [summatory]

lemma summatory_succ (k n : ℕ) (hk : k ≤ n + 1) :
  summatory a k (n+1) = a (n + 1) + summatory a k n :=
by rw [summatory_nat, ←nat.cast_add_one, summatory_nat, ←nat.Ico_succ_right, @add_comm M,
  finset.sum_Ico_succ_top hk, nat.Ico_succ_right]

lemma summatory_succ_sub {M : Type*} [add_comm_group M] (a : ℕ → M) (k : ℕ) (n : ℕ)
  (hk : k ≤ n + 1) :
  a (n + 1) = summatory a k (n + 1) - summatory a k n :=
begin
  rwa [←nat.cast_add_one, summatory_nat, summatory_nat, ←nat.Ico_succ_right,
    finset.sum_Ico_succ_top, nat.Ico_succ_right, add_sub_cancel'],
end

lemma summatory_eq_sub {M : Type*} [add_comm_group M] (a : ℕ → M) :
  ∀ n, n ≠ 0 → a n = summatory a 1 n - summatory a 1 (n - 1)
| 0 h := (h rfl).elim
| (n+1) _ := by simpa using summatory_succ_sub a 1 n

lemma abs_summatory_le_sum {M : Type*} [semi_normed_group M] (a : ℕ → M) {k : ℕ} {x : ℝ} :
  ∥summatory a k x∥ ≤ ∑ i in finset.Icc k ⌊x⌋₊, ∥a i∥ :=
norm_sum_le _ _

lemma summatory_const_one {x : ℝ} :
  summatory (λ _, (1 : ℝ)) 1 x = (⌊x⌋₊ : ℝ) :=
by { rw [summatory, finset.sum_const, nat.card_Icc, nat.smul_one_eq_coe], refl }

lemma summatory_nonneg' {M : Type*} [ordered_add_comm_group M] {a : ℕ → M} (k : ℕ) (x : ℝ)
  (ha : ∀ (i : ℕ), k ≤ i → (i : ℝ) ≤ x → 0 ≤ a i) (hk : k ≠ 0) :
  0 ≤ summatory a k x :=
begin
  apply finset.sum_nonneg,
  simp only [and_imp, finset.mem_Icc],
  intros i hi₁ hi₂,
  apply ha i hi₁ ((nat.le_floor_iff' (ne_of_gt (lt_of_lt_of_le hk.bot_lt hi₁))).1 hi₂),
end

lemma summatory_nonneg {M : Type*} [ordered_add_comm_group M] (a : ℕ → M) (x : ℝ) (k : ℕ)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  0 ≤ summatory a k x :=
finset.sum_nonneg (λ i _, ha _)

lemma summatory_monotone_of_nonneg {M : Type*} [ordered_add_comm_group M] (a : ℕ → M) (k : ℕ)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  monotone (summatory a k) :=
begin
  intros i j h,
  refine finset.sum_le_sum_of_subset_of_nonneg _ (λ k _ _, ha _),
  apply finset.Icc_subset_Icc le_rfl (nat.floor_mono h),
end

lemma abs_summatory_bound {M : Type*} [semi_normed_group M] (a : ℕ → M) (k z : ℕ)
  {x : ℝ} (hx : x ≤ z) :
  ∥summatory a k x∥ ≤ ∑ i in finset.Icc k z, ∥a i∥ :=
(abs_summatory_le_sum a).trans
  (finset.sum_le_sum_of_subset_of_nonneg
    (finset.Icc_subset_Icc le_rfl (nat.floor_le_of_le hx)) (by simp))

open measure_theory

@[measurability] lemma measurable_summatory {M : Type*} [add_comm_monoid M] [measurable_space M]
  {k : ℕ} {a : ℕ → M} :
  measurable (summatory a k) :=
begin
  change measurable ((λ y, ∑ i in finset.Icc k y, a i) ∘ _),
  exact measurable_from_nat.comp nat.measurable_floor,
end

lemma partial_summation_integrable {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) {f : ℝ → 𝕜} {x y : ℝ}
  {k : ℕ} (hf' : integrable_on f (Icc x y)) :
  integrable_on (summatory a k * f) (Icc x y) :=
begin
  let b := ∑ i in finset.Icc k ⌈y⌉₊, ∥a i∥,
  have : integrable_on (b • f) (Icc x y) := integrable.smul b hf',
  refine this.integrable.mono (measurable_summatory.ae_strongly_measurable.mul hf'.1) _,
  rw ae_restrict_iff' (measurable_set_Icc : measurable_set (Icc x _)),
  refine eventually_of_forall (λ z hz, _),
  rw [pi.mul_apply, norm_mul, pi.smul_apply, norm_smul],
  refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ _).trans _) (norm_nonneg _),
  { exact hz.2.trans (nat.le_ceil y) },
  rw real.norm_eq_abs,
  exact le_abs_self b,
end

/-- A version of partial summation where the upper bound is a natural number, useful to prove the
general case. -/
theorem partial_summation_nat {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  {k : ℕ} {N : ℕ} (hN : k ≤ N)
  (hf : ∀ i ∈ Icc (k : ℝ) N, has_deriv_at f (f' i) i) (hf' : integrable_on f' (Icc k N)) :
  ∑ n in finset.Icc k N, a n * f n =
    summatory a k N * f N - ∫ t in Icc (k : ℝ) N, summatory a k t * f' t :=
begin
  rw ←nat.Ico_succ_right,
  revert hf hf',
  refine nat.le_induction _ _ _ hN,
  { simp },
  intros N hN' ih hf hf',
  have hN'' : (N:ℝ) ≤ N + 1 := by simp only [zero_le_one, le_add_iff_nonneg_right],
  have : Icc (k:ℝ) (N+1) = Icc k N ∪ Icc N (N+1),
  { refine (Icc_union_Icc_eq_Icc _ hN'').symm,
    rwa nat.cast_le },
  simp only [nat.cast_succ, this, mem_union_eq, or_imp_distrib, forall_and_distrib,
    integrable_on_union] at ih hf hf' ⊢,
  replace ih := ih hf.1 hf'.1,
  have hN''' := hN'.trans le_self_add,
  rw [finset.sum_Ico_succ_top hN''', ih, summatory_succ _ _ _ hN''', add_mul, add_sub_assoc,
    add_comm, nat.cast_add_one, add_right_inj, eq_comm, sub_eq_sub_iff_sub_eq_sub, ←mul_sub,
    integral_union_ae, add_sub_cancel',
    ←set_integral_congr_set_ae (Ico_ae_eq_Icc' volume_singleton)],
  rotate, -- the first goal is the only hard one
  { rw [ae_disjoint, Icc_inter_Icc_eq_singleton _ hN'', volume_singleton],
    rwa nat.cast_le },
  { exact measurable_set_Icc.null_measurable_set },
  { exact partial_summation_integrable a hf'.1 },
  { exact partial_summation_integrable a hf'.2 },
  have : eq_on (λ x, summatory a k x * f' x) (λ x, summatory a k N • f' x) (Ico N (N+1)) :=
      λ x hx, congr_arg2 (*) (summatory_eq_of_Ico _ hx) rfl,
  rw [set_integral_congr measurable_set_Ico this, integral_smul, algebra.id.smul_eq_mul,
      set_integral_congr_set_ae (Ico_ae_eq_Ioc' volume_singleton volume_singleton),
      ←interval_integral.integral_of_le hN'', interval_integral.integral_eq_sub_of_has_deriv_at],
  { rw interval_of_le hN'',
    exact hf.2 },
  { exact (interval_integrable_iff_integrable_Icc_of_le hN'').2 hf'.2 },
end

/--
Right now this works for functions taking values in R or C, I think it should work for more target
spaces.
Also valid if k = 0 and a 0 = 0, not sure which is more interesting
-/
theorem partial_summation {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜) {k : ℕ} {x : ℝ}
  (hk : k ≠ 0) (hf : ∀ i ∈ Icc (k:ℝ) x, has_deriv_at f (f' i) i)
  (hf' : integrable_on f' (Icc k x)) :
  summatory (λ n, a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t :=
begin
  cases lt_or_le x k,
  { rw [Icc_eq_empty_of_lt h, measure.restrict_empty, integral_zero_measure, sub_zero,
      summatory_eq_of_lt_one _ hk h, summatory_eq_of_lt_one _ hk h, zero_mul] },
  have hx : k ≤ ⌊x⌋₊ := by rwa [nat.le_floor_iff' hk],
  have hx' : (⌊x⌋₊ : ℝ) ≤ x := nat.floor_le (le_trans (nat.cast_nonneg _) h),
  have hx'' : (k : ℝ) ≤ ⌊x⌋₊ := by rwa nat.cast_le,
  have : Icc (k : ℝ) x = Icc k ⌊x⌋₊ ∪ Icc ⌊x⌋₊ x := (Icc_union_Icc_eq_Icc hx'' hx').symm,
  simp only [this, integrable_on_union, mem_union, or_imp_distrib, forall_and_distrib] at hf hf' ⊢,
  rw [summatory, partial_summation_nat a f f' hx hf.1 hf'.1, eq_comm,
    sub_eq_sub_iff_sub_eq_sub, summatory_eq_floor, ←mul_sub,
    integral_union_ae _ (measurable_set_Icc.null_measurable_set : null_measurable_set (Icc (_:ℝ) _)),
    add_sub_cancel'],
  { have : eq_on (λ y, summatory a k y * f' y) (λ y, summatory a k ⌊x⌋₊ • f' y) (Icc ⌊x⌋₊ x),
    { intros y hy,
      dsimp,
      rw summatory_eq_floor,
      congr' 3,
      exact nat.floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_lt (nat.lt_floor_add_one _)⟩ },
    rw [set_integral_congr measurable_set_Icc this, integral_smul, algebra.id.smul_eq_mul,
      ←set_integral_congr_set_ae (Ioc_ae_eq_Icc' volume_singleton),
      ←interval_integral.integral_of_le hx',
      interval_integral.integral_eq_sub_of_has_deriv_at],
    { rw interval_of_le hx',
      exact hf.2 },
    { exact (interval_integrable_iff_integrable_Icc_of_le hx').2 hf'.2 } },
  { apply partial_summation_integrable _ hf'.1 },
  { apply partial_summation_integrable _ hf'.2 },
  { rw [ae_disjoint, Icc_inter_Icc_eq_singleton hx'' hx',
      volume_singleton] },
end

theorem partial_summation_cont {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜) {k : ℕ} {x : ℝ}
  (hk : k ≠ 0) (hf : ∀ i ∈ Icc (k:ℝ) x, has_deriv_at f (f' i) i) (hf' : continuous_on f' (Icc k x)) :
  summatory (λ n, a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t :=
partial_summation _ _ _ hk hf hf'.integrable_on_Icc

/--
A variant of partial summation where we assume differentiability of `f` and integrability of `f'` on
`[1, ∞)` and derive the partial summation equation for all `x`.
-/
theorem partial_summation' {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜) {k : ℕ} (hk : k ≠ 0)
  (hf : ∀ i ∈ Ici (k:ℝ), has_deriv_at f (f' i) i) (hf' : integrable_on f' (Ici k)) {x : ℝ} :
  summatory (λ n, a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t :=
partial_summation _ _ _ hk (λ i hi, hf _ hi.1) (hf'.mono_set Icc_subset_Ici_self)

/--
A variant of partial summation where we assume differentiability of `f` and continuity of `f'` on
`[1, ∞)` and derive the partial summation equation for all `x`.
-/
theorem partial_summation_cont' {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜) {k : ℕ}
  (hk : k ≠ 0) (hf : ∀ i ∈ Ici (k:ℝ), has_deriv_at f (f' i) i) (hf' : continuous_on f' (Ici k))
  (x : ℝ) :
  summatory (λ n, a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t :=
partial_summation_cont _ _ _ hk (λ i hi, hf _ hi.1) (hf'.mono Icc_subset_Ici_self)

-- BM: A definition of the Euler-Mascheroni constant
-- Maybe a different form is a better definition, and in any case it would be nice to show the
-- different definitions are equivalent.
-- This version uses an integral over an infinite interval, which in mathlib is *not* defined
-- as the limit of integrals over finite intervals, but there is a result saying they are equal:
-- see measure_theory.integral.integral_eq_improper: `interval_integral_tendsto_integral_Ioi`
def euler_mascheroni : ℝ := 1 - ∫ t in Ioi 1, int.fract t * (t^2)⁻¹

lemma fract_mul_integrable {f : ℝ → ℝ} (s : set ℝ)
  (hf' : integrable_on f s) :
  integrable_on (int.fract * f) s :=
begin
  refine integrable.mono hf' _ (eventually_of_forall _),
  { exact measurable_fract.ae_strongly_measurable.mul hf'.1 },
  intro x,
  simp only [norm_mul, pi.mul_apply, norm_of_nonneg (int.fract_nonneg _)],
  exact mul_le_of_le_one_left (norm_nonneg _) (int.fract_lt_one _).le,
end

lemma euler_mascheroni_convergence_rate :
  is_O_with 1 at_top
    (λ x : ℝ, 1 - (∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) - euler_mascheroni) (λ x, x⁻¹) :=
begin
  apply is_O_with.of_bound,
  rw eventually_at_top,
  refine ⟨1, λ x (hx : _ ≤ _), _⟩,
  have h : integrable_on (λ (x : ℝ), int.fract x * (x ^ 2)⁻¹) (Ioi 1),
  { apply fract_mul_integrable,
    apply integrable_on_pow_inv_Ioi one_lt_two zero_lt_one },
  rw [one_mul, euler_mascheroni, norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans hx)),
    sub_sub_sub_cancel_left, ←integral_diff measurable_set_Ioc h (h.mono_set Ioc_subset_Ioi_self)
    Ioc_subset_Ioi_self, Ioi_diff_Icc hx, norm_of_nonneg],
  { apply (set_integral_mono_on (h.mono_set (Ioi_subset_Ioi hx))
      (integrable_on_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx)) measurable_set_Ioi _).trans,
    { rw integral_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx),
      norm_num },
    { intros t ht,
      exact mul_le_of_le_one_left (inv_nonneg.2 (sq_nonneg _)) (int.fract_lt_one _).le } },
  exact set_integral_nonneg measurable_set_Ioi
    (λ t ht, div_nonneg (int.fract_nonneg _) (sq_nonneg _)),
end

lemma euler_mascheroni_integral_Ioc_convergence :
  tendsto (λ x : ℝ, 1 - ∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) at_top (𝓝 euler_mascheroni) :=
by simpa using
  (euler_mascheroni_convergence_rate.is_O.trans_tendsto tendsto_inv_at_top_zero).add_const
    euler_mascheroni

lemma euler_mascheroni_interval_integral_convergence :
  tendsto (λ x : ℝ, (1 : ℝ) - ∫ t in 1..x, int.fract t * (t^2)⁻¹) at_top (𝓝 euler_mascheroni) :=
begin
  apply euler_mascheroni_integral_Ioc_convergence.congr' _,
  rw [eventually_eq, eventually_at_top],
  exact ⟨1, λ x hx, by rw interval_integral.integral_of_le hx⟩,
end

lemma harmonic_series_is_O_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (λ i, (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni =
    (1 - (∫ t in Ioc 1 x, int.fract t * (t^2)⁻¹) - euler_mascheroni) - int.fract x * x⁻¹ :=
begin
  have diff : (∀ (i ∈ Ici (1:ℝ)), has_deriv_at (λ x, x⁻¹) (-(i ^ 2)⁻¹) i),
  { rintro i (hi : (1:ℝ) ≤ _),
    apply has_deriv_at_inv (zero_lt_one.trans_le hi).ne' },
  have cont : continuous_on (λ (i : ℝ), (i ^ 2)⁻¹) (Ici 1),
  { refine ((continuous_pow 2).continuous_on.inv₀ _),
    rintro i (hi : _ ≤ _),
    exact (pow_ne_zero_iff nat.succ_pos').2 (zero_lt_one.trans_le hi).ne' },
  have ps := partial_summation_cont' (λ _, (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont.neg) x,
  simp only [one_mul] at ps,
  simp only [ps, integral_Icc_eq_integral_Ioc],
  rw [summatory_const_one, nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx),
    ←int.self_sub_floor, sub_mul, mul_inv_cancel (zero_lt_one.trans_le hx).ne', sub_sub (1 : ℝ),
    sub_sub_sub_cancel_left, sub_sub, sub_sub, sub_right_inj, ←add_assoc, add_left_inj,
    ←eq_sub_iff_add_eq', nat.cast_one, ←integral_sub],
  rotate,
  { apply fract_mul_integrable,
    exact (cont.mono Icc_subset_Ici_self).integrable_on_Icc.mono_set Ioc_subset_Icc_self },
  { refine integrable_on.congr_set_ae _ Ioc_ae_eq_Icc,
    exact partial_summation_integrable _ (cont.neg.mono Icc_subset_Ici_self).integrable_on_Icc },
  have : eq_on (λ a : ℝ, int.fract a * (a ^ 2)⁻¹ - summatory (λ _, (1 : ℝ)) 1 a * -(a ^ 2)⁻¹)
    (λ y : ℝ, y⁻¹) (Ioc 1 x),
  { intros y hy,
    dsimp,
    have : 0 < y := zero_lt_one.trans hy.1,
    rw [summatory_const_one, nat.cast_floor_eq_cast_int_floor this.le, mul_neg, sub_neg_eq_add,
      ←add_mul, int.fract_add_floor, sq, mul_inv, mul_inv_cancel_left₀ this.ne'] },
  rw [set_integral_congr measurable_set_Ioc this, ←interval_integral.integral_of_le hx,
    integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one],
end

lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  is_O_with 1 at_top (λ (x : ℝ), int.fract x * f x) f :=
begin
  apply is_O_with.of_bound (eventually_of_forall _),
  intro x,
  simp only [one_mul, norm_mul],
  refine mul_le_of_le_one_left (norm_nonneg _) _,
  rw norm_of_nonneg (int.fract_nonneg _),
  exact (int.fract_lt_one x).le,
end

lemma harmonic_series_is_O_with :
  is_O_with 2 at_top (λ x, summatory (λ i, (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni) (λ x, x⁻¹) :=
begin
  have : is_O_with 1 at_top (λ (x : ℝ), int.fract x * x⁻¹) (λ x, x⁻¹) := is_O_with_one_fract_mul _,
  refine (euler_mascheroni_convergence_rate.sub this).congr' _ _ eventually_eq.rfl,
  { norm_num1 }, -- I seriously need to prove 1 + 1 = 2
  filter_upwards [eventually_ge_at_top (1 : ℝ)],
  intros x hx,
  exact (harmonic_series_is_O_aux hx).symm,
end

lemma harmonic_series_real_limit :
  tendsto (λ x, (∑ i in finset.Icc 1 ⌊x⌋₊, (i : ℝ)⁻¹) - log x) at_top (𝓝 euler_mascheroni) :=
by simpa using
  (harmonic_series_is_O_with.is_O.trans_tendsto tendsto_inv_at_top_zero).add_const euler_mascheroni

lemma harmonic_series_limit :
  tendsto (λ (n : ℕ), (∑ i in finset.Icc 1 n, (i : ℝ)⁻¹) - log n) at_top (𝓝 euler_mascheroni) :=
(harmonic_series_real_limit.comp tendsto_coe_nat_at_top_at_top).congr (λ x, by simp)

lemma summatory_log_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (λ i, log i) 1 x - (x * log x - x) =
    1 + ((∫ t in 1..x, int.fract t * t⁻¹) - int.fract x * log x) :=
begin
  rw interval_integral.integral_of_le hx,
  have diff : (∀ (i ∈ Ici (1:ℝ)), has_deriv_at log (i⁻¹) i),
  { rintro i (hi : (1:ℝ) ≤ _),
    exact has_deriv_at_log (zero_lt_one.trans_le hi).ne' },
  have cont : continuous_on (λ x : ℝ, x⁻¹) (Ici 1),
  { exact continuous_on_inv₀.mono  (λ x (hx : _ ≤ _), (zero_lt_one.trans_le hx).ne') },
  have ps := partial_summation_cont' (λ _, (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont) x,
  simp only [one_mul] at ps,
  simp only [ps, integral_Icc_eq_integral_Ioc],
  clear ps,
  rw [summatory_const_one, nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx), ←int.self_sub_fract,
    sub_mul, sub_sub (x * log x), sub_sub_sub_cancel_left, sub_eq_iff_eq_add, add_assoc,
    ←sub_eq_iff_eq_add', ←add_assoc, sub_add_cancel, nat.cast_one, ←integral_add],
  { rw [←integral_one, interval_integral.integral_of_le hx, set_integral_congr],
    { apply measurable_set_Ioc },
    intros y hy,
    have hy' : 0 < y := zero_lt_one.trans hy.1,
    rw [←add_mul, summatory_const_one, nat.cast_floor_eq_cast_int_floor hy'.le, int.fract_add_floor,
      mul_inv_cancel hy'.ne'] },
  { apply fract_mul_integrable,
    exact (cont.mono Icc_subset_Ici_self).integrable_on_Icc.mono_set Ioc_subset_Icc_self },
  { apply (partial_summation_integrable _ _).mono_set Ioc_subset_Icc_self,
    exact (cont.mono Icc_subset_Ici_self).integrable_on_Icc },
end

lemma is_o_const_of_tendsto_at_top (f : ℝ → ℝ) (l : filter ℝ) (h : tendsto f l at_top) (c : ℝ) :
  is_o l (λ (x : ℝ), c) f :=
begin
  rw is_o_iff,
  intros ε hε,
  have : ∀ᶠ (x : ℝ) in at_top, ∥c∥ ≤ ε * ∥x∥,
  { filter_upwards [eventually_ge_at_top (∥c∥ * ε⁻¹), eventually_ge_at_top (0:ℝ)],
    intros x hx₁ hx₂,
    rwa [←mul_inv_le_iff hε, norm_of_nonneg hx₂] },
  exact h.eventually this,
end

lemma is_o_one_log (c : ℝ) : is_o at_top (λ (x : ℝ), c) log :=
is_o_const_of_tendsto_at_top _ _ tendsto_log_at_top _

lemma summatory_log {c : ℝ} (hc : 2 < c) :
  is_O_with c at_top (λ x, summatory (λ i, log i) 1 x - (x * log x - x)) (λ x, log x) :=
begin
  have f₁ : is_O_with 1 at_top (λ (x : ℝ), int.fract x * log x) (λ x, log x) :=
    is_O_with_one_fract_mul _,
  have f₂ : is_o at_top (λ (x : ℝ), (1 : ℝ)) log  := is_o_one_log _,
  have f₃ : is_O_with 1 at_top (λ (x : ℝ), ∫ t in 1..x, int.fract t * t⁻¹) log,
  { simp only [is_O_with_iff, eventually_at_top, ge_iff_le, one_mul],
    refine ⟨1, λ x hx, _⟩,
    rw [norm_of_nonneg (log_nonneg hx), norm_of_nonneg, ←div_one x,
      ←integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one],
    swap,
    { apply interval_integral.integral_nonneg hx,
      intros y hy,
      exact mul_nonneg (int.fract_nonneg _) (inv_nonneg.2 (zero_le_one.trans hy.1)) },
    { have h₁ : interval_integrable (λ (u : ℝ), u⁻¹) volume 1 x,
      { refine interval_integral.interval_integrable_inv _ continuous_on_id,
        intros y hy,
        rw interval_of_le hx at hy,
        exact (zero_lt_one.trans_le hy.1).ne' },
      have h₂ : ∀ y ∈ Icc 1 x, int.fract y * y⁻¹ ≤ y⁻¹,
      { intros y hy,
        refine mul_le_of_le_one_left (inv_nonneg.2 _) (int.fract_lt_one _).le,
        exact zero_le_one.trans hy.1 },
      apply interval_integral.integral_mono_on hx _ h₁ h₂,
      { refine h₁.mono_fun' _ _,
        { exact measurable.ae_strongly_measurable (by measurability) },
        rw [eventually_le, ae_restrict_iff'],
        { apply eventually_of_forall,
          intros y hy,
          rw interval_oc_of_le hx at hy,
          rw [norm_mul, norm_inv, norm_of_nonneg (int.fract_nonneg _),
            norm_of_nonneg (zero_le_one.trans hy.1.le)],
          apply h₂,
          exact Ioc_subset_Icc_self hy },
        exact measurable_set_interval_oc } } },
  apply (f₂.add_is_O_with (f₃.sub f₁) _).congr' rfl _ eventually_eq.rfl,
  { norm_num [hc] },
  rw [eventually_eq, eventually_at_top],
  exact ⟨1, λ x hx, (summatory_log_aux hx).symm⟩,
end

lemma summatory_mul_floor_eq_summatory_sum_divisors {x y : ℝ}
  (hy : 0 ≤ x) (xy : x ≤ y) (f : ℕ → ℝ) :
  summatory (λ n, f n * ⌊x / n⌋) 1 y = summatory (λ n, ∑ i in n.divisors, f i) 1 x :=
begin
  simp_rw [summatory, ←nat.cast_floor_eq_cast_int_floor (div_nonneg hy (nat.cast_nonneg _)),
    ←summatory_const_one, summatory, finset.mul_sum, mul_one, finset.sum_sigma'],
  refine finset.sum_bij _ _ _ _ _,
  -- Construct the forward function
  { intros i hi,
    exact ⟨i.1 * i.2, i.1⟩ },
  -- Show it lands in the correct set
  { rintro ⟨i, j⟩ hi,
    simp_rw [finset.mem_sigma, finset.mem_Icc, nat.mem_divisors, dvd_mul_right, true_and, ne.def,
      nat.mul_eq_zero, not_or_distrib, ←ne.def, nat.le_floor_iff hy, nat.cast_mul,
      ←pos_iff_ne_zero, nat.succ_le_iff],
    simp only [finset.mem_Icc, finset.mem_sigma, nat.succ_le_iff,
      nat.le_floor_iff (div_nonneg hy (nat.cast_nonneg _))] at hi,
    refine ⟨⟨mul_pos hi.1.1 hi.2.1, _⟩, hi.1.1, hi.2.1⟩,
    apply (le_div_iff' _).1 hi.2.2,
    exact nat.cast_pos.2 hi.1.1 },
  -- Show it respects the function
  { rintro ⟨i, j⟩,
    simp },
  -- Show it's injective
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    dsimp at h,
    simp only [finset.mem_Icc, finset.mem_sigma, nat.succ_le_iff] at h₁ h₂,
    simp only [heq_iff_eq] at h ⊢,
    cases h.2,
    rw mul_right_inj' h₁.1.1.ne' at h,
    exact ⟨h.2, h.1⟩ },
  -- Show it's surjective
  { rintro ⟨i, j⟩ h,
    refine ⟨⟨j, i / j⟩, _⟩,
    simp_rw [finset.mem_sigma, finset.mem_Icc, nat.mem_divisors, nat.le_floor_iff hy,
      nat.succ_le_iff] at h,
    obtain ⟨⟨hij, hx'⟩, ⟨i, rfl⟩, -⟩ := h,
    simp_rw [exists_prop],
    simp only [canonically_ordered_comm_semiring.mul_pos] at hij,
    simp only [finset.mem_Icc, and_true, true_and, eq_self_iff_true, finset.mem_sigma, heq_iff_eq,
      nat.succ_le_iff, hij.1, hij.2, nat.mul_div_right, le_div_iff, nat.le_floor_iff (hy.trans xy),
      nat.le_floor_iff (div_nonneg hy (nat.cast_nonneg _)), nat.cast_pos, ←nat.cast_mul],
    rw [mul_comm] at hx',
    refine ⟨le_trans _ (hx'.trans xy), hx'⟩,
    rw nat.cast_le,
    apply nat.le_mul_of_pos_left hij.2 }
end

namespace nat.arithmetic_function

lemma sigma_zero_eq_zeta_mul_zeta :
  σ 0 = ζ * ζ :=
by rw [←zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]

lemma sigma_zero_apply_eq_sum_divisors {i : ℕ} :
  σ 0 i = ∑ d in i.divisors, 1 :=
begin
  rw [sigma_apply, finset.sum_congr rfl],
  intros x hx,
  apply pow_zero,
end

lemma sigma_zero_apply_eq_card_divisors {i : ℕ} :
  σ 0 i = i.divisors.card :=
 by rw [sigma_zero_apply_eq_sum_divisors, finset.card_eq_sum_ones]

end nat.arithmetic_function

localized "notation `τ` := nat.arithmetic_function.sigma 0" in arithmetic_function
open nat.arithmetic_function

lemma exp_sub_mul {x c : ℝ} {hc : 0 ≤ c} : c - c * log c ≤ exp x - c * x :=
begin
  rcases eq_or_lt_of_le hc with rfl | hc,
  { simp [(exp_pos _).le] },
  suffices : exp (log c) - c * log c ≤ exp x - c * x,
  { rwa exp_log hc at this },
  have h₁ : differentiable ℝ (λ x, exp x - c * x) :=
    differentiable_exp.sub (differentiable_id.const_mul _),
  have h₂ : ∀ t, deriv (λ y, exp y - c * y) t = exp t - c := by simp,
  cases le_total (log c) x with hx hx,
  { refine (convex_Icc (log c) x).monotone_on_of_deriv_nonneg h₁.continuous.continuous_on
      h₁.differentiable_on _ (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx,
    intros y hy,
    rw interior_Icc at hy,
    rw [h₂, sub_nonneg, ←log_le_iff_le_exp hc],
    apply hy.1.le },
  { refine (convex_Icc x (log c)).antitone_on_of_deriv_nonpos h₁.continuous.continuous_on
      h₁.differentiable_on _ (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx,
    intros y hy,
    rw interior_Icc at hy,
    rw [h₂, sub_nonpos, ←le_log_iff_exp_le hc],
    apply hy.2.le },
end

lemma div_bound_aux1 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ^ K ≤ n) (h2 : 0 < K) :
  (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) :=
begin
  transitivity (2 : ℝ) ^ (r : ℝ),
  { rw add_comm, simpa using one_add_mul_le_pow (show (-2 : ℝ) ≤ 1, by norm_num) r },
  { refine le_trans _ (rpow_le_rpow _ h1 _),
    { rw [←rpow_mul (zero_le_two : (0 : ℝ) ≤ 2), mul_div_cancel' _ h2.ne'] },
    { refine rpow_nonneg_of_nonneg zero_le_two _ },
    { exact div_nonneg (nat.cast_nonneg _) h2.le } }
end

lemma bernoulli_aux (x : ℝ) : x + 1 / 2 ≤ 2 ^ x :=
begin
  have h : (0 : ℝ) < log (2 : ℝ) := log_pos one_lt_two,
  have h₁ :
    1 / real.log 2 - 1 / real.log 2 * log (1 / real.log 2) ≤
      exp (real.log 2 * x) - 1 / real.log 2 * (real.log 2 * x),
  { apply exp_sub_mul,
    simp only [one_div, inv_nonneg],
    apply h.le },
  rw [rpow_def_of_pos zero_lt_two, ←le_sub_iff_add_le'],
  rw [←mul_assoc, div_mul_cancel _ h.ne', one_mul] at h₁,
  apply le_trans _ h₁,
  rw [one_div (real.log 2), log_inv],
  simp only [one_div, mul_neg, sub_neg_eq_add],
  suffices : real.log 2 / 2 - 1 ≤ log (real.log 2),
  { field_simp [h],
    rw le_div_iff h,
    linarith },
  transitivity' (-1/2),
  { linarith [log_two_lt_d9] },
  rw [div_le_iff' (@zero_lt_two ℝ _ _), ←log_rpow h, le_log_iff_exp_le (rpow_pos_of_pos h _)],
  apply exp_neg_one_lt_d9.le.trans _,
  apply le_trans _ (rpow_le_rpow _ log_two_gt_d9.le zero_le_two),
  { rw [real.rpow_two],
    norm_num },
  { norm_num }
end

lemma div_bound_aux2 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ≤ n) (h2 : 2 ≤ K) :
  (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) * K :=
begin
  have h4 : ((r : ℝ) + 1) / K ≤ 2 ^ ((r : ℝ) / K),
  { transitivity (r : ℝ) / K + 1 / 2,
    { rw add_div,
      simp only [one_div, add_le_add_iff_left],
      exact inv_le_inv_of_le zero_lt_two h2 },
    exact bernoulli_aux _ },
  have : 0 < K := by linarith,
  transitivity (2 : ℝ) ^ ((r : ℝ) / K) * K,
  { rwa ← div_le_iff this },
  apply mul_le_mul_of_nonneg_right _ this.le,
  exact rpow_le_rpow zero_le_two h1 (div_nonneg (nat.cast_nonneg _) this.le),
end

lemma divisor_function_exact_prime_power (r : ℕ) {p : ℕ} (h : p.prime) : σ 0 (p ^ r) = r + 1 :=
begin
  rw [nat.arithmetic_function.sigma_zero_apply_eq_card_divisors, nat.divisors_prime_pow h,
    finset.card_map, finset.card_range],
end

variables {R : Type*}

lemma divisor_function_exact {n : ℕ} :
  n ≠ 0 → σ 0 n = n.factorization.prod (λ _ k, k + 1) :=
begin
  intro hn,
  rw [nat.arithmetic_function.is_multiplicative_sigma.multiplicative_factorization _ hn],
  apply finsupp.prod_congr,
  intros p hp,
  rw divisor_function_exact_prime_power _ (nat.prime_of_mem_factorization hp),
end

lemma divisor_function_div_pow_eq {n : ℕ} (K : ℝ) (hn : n ≠ 0) :
  (σ 0 n : ℝ) / n ^ K⁻¹ = n.factorization.prod (λ p k, (k + 1) / (p ^ (↑k / K))) :=
begin
  simp only [finsupp.prod, finset.prod_div_distrib, rpow_nat_cast, ←nat.cast_pow, ←finset.prod_rpow,
    div_eq_mul_inv (coe _) K, rpow_mul, nat.cast_nonneg, implies_true_iff, ←nat.cast_prod],
  rw [←finsupp.prod, nat.factorization_prod_pow_eq_self hn, divisor_function_exact hn, finsupp.prod,
    nat.cast_prod],
  simp only [nat.cast_add_one],
end

@[to_additive sum_le_sum_of_subset_of_nonpos]
lemma prod_le_prod_of_subset_of_le_one' {ι N : Type*} [ordered_comm_monoid N]
  {s t : finset ι} {f : ι → N} (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
by classical;
calc ∏ i in t, f i = ∏ i in t \ s ∪ s, f i : by rw [finset.sdiff_union_of_subset h]
    ... = (∏ i in t \ s, f i) * ∏ i in s, f i : finset.prod_union finset.sdiff_disjoint
    ... ≤ ∏ i in s, f i : mul_le_of_le_one_left' $ finset.prod_le_one' $ by simpa

lemma prod_le_prod_of_subset_of_le_one {ι N : Type*} [ordered_comm_semiring N]
  {s t : finset ι} {f : ι → N} (h : s ⊆ t) (hs : ∀ i ∈ t, 0 ≤ f i) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
by classical;
calc ∏ i in t, f i = (∏ i in t \ s, f i) * ∏ i in s, f i : (finset.prod_sdiff h).symm
    ... ≤ ∏ i in s, f i :
      mul_le_of_le_one_left (finset.prod_nonneg (λ i hi, hs _ (h hi))) $
        finset.prod_le_one (λ i hi, hs _ (finset.sdiff_subset _ _ hi)) (by simpa)

lemma prod_of_subset_le_prod_of_one_le {ι N : Type*} [ordered_comm_semiring N]
  {s t : finset ι} {f : ι → N} (h : t ⊆ s) (hs : ∀ i ∈ t, 0 ≤ f i) (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
by classical;
calc ∏ i in t, f i ≤ (∏ i in s \ t, f i) * ∏ i in t, f i :
      le_mul_of_one_le_left (finset.prod_nonneg hs) (one_le_prod (by simpa using hf))
    ... = ∏ i in s, f i : finset.prod_sdiff h

lemma anyk_divisor_bound (n : ℕ) {K : ℝ} (hK : 2 ≤ K) :
  (σ 0 n : ℝ) ≤ (n : ℝ) ^ (1 / K) * K ^ ((2 : ℝ) ^ K) :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp only [one_div, finset.card_empty, algebra.id.smul_eq_mul, nat.divisors_zero,
      nat.cast_zero, zero_mul, finset.sum_const, pow_zero, nat.arithmetic_function.sigma_apply],
    rw zero_rpow, { simp },
    simp only [inv_eq_zero, ne.def],
    linarith },
  rw [←div_le_iff' (rpow_pos_of_pos (nat.cast_pos.2 hn) _), one_div,
    divisor_function_div_pow_eq _ hn.ne', finsupp.prod, nat.support_factorization],
  have : n.factors.to_finset.filter (λ p, ↑p < (2 : ℝ) ^ K) ⊆ _ := finset.filter_subset _ _,
  refine (prod_le_prod_of_subset_of_le_one this _ _).trans _,
  { intros i hi,
    exact div_nonneg (nat.cast_add_one_pos _).le (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) },
  { simp only [list.mem_to_finset, finset.mem_filter, true_and, not_lt] {contextual := tt},
    intros p hp hp',
    refine div_le_one_of_le _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
    apply div_bound_aux1 _ _ _ hp',
    linarith },
  refine (finset.prod_le_prod _ _).trans ((finset.prod_const K).trans_le _),
  { intros i _,
    exact div_nonneg (nat.cast_add_one_pos _).le (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) },
  swap,
  { rw ←rpow_nat_cast,
    refine rpow_le_rpow_of_exponent_le (by linarith) _,
    simp only [←nat.le_floor_iff (rpow_nonneg_of_nonneg zero_le_two _)],
    rw [←nat.sub_zero ⌊(_ : ℝ)⌋₊, ←nat.card_Ioc 0 ⌊(2 : ℝ) ^ K⌋₊],
    refine finset.card_le_of_subset _,
    intros p,
    simp only [finset.mem_filter, list.mem_to_finset, finset.mem_Ioc, and_imp],
    intros hp₁ hp₂,
    refine ⟨nat.pos_of_mem_factors hp₁, _⟩,
    rw [nat.le_floor_iff (rpow_nonneg_of_nonneg zero_le_two _)],
    exact hp₂.le },
  intros p hp,
  simp only [finset.mem_filter, list.mem_to_finset] at hp,
  have hp' := nat.prime_of_mem_factors hp.1,
  rw div_le_iff',
  apply div_bound_aux2 _ _ _ _ hK,
  { exact_mod_cast hp'.two_le },
  exact rpow_pos_of_pos (nat.cast_pos.2 hp'.pos) _,
end.

lemma log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
(log_le_log hx (hx.trans_le hxy)).2 hxy

lemma log_log_mul_log_div_rpow {ε : ℝ} (hε : 0 < ε) :
  tendsto (λ x : ℝ, log (log x) * log x / x ^ ε) at_top (𝓝 0) :=
begin
  refine is_o.tendsto_div_nhds_zero _,
  refine ((is_o_log_id_at_top.comp_tendsto tendsto_log_at_top).mul_is_O (is_O_refl _ _)).trans _,
  refine ((is_o_log_rpow_at_top (half_pos hε)).pow zero_lt_two).congr' _ _,
  { filter_upwards with x using by simp [sq] },
  filter_upwards [eventually_ge_at_top (0 : ℝ)] with x hx,
  rw [←rpow_two, ←rpow_mul hx, div_mul_cancel ε two_ne_zero],
end

lemma divisor_bound₁ {ε : ℝ} (hε1 : 0 < ε) (hε2 : ε ≤ 1) :
  ∀ᶠ (n : ℕ) in at_top, (σ 0 n : ℝ) ≤ n ^ (real.log 2 / log (log (n : ℝ)) * (1 + ε)) :=
begin
  have h : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have hl := tendsto_log_at_top.comp h,
  have hx : tendsto
    (λ n : ℕ, 2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3)))
    at_top (𝓝 0),
  { simpa using ((log_log_mul_log_div_rpow (div_pos hε1 zero_lt_three)).comp hl).const_mul 2 },
  have hε : 0 < real.log 2 * ε / 2 := half_pos (mul_pos (log_pos one_lt_two) hε1),
  filter_upwards [tendsto_log_log_coe_at_top (eventually_ge_at_top (real.log 2 * (1 + ε / 2))⁻¹),
    tendsto_log_log_coe_at_top (eventually_gt_at_top 0), hl (eventually_gt_at_top 0),
    tendsto_log_log_coe_at_top (eventually_ge_at_top (2 * real.log 2 * (1 + ε / 2))),
    h (eventually_gt_at_top 0),
    hx (metric.closed_ball_mem_nhds 0 hε)] with n hlln' hlln hln hlln'' hn hx',
  dsimp at hlln hlln' hln hlln'' hn,
  simp only [mem_preimage, mem_closed_ball_zero_iff, norm_eq_abs] at hx',
  set K := log (log (n : ℝ)) / ((real.log 2) * (1 + ε / 2)) with hK,
  have hpowK_pos : 0 < (2 : ℝ) ^ K := rpow_pos_of_pos zero_lt_two _,
  have hε : 0 < real.log 2 * (1 + ε / 2),
  { exact mul_pos (log_pos one_lt_two) (by linarith) },
  have hpowK : 2 ^ K ≤ real.log n ^ (1 - ε / 3),
  { rw [←log_le_log hpowK_pos (rpow_pos_of_pos hln _), log_rpow zero_lt_two, log_rpow hln, hK,
      mul_comm (real.log 2), ←div_div, div_mul_cancel _ (log_pos one_lt_two).ne',
      div_le_iff', ←mul_assoc],
    { exact le_mul_of_one_le_left hlln.le (by nlinarith) },
    { linarith } },
  have hlogK : log K ≤ 2 * log (log (real.log n)),
  { rwa [hK, div_eq_mul_inv, log_mul hlln.ne' (ne_of_gt _), two_mul, add_le_add_iff_left,
      log_le_log _ hlln];
    exact inv_pos.2 hε },
  have hK₂ : 2 ≤ K,
  { rwa [le_div_iff hε, ←mul_assoc] },
  have hK₀ : 0 < K := zero_lt_two.trans_le hK₂,
  have hK' : 0 < K ^ ((2 : ℝ) ^ K) := rpow_pos_of_pos hK₀ _,
  refine (anyk_divisor_bound n hK₂).trans _,
  rw [←log_le_log (mul_pos (rpow_pos_of_pos hn _) hK') (rpow_pos_of_pos hn _),
    log_mul (rpow_pos_of_pos hn _).ne' hK'.ne', log_rpow hn, log_rpow hK₀, log_rpow hn],
  refine (add_le_add_left (mul_le_mul hpowK hlogK (log_nonneg (one_le_two.trans hK₂))
    (rpow_nonneg_of_nonneg hln.le _)) _).trans _,
  rw [hK, one_div_div, ←div_mul_eq_mul_div],
  suffices : log (n : ℝ) ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) ≤
    log (2 : ℝ) / log (log (n : ℝ)) * (ε / 2) * log (n : ℝ),
  { linarith },
  suffices : 2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / (log (n : ℝ) ^ (ε / 3))) ≤
    log (2 : ℝ) * ε / 2,
  { rw [rpow_sub hln, div_eq_mul_one_div, rpow_one, div_mul_eq_mul_div,
      mul_comm _ (log (n : ℝ)), mul_assoc],
    refine mul_le_mul_of_nonneg_left _ hln.le,
    rw le_div_iff hlln,
    field_simp at this ⊢,
    rwa [mul_assoc] },
  exact le_of_abs_le hx',
end

lemma divisor_bound {ε : ℝ} (hε1 : 0 < ε) :
  ∀ᶠ (n : ℕ) in at_top, (σ 0 n : ℝ) ≤ n ^ (real.log 2 / log (log (n : ℝ)) * (1 + ε)) :=
begin
  cases le_total ε 1,
  { apply divisor_bound₁ hε1 h },
  have t := tendsto_log_at_top,
  have t' := (t.comp t).comp tendsto_coe_nat_at_top_at_top,
  filter_upwards [divisor_bound₁ zero_lt_one le_rfl, t' (eventually_ge_at_top 0),
    eventually_ge_at_top 1] with n hn hn' hn'',
  dsimp at hn',
  apply hn.trans (rpow_le_rpow_of_exponent_le _ _),
  { rwa nat.one_le_cast },
  exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (log_nonneg one_le_two) hn'),
end

lemma trivial_divisor_bound {n : ℕ} :
  σ 0 n ≤ n :=
begin
  rw [sigma_zero_apply_eq_card_divisors],
  exact (finset.card_le_of_subset (finset.filter_subset _ _)).trans_eq (by simp),
end

lemma weak_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ (n : ℕ) in at_top, (σ 0 n : ℝ) ≤ (n : ℝ)^ε :=
begin
  cases le_total (1 : ℝ) ε,
  { filter_upwards [eventually_ge_at_top 1] with n hn,
    refine (nat.cast_le.2 _).trans (real.le_rpow_self_of_one_le (nat.one_le_cast.2 hn) h),
    exact trivial_divisor_bound },
  let t := tendsto_log_at_top,
  have hx : tendsto (λ n : ℕ, log (2 : ℝ) * 2 * (log (log (n : ℝ)))⁻¹) at_top (𝓝 0),
  { simpa using ((t.comp t).comp tendsto_coe_nat_at_top_at_top).inv_tendsto_at_top.const_mul
      (log (2 : ℝ) * 2) },
  filter_upwards [divisor_bound zero_lt_one, eventually_ge_at_top 1,
    hx (metric.closed_ball_mem_nhds 0 hε)] with n hn hn' hx',
  refine hn.trans (rpow_le_rpow_of_exponent_le (nat.one_le_cast.2 hn') _),
  rw [div_mul_eq_mul_div, div_eq_mul_inv],
  simp only [mem_preimage, mem_closed_ball_zero_iff, norm_eq_abs] at hx',
  exact le_of_abs_le hx'
end

lemma von_mangoldt_upper {n : ℕ} : Λ n ≤ log (n : ℝ) :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  rw ←von_mangoldt_sum, exact finset.single_le_sum (λ i hi, von_mangoldt_nonneg)
    (nat.mem_divisors_self _ hn.ne'),
end

lemma von_mangoldt_summatory {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
  summatory (λ n, Λ n * ⌊x / n⌋) 1 y = summatory (λ n, real.log n) 1 x :=
by simp only [summatory_mul_floor_eq_summatory_sum_divisors hx xy,
  von_mangoldt_sum]

lemma helpful_floor_identity {x : ℝ} :
  ⌊x⌋ - 2 * ⌊x/2⌋ ≤ 1 :=
begin
  rw [←int.lt_add_one_iff, ←@int.cast_lt ℝ],
  push_cast,
  linarith [int.sub_one_lt_floor (x/2), int.floor_le x],
end

lemma helpful_floor_identity2 {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x < 2) :
  ⌊x⌋ - 2 * ⌊x/2⌋ = 1 :=
begin
  have h₁ : ⌊x⌋ = 1,
  { rw [int.floor_eq_iff, int.cast_one],
    exact ⟨hx₁, hx₂⟩ },
  have h₂ : ⌊x/2⌋ = 0,
  { rw [int.floor_eq_iff],
    norm_cast,
    split;
    linarith },
  rw [h₁, h₂],
  simp,
end

lemma helpful_floor_identity3 {x : ℝ} :
  2 * ⌊x/2⌋ ≤ ⌊x⌋ :=
begin
  have h₄ : (2 : ℝ) * ⌊x / 2⌋ - 1 < ⌊x⌋ :=
    lt_of_le_of_lt (sub_le_sub_right ((le_div_iff' (by norm_num1)).1 (int.floor_le _)) _)
      (int.sub_one_lt_floor x),
  norm_cast at h₄,
  rwa ←int.sub_one_lt_iff,
end

def chebyshev_error (x : ℝ) : ℝ :=
  (summatory (λ i, real.log i) 1 x - (x * log x - x))
    - 2 * (summatory (λ i, real.log i) 1 (x/2) - (x/2 * log (x/2) - x/2))

lemma von_mangoldt_floor_sum {x : ℝ} (hx₀ : 0 < x) :
  summatory (λ n, Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x = real.log 2 * x + chebyshev_error x :=
begin
  rw [chebyshev_error, mul_sub, log_div hx₀.ne' two_ne_zero, mul_sub, ←mul_assoc,
    mul_div_cancel' x two_ne_zero, mul_sub, sub_right_comm (x * log x), ←sub_add _ (_ - _),
    sub_add_eq_add_sub, sub_sub_sub_cancel_right, ←sub_sub, mul_comm x, add_sub_cancel'_right,
    ←von_mangoldt_summatory hx₀.le le_rfl, summatory,
    ←von_mangoldt_summatory (div_nonneg hx₀.le zero_le_two) (half_le_self hx₀.le), summatory,
    summatory, finset.mul_sum, ←finset.sum_sub_distrib, finset.sum_congr rfl],
  intros i hi,
  rw div_right_comm,
  ring,
end

def chebyshev_first (x : ℝ) : ℝ := ∑ n in (finset.range (⌊x⌋₊ + 1)).filter nat.prime, real.log n
def chebyshev_second (x : ℝ) : ℝ := ∑ n in finset.range (⌊x⌋₊ + 1), Λ n
def chebyshev_first' (x : ℝ) : ℝ := ∑ n in (finset.range ⌊x⌋₊).filter nat.prime, real.log n
def chebyshev_second' (x : ℝ) : ℝ := ∑ n in finset.range ⌊x⌋₊, Λ n
localized "notation `ϑ` := chebyshev_first" in analytic_number_theory
localized "notation `ψ` := chebyshev_second" in analytic_number_theory
localized "notation `ϑ'` := chebyshev_first'" in analytic_number_theory
localized "notation `ψ'` := chebyshev_second'" in analytic_number_theory

lemma chebyshev_first_eq {x : ℝ} :
  ϑ x = ∑ n in (finset.range (⌊x⌋₊ + 1)).filter nat.prime, Λ n :=
finset.sum_congr rfl (by simp [von_mangoldt_apply_prime] {contextual := tt})

lemma chebyshev_first'_eq {x : ℝ} :
  ϑ' x = ∑ n in (finset.range ⌊x⌋₊).filter nat.prime, Λ n :=
finset.sum_congr rfl (by simp [von_mangoldt_apply_prime] {contextual := tt})

lemma chebyshev_first_le_chebyshev_second : ϑ ≤ ψ :=
begin
  intro x,
  rw chebyshev_first_eq,
  exact finset.sum_le_sum_of_subset_of_nonneg (finset.filter_subset _ _)
    (λ _ _ _, von_mangoldt_nonneg),
end

lemma chebyshev_first'_le_chebyshev_second' : ϑ' ≤ ψ' :=
begin
  intro x,
  rw chebyshev_first'_eq,
  exact finset.sum_le_sum_of_subset_of_nonneg (finset.filter_subset _ _)
    (λ _ _ _, von_mangoldt_nonneg),
end

lemma chebyshev_first_nonneg : 0 ≤ ϑ :=
λ x, by { rw chebyshev_first_eq, exact finset.sum_nonneg' (λ _, von_mangoldt_nonneg) }

lemma chebyshev_first'_nonneg : 0 ≤ ϑ' :=
λ x, by { rw chebyshev_first'_eq, exact finset.sum_nonneg' (λ _, von_mangoldt_nonneg) }

lemma chebyshev_second_nonneg : 0 ≤ ψ :=
λ x, finset.sum_nonneg' (λ _, von_mangoldt_nonneg)

lemma chebyshev_second'_nonneg : 0 ≤ ψ' :=
λ x, finset.sum_nonneg' (λ _, von_mangoldt_nonneg)

lemma log_nat_nonneg : ∀ (n : ℕ), 0 ≤ log (n : ℝ)
| 0 := by simp
| (n+1) := log_nonneg (by simp)

lemma chebyshev_first_monotone : monotone ϑ :=
begin
  intros x₁ x₂ h,
  apply finset.sum_le_sum_of_subset_of_nonneg,
  { apply finset.filter_subset_filter _ (finset.range_mono (add_le_add_right _ _)),
    exact nat.floor_mono h },
  rintro i - -,
  apply log_nat_nonneg,
end

lemma is_O_chebyshev_first_chebyshev_second : is_O at_top ϑ ψ :=
is_O_of_le _
  (λ x, by { rw [norm_of_nonneg (chebyshev_first_nonneg _),
                 norm_of_nonneg (chebyshev_second_nonneg _)],
             exact chebyshev_first_le_chebyshev_second _ })

lemma chebyshev_second_eq_summatory : ψ = summatory Λ 1 :=
begin
  ext x,
  rw [chebyshev_second, summatory, eq_comm, finset.sum_subset_zero_on_sdiff],
  { exact finset.Icc_subset_range_add_one },
  { intros y hy,
    rw [finset.mem_sdiff, finset.mem_range, finset.mem_Icc, nat.lt_add_one_iff, not_and', not_le,
      nat.lt_one_iff] at hy,
    rw hy.2 hy.1,
    simp },
  { intros,
    refl }
end

@[simp] lemma chebyshev_first_zero : ϑ 0 = 0 :=
by simp [chebyshev_first_eq, finset.filter_singleton, nat.not_prime_zero]
@[simp] lemma chebyshev_second_zero : ψ 0 = 0 := by simp [chebyshev_second]
@[simp] lemma chebyshev_first'_zero : ϑ' 0 = 0 := by simp [chebyshev_first']
@[simp] lemma chebyshev_second'_zero : ψ' 0 = 0 := by simp [chebyshev_second']

lemma chebyshev_lower_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_error x ≤ ψ x - real.log 2 * x :=
begin
  rw [le_sub_iff_add_le', ←von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory],
  apply finset.sum_le_sum,
  intros i hi,
  apply mul_le_of_le_one_right von_mangoldt_nonneg,
  norm_cast,
  apply helpful_floor_identity,
end

lemma chebyshev_upper_aux {x : ℝ} (hx : 0 < x) :
  ψ x - ψ (x / 2) - real.log 2 * x ≤ chebyshev_error x :=
begin
  rw [sub_le_iff_le_add', ←von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory],
  have : finset.Icc 1 ⌊x/2⌋₊ ⊆ finset.Icc 1 ⌊x⌋₊,
  { exact finset.Icc_subset_Icc le_rfl (nat.floor_mono (half_le_self hx.le)) },
  rw [summatory, ←finset.sum_sdiff this, add_sub_cancel],
  refine (finset.sum_le_sum _).trans
    (finset.sum_le_sum_of_subset_of_nonneg (finset.sdiff_subset _ _) _),
  { simp_rw [finset.mem_sdiff, finset.mem_Icc, and_imp, not_and, not_le, nat.le_floor_iff hx.le,
      nat.floor_lt (div_nonneg hx.le zero_le_two), nat.succ_le_iff],
    intros i hi₁ hi₂ hi₃,
    replace hi₃ := hi₃ hi₁,
    norm_cast,
    rw [helpful_floor_identity2, int.cast_one, mul_one],
    { refine (one_le_div _).2 hi₂,
      rwa [nat.cast_pos] },
    rwa [div_lt_iff, ←div_lt_iff'],
    { norm_num1 },
    rwa [nat.cast_pos] },
  rintro i - -,
  apply mul_nonneg von_mangoldt_nonneg _,
  rw sub_nonneg,
  norm_cast,
  apply helpful_floor_identity3,
end

lemma chebyshev_error_O :
  is_O at_top chebyshev_error log :=
begin
  have t : (2 : ℝ) < 3 := by norm_num,
  refine (summatory_log t).is_O.sub (is_O.const_mul_left _ _),
  refine ((summatory_log t).is_O.comp_tendsto (tendsto_id.at_top_div_const zero_lt_two)).trans _,
  apply is_O.of_bound 1,
  filter_upwards [eventually_ge_at_top (2 : ℝ)],
  intros x hx,
  rw [function.comp_app, id.def, one_mul, norm_of_nonneg (log_nonneg _),
    norm_of_nonneg (log_nonneg _), log_le_log];
  linarith
end

lemma chebyshev_lower_explicit {c : ℝ} (hc : c < real.log 2) :
  ∀ᶠ x : ℝ in at_top, c * x ≤ ψ x :=
begin
  have h₁ := (chebyshev_error_O.trans_is_o is_o_log_id_at_top).bound (sub_pos_of_lt hc),
  filter_upwards [eventually_ge_at_top (1 : ℝ), h₁],
  intros x hx₁ hx₂,
  rw [id.def, norm_of_nonneg (zero_le_one.trans hx₁), real.norm_eq_abs] at hx₂,
  have := (neg_le_of_abs_le hx₂).trans (chebyshev_lower_aux (zero_lt_one.trans_le hx₁)),
  linarith,
end

lemma chebyshev_lower :
  is_O at_top id ψ :=
begin
  rw [is_O_iff],
  refine ⟨(real.log 2 / 2)⁻¹, _⟩,
  filter_upwards [eventually_ge_at_top (0 : ℝ),
    chebyshev_lower_explicit (half_lt_self (log_pos one_lt_two))],
  intros x hx₁ hx₂,
  rw [mul_comm, ←div_eq_mul_inv, le_div_iff' (div_pos (log_pos one_lt_two) zero_lt_two),
    id.def, norm_of_nonneg hx₁, real.norm_eq_abs],
  exact hx₂.trans (le_abs_self _),
end

lemma chebyshev_trivial_upper_nat (n : ℕ) :
  ψ n ≤ n * real.log n :=
begin
  rw [chebyshev_second_eq_summatory, summatory_nat, ←nsmul_eq_mul],
  apply (finset.sum_le_card_nsmul _ _ (real.log n) (λ i hi, _)).trans _,
  { apply von_mangoldt_upper.trans,
    simp only [finset.mem_Icc] at hi,
    exact (log_le_log (nat.cast_pos.2 hi.1) (nat.cast_pos.2 (hi.1.trans hi.2))).2
      (nat.cast_le.2 hi.2) },
  simp
end

lemma chebyshev_trivial_upper {x : ℝ} (hx : 1 ≤ x) :
  ψ x ≤ x * log x :=
begin
  have hx₀ : 0 < x := zero_lt_one.trans_le hx,
  rw [chebyshev_second_eq_summatory, summatory_eq_floor, ←chebyshev_second_eq_summatory],
  apply (chebyshev_trivial_upper_nat _).trans _,
  exact mul_le_mul (nat.floor_le hx₀.le)
    ((log_le_log (by rwa [nat.cast_pos, nat.floor_pos]) hx₀).2 (nat.floor_le hx₀.le))
    (log_nonneg (by rwa [nat.one_le_cast, nat.le_floor_iff hx₀.le, nat.cast_one])) hx₀.le,
end

lemma chebyshev_upper_inductive {c : ℝ} (hc : real.log 2 < c) :
  ∃ C, 1 ≤ C ∧ ∀ x : ℕ, ψ x ≤ 2 * c * x + C * log C :=
begin
  have h₁ := (chebyshev_error_O.trans_is_o is_o_log_id_at_top).bound (sub_pos_of_lt hc),
  -- Pull out the constant from h₁. I'd like to use `eventually_at_top` but to make sure the
  -- constant is big, I go via `at_top_basis'` instead.
  obtain ⟨C, hC₁, hC : ∀ x, C ≤ x → _ ≤ _ * ∥x∥⟩ := (at_top_basis' 1).mem_iff.1 h₁,
  refine ⟨C, hC₁, _⟩,
  intro n,
  apply nat.strong_induction_on n, clear n,
  intros n ih,
  cases le_or_lt (n : ℝ) C with hn hn,
  -- Do the case n ≤ C first.
  { rw chebyshev_second_eq_summatory,
    refine (summatory_monotone_of_nonneg _ _ _ hn).trans _,
    { exact λ _, von_mangoldt_nonneg },
    rw ←chebyshev_second_eq_summatory,
    refine (chebyshev_trivial_upper hC₁).trans _,
    refine le_add_of_nonneg_left (mul_nonneg _ (nat.cast_nonneg _)),
    exact mul_nonneg zero_le_two ((log_nonneg one_le_two).trans hc.le) },
  have hn' : 0 < n := nat.succ_le_iff.2 (nat.one_le_cast.1 (hC₁.trans hn.le)),
  have h₁ := chebyshev_upper_aux (nat.cast_pos.2 hn'),
  rw [sub_sub, sub_le_iff_le_add] at h₁,
  apply h₁.trans, clear h₁,
  rw [chebyshev_second_eq_summatory, summatory_eq_floor, ←nat.cast_two, nat.floor_div_eq_div,
    nat.cast_two, ←add_assoc],
  have h₃ := hC _ hn.le,
  rw real.norm_eq_abs at h₃,
  replace h₃ := le_of_abs_le h₃,
  have h₂ := ih (n / 2) (nat.div_lt_self hn' one_lt_two),
  rw ←chebyshev_second_eq_summatory,
  apply (add_le_add_right (add_le_add h₃ h₂) _).trans,
  rw [add_right_comm, ←add_assoc, add_le_add_iff_right, norm_coe_nat, ←add_mul, sub_add_cancel,
    mul_assoc _ c n, two_mul (_ * _), add_le_add_iff_left, mul_assoc, mul_left_comm],
  apply mul_le_mul_of_nonneg_left _ (le_trans (log_nonneg one_le_two) hc.le),
  rw ←le_div_iff' (zero_lt_two : (0 : ℝ) < 2),
  { convert nat.cast_div_le,
    simp },
  apply_instance,
end

lemma chebyshev_upper_real {c : ℝ} (hc : 2 * real.log 2 < c) :
  ∃ C, 1 ≤ C ∧ is_O_with 1 at_top ψ (λ x, c * x + C * log C) :=
begin
  have hc' : real.log 2 < c / 2 := by rwa lt_div_iff' (zero_lt_two : (0 : ℝ) < _),
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_inductive hc',
  refine ⟨C, hC₁, _⟩,
  rw [is_O_with_iff, eventually_at_top],
  refine ⟨0, λ x hx, _⟩,
  rw [norm_of_nonneg (chebyshev_second_nonneg x), chebyshev_second_eq_summatory, summatory_eq_floor,
    ←chebyshev_second_eq_summatory, one_mul],
  refine (hC ⌊x⌋₊).trans (le_trans _ (le_abs_self _)),
  rw [mul_div_cancel' _ (@two_ne_zero ℝ _ _), add_le_add_iff_right],
  refine mul_le_mul_of_nonneg_left (nat.floor_le hx) _,
  exact (mul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) (log_nonneg one_le_two)).trans hc.le,
end

lemma chebyshev_upper_explicit {c : ℝ} (hc : 2 * real.log 2 < c) :
  is_O_with c at_top ψ id :=
begin
  let c' := real.log 2 + c/2,
  have hc'₁ : c' < c,
  { rwa [←lt_sub_iff_add_lt, sub_half, lt_div_iff' (@zero_lt_two ℝ _ _)] },
  have hc'₂ : 2 * real.log 2 < c',
  { rwa [←sub_lt_iff_lt_add', two_mul, add_sub_cancel, lt_div_iff' (@zero_lt_two ℝ _ _)] },
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_real hc'₂,
  refine (hC.trans _ zero_le_one).congr_const (one_mul _),
  apply (is_O_with_const_mul_self c' _ _).add_is_o (is_o_const_of_tendsto_at_top _ _ tendsto_id _),
  rwa [real.norm_eq_abs, abs_of_nonneg],
  exact le_trans (mul_nonneg zero_le_two (log_nonneg one_le_two)) hc'₂.le,
end

lemma chebyshev_upper : is_O at_top ψ id :=
(chebyshev_upper_explicit (lt_add_one _)).is_O

lemma chebyshev_first_upper : is_O at_top ϑ id :=
is_O_chebyshev_first_chebyshev_second.trans chebyshev_upper

lemma is_O_sum_one_of_summable {f : ℕ → ℝ} (hf : summable f) :
  is_O at_top (λ (n : ℕ), ∑ i in finset.range n, f i) (λ _, (1 : ℝ)) :=
is_O_one_of_tendsto _ hf.has_sum.tendsto_sum_nat

lemma log_le_thing {x : ℝ} (hx : 1 ≤ x) :
  log x ≤ x^(1/2 : ℝ) - x^(-1/2 : ℝ) :=
begin
  set f : ℝ → ℝ := log,
  set g : ℝ → ℝ := λ x, x^(1/2 : ℝ) - x^(-1/2 : ℝ),
  set f' : ℝ → ℝ := has_inv.inv,
  set g' : ℝ → ℝ := λ x, 1/2 * x ^ (-3/2 : ℝ) + 1/2 * x^(-1/2 : ℝ),
  suffices : ∀ y ∈ Icc 1 x, f y ≤ g y,
  { exact this x ⟨hx, le_rfl⟩ },
  have f_deriv : ∀ y ∈ Ico 1 x, has_deriv_within_at f (f' y) (Ici y) y,
  { intros y hy,
    exact (has_deriv_at_log (zero_lt_one.trans_le hy.1).ne').has_deriv_within_at },
  have g_deriv : ∀ y ∈ Ico 1 x, has_deriv_within_at g (g' y) (Ici y) y,
  { intros y hy,
    have hy' : 0 < y := zero_lt_one.trans_le hy.1,
    change has_deriv_within_at _ (_ + _) _ _,
    rw [add_comm, ←sub_neg_eq_add, neg_mul_eq_neg_mul],
    refine has_deriv_within_at.sub _ _,
    { convert (has_deriv_within_at_id _ _).rpow_const (or.inl hy'.ne'); norm_num1 },
    { convert (has_deriv_within_at_id _ _).rpow_const (or.inl hy'.ne'); norm_num1 } },
  refine image_le_of_deriv_right_le_deriv_boundary _ f_deriv (by simp [f]) _ g_deriv _,
  { exact continuous_on_log.mono (λ y hy, (zero_lt_one.trans_le hy.1).ne') },
  { exact (continuous_on_id.rpow_const (by simp)).sub
      (continuous_on_id.rpow_const (λ y hy, or.inl (zero_lt_one.trans_le hy.1).ne')) },
  intros y hy,
  dsimp [f', g'],
  rw [←mul_add, mul_comm, ←div_eq_mul_one_div, le_div_iff' (@zero_lt_two ℝ _ _), ←sub_nonneg,
    ←rpow_neg_one],
  convert sq_nonneg (y ^ (- 1 / 4 : ℝ) - y^(- 3 / 4 : ℝ)) using 1,
  have hy' : 0 < y := zero_lt_one.trans_le hy.1,
  rw [sub_sq, ←rpow_nat_cast, ←rpow_nat_cast, nat.cast_two, ←rpow_mul hy'.le, mul_assoc,
    ←rpow_add hy', ←rpow_mul hy'.le],
  norm_num,
  ring,
end

lemma log_div_sq_sub_le {x : ℝ} (hx : 1 < x) :
  log x * ((x⁻¹)^2 / (1 - x⁻¹)) ≤ x^(-3/2 : ℝ) :=
begin
  have hx' : x ≠ 0 := by linarith,
  rw [inv_eq_one_div, one_sub_div hx', div_div_eq_mul_div, one_div, sq, inv_mul_cancel_right₀ hx',
    ←one_div, div_div, ←div_eq_mul_one_div, div_le_iff, ←mul_assoc, ←rpow_add_one hx',
    mul_sub, ←rpow_add_one hx', mul_one],
  { convert log_le_thing hx.le;
    norm_num1 },
  nlinarith,
end

open finset

@[to_additive]
lemma prod_prime_powers' {M : Type*} [comm_monoid M] {x : ℕ} {f : ℕ → M} :
  ∏ n in (finset.Icc 1 x).filter is_prime_pow, f n =
    ∏ p in (finset.Icc 1 x).filter nat.prime,
      ∏ k in (finset.Icc 1 x).filter (λ k, p ^ k ≤ x), f (p ^ k) :=
begin
  rw [finset.prod_sigma', eq_comm],
  refine finset.prod_bij (λ pk _, pk.1 ^ pk.2) _ _ _ _,
  { rintro ⟨p, k⟩ hpk,
    simp only [finset.mem_sigma, finset.mem_filter, finset.mem_Icc] at hpk,
    simp only [finset.mem_filter, finset.mem_Icc, is_prime_pow_nat_iff],
    exact ⟨⟨nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩ },
  { simp only [nat.cast_pow, eq_self_iff_true, implies_true_iff] },
  { rintro ⟨p₁, k₁⟩ ⟨p₂, k₂⟩ h₁ h₂ t,
    simp only [finset.mem_sigma, finset.mem_filter, finset.mem_Icc] at h₁ h₂,
    simp only at t,
    cases eq_of_prime_pow_eq (nat.prime_iff.1 h₁.1.2) (nat.prime_iff.1 h₂.1.2) h₁.2.1.1 t,
    rw (nat.pow_right_strict_mono h₁.1.2.two_le).injective t },
  { simp only [is_prime_pow_nat_iff_bounded, finset.mem_filter, finset.mem_Icc, and_imp,
      exists_and_distrib_left, finset.mem_sigma, exists_prop, sigma.exists, forall_exists_index,
      and_assoc],
    rintro _ hpk₁ hpk₂ p hpn k hkn hp hk rfl,
    exact ⟨p, hp.pos, hpn.trans hpk₂, hp, k, hk, hkn.trans hpk₂, hpk₂, rfl⟩ },
end

@[to_additive]
lemma prod_prime_powers {M : Type*} [comm_monoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n in (finset.Icc 1 ⌊x⌋₊).filter is_prime_pow, f n =
    ∏ p in (finset.Icc 1 ⌊x⌋₊).filter nat.prime,
      ∏ k in (finset.Icc 1 ⌊x⌋₊).filter (λ k, (p ^ k : ℝ) ≤ x), f (p ^ k) :=
begin
  rw prod_prime_powers',
  refine finset.prod_congr rfl _,
  intros p hp,
  refine finset.prod_congr (filter_congr _) (λ _ _, rfl),
  intros k hk,
  rw [nat.le_floor_iff', nat.cast_pow],
  rw mem_filter at hp,
  exact pow_ne_zero _ hp.2.ne_zero,
end

@[to_additive]
lemma exact_prod_prime_powers {M : Type*} [comm_monoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n in (finset.Icc 1 ⌊x⌋₊).filter is_prime_pow, f n =
    ∏ p in (finset.Icc 1 ⌊x⌋₊).filter nat.prime,
      ∏ k in (finset.Icc 1 ⌊log x / real.log p⌋₊), f (p ^ k) :=
begin
  refine prod_prime_powers.trans (finset.prod_congr rfl (λ p hp, finset.prod_congr _ (λ _ _, rfl))),
  rw [mem_filter, finset.mem_Icc, and_assoc] at hp,
  rcases hp with ⟨hp₁, hp₂, hp⟩,
  rw nat.le_floor_iff' hp.ne_zero at hp₂,
  ext k,
  have hx : 0 < x := zero_lt_one.trans_le ((nat.one_le_cast.2 hp₁).trans hp₂),
  rw [mem_filter, finset.mem_Icc, finset.mem_Icc, nat.le_floor_iff hx.le, and_assoc,
    and_congr_right (λ hk, _)],
  rw [nat.le_floor_iff' (nat.succ_le_iff.1 hk).ne', log_div_log, le_logb_iff_rpow_le _ hx,
    rpow_nat_cast, and_iff_right_iff_imp],
  { intros hk',
    apply le_trans _ hk',
    exact_mod_cast (k.lt_pow_self hp.one_lt).le },
  exact_mod_cast hp.one_lt,
end

theorem geom_sum_Ico'_le {α : Type*} [linear_ordered_field α]
  {x : α} (hx₀ : 0 ≤ x) (hx₁ : x < 1) {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i ≤ x ^ m / (1 - x) :=
begin
  rw [geom_sum_Ico' hx₁.ne hmn, div_le_div_right, sub_le_self_iff],
  { apply pow_nonneg hx₀ },
  rwa sub_pos,
end

lemma abs_von_mangoldt_div_self_sub_log_div_self_le {x : ℝ} :
  |∑ n in Icc 1 ⌊x⌋₊, Λ n / n - ∑ p in filter nat.prime (Icc 1 ⌊x⌋₊), real.log p / p| ≤
    ∑ n in Icc 1 ⌊x⌋₊, n ^ (- 3 / 2 : ℝ) :=
begin
  have h₁ : ∑ n in Icc 1 ⌊x⌋₊, Λ n / n = ∑ n in filter is_prime_pow (Icc 1 ⌊x⌋₊), Λ n / n,
  { simp only [sum_filter_of_ne, div_ne_zero_iff, von_mangoldt_ne_zero_iff, implies_true_iff]
    { contextual := tt } },
  have h₂ : ∑ p in filter nat.prime (Icc 1 ⌊x⌋₊), real.log p / p =
          ∑ p in filter nat.prime (Icc 1 ⌊x⌋₊), Λ p / p,
  { refine sum_congr rfl (λ p hp, _),
    rw von_mangoldt_apply_prime (mem_filter.1 hp).2 },
  rw [h₁, h₂, sum_prime_powers, ←sum_sub_distrib, sum_filter],
  apply (abs_sum_le_sum_abs _ _).trans _,
  apply sum_le_sum,
  simp only [finset.mem_Icc, nat.cast_pow, and_imp],
  intros p hp₁ hp₂,
  split_ifs,
  { have hp₃ := (nat.le_floor_iff' h.ne_zero).1 hp₂,
    have : insert 1 (filter (λ k, (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊)) =
            filter (λ k, (p ^ k : ℝ) ≤ x) (Icc 1 ⌊x⌋₊),
    { rwa [nat.Icc_succ_left 1, ←finset.Ioc_insert_left (hp₁.trans hp₂), filter_insert, pow_one,
        if_pos] },
    have h1 : 1 ∉ filter (λ (k : ℕ), (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊),
    { simp [not_and_distrib] },
    rw [←this, sum_insert h1, add_comm, pow_one, pow_one, add_sub_cancel],
    apply (abs_sum_le_sum_abs _ _).trans _,
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) _).trans _,
    { simp only [abs_nonneg, implies_true_iff] },
    have : (∑ i in Icc 2 ⌊x⌋₊, |Λ (p ^ i) / p ^ i|) = ∑ i in Icc 2 ⌊x⌋₊, Λ p / p ^ i,
    { refine finset.sum_congr rfl (λ k hk, _),
      rw [von_mangoldt_apply_pow (zero_lt_two.trans_le (finset.mem_Icc.1 hk).1).ne', abs_div,
        abs_of_nonneg von_mangoldt_nonneg, abs_pow, nat.abs_cast] },
    rw [this, von_mangoldt_apply_prime h],
    simp only [div_eq_mul_inv (log (p : ℝ)), ←mul_sum, ←inv_pow],
    apply le_trans _ (log_div_sq_sub_le (nat.one_lt_cast.2 h.one_lt)),
    rw [←nat.Ico_succ_right],
    refine mul_le_mul_of_nonneg_left (geom_sum_Ico'_le _ _ _) _;
    simp only [inv_nonneg, nat.succ_le_succ_iff, log_nonneg, hp₁.trans hp₂, nat.cast_nonneg,
      inv_lt_one, h.one_lt, nat.one_lt_cast, nat.one_le_cast, hp₁] },
  rw abs_zero,
  exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _,
end

lemma is_O_von_mangoldt_div_self_sub_log_div_self :
  is_O at_top
    (λ x, ∑ n in Icc 1 ⌊x⌋₊, Λ n * n⁻¹ - ∑ p in filter nat.prime (Icc 1 ⌊x⌋₊), real.log p * p⁻¹)
    (λ _ : ℝ, (1 : ℝ)) :=
begin
  have : ∀ x : ℝ,
    ∥∑ n in Icc 1 ⌊x⌋₊, Λ n / n - ∑ p in filter nat.prime (Icc 1 ⌊x⌋₊), real.log p / p∥
      ≤ ∥(∑ n in range (⌊x⌋₊ + 1), n ^ (- 3 / 2 : ℝ) : ℝ)∥,
  { intro x,
    rw [real.norm_eq_abs, real.norm_eq_abs],
    apply abs_von_mangoldt_div_self_sub_log_div_self_le.trans (le_trans _ (le_abs_self _)),
    rw [range_eq_Ico, nat.Ico_succ_right],
    exact sum_mono_set_of_nonneg (by simp [rpow_nonneg_of_nonneg])
      (Icc_subset_Icc_left zero_le_one) },
  refine (is_O_of_le at_top this).trans _,
  have : (-3/2 : ℝ) < -1 := by norm_num1,
  have z : tendsto (λ x : ℝ, finset.range (⌊x⌋₊ + 1)) at_top at_top :=
    tendsto_finset_range.comp (tendsto_at_top_add_nonneg_right tendsto_nat_floor_at_top (by simp)),
  exact (is_O_one_of_tendsto _ ((real.summable_nat_rpow.2 this).has_sum.comp z)),
end

lemma summatory_log_sub :
  is_O at_top (λ x, (∑ n in Icc 1 ⌊x⌋₊, log (n : ℝ)) - x * ∑ n in Icc 1 ⌊x⌋₊, Λ n * n⁻¹) (λ x, x) :=
begin
  have : ∀ (x : ℝ), 0 ≤ x →
    |(∑ n in Icc 1 ⌊x⌋₊, log (n : ℝ)) - x * ∑ n in Icc 1 ⌊x⌋₊, Λ n / n| ≤
      ∑ (n : ℕ) in Icc 1 ⌊x⌋₊, Λ n,
  { intros x hx,
    rw [←summatory, ←von_mangoldt_summatory hx le_rfl, mul_sum, summatory, ←sum_sub_distrib],
    refine (abs_sum_le_sum_abs _ _).trans _,
    simp only [mul_div_left_comm x, abs_sub_comm, ←mul_sub, abs_mul, von_mangoldt_nonneg,
      abs_of_nonneg, int.self_sub_floor, int.fract_nonneg],
    refine finset.sum_le_sum (λ n hn, _),
    exact mul_le_of_le_one_right von_mangoldt_nonneg (int.fract_lt_one _).le },
  apply is_O.trans _ chebyshev_upper,
  apply is_O.of_bound 1,
  filter_upwards [eventually_ge_at_top (0 : ℝ)] with x hx,
  rw [one_mul, norm_eq_abs, chebyshev_second_eq_summatory,
    norm_of_nonneg (summatory_nonneg _ _ _ _)],
  { exact this _ hx },
  { exact λ _, von_mangoldt_nonneg }
end

lemma is_O_von_mangoldt_div_self :
  is_O at_top (λ x : ℝ, ∑ n in Icc 1 ⌊x⌋₊, Λ n * n⁻¹ - log x) (λ _, (1 : ℝ)) :=
begin
  suffices : is_O at_top (λ x : ℝ, x * ∑ n in Icc 1 ⌊x⌋₊, Λ n * n⁻¹ - x * log x) (λ x, x),
  { refine ((is_O_refl (λ (x : ℝ), x⁻¹) _).mul this).congr' _ _,
    { filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx,
      rw [←mul_sub, inv_mul_cancel_left₀ hx.ne'] },
    { filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx,
      rw inv_mul_cancel hx.ne' } },
  refine summatory_log_sub.symm.triangle _,
  have h₁ := (summatory_log (lt_add_one _)).is_O,
  apply ((h₁.trans is_o_log_id_at_top.is_O).sub (is_O_refl _ _)).congr_left _,
  intro x,
  dsimp only [summatory, id.def],
  ring
end

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ k ≤ p ≤ x, a(p) where `p` is prime.
-/
def prime_summatory {M : Type*} [add_comm_monoid M] (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n in (finset.Icc k ⌊x⌋₊).filter nat.prime, a n
-- BM: equivalently could say it's `summatory (λ n, if (a n).prime then a n else 0) x`

lemma prime_summatory_eq_summatory :
  prime_summatory a = summatory (λ n, if n.prime then a n else 0) :=
begin
  ext k x,
  exact finset.sum_filter _ _,
end

lemma prime_summatory_one_eq_prime_summatory_two {M : Type*} [add_comm_monoid M] (a : ℕ → M) :
  prime_summatory a 1 = prime_summatory a 2 :=
begin
  ext x,
  rw [prime_summatory, prime_summatory],
  refine (sum_subset_zero_on_sdiff (filter_subset_filter _ (finset.Icc_subset_Icc_left one_le_two))
    (λ y hy, _) (λ _ _, rfl)).symm,
  simp only [mem_sdiff, mem_filter, finset.mem_Icc, and_imp, not_and', not_le,
    nat.lt_add_one_iff] at hy {contextual := tt},
  cases hy.1.2.ne_one ((hy.2 hy.1.2 hy.1.1.2).antisymm hy.1.1.1),
end

lemma log_reciprocal :
  is_O at_top (λ x, prime_summatory (λ p, real.log p / p) 1 x - log x) (λ _, (1 : ℝ)) :=
is_O_von_mangoldt_div_self_sub_log_div_self.symm.triangle is_O_von_mangoldt_div_self

open_locale nat

lemma prime_counting_le_self (x : ℕ) : π x ≤ x :=
begin
  rw [nat.prime_counting, nat.prime_counting', nat.count_eq_card_filter_range],
  have : (finset.range (x + 1)).filter nat.prime ⊆ finset.Ioc 0 x,
  { simp [finset.subset_iff, nat.lt_add_one_iff, nat.prime.pos] {contextual := tt} },
  exact (card_le_of_subset this).trans (by simp),
end

lemma chebyshev_first_eq_prime_summatory :
  ϑ = prime_summatory (λ n, real.log n) 1 :=
begin
  ext x,
  rw [chebyshev_first, prime_summatory, eq_comm, finset.sum_subset_zero_on_sdiff],
  { exact filter_subset_filter _ finset.Icc_subset_range_add_one },
  { simp [nat.lt_add_one_iff, imp_false, le_zero_iff] {contextual := tt} },
  { intros, refl }
end

@[simp] lemma prime_counting'_zero : π' 0 = 0 := rfl
@[simp] lemma prime_counting'_one : π' 1 = 0 := rfl
@[simp] lemma prime_counting'_two : π' 2 = 0 := rfl
@[simp] lemma prime_counting_zero : π 0 = 0 := rfl
@[simp] lemma prime_counting_one : π 1 = 0 := rfl

local attribute [pp_nodot] nat.prime_counting

lemma chebyshev_first_trivial_bound (x : ℝ) :
  ϑ x ≤ π ⌊x⌋₊ * log x :=
begin
  rcases le_or_lt x 0 with hx | hx,
  { rw [chebyshev_first, nat.floor_eq_zero.2 (hx.trans_lt zero_lt_one)],
    simp [filter_singleton, nat.not_prime_zero] },
  rw [nat.prime_counting, nat.prime_counting', nat.count_eq_card_filter_range, ←nsmul_eq_mul],
  refine sum_le_card_nsmul _ _ (log x) _,
  intros y hy,
  simp only [mem_filter, finset.mem_range, nat.lt_add_one_iff] at hy,
  rw [log_le_log _ hx, ←nat.le_floor_iff'],
  { exact hy.1 },
  { exact hy.2.ne_zero },
  { rw nat.cast_pos,
    exact hy.2.pos },
end

lemma prime_counting_eq_card_primes {x : ℕ} :
  π x = ((finset.Icc 1 x).filter nat.prime).card :=
begin
  rw [nat.prime_counting, nat.prime_counting', nat.count_eq_card_filter_range, range_eq_Ico,
    nat.Ico_succ_right],
  congr' 1,
  simp [finset.ext_iff, nat.one_le_iff_ne_zero, nat.prime.ne_zero] {contextual := tt},
end

lemma prime_counting_eq_prime_summatory {x : ℕ} :
  π x = prime_summatory (λ _, 1) 1 x :=
by rw [prime_summatory_eq_summatory, summatory, nat.floor_coe, sum_boole, nat.cast_id,
  prime_counting_eq_card_primes]

lemma prime_counting_eq_prime_summatory' {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) = prime_summatory (λ _, (1 : ℝ)) 1 x :=
begin
  rw [prime_counting_eq_prime_summatory],
  simp only [nat.cast_one, nat.cast_sum, nat.floor_coe, prime_summatory],
end

lemma chebyshev_first_sub_prime_counting_mul_log_eq {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) * log x - ϑ x = ∫ t in Icc 1 x, π ⌊t⌋₊ * t⁻¹ :=
begin
  have : (λ (n : ℕ), ite (nat.prime n) (real.log n : ℝ) 0) =
    (λ n : ℕ, ite (nat.prime n) 1 0 * real.log n),
  { ext n,
    rw boole_mul },
  simp only [chebyshev_first_eq_prime_summatory, prime_summatory_eq_summatory,
    prime_counting_eq_prime_summatory'],
  rw [sub_eq_iff_eq_add, ←sub_eq_iff_eq_add', this,
    partial_summation_cont' (λ n, _) real.log (λ y, y⁻¹) one_ne_zero, nat.cast_one],
  { simp only [nat.cast_one, set.mem_Ici],
    intros y hy,
    apply has_deriv_at_log,
    linarith },
  { simp only [nat.cast_one],
    refine continuous_on_inv₀.mono (λ y hy, _),
    simp only [mem_compl_eq, mem_singleton_iff, set.mem_Ici] at hy ⊢,
    rintro rfl,
    linarith }
end

lemma is_O_chebyshev_first_sub_prime_counting_mul_log :
  is_O at_top (λ x, (π ⌊x⌋₊ : ℝ) * real.log x - ϑ x) id :=
begin
  simp only [chebyshev_first_sub_prime_counting_mul_log_eq],
  apply is_O.of_bound 1,
  filter_upwards [eventually_gt_at_top (1 : ℝ)],
  intros x hx,
  rw [id.def, one_mul],
  have b₁ : ∀ (y : ℝ), 1 ≤ y → 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹ :=
    λ y hy, mul_nonneg (nat.cast_nonneg _) (inv_nonneg.2 (by linarith)),
  have b₃ : (λ (a : ℝ), (π ⌊a⌋₊ : ℝ) * a⁻¹) ≤ᵐ[volume.restrict (Icc 1 x)] (λ x, 1),
  { simp only [eventually_le, ae_restrict_iff', measurable_set_Icc],
    apply eventually_of_forall,
    rintro y ⟨hy₁, hy₂⟩,
    rw [←div_eq_mul_inv, div_le_one (zero_lt_one.trans_le hy₁)],
    exact le_trans (nat.cast_le.2 (prime_counting_le_self _)) (nat.floor_le (by linarith)) },
  rw [norm_of_nonneg (zero_le_one.trans hx.le),
    norm_of_nonneg (set_integral_nonneg measurable_set_Icc (λ _ y, b₁ _ y.1))],
  refine (integral_mono_of_nonneg _ _ b₃).trans _,
  { simp only [eventually_le, ae_restrict_iff', measurable_set_Icc, pi.zero_apply, set.mem_Icc,
      and_imp],
    refine eventually_of_forall (λ y hy₁ hy₂, _),
    exact mul_nonneg (nat.cast_nonneg _) (inv_nonneg.2 (zero_le_one.trans hy₁)) },
  { simp [integrable_const_iff] },
  { simp [hx.le] },
end

lemma is_O_prime_counting_div_log :
  is_O at_top (λ x, (π ⌊x⌋₊ : ℝ)) (λ x, x / log x) :=
begin
  have : is_O at_top (λ x, (π ⌊x⌋₊ : ℝ) * real.log x) id,
  { apply (is_O_chebyshev_first_sub_prime_counting_mul_log.add chebyshev_first_upper).congr_left _,
    simp },
  refine (is_O.mul this (is_O_refl (λ x, (real.log x)⁻¹) _)).congr' _ _,
  { filter_upwards [eventually_gt_at_top (1 : ℝ)] with x hx,
    rw mul_inv_cancel_right₀ (log_pos hx).ne' },
  filter_upwards with x using by simp [div_eq_mul_inv],
end

lemma log_lt_self {x : ℝ} (hx : 0 < x) : log x < x :=
(log_le_sub_one_of_pos hx).trans_lt (by simp)

lemma prime_counting_le_const_mul_div_log :
  ∃ c, 0 < c ∧ ∀ x : ℝ, (π ⌊x⌋₊ : ℝ) ≤ c * ∥x / real.log x∥ :=
begin
  obtain ⟨c₀, hc₀', hc₀⟩ := is_O_prime_counting_div_log.exists_pos,
  rw [is_O_with_iff, eventually_at_top] at hc₀,
  obtain ⟨c₁, hc₁⟩ := hc₀,
  refine ⟨max c₀ c₁, lt_max_of_lt_left hc₀', λ x, _⟩,
  simp only [ge_iff_le, norm_coe_nat] at hc₁,
  cases le_total c₁ x with h₀ h₀,
  { exact (hc₁ _ h₀).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) },
  rcases lt_trichotomy x 1 with h₁ | rfl | h₁,
  { rw [nat.floor_eq_zero.2 h₁, prime_counting_zero, nat.cast_zero],
    exact mul_nonneg (le_max_of_le_left hc₀'.le) (norm_nonneg _) },
  { simp },
  refine (nat.cast_le.2 (prime_counting_le_self ⌊x⌋₊)).trans _,
  refine (((nat.floor_le (zero_le_one.trans h₁.le)).trans h₀).trans (le_max_right c₀ _)).trans _,
  rw [le_mul_iff_one_le_right (lt_max_of_lt_left hc₀'), norm_div, norm_of_nonneg (log_nonneg h₁.le),
    norm_of_nonneg (zero_le_one.trans h₁.le), one_le_div (log_pos h₁)],
  exact (log_le_sub_one_of_pos (zero_le_one.trans_lt h₁)).trans (by simp),
end

lemma chebyshev_second_eq_sum_chebyshev_first {x : ℝ} (hx : 0 ≤ x) :
  ψ x = ∑ k in Icc 1 ⌊logb 2 x⌋₊, ϑ (x ^ (1 / k : ℝ)) :=
begin
  rcases eq_or_lt_of_le hx with rfl | hx,
  { simp },
  simp only [chebyshev_first_eq],
  rw [sum_sigma', chebyshev_second, eq_comm],
  refine sum_bij_ne_zero (λ pk _ _, pk.2 ^ pk.1) _ _ _ _,
  { rintro ⟨k, p⟩,
    simp only [mem_sigma, finset.mem_Icc, mem_filter, finset.mem_range, ne.def, and_imp,
      nat.lt_add_one_iff],
    rintro hk₁ hk₂ hp' hp -,
    apply nat.le_floor,
    rw nat.le_floor_iff' hp.ne_zero at hp',
    rw [nat.cast_pow, ←rpow_nat_cast],
    refine (rpow_le_rpow (nat.cast_nonneg _) hp' (nat.cast_nonneg _)).trans _,
    rw [←rpow_mul hx.le, one_div, inv_mul_cancel, rpow_one],
    { rw [nat.cast_ne_zero],
      exact ne_of_gt hk₁ } },
  { rintro ⟨k₁, p₁⟩ ⟨k₂, p₂⟩,
    simp only [one_div, mem_sigma, finset.mem_Icc, mem_filter, finset.mem_range, ne.def, heq_iff_eq,
      and_imp, nat.lt_add_one_iff],
    rintro hk₁ hk₁' hp₁' hp₁ - hk₂ hk₂' hp₂' hp₂ - t,
    cases eq_of_prime_pow_eq (nat.prime_iff.1 hp₁) (nat.prime_iff.1 hp₂) hk₁ t,
    rw (nat.pow_right_strict_mono hp₁.two_le).injective t,
    exact ⟨rfl, rfl⟩ },
  { intro n,
    simp only [nat.lt_add_one_iff, finset.mem_range, mem_sigma, finset.mem_Icc, mem_filter,
      one_div, exists_prop, sigma.exists, @von_mangoldt_ne_zero_iff n,
      is_prime_pow_nat_iff_bounded n, forall_exists_index, and_imp],
    rintro _ p hp₁ k hk₁ hp₂ hk₂ rfl,
    rw [nat.le_floor_iff' (pow_ne_zero _ hp₂.ne_zero), nat.cast_pow] at H,
    refine ⟨_, _, ⟨⟨hk₂, _⟩, _, hp₂⟩, _, rfl⟩,
    { have : 2 ^ k ≤ x,
      { refine le_trans (pow_le_pow_of_le_left zero_le_two _ _) H,
        exact_mod_cast hp₂.two_le },
      rwa [nat.le_floor_iff' hk₂.ne', le_logb_iff_rpow_le one_lt_two hx, rpow_nat_cast] },
    { rw nat.le_floor_iff' hp₂.ne_zero,
      refine le_trans _ (rpow_le_rpow (pow_nonneg (nat.cast_nonneg _) _) H
        (inv_nonneg.2 (nat.cast_nonneg _))),
      rw [←rpow_nat_cast, ←rpow_mul (nat.cast_nonneg _), mul_inv_cancel, rpow_one],
      rw nat.cast_ne_zero,
      apply hk₂.ne' },
    rw von_mangoldt_ne_zero_iff,
    apply prime.is_prime_pow,
    rwa ←nat.prime_iff },
  { simp only [one_div, mem_sigma, finset.mem_Icc, mem_filter, finset.mem_range, ne.def, and_imp,
      sigma.forall],
    rintro k p hk - - - -,
    rw von_mangoldt_apply_pow,
    rwa ←pos_iff_ne_zero },
end

lemma finset.Icc_succ_left {a b : ℕ} : finset.Icc a.succ b = Ioc a b :=
begin
  ext n,
  simp [nat.succ_le_iff],
end

lemma finset.Icc_eq_insert_Icc_succ {a b : ℕ} (h : a ≤ b) : finset.Icc a b = insert a (Icc (a+1) b) :=
by rw [finset.Icc_succ_left, finset.Ioc_insert_left h]

-- Note this inequality can be improved, eg to
-- ψ - ϑ << x ^ (1/2) * (log x)
-- but this is good enough for me!
lemma chebyshev_second_sub_chebyshev_first_eq {x : ℝ} (hx : 2 ≤ x) :
  ψ x - ϑ x ≤ x ^ (1 / 2 : ℝ) * (log x)^2 :=
begin
  have h₁ : ∑ n in Icc 1 ⌊x⌋₊, Λ n = ∑ n in filter is_prime_pow (Icc 1 ⌊x⌋₊), Λ n,
  { simp only [sum_filter_of_ne, div_ne_zero_iff, von_mangoldt_ne_zero_iff, implies_true_iff]
    { contextual := tt } },
  rw chebyshev_second_eq_sum_chebyshev_first (zero_le_two.trans hx),
  rw finset.Icc_eq_insert_Icc_succ,
  { rw [sum_insert, nat.cast_one, div_one, rpow_one, add_tsub_cancel_left],
    refine (sum_le_card_nsmul _ _ (1/2 * x^(1 / 2 : ℝ) * log x) _).trans _,
    { intros k hk,
      simp only [finset.mem_Icc] at hk,
      have : x ^ (1 / k : ℝ) ≤ x ^ (1 / 2 : ℝ),
      { apply rpow_le_rpow_of_exponent_le (one_le_two.trans hx),
        refine one_div_le_one_div_of_le zero_lt_two _,
        exact_mod_cast hk.1 },
      apply (chebyshev_first_monotone this).trans _,
      refine (chebyshev_first_le_chebyshev_second (x ^ (1 / 2 : ℝ))).trans _,
      apply (chebyshev_trivial_upper _).trans,
      { rw [log_rpow (zero_lt_two.trans_le hx), mul_left_comm, mul_assoc] },
      exact one_le_rpow (one_le_two.trans hx) (by norm_num) },
    { rw [nat.card_Icc, nat.succ_sub_succ_eq_sub, nsmul_eq_mul],
      suffices : ((⌊logb 2 x⌋₊ - 1 : ℕ) : ℝ) ≤ log x / real.log 2,
      { apply (mul_le_mul_of_nonneg_right this (mul_nonneg _ (log_nonneg _))).trans,
        { rw [mul_comm, mul_assoc, mul_div_assoc', mul_assoc, ←sq, mul_div_assoc', mul_div_assoc',
            mul_comm, mul_div_assoc],
          refine mul_le_of_le_one_right (mul_nonneg (rpow_nonneg_of_nonneg _ _) (sq_nonneg _)) _,
          { exact zero_le_two.trans hx },
          apply div_le_one_of_le;
          linarith [log_two_gt_d9] },
        { exact mul_nonneg (by norm_num1) (rpow_nonneg_of_nonneg (zero_le_two.trans hx) _) },
        { apply one_le_two.trans hx } },
      transitivity' ⌊logb 2 x⌋₊,
      { rw nat.cast_le,
        exact nat.sub_le _ 1 },
      exact (nat.floor_le (logb_nonneg one_lt_two (one_le_two.trans hx))).trans le_rfl },
    simp },
  apply nat.le_floor,
  rwa [nat.cast_one, logb, one_le_div (log_pos one_lt_two), log_le_log zero_lt_two],
  linarith
end

@[simp] lemma nat.floor_two {R : Type*} [linear_ordered_semiring R] [floor_semiring R] :
  ⌊(2 : R)⌋₊ = 2 :=
by rw [←nat.cast_two, nat.floor_coe]

lemma chebyshev_first_two : ϑ 2 = real.log 2 :=
begin
  rw [chebyshev_first, nat.floor_two],
  simp_rw [range_succ, filter_insert, if_neg nat.not_prime_zero, if_neg nat.not_prime_one,
    if_pos nat.prime_two, range_zero, filter_empty, insert_emptyc_eq, sum_singleton, nat.cast_two],
end

lemma chebyshev_first_trivial_lower : ∀ x, 2 ≤ x → 0.5 ≤ ϑ x :=
begin
  intros x hx,
  apply (chebyshev_first_monotone hx).trans',
  rw chebyshev_first_two,
  exact log_two_gt_d9.le.trans' (by norm_num),
end

lemma chebyshev_first_pos : ∀ x, 2 ≤ x → 0 < ϑ x :=
λ x hx, lt_of_lt_of_le (by norm_num) (chebyshev_first_trivial_lower x hx)

lemma chebyshev_first_lower : is_O at_top id ϑ :=
begin
  have : is_O at_top (ψ - ϑ) (λ x, x ^ (1 / 2 : ℝ) * (log x)^2),
  { apply is_O.of_bound 1,
    filter_upwards [eventually_ge_at_top (2 : ℝ)],
    intros x hx,
    rw [pi.sub_apply, one_mul, norm_eq_abs, norm_eq_abs, abs_mul, abs_pow, pow_bit0_abs,
      abs_of_nonneg (sub_nonneg_of_le (chebyshev_first_le_chebyshev_second x)),
      abs_of_nonneg (rpow_nonneg_of_nonneg (zero_le_two.trans hx) _)],
    apply chebyshev_second_sub_chebyshev_first_eq hx },
  have : is_o at_top (ψ - ϑ) id,
  { refine this.trans_is_o _,
    have t := (is_o_log_rpow_at_top (show (0 : ℝ) < 1 / 4, by norm_num1)).pow zero_lt_two,
    refine (is_O.mul_is_o _ t).congr' eventually_eq.rfl _,
    { exact (λ x, x ^ (1 / 2 : ℝ)) },
    { exact is_O_refl _ _ },
    { filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx,
      rw [←rpow_nat_cast, ←rpow_mul hx.le, ←rpow_add hx],
      norm_num } },
  have := this.symm.trans_is_O chebyshev_lower,
  apply (chebyshev_lower.trans (is_o.right_is_O_add this)).congr_right _,
  simp
end

lemma chebyshev_first_all : ∃ c, 0 < c ∧ ∀ x, 2 ≤ x → c * ∥x∥ ≤ ∥ϑ x∥ :=
begin
  obtain ⟨c₀, hc₀, h⟩ := chebyshev_first_lower.exists_pos,
  obtain ⟨X, hX⟩ := eventually_at_top.1 h.bound,
  let c := max c₀ (2 * X),
  have hc : 0 < c := lt_max_of_lt_left hc₀,
  refine ⟨c⁻¹, inv_pos.2 hc, λ x hx, _⟩,
  rw [inv_mul_le_iff hc],
  cases le_total X x with hx' hx',
  { exact (hX _ hx').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) },
  rw [norm_of_nonneg (chebyshev_first_nonneg _), norm_of_nonneg (zero_le_two.trans hx)],
  refine hx'.trans (eq.trans_le _ (mul_le_mul (le_max_right _ _)
    (chebyshev_first_trivial_lower _ hx) (by norm_num) hc.le)),
  ring
end

lemma is_O_div_log_prime_counting :
  is_O at_top (λ x, x / log x) (λ x, (π ⌊x⌋₊ : ℝ)) :=
begin
  have : is_O at_top ϑ (λ x, (π ⌊x⌋₊ : ℝ) * real.log x),
  { apply is_O_of_le _ _,
    intro x,
    rw [norm_of_nonneg (chebyshev_first_nonneg x), norm_eq_abs],
    exact (chebyshev_first_trivial_bound _).trans (le_abs_self _) },
  apply ((chebyshev_first_lower.trans this).mul (is_O_refl (λ x, (log x)⁻¹) _)).congr' _ _,
  { apply eventually_of_forall,
    intro x,
    simp only [id.def, div_eq_mul_inv] },
  { filter_upwards [eventually_gt_at_top (1 : ℝ)] with x hx,
    rw mul_inv_cancel_right₀ (log_pos hx).ne' }
end

-- lemma prime_counting_asymptotic :
--   is_O (λ x, prime_summatory (λ _, (1 : ℝ)) 1 x - ψ x / log x)
--     (λ x, x / (log x)^2) at_top :=
-- sorry

def prime_log_div_sum_error (x : ℝ) : ℝ := prime_summatory (λ p, real.log p * p⁻¹) 1 x - log x

lemma prime_summatory_log_mul_inv_eq :
  prime_summatory (λ p, real.log p * p⁻¹) 2 = log + prime_log_div_sum_error :=
begin
  ext x,
  rw [pi.add_apply, prime_log_div_sum_error, add_sub_cancel'_right,
    prime_summatory_one_eq_prime_summatory_two]
end

lemma is_O_prime_log_div_sum_error : is_O at_top prime_log_div_sum_error (λ _, (1 : ℝ)) :=
log_reciprocal

@[measurability] lemma measurable_prime_log_div_sum_error :
  measurable prime_log_div_sum_error :=
begin
  change measurable (λ x, _),
  simp only [prime_summatory_one_eq_prime_summatory_two, prime_summatory_eq_summatory],
  measurability
end

def prime_reciprocal_integral : ℝ :=
  ∫ x in Ioi 2, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹.

lemma my_func_continuous_on : continuous_on (λ x, (x * log x ^ 2)⁻¹) (Ioi 1) :=
begin
  refine (continuous_on_id.mul ((continuous_on_log.mono _).pow _)).inv₀ _,
  { simp [imp_not_comm, set.subset_def] },
  rintro x (hx : _ < _),
  exact mul_ne_zero (show x ≠ 0, by linarith) (pow_ne_zero _ (log_pos hx).ne'),
end

lemma integral_inv_self_mul_log_sq {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log b)⁻¹ :=
begin
  have : (∀ y ∈ interval a b, has_deriv_at (λ x, - (log x)⁻¹) (y * log y ^ 2)⁻¹ y),
  { intros y hy,
    have : (y * log y ^ 2)⁻¹ = - ((- y⁻¹) / (log y) ^ 2),
    { rw [neg_div, neg_neg, div_eq_mul_inv, mul_inv] },
    rw this,
    have : 1 < y := (lt_min_iff.2 ⟨ha, hb⟩).trans_le hy.1,
    exact ((has_deriv_at_log (by linarith)).inv (log_pos this).ne').neg },
  rw [interval_integral.integral_eq_sub_of_has_deriv_at this, neg_sub_neg],
  apply continuous_on.interval_integrable,
  apply my_func_continuous_on.mono,
  intros y hy,
  exact (lt_min_iff.2 ⟨ha, hb⟩).trans_le hy.1,
end

lemma integral_Ioi_my_func_tendsto_aux {a : ℝ} (ha : 1 < a)
  {ι : Type*} {b : ι → ℝ} {l : filter ι} (hb : tendsto b l at_top) :
  tendsto (λ i, ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 (log a)⁻¹) :=
begin
  suffices :
    tendsto (λ i, ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (nhds ((log a)⁻¹ - 0)),
  { simpa using this },
  have : ∀ᶠ i in l, ∫ x in a..b i, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log (b i))⁻¹,
  { filter_upwards [hb.eventually (eventually_ge_at_top a)],
    intros i hi,
    rw integral_inv_self_mul_log_sq ha (ha.trans_le hi) },
  rw tendsto_congr' this,
  exact (tendsto_inv_at_top_zero.comp (tendsto_log_at_top.comp hb)).const_sub _,
end

-- TODO: Move to mathlib
lemma integrable_on_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  integrable_on (λ x, (x * log x ^ 2)⁻¹) (Ioi a) :=
begin
  have hb : tendsto (λ (x : ℝ≥0), a + x) at_top at_top :=
    tendsto_at_top_add_const_left _ _ (nnreal.tendsto_coe_at_top.2 tendsto_id),
  refine integrable_on_Ioi_of_interval_integral_norm_tendsto (log a)⁻¹ a _ hb _,
  { intros i,
    refine (continuous_on.integrable_on_Icc _).mono_set set.Ioc_subset_Icc_self,
    apply my_func_continuous_on.mono,
    rintro y ⟨hy, -⟩,
    exact ha.trans_le hy },
  apply (integral_Ioi_my_func_tendsto_aux ha hb).congr (λ x, _),
  refine interval_integral.integral_congr (λ i hi, _),
  apply (real.norm_of_nonneg _).symm,
  refine inv_nonneg.2 (mul_nonneg _ (sq_nonneg _)),
  refine le_trans _ hi.1,
  exact le_min (by linarith) (add_nonneg (by linarith) x.2),
end

-- TODO: Move to mathlib
lemma integral_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  ∫ x in Ioi a, (x * log x ^ 2)⁻¹ = (log a)⁻¹ :=
tendsto_nhds_unique
  (interval_integral_tendsto_integral_Ioi _ (integrable_on_my_func_Ioi ha) tendsto_id)
  (integral_Ioi_my_func_tendsto_aux ha tendsto_id)

lemma my_func2_continuous_on : continuous_on (λ x, (x * log x)⁻¹) (Ioi 1) :=
begin
  refine (continuous_on_id.mul (continuous_on_log.mono _)).inv₀ _,
  { simp [imp_not_comm, set.subset_def] },
  rintro x (hx : _ < _),
  exact mul_ne_zero (show x ≠ 0, by linarith) (log_pos hx).ne',
end

lemma integral_inv_self_mul_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x)⁻¹ = log (log b) - log (log a) :=
begin
  have : (∀ y ∈ interval a b, has_deriv_at (λ x, log (log x)) (y * log y)⁻¹ y),
  { intros y hy,
    rw [mul_inv, ←div_eq_mul_inv],
    have : 1 < y := (lt_min_iff.2 ⟨ha, hb⟩).trans_le hy.1,
    exact (has_deriv_at_log (by linarith)).log (log_pos this).ne' },
  rw [interval_integral.integral_eq_sub_of_has_deriv_at this],
  apply continuous_on.interval_integrable,
  apply my_func2_continuous_on.mono,
  intros y hy,
  exact (lt_min_iff.2 ⟨ha, hb⟩).trans_le hy.1,
end

lemma integrable_on_prime_log_div_sum_error :
  integrable_on (λ x, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹) (Ici 2) :=
begin
  obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound,
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → _ ≤ c * ∥(1 : ℝ)∥⟩ := (at_top_basis' 2).mem_iff.1 hc,
  have : set.Ici 2 = set.Ico 2 k ∪ set.Ici k,
  { rw Ico_union_Ici_eq_Ici hk₂ },
  rw this,
  have hlog : continuous_on log (Icc 2 k),
  { apply continuous_on_log.mono _,
    rintro y ⟨hy, -⟩ (rfl : y = 0),
    norm_num at hy },
  have hlog' : continuous_on (λ (i : ℝ), (i * log i ^ 2)⁻¹) (Icc 2 k),
  { apply continuous_on.inv₀,
    { exact continuous_on_id.mul (continuous_on.pow hlog 2) },
    rintro y ⟨hy, -⟩,
    exact mul_ne_zero (by linarith) (pow_ne_zero _ (log_pos (by linarith)).ne') },
  apply integrable_on.union,
  { refine integrable_on.congr_set_ae _ Ico_ae_eq_Icc,
    simp only [prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two,
      prime_summatory_eq_summatory, sub_mul],
    apply integrable.sub,
    { exact partial_summation_integrable _ (continuous_on.integrable_on_Icc hlog') },
    refine continuous_on.integrable_on_Icc _,
    exact hlog.mul hlog' },
  have : ∀ᵐ (x : ℝ) ∂volume.restrict (Ici k),
    ∥prime_log_div_sum_error x * (x * log x ^ 2)⁻¹∥ ≤ ∥c * (x * log x ^ 2)⁻¹∥,
  { rw ae_restrict_iff' (@measurable_set_Ici ℝ _ _ _ _ _ _),
    filter_upwards with x hx,
    rw [norm_mul, norm_mul],
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
    apply le_trans (hk _ hx) _,
    simp [norm_eq_abs, le_abs_self] },
  refine integrable.mono _ (measurable.ae_strongly_measurable (by measurability)) this,
  apply integrable.const_mul,
  refine integrable_on.congr_set_ae _ Ioi_ae_eq_Ici.symm,
  apply integrable_on_my_func_Ioi,
  linarith
end

lemma prime_reciprocal_eq {x : ℝ} (hx : 2 ≤ x) :
  prime_summatory (λ p, (p : ℝ)⁻¹) 2 x -
    (log (log x) + (1 - log (real.log 2) + prime_reciprocal_integral))
    = prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2) :=
begin
  let a : ℕ → ℝ := λ n, if n.prime then real.log n * n⁻¹ else 0,
  let f : ℝ → ℝ := λ x, (log x)⁻¹,
  let f' : ℝ → ℝ := λ x, ((- x⁻¹) / log x ^ 2),
  have hdiff : ∀ i ∈ set.Ici ((2 : ℕ) : ℝ), has_deriv_at f (f' i) i,
  { rintro i (hi : _ ≤ _),
    rw nat.cast_two at hi,
    exact (has_deriv_at_log (by linarith)).inv (ne_of_gt (log_pos (by linarith))) },
  have h : ∀ x : ℝ, x ∈ set.Ici (2 : ℝ) → x ≠ 0,
  { simp only [imp_not_comm, set.mem_Ici, not_le, forall_eq, zero_lt_bit0, zero_lt_one] },
  -- have h' : ∀ x : ℝ, x ∈ set.Ici ((2 : ℕ) : ℝ) → x ≠ 0 := by exact_mod_cast h,
  have hcont : continuous_on f' (Ici ((2 : ℕ) : ℝ)),
  { rw nat.cast_two,
    apply continuous_on.div,
    { exact (continuous_on_inv₀.mono h).neg },
    { exact (continuous_on_log.mono h).pow _ },
    intros x hx,
    refine pow_ne_zero _ (log_pos _).ne',
    exact one_lt_two.trans_le hx },
  have := partial_summation_cont' a f f' two_ne_zero hdiff hcont x,
  rw [sub_eq_iff_eq_add],
  convert this using 1,
  { rw prime_summatory_eq_summatory,
    refine finset.sum_congr rfl _,
    intros y hy,
    simp only [],
    rw [ite_mul, zero_mul, mul_right_comm, mul_inv_cancel, one_mul],
    apply (log_pos _).ne',
    rw [nat.one_lt_cast, ←nat.succ_le_iff],
    simp only [finset.mem_Icc] at hy,
    apply hy.1 },
  rw [←prime_summatory_eq_summatory, prime_summatory_log_mul_inv_eq, nat.cast_two],
  simp only [div_eq_mul_inv, pi.add_apply, add_mul, f', f, neg_mul, mul_neg,
    integral_neg, sub_neg_eq_add, ←mul_inv],
  have h₁ : integrable (λ a, (a * log a)⁻¹) (volume.restrict (Icc 2 x)),
  { apply continuous_on.integrable_on_Icc,
    apply my_func2_continuous_on.mono,
    intros y hy,
    exact one_lt_two.trans_le hy.1 },
  have :
    ∫ a in Icc 2 x, real.log a * (a * real.log a ^ 2)⁻¹ +
        prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
    ∫ a in Icc 2 x, (a * real.log a)⁻¹ + prime_log_div_sum_error a * (a * log a ^ 2)⁻¹,
  { refine set_integral_congr measurable_set_Icc (λ y hy, _),
    dsimp,
    rw [mul_inv, mul_inv, mul_left_comm, ←div_eq_mul_inv, sq, div_self_mul_self'] },
  rw [mul_inv_cancel (log_pos (one_lt_two.trans_le hx)).ne', this,
    integral_add h₁ (integrable_on_prime_log_div_sum_error.mono_set Icc_subset_Ici_self),
    sub_add_eq_add_sub, add_comm (1 : ℝ), add_sub_assoc, add_assoc, add_right_inj,
    integral_Icc_eq_integral_Ioc, ←interval_integral.integral_of_le hx, ←add_assoc,
    ←add_assoc (1 : ℝ), add_sub, integral_inv_self_mul_log one_lt_two (one_lt_two.trans_le hx),
    add_comm (real.log _), add_sub, add_sub_assoc, add_right_inj, sub_eq_iff_eq_add,
    integral_Icc_eq_integral_Ioc, set_integral_congr_set_ae (Ioi_ae_eq_Ici' volume_singleton).symm,
    ←integral_union _ _ (integrable_on_prime_log_div_sum_error.mono_set _)
    (integrable_on_prime_log_div_sum_error.mono_set _),
    Ioc_union_Ioi_eq_Ioi hx],
  { refl },
  { exact disjoint.mono_left set.Ioc_subset_Iic_self (Iic_disjoint_Ioi le_rfl) },
  { exact measurable_set_Ioi },
  { exact set.Ioc_subset_Icc_self.trans set.Icc_subset_Ici_self },
  { rintro y (hy : _ < _),
    apply hx.trans hy.le },
end

lemma prime_reciprocal_error :
  is_O at_top (λ x, prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2)) (λ x, (log x)⁻¹) :=
begin
  simp only [div_eq_mul_inv],
  apply is_O.sub,
  { apply (is_O_prime_log_div_sum_error.mul (is_O_refl _ _)).trans _,
    simpa using is_O_refl _ _ },
  obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound,
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → _ ≤ c * ∥(1 : ℝ)∥⟩ := (at_top_basis' 2).mem_iff.1 hc,
  have : ∀ y, k ≤ y → ∀ᵐ (x : ℝ) ∂volume.restrict (Ici y),
    ∥prime_log_div_sum_error x * (x * log x ^ 2)⁻¹∥ ≤ c * (x * log x ^ 2)⁻¹,
  { intros y hy,
    rw ae_restrict_iff' (@measurable_set_Ici ℝ _ _ _ _ _ _),
    filter_upwards with x hx,
    rw [norm_mul],
    apply (mul_le_mul_of_nonneg_right (hk _ (hy.trans hx)) (norm_nonneg _)).trans _,
    rw [norm_eq_abs, abs_one, mul_one, norm_eq_abs, abs_inv, abs_mul, abs_sq, abs_of_nonneg],
    exact zero_le_two.trans (hk₂.trans (hy.trans hx)) },
  have : is_O at_top (λ y, ∫ x in Ici y, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹)
          (λ y, ∫ x in Ici y, c * (x * log x ^ 2)⁻¹),
  { apply is_O.of_bound 1,
    filter_upwards [eventually_ge_at_top k] with y hy,
    apply (norm_integral_le_integral_norm _).trans _,
    rw [norm_eq_abs, one_mul],
    apply le_trans _ (le_abs_self _),
    refine integral_mono_of_nonneg (eventually_of_forall (λ x, norm_nonneg _)) _ (this _ hy),
    refine integrable.const_mul _ _,
    refine integrable_on.congr_set_ae _ Ioi_ae_eq_Ici.symm,
    exact integrable_on_my_func_Ioi (one_lt_two.trans_le (hk₂.trans hy)) },
  apply this.trans,
  simp only [←smul_eq_mul, integral_smul],
  simp only [smul_eq_mul],
  apply (is_O_const_mul_self c _ _).trans _,
  apply is_O.of_bound 1,
  filter_upwards [eventually_gt_at_top (1 : ℝ)] with y hy,
  rw [set_integral_congr_set_ae (Ioi_ae_eq_Ici' volume_singleton).symm, integral_my_func_Ioi hy,
    one_mul],
end

def meissel_mertens := 1 - log (real.log 2) + prime_reciprocal_integral

lemma prime_reciprocal :
  is_O at_top (λ x, prime_summatory (λ p, (p : ℝ)⁻¹) 1 x - (log (log x) + meissel_mertens))
    (λ x, (log x)⁻¹) :=
begin
  apply prime_reciprocal_error.congr' _ eventually_eq.rfl,
  filter_upwards [eventually_ge_at_top (2 : ℝ)] with x hx,
  rw [prime_summatory_one_eq_prime_summatory_two, ←prime_reciprocal_eq hx],
  refl
end

lemma is_o_log_inv_one {c : ℝ} (hc : c ≠ 0) : is_o at_top (λ x : ℝ, (log x)⁻¹) (λ x, (c : ℝ)) :=
(is_o.inv_rev (is_o_one_log c⁻¹) (by simp [hc])).congr_right (by simp)

lemma is_o_const_log_log (c : ℝ) : is_o at_top (λ x : ℝ, (c : ℝ)) (λ x : ℝ, log (log x)) :=
is_o_const_of_tendsto_at_top _ _ (tendsto_log_at_top.comp tendsto_log_at_top) _

lemma prime_reciprocal_upper :
  is_O at_top (λ x, prime_summatory (λ p, (p : ℝ)⁻¹) 1 x) (λ x, log (log x)) :=
((prime_reciprocal.trans ((is_o_log_inv_one one_ne_zero).trans (is_o_const_log_log _)).is_O).add
  ((is_O_refl _ _).add_is_o (is_o_const_log_log _))).congr (λ x, sub_add_cancel _ _) (λ _, rfl)

lemma mul_add_one_inv (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x + 1 ≠ 0) :
  (x * (x + 1))⁻¹ = x⁻¹ - (x + 1)⁻¹ :=
by field_simp [hx₀, hx₁]

lemma sum_thing_has_sum (k : ℕ) : has_sum (λ n : ℕ, ((n + k + 1) * (n + k + 2) : ℝ)⁻¹) (k + 1)⁻¹ :=
begin
  refine (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _,
  { exact λ i, inv_nonneg.2 (by exact_mod_cast zero_le') },
  have : ∀ i : ℕ, ((i + k + 1 : ℝ) * (i + k + 2))⁻¹ = (↑(i + (k + 1)))⁻¹ - (↑(i + 1 + (k + 1)))⁻¹,
  { intro i,
    simp only [nat.cast_add_one, nat.cast_add _ (_ + _), add_right_comm (i : ℝ) 1,
      ←add_assoc (i : ℝ)],
    convert mul_add_one_inv (i + k + 1) _ _ using 2,
    { norm_num [add_assoc] },
    { exact_mod_cast nat.succ_ne_zero (i + k) },
    { exact_mod_cast nat.succ_ne_zero (i + k + 1) } },
  simp only [this, sum_range_sub', zero_add, nat.cast_add_one],
  simpa using (tendsto_inverse_at_top_nhds_0_nat.comp (tendsto_add_at_top_nat (k + 1))).const_sub
    (k + 1 : ℝ)⁻¹,
end

lemma sum_thing'_has_sum : has_sum (λ n : ℕ, ((n - 1) * n : ℝ)⁻¹) 1 :=
begin
  refine (has_sum_nat_add_iff' 2).1 _,
  convert sum_thing_has_sum 0,
  { norm_num [add_sub_assoc] },
  simp [sum_range_succ],
end

lemma sum_thing'''_has_sum {k : ℕ} (hk : 1 ≤ k) :
  has_sum (λ n : ℕ, ((n + k) * (n + k + 1) : ℝ)⁻¹) k⁻¹ :=
begin
  convert sum_thing_has_sum (k - 1),
  { ext n,
    rw [add_assoc, add_assoc, nat.cast_sub hk, nat.cast_one, sub_add_cancel, add_sub, sub_add],
    norm_num [add_assoc] },
  simp [hk]
end

lemma sum_thing''_indicator_has_sum {k : ℕ} (hk : 1 ≤ k) :
  has_sum ({n | k < n}.indicator (λ n, ((n - 1) * n : ℝ)⁻¹)) k⁻¹ :=
begin
  have : set.range (λ i, i + (k + 1)) = {n | k < n},
  { ext i,
    simp only [set.mem_range, mem_set_of_eq, ←nat.add_one_le_iff, le_iff_exists_add,
      add_comm (k + 1), eq_comm] },
  rw ←this,
  have : function.injective (λ i, i + (k + 1)) := add_left_injective (k + 1),
  apply (function.injective.has_sum_iff this _).1,
  { convert sum_thing'''_has_sum hk using 1,
    ext n,
    simp [←add_assoc, set.indicator_of_mem] },
  simp [set.indicator_apply, if_false] {contextual := tt},
end

lemma prime_sum_thing_summable' (s : set ℕ) :
  summable (s.indicator ((set_of nat.prime).indicator (λ n, ((n - 1) * n : ℝ)⁻¹))) :=
(sum_thing'_has_sum.summable.indicator _).indicator _

lemma indicator_mono {α β : Type*} [ordered_add_comm_monoid β] {s t : set α} {f : α → β} (h : s ⊆ t)
  (hf : ∀ x, x ∉ s → x ∈ t → 0 ≤ f x) :
  indicator s f ≤ indicator t f :=
begin
  classical,
  intros x,
  simp only [set.indicator_apply],
  split_ifs,
  { refl },
  { cases h_2 (h h_1) },
  { apply hf _ h_1 h_2 },
  { refl },
end

lemma prime_sum_thing {k : ℕ} (hk : 1 ≤ k) :
  tsum ({n | k < n}.indicator ((set_of nat.prime).indicator (λ n, ((n - 1) * n : ℝ)⁻¹))) ≤ k⁻¹ :=
begin
  refine has_sum_mono ((prime_sum_thing_summable' _).has_sum) (sum_thing''_indicator_has_sum hk) _,
  rw [indicator_indicator, set.inter_comm, ←indicator_indicator],
  refine indicator_le_self' (λ _ _, indicator_nonneg (λ n (hn : _ < _), _) _),
  simp [inv_nonneg, hk.trans hn.le, mul_nonneg],
end

lemma my_mul_thing : ∀ {n : ℕ}, (0 : ℝ) ≤ (n - 1) * n
| 0 := by simp
| (n+1) := mul_nonneg (by simp) (nat.cast_nonneg _)

lemma my_mul_thing' : ∀ {n : ℕ}, (0 : ℝ) ≤ ((n - 1) * n)⁻¹ := λ n, inv_nonneg.2 my_mul_thing

lemma is_O_partial_of_bound {f : ℕ → ℝ} (hf : ∀ n, f n ≤ ((n - 1) * n)⁻¹) (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, is_O at_top (λ x : ℝ, ∑ i in range (⌊x⌋₊ + 1), f i - c) (λ x, x⁻¹) :=
begin
  have hf'' : summable f := summable_of_nonneg_of_le hf' hf sum_thing'_has_sum.summable,
  refine ⟨tsum f, (is_O.of_bound 2 _).symm⟩,
  filter_upwards [eventually_ge_at_top (1 : ℝ)] with x hx,
  have hx' : 1 ≤ ⌊x⌋₊ := by rwa [nat.le_floor_iff' one_ne_zero, nat.cast_one],
  have hx'' : (1 : ℝ) ≤ ⌊x⌋₊ := by simpa,
  rw [←sum_add_tsum_nat_add _ hf'', add_tsub_cancel_left, norm_inv,
    norm_of_nonneg (tsum_nonneg (λ i, hf' (i + _))), norm_of_nonneg (zero_le_one.trans hx)],
  transitivity (⌊x⌋₊ : ℝ)⁻¹,
  { refine has_sum_le (λ n, _) ((summable_nat_add_iff _).2 hf'').has_sum (sum_thing'''_has_sum hx'),
    refine (hf _).trans _,
    rw [nat.cast_add, nat.cast_add_one, ←add_assoc, add_sub_cancel] },
  rw [←div_eq_mul_inv, le_div_iff' (zero_lt_one.trans_le hx), ←div_eq_mul_inv,
    div_le_iff (zero_lt_one.trans_le hx'')],
  linarith [nat.lt_floor_add_one x],
end

lemma is_O_partial_of_bound' {f : ℕ → ℝ} (hf : ∀ n, f n ≤ ((n - 1) * n)⁻¹) (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, is_O at_top (λ x : ℝ, ∑ i in Icc 1 ⌊x⌋₊, f i - c) (λ x, x⁻¹) :=
begin
  obtain ⟨c, hc⟩ := is_O_partial_of_bound hf hf',
  refine ⟨c, hc.congr_left (λ x, eq.symm _)⟩,
  rw [range_eq_Ico, sum_subset, nat.Ico_succ_right],
  { exact Icc_subset_Icc_left zero_le_one },
  simp only [finset.mem_Icc, zero_le', true_and, and_true, not_le, nat.lt_one_iff]
    {contextual := tt},
  intros _ _ _,
  exact (hf' 0).antisymm' (by simpa using hf 0),
end

lemma intermediate_bound :
  ∃ c, is_O at_top (λ x, prime_summatory (λ p, ((p - 1) * p : ℝ)⁻¹) 1 x - c) (λ x, x⁻¹) :=
begin
  simp only [prime_summatory, sum_filter],
  refine is_O_partial_of_bound' (λ n, _) (λ n, _);
  split_ifs;
  exact my_mul_thing' <|> refl
end

lemma prime_proper_powers {x : ℝ} {f : ℕ → ℝ} :
  (∑ q in (finset.Icc 1 ⌊x⌋₊).filter is_prime_pow, f q) - prime_summatory f 1 x =
    ∑ p in (finset.Icc 1 ⌊x⌋₊).filter nat.prime,
      ∑ k in (finset.Icc 2 ⌊log x / real.log p⌋₊), f (p ^ k) :=
begin
  rw [exact_sum_prime_powers, prime_summatory, sub_eq_iff_eq_add, ←sum_add_distrib],
  refine finset.sum_congr rfl (λ p hp, _),
  rw [mem_filter, finset.mem_Icc] at hp,
  have : 0 < p := hp.1.1,
  rw [nat.le_floor_iff' this.ne'] at hp,
  have : (0 : ℝ) < p := by exact_mod_cast this,
  have : 1 ≤ ⌊log x / real.log p⌋₊,
  { rw [nat.le_floor_iff' one_ne_zero, nat.cast_one, one_le_div, log_le_log ‹_›
      (this.trans_le hp.1.2)],
    { exact hp.1.2 },
    apply log_pos,
    exact_mod_cast hp.2.one_lt },
  rw [finset.Icc_eq_insert_Icc_succ this, sum_insert, pow_one, add_comm],
  rw [finset.mem_Icc],
  norm_num,
end

lemma is_O_reciprocal_difference_aux {x : ℝ} :
  |(∑ q in (finset.Icc 1 ⌊x⌋₊).filter is_prime_pow, (q : ℝ)⁻¹) -
    prime_summatory (λ p, p⁻¹) 1 x - prime_summatory (λ p, (((p - 1) * p : ℝ)⁻¹)) 1 x| ≤
      ∑ p in (finset.Icc 1 ⌊x⌋₊).filter nat.prime, (2 * x⁻¹) :=
begin
  rw [prime_proper_powers, prime_summatory, ←sum_sub_distrib],
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (λ p hp, _)),
  rw [mem_filter, finset.mem_Icc] at hp,
  have : 0 < p := hp.1.1,
  rw [nat.le_floor_iff' this.ne'] at hp,
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast this,
  have hp₁ : (1 : ℝ) < (p : ℝ) := by simpa using hp.2.one_lt,
  have hx : 0 < x := hp₀.trans_le hp.1.2,
  have hf : 1 ≤ ⌊log x / real.log p⌋₊,
  { rw [nat.le_floor_iff' one_ne_zero, nat.cast_one, one_le_div, log_le_log ‹_› hx],
    { exact hp.1.2 },
    apply log_pos,
    exact_mod_cast hp.2.one_lt },
  simp only [←nat.Ico_succ_right, nat.cast_pow, ←inv_pow],
  rw [geom_sum_Ico', inv_pow, inv_pow, ←one_div (p : ℝ), one_sub_div hp₀.ne', div_div_eq_mul_div,
    sq, pow_succ', mul_inv, mul_inv, ←sub_mul, inv_mul_cancel_right₀ hp₀.ne', sub_div,
    div_eq_mul_inv, mul_inv, mul_comm, sub_sub_cancel_left, abs_neg, abs_div, abs_inv, abs_pow,
    abs_of_nonneg (sub_nonneg_of_le hp₁.le), nat.abs_cast, div_le_iff (sub_pos_of_lt hp₁)],
  rotate 1,
  { simpa only [ne.def, inv_eq_one] using hp₁.ne' },
  { rwa nat.succ_le_succ_iff },
  transitivity x⁻¹ * p,
  { rw [mul_comm, ←div_eq_mul_inv, le_div_iff' hx, ←div_eq_mul_inv, div_le_iff, ←pow_succ,
      ←rpow_nat_cast, ←logb_le_iff_le_rpow hp₁ hx, log_div_log],
    { exact (nat.lt_floor_add_one _).le },
    { exact pow_pos hp₀ _, } },
  rw [mul_comm (2 : ℝ), mul_assoc],
  refine mul_le_mul_of_nonneg_left _ _,
  { norm_cast,
    linarith [hp.2.two_le] },
  exact inv_nonneg.2 hx.le,
end

lemma is_O_reciprocal_difference : ∃ c,
  is_O at_top (λ x : ℝ, (∑ q in (finset.Icc 1 ⌊x⌋₊).filter is_prime_pow, (q : ℝ)⁻¹) -
          prime_summatory (λ p, p⁻¹) 1 x - c)
    (λ x, (log x)⁻¹) :=
begin
  obtain ⟨c, hc⟩ := intermediate_bound,
  refine ⟨c, _⟩,
  have hc' : is_O at_top (λ x, prime_summatory (λ p, ((p - 1) * p : ℝ)⁻¹) 1 x - c) (λ x, (log x)⁻¹),
  { refine hc.trans (is_o_log_id_at_top.is_O.inv_rev _),
    filter_upwards [eventually_gt_at_top (1 : ℝ)] with x hx i using ((log_pos hx).ne' i).elim },
  refine is_O.triangle _ hc',
  have : is_O at_top (λ x, (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ)) (λ x, (log x)⁻¹),
  { simp_rw [mul_left_comm],
    apply is_O.const_mul_left,
    refine (is_O_prime_counting_div_log.mul (is_O_refl _ _)).congr' eventually_eq.rfl _,
    filter_upwards [eventually_gt_at_top (0 : ℝ)] with x hx,
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel hx.ne', one_mul] },
  refine is_O.trans (is_O_of_le _ _) this,
  intro x,
  rw [norm_eq_abs, norm_eq_abs],
  apply is_O_reciprocal_difference_aux.trans (le_trans (le_of_eq _) (le_abs_self _)),
  rw [sum_const, prime_counting_eq_card_primes, nsmul_eq_mul],
end

lemma prime_power_reciprocal : ∃ b,
  is_O at_top (λ x : ℝ, (∑ q in (finset.Icc 1 ⌊x⌋₊).filter is_prime_pow, (q : ℝ)⁻¹) - (log (log x) + b))
    (λ x, (log x)⁻¹) :=
begin
  obtain ⟨c, hc⟩ := is_O_reciprocal_difference,
  exact ⟨_ + c, (hc.add prime_reciprocal).congr_left (λ x, by ring_nf)⟩,
end

lemma summable_indicator_iff_subtype {α β : Type*} [topological_space α] [add_comm_monoid α]
  {s : set β} (f : β → α) :
  summable (f ∘ coe : s → α) ↔ summable (s.indicator f) :=
exists_congr (λ _, has_sum_subtype_iff_indicator)

lemma is_unit_of_is_unit_pow {α : Type*} [comm_monoid α] {a : α} :
  ∀ n, n ≠ 0 → (is_unit (a ^ n) ↔ is_unit a)
| 0 h := (h rfl).elim
| 1 _ := by simp
| (n+2) _ := by rw [pow_succ, is_unit.mul_iff, is_unit_of_is_unit_pow _ n.succ_ne_zero, and_self]

lemma is_prime_pow_and_not_prime_iff {α : Type*} [cancel_comm_monoid_with_zero α] (x : α) :
  is_prime_pow x ∧ ¬ prime x ↔ (∃ p k, prime p ∧ 1 < k ∧ p ^ k = x) :=
begin
  split,
  { rintro ⟨⟨p, k, hp, hk, rfl⟩, t⟩,
    refine ⟨_, k, hp, _, rfl⟩,
    rw ←nat.succ_le_iff at hk,
    apply lt_of_le_of_ne hk,
    rintro rfl,
    apply t,
    rwa pow_one },
  { rintro ⟨p, k, hp, hk, rfl⟩,
    have : k ≠ 0 := by linarith,
    refine ⟨is_prime_pow.pow hp.is_prime_pow ‹k ≠ 0›, λ t, _⟩,
    have : p ^ k = p * (p ^ (k - 1)),
    { rw [←pow_succ, tsub_add_cancel_of_le hk.le] },
    have := (t.irreducible.is_unit_or_is_unit this).resolve_left hp.not_unit,
    apply hp.not_unit,
    rwa is_unit_of_is_unit_pow at this,
    rwa [ne.def, tsub_eq_zero_iff_le, not_le] }
end

lemma log_one_sub_recip {p : ℕ} (hp : 1 < p) :
  |(p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)| ≤ ((p - 1) * p)⁻¹ :=
begin
  have hp₁ : (1 : ℝ) < p := nat.one_lt_cast.2 hp,
  have hp₀ : (0 : ℝ) < p := zero_le_one.trans_lt hp₁,
  have hp_inv : |(p : ℝ)⁻¹| < 1,
  { rwa [abs_inv, nat.abs_cast, inv_lt_one_iff_of_pos hp₀] },
  have := abs_log_sub_add_sum_range_le hp_inv 1,
  rwa [range_one, sum_singleton, nat.cast_zero, abs_inv, nat.abs_cast, zero_add, zero_add, div_one,
    pow_one, inv_pow _ 2, inv_div_left, sq, ←mul_assoc, sub_mul, one_mul,
    inv_mul_cancel hp₀.ne'] at this,
end

lemma my_func_neg {p : ℕ} (hp : 1 < p) : (p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹) ≤ 0 :=
by linarith [log_le_sub_one_of_pos (sub_pos_of_lt (inv_lt_one (nat.one_lt_cast.2 hp)))]

lemma mertens_third_log_error :
  ∃ c, is_O at_top
    (λ x, ∑ p in (finset.Icc 1 ⌊x⌋₊).filter nat.prime, -((p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)) - c)
      (λ x : ℝ, x⁻¹) :=
begin
  simp only [sum_filter],
  refine is_O_partial_of_bound' (λ n, _) (λ n, _); split_ifs,
  { exact neg_le_of_neg_le (neg_le_of_abs_le (log_one_sub_recip h.one_lt)) },
  { exact my_mul_thing' },
  { rw neg_nonneg, exact my_func_neg h.one_lt },
  { refl },
end

lemma mertens_third_log :
  ∃ c, is_O at_top
    (λ x : ℝ,
      ∑ p in (finset.Icc 1 ⌊x⌋₊).filter nat.prime, log (1 - (p : ℝ)⁻¹)⁻¹ - (log (log x) + c))
      (λ x : ℝ, (log x)⁻¹) :=
begin
  obtain ⟨c₂, hc₂⟩ := mertens_third_log_error,
  replace hc₂ := hc₂.trans (is_o_log_id_at_top.is_O.inv_rev _),
  swap,
  { filter_upwards [eventually_gt_at_top (1 : ℝ)] with x hx i using ((log_pos hx).ne' i).elim },
  refine ⟨c₂ + meissel_mertens, (prime_reciprocal.add hc₂).congr_left _⟩,
  intro x,
  simp only [log_inv, sum_neg_distrib, sum_add_distrib, neg_add, prime_summatory, sum_sub_distrib],
  ring,
end

def partial_euler_product (n : ℕ) := ∏ p in (finset.Icc 1 n).filter nat.prime, (1 - (p : ℝ)⁻¹)⁻¹

@[simp] lemma partial_euler_product_zero : partial_euler_product 0 = 1 :=
by simp [partial_euler_product]

/-- A trivial global upper bound on the partial euler product -/
lemma partial_euler_trivial_upper_bound {n : ℕ} : partial_euler_product n ≤ 2 ^ π n :=
begin
  rw [partial_euler_product, prime_counting_eq_card_primes, ←prod_const],
  have : ∀ i, nat.prime i → 0 < (1 - (i : ℝ)⁻¹) :=
    λ i hi, (sub_pos_of_lt (inv_lt_one (nat.one_lt_cast.2 hi.one_lt))),
  refine prod_le_prod (λ i hi, (inv_pos.2 (this i (mem_filter.1 hi).2)).le) (λ i hi, _),
  simp only [mem_filter] at hi,
  rw [inv_le (this _ hi.2) (by norm_num : (0 : ℝ) < 2), le_sub, inv_le],
  { norm_num,
    exact_mod_cast hi.2.two_le },
  { exact nat.cast_pos.2 hi.2.pos },
  { norm_num1 },
end

/-- A trivial global lower bound on the partial euler product -/
lemma partial_euler_trivial_lower_bound {n : ℕ} : 1 ≤ partial_euler_product n :=
begin
  refine one_le_prod (λ p hp, _),
  simp only [mem_filter] at hp,
  exact one_le_inv (sub_pos_of_lt (inv_lt_one (nat.one_lt_cast.2 hp.2.one_lt))) (by simp),
end

lemma mertens_third :
  ∃ c, 0 < c ∧ is_O at_top (λ x, partial_euler_product ⌊x⌋₊ - c * real.log x) (λ _, (1 : ℝ)) :=
begin
  obtain ⟨c, hc⟩ := mertens_third_log,
  obtain ⟨k, hk₀, hk⟩ := hc.exists_pos,
  refine ⟨exp c, exp_pos _, is_O.of_bound (2 * (k * exp c)) _⟩,
  filter_upwards [hk.bound, tendsto_log_at_top.eventually (eventually_ge_at_top k)] with x hx hx',
  have hk' : k * (log x)⁻¹ ≤ 1,
  { rwa [mul_inv_le_iff (hk₀.trans_le hx'), mul_one] },
  rw [norm_eq_abs, norm_inv, norm_of_nonneg (hk₀.le.trans hx')] at hx,
  have i := (real.abs_exp_sub_one_le (hx.trans hk')).trans
    (mul_le_mul_of_nonneg_left hx zero_le_two),
  have hx'' : 0 < log x := hk₀.trans_le hx',
  have hx''' : 0 < exp c * log x := mul_pos (exp_pos _) hx'',
  have hp : ∀ p, p ∈ filter nat.prime (Icc 1 ⌊x⌋₊) → 0 < (1 - (p : ℝ)⁻¹)⁻¹,
  { intros p hp,
    simp only [mem_filter] at hp,
    exact inv_pos.2 (sub_pos_of_lt (inv_lt_one (nat.one_lt_cast.2 hp.2.one_lt))) },
  rw [exp_sub, exp_add, exp_log hx'', ←log_prod _ _ (λ p h, (hp p h).ne'), exp_log (prod_pos hp),
    mul_comm, div_sub_one hx'''.ne', abs_div, abs_of_nonneg hx'''.le, div_le_iff hx''', mul_assoc,
    mul_mul_mul_comm, inv_mul_cancel hx''.ne', mul_one] at i,
  rwa [norm_eq_abs, norm_one, mul_one],
end

lemma weak_mertens_third_upper : is_O at_top (λ x, partial_euler_product ⌊x⌋₊) log :=
let ⟨c, _, hc⟩ := mertens_third in
  ((hc.trans (is_o_one_log 1).is_O).add (is_O_const_mul_self c _ _)).congr_left (by simp)

lemma weak_mertens_third_lower : is_O at_top log (λ x, partial_euler_product ⌊x⌋₊) :=
begin
  obtain ⟨c, hc₀, hc⟩ := mertens_third,
  have h := is_O_self_const_mul _ hc₀.ne' log at_top,
  have := hc.trans_is_o ((is_o_one_log 1).trans_is_O h),
  exact (h.trans this.right_is_O_add).congr_right (by simp),
end

lemma weak_mertens_third_upper_all :
  ∃ c, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → ∥partial_euler_product ⌊x⌋₊∥ ≤ c * ∥log x∥ :=
begin
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_upper.exists_pos,
  rw [is_O_with_iff, eventually_at_top] at hc,
  obtain ⟨c₁, hc₁⟩ := hc,
  refine ⟨max c (2 ^ c₁ / real.log 2), lt_max_of_lt_left hc₀, λ x hx, _⟩,
  cases le_total c₁ x,
  { exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) },
  rw [norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
    norm_of_nonneg (log_nonneg (one_le_two.trans hx))],
  have : (2 : ℝ) ^ π ⌊x⌋₊ ≤ 2 ^ c₁,
  { rw ←rpow_nat_cast,
    apply rpow_le_rpow_of_exponent_le one_le_two,
    refine le_trans _ ((nat.floor_le (zero_le_two.trans hx)).trans h),
    exact nat.cast_le.2 (prime_counting_le_self ⌊x⌋₊) },
  apply (partial_euler_trivial_upper_bound.trans this).trans _,
  refine le_trans _ (mul_le_mul (le_max_right _ _)
    ((log_le_log zero_lt_two (zero_lt_two.trans_le hx)).2 hx) (log_nonneg one_le_two)
    (le_max_of_le_left hc₀.le)),
  rw div_mul_cancel _ (log_pos one_lt_two).ne',
end

lemma weak_mertens_third_lower_all :
  ∃ c, 0 < c ∧ ∀ x : ℝ, 1 ≤ x → c * ∥log x∥ ≤ ∥partial_euler_product ⌊x⌋₊∥ :=
begin
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_lower.exists_pos,
  rw [is_O_with_iff, eventually_at_top] at hc,
  obtain ⟨c₁, hc₁⟩ := hc,
  let c' := max c (log c₁),
  have hc' : 0 < c' := lt_max_of_lt_left hc₀,
  refine ⟨c'⁻¹, inv_pos.2 hc', λ x hx, _⟩,
  cases le_total c₁ x,
  { rw inv_mul_le_iff hc',
    exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) },
  rw [norm_of_nonneg (log_nonneg hx),
    norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound)],
  refine le_trans _ partial_euler_trivial_lower_bound,
  rw [inv_mul_le_iff hc', mul_one],
  exact le_trans ((log_le_log (zero_lt_one.trans_le hx) (by linarith)).2 h) (le_max_right _ _),
end

lemma two_pow_card_distinct_divisors_le_divisor_count {n : ℕ} (hn : n ≠ 0) :
  2 ^ ω n ≤ σ 0 n :=
begin
  rw [card_distinct_factors_apply, ←list.card_to_finset, divisor_function_exact hn, finsupp.prod,
    ←nat.support_factorization],
  apply finset.pow_card_le_prod,
  intros p hp,
  rwa [nat.succ_le_iff, lt_add_iff_pos_left, pos_iff_ne_zero, ←finsupp.mem_support_iff],
end

lemma mul_eq_mul_iff {a b c d : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbd : b ≤ d) :
  a * b = c * d ↔ a = c ∧ b = d :=
begin
  refine ⟨λ h, _, λ h, by rw [h.1, h.2]⟩,
  rcases hac.eq_or_lt with rfl | hac,
  { exact ⟨rfl, mul_left_cancel₀ ha.ne' h⟩ },
  rcases eq_or_lt_of_le hbd with rfl | hbd,
  { exact ⟨mul_right_cancel₀ hb.ne' h, rfl⟩ },
  exact ((mul_lt_mul'' hac hbd ha.le hb.le).ne h).elim,
end

lemma finset.prod_eq_prod_iff_of_le' {ι : Type*}
  {s : finset ι} {f g : ι → ℕ} (hf : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i ≤ g i) :
  ∏ i in s, f i = ∏ i in s, g i ↔ ∀ i ∈ s, f i = g i :=
begin
  induction s using finset.cons_induction_on with a s has ih generalizing hf h,
  { simp },
  simp only [prod_cons, mem_cons, forall_eq_or_imp] at ⊢ hf h,
  rw [mul_eq_mul_iff hf.1 (prod_pos hf.2) h.1 (prod_le_prod (λ i hi, (hf.2 i hi).le) h.2),
    ih hf.2 h.2],
end

lemma divisor_count_eq_pow_iff_squarefree {n : ℕ} :
  σ 0 n = 2 ^ ω n ↔ squarefree n :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  rw [card_distinct_factors_apply, ←list.card_to_finset, divisor_function_exact hn, finsupp.prod,
    ←nat.support_factorization, ←prod_const, nat.squarefree_iff_factorization_le_one hn, eq_comm],
  rw finset.prod_eq_prod_iff_of_le',
  { split,
    { intros h p,
      by_cases hp : p ∈ n.factorization.support,
      { rw ←nat.succ.inj (h _ hp) },
      rw finsupp.not_mem_support_iff.1 hp,
      exact zero_le_one },
    intros h p hp,
    rw nat.succ_inj',
    exact le_antisymm (finsupp.mem_support_iff.1 hp).bot_lt (h _) },
  { intros,
    exact zero_lt_two },
  intros p hp,
  rw nat.succ_le_succ_iff,
  exact (finsupp.mem_support_iff.1 hp).bot_lt,
end

local notation n`#` := primorial n

lemma primorial_pos (n : ℕ) : 0 < n# :=
prod_pos (by simp [nat.prime.pos] {contextual := tt})

lemma primorial_dvd_primorial_of_le {n m : ℕ} (h : n ≤ m) :
  n# ∣ m# :=
begin
  apply finset.prod_dvd_prod_of_subset,
  apply filter_subset_filter,
  rw finset.range_subset,
  exact add_le_add h (le_refl 1),
end

lemma primorial_monotone : monotone primorial :=
λ m n h, nat.le_of_dvd (primorial_pos _) (primorial_dvd_primorial_of_le h)

lemma dvd_primorial_of_prime {n p : ℕ} (hp : p.prime) (hn : p ≤ n) : p ∣ n# :=
dvd_prod_of_mem _ (by simp [hp, hn, nat.lt_add_one_iff])

lemma dvd_primorial_self {p : ℕ} (hp : p.prime) : p ∣ p# :=
dvd_primorial_of_prime hp le_rfl

lemma tendsto_primorial_at_top :
  tendsto primorial at_top at_top :=
begin
  apply primorial_monotone.tendsto_at_top_at_top,
  intro a,
  obtain ⟨p, hp₁, hp₂⟩ := nat.exists_infinite_primes a,
  exact ⟨p, hp₁.trans (nat.le_of_dvd (primorial_pos _) (dvd_primorial_self hp₂))⟩,
end

lemma primorial_zero : primorial 0 = 1 := rfl
lemma primorial_one : primorial 1 = 1 := rfl
lemma primorial_two : primorial 2 = 2 := rfl
lemma primorial_three : primorial 3 = 6 :=
by norm_num [primorial, filter_insert, range_succ, range_one, filter_singleton]

lemma two_le_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ≤ primorial n :=
begin
  rw ←primorial_two,
  exact primorial_monotone hn,
end

lemma squarefree_prime_prod {ι : Type*} {s : finset ι} (f : ι → ℕ) (hs : ∀ i ∈ s, (f i).prime)
  (hf : (s : set ι).inj_on f):
  squarefree (s.prod f) :=
begin
  unfreezingI { induction s using finset.cons_induction_on with a s has ih generalizing hs },
  { simp },
  simp only [prod_cons, mem_cons, forall_eq_or_imp] at hs ⊢,
  simp only [coe_cons, set.inj_on_insert (mem_coe.not.2 has), set.mem_image, not_exists,
    mem_coe, not_and] at hf,
  rw nat.squarefree_mul,
  { exact ⟨hs.1.squarefree, ih hf.1 hs.2⟩ },
  { apply nat.coprime_prod_right,
    intros i hi,
    rw nat.coprime_primes hs.1 (hs.2 _ hi),
    exact ne.symm (hf.2 _ hi) },
end

lemma squarefree_primorial (n : ℕ) : squarefree (primorial n) :=
squarefree_prime_prod _ (by simp) (function.injective_id.inj_on _)

lemma divisor_lower_bound_aux (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ n : ℕ in at_top, 1 / log (log (n : ℝ)) * (1 - ε) ≤ 1 / (log (log (n : ℝ)) - c) :=
begin
  suffices : ∀ᶠ x : ℝ in at_top, 1 / x * (1 - ε) ≤ 1 / (x - c),
  { exact (tendsto_log_at_top.comp tendsto_log_at_top).comp tendsto_coe_nat_at_top_at_top this },
  filter_upwards [eventually_ge_at_top (c + -c / ε), eventually_gt_at_top (0 : ℝ),
    eventually_gt_at_top c] with x hx hx' hx'',
  rwa [mul_comm, ←div_eq_mul_one_div, div_le_div_iff hx' (sub_pos_of_lt hx''), one_sub_mul, sub_sub,
    one_mul, sub_le_self_iff, ←neg_le_iff_add_nonneg', ←div_le_iff' hε, le_sub_iff_add_le'],
end

lemma log_primorial_eq {n : ℕ} : real.log (primorial n) = ϑ n :=
begin
  rw [primorial, chebyshev_first, nat.cast_prod, log_prod, nat.floor_coe],
  simp [nat.prime.ne_zero] {contextual := tt},
end

lemma factors_primorial {n : ℕ} :
  (primorial n).factors = (list.range (n + 1)).filter nat.prime :=
begin
  rw [primorial],
  refine (list.eq_of_perm_of_sorted (nat.factors_unique _ _) _ (nat.factors_sorted _)).symm,
  { rw [prod_eq_multiset_prod, filter_val, range_coe, multiset.map_id', ←multiset.coe_prod,
      ←multiset.coe_filter],
    refl },
  { simp },
  refine list.pairwise.sublist (list.filter_sublist _) _,
  exact (list.pairwise_lt_range _).imp (λ _ _, le_of_lt),
end

@[simp] lemma to_finset_filter
  {α : Type*} {l : list α} (p : α → Prop) [decidable_eq α] [decidable_pred p] :
  (l.filter p).to_finset = l.to_finset.filter p :=
by { ext x, simp }

@[simp] lemma to_finset_range {n : ℕ} : (list.range n).to_finset = finset.range n :=
by { ext x, simp }

lemma factors_to_finset_primorial {n : ℕ} :
  (primorial n).factors.to_finset = (finset.range (n + 1)).filter nat.prime :=
by { rw factors_primorial, simp }

lemma card_distinct_factors_primorial {n : ℕ} : ω (primorial n) = π n :=
by rw [card_distinct_factors_apply, ←list.card_to_finset, factors_to_finset_primorial,
    nat.prime_counting, nat.prime_counting', nat.count_eq_card_filter_range]

lemma card_factors_primorial {n : ℕ} : Ω (primorial n) = π n :=
begin
  rw [←card_distinct_factors_primorial, eq_comm,
    card_distinct_factors_eq_card_factors_iff_squarefree (primorial_pos _).ne'],
  exact squarefree_primorial _
end

lemma le_log_sigma_zero_primorial :
  ∃ c : ℝ, ∀ p, 2 ≤ p →
    (log (primorial p : ℝ) * real.log 2) / (log (log (primorial p : ℝ)) - c) ≤
      real.log (σ 0 (primorial p)) :=
begin
  obtain ⟨c, hc₀, hc⟩ := chebyshev_first_all,
  refine ⟨log c, λ p hp, _⟩,
  set n := primorial p with hn,
  have hp₁ : 2 ≤ (p : ℝ) := by exact_mod_cast hp,
  have hp₂ : 0 < (p : ℝ) := zero_lt_two.trans_le hp₁,
  have hp₃ : 0 < ϑ p := chebyshev_first_pos _ hp₁,
  rw [divisor_count_eq_pow_iff_squarefree.2 (squarefree_primorial _), nat.cast_pow, log_pow,
    card_distinct_factors_primorial, nat.cast_two, log_primorial_eq],
  have h₁ : ϑ p ≤ π p * log (p : ℝ),
  { simpa using chebyshev_first_trivial_bound p },
  have h₂ : log (p : ℝ) ≤ log (ϑ p) - log c,
  { simpa [log_mul, hc₀.ne', hp₂.ne', norm_of_nonneg hp₃.le, le_sub_iff_add_le'] using
      log_le_log_of_le (mul_pos hc₀ (by rwa norm_coe_nat)) (hc _ hp₁) },
  have h₃ : 0 < log (p : ℝ) := log_pos (by simpa),
  have h₄ : 0 ≤ log (2 : ℝ) := log_nonneg one_le_two,
  have h₅ : (0 : ℝ) ≤ π p := nat.cast_nonneg (π p),
  rw div_le_iff (h₃.trans_le h₂),
  nlinarith [mul_nonneg h₅ h₄],
end

lemma nat.divisors_nonempty_iff {n : ℕ} : n.divisors.nonempty ↔ n ≠ 0 :=
⟨λ h₁ h₂, h₁.ne_empty (by simp [h₂]), λ _, ⟨1, by simpa⟩⟩

lemma one_le_sigma {k n : ℕ} (hn : n ≠ 0) : 1 ≤ σ k n :=
by simpa using @finset.single_le_sum _ _ _ (λ d, d ^ k) n.divisors (by simp) 1 (by simp [hn])

lemma sigma_pos {k n : ℕ} (hn : n ≠ 0) : 0 < σ k n :=
one_le_sigma hn

lemma divisor_lower_bound_log {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in at_top, (real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ) ≤ log (σ 0 n : ℝ) :=
begin
  obtain ⟨c, hc⟩ := le_log_sigma_zero_primorial,
  have : ∃ᶠ n : ℕ in at_top, log (n : ℝ) * real.log 2 / (log (log (n : ℝ)) - c) ≤ log (σ 0 n : ℝ) :=
    tendsto_primorial_at_top.frequently (eventually_at_top.2 ⟨2, hc⟩).frequently,
  apply (this.and_eventually (divisor_lower_bound_aux c hε)).mp,
  simp only [and_imp],
  filter_upwards [eventually_ge_at_top 1] with n hn₀ hn₁ hn₂,
  apply hn₁.trans',
  rw [mul_div_assoc, mul_comm (log (n : ℝ))],
  apply mul_le_mul_of_nonneg_right _ (log_nonneg (nat.one_le_cast.2 hn₀)),
  rw [div_eq_mul_one_div, mul_assoc, div_eq_mul_one_div (real.log 2)],
  apply mul_le_mul_of_nonneg_left hn₂ (log_nonneg one_le_two),
end

lemma divisor_lower_bound {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in at_top, (n : ℝ) ^ (real.log 2 / log (log (n : ℝ)) * (1 - ε)) ≤ σ 0 n :=
begin
  apply (divisor_lower_bound_log hε).mp,
  filter_upwards [eventually_ge_at_top 1] with n hn₀ hn₁,
  have hn₀' : 0 < n := hn₀,
  have hn₀'' : (0 : ℝ) < n := by simpa,
  rwa [←log_le_log (rpow_pos_of_pos hn₀'' _) (nat.cast_pos.2 (sigma_pos hn₀'.ne')), log_rpow hn₀'']
end

-- useful to have c explicit here so hc is a created goal
lemma cobounded_of_frequently {α : Type*} [conditionally_complete_lattice α]
  {f : filter α} (c : α) (hc : ∃ᶠ x in f, c ≤ x) :
  is_cobounded (≤) f :=
⟨c, λ d hd, let ⟨x, hxc, hxd⟩ := (hc.and_eventually hd).exists in hxc.trans hxd⟩

lemma Limsup_eq_of_eventually_of_frequently {f : filter ℝ} (c : ℝ)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c + ε)
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c - ε ≤ x) :
  Limsup f = c :=
begin
  have hb : is_bounded (≤) f := ⟨c + 1, upper 1 zero_lt_one⟩,
  have hc : is_cobounded (≤) f :=
    cobounded_of_frequently (c - 1) (by simpa using lower 1 zero_lt_one),
  apply le_antisymm,
  { rw le_iff_forall_pos_le_add,
    exact λ ε hε, Limsup_le_of_le hc (upper _ hε) },
  rw le_iff_forall_pos_le_add,
  intros ε hε,
  rw ←sub_le_iff_le_add,
  apply le_limsup_of_frequently_le (lower _ hε) hb,
end

lemma Limsup_eq_of_eventually_of_frequently_mul {f : filter ℝ} {c : ℝ} (hc : 0 ≤ c)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c * (1 + ε))
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c * (1 - ε) ≤ x) :
  Limsup f = c :=
begin
  rcases hc.eq_or_lt with rfl | hc,
  { refine Limsup_eq_of_eventually_of_frequently _ (λ ε hε, _) (λ ε hε, _),
    { apply eventually_le.trans (upper 1 zero_lt_one) (eventually_of_forall (λ x, _)),
      simpa using hε.le },
    apply (lower 1 zero_lt_one).mono,
    intros,
    linarith [hε.le] },
  apply Limsup_eq_of_eventually_of_frequently,
  { intros ε hε,
    simpa only [mul_one_add, mul_div_cancel' _ hc.ne'] using upper _ (div_pos hε hc) },
  { intros ε hε,
    simpa only [mul_one_sub, mul_div_cancel' _ hc.ne'] using lower _ (div_pos hε hc) }
end

lemma divisor_limsup :
  at_top.limsup (λ n : ℕ, log (σ 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)) = log (2 : ℝ) :=
begin
  have h : tendsto (λ n : ℕ, (n : ℝ)) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have l := tendsto_log_at_top,
  refine Limsup_eq_of_eventually_of_frequently_mul (log_nonneg one_le_two) (λ ε hε, _) (λ ε hε, _),
  { change ∀ᶠ x : ℕ in at_top, _,
    filter_upwards [divisor_bound hε, eventually_gt_at_top 0, h (eventually_gt_at_top 0),
      h $ l $ eventually_gt_at_top 0, h $ l $ l $ eventually_gt_at_top 0] with n hn hn₀ hn₁ hn₂ hn₃,
    dsimp at hn₁ hn₂ hn₃,
    have := log_le_log_of_le (nat.cast_pos.2 (sigma_pos hn₀.ne')) hn,
    simpa [log_rpow hn₁, ←div_le_iff hn₂, le_div_iff hn₃, div_mul_eq_mul_div] },
  change ∃ᶠ x : ℕ in at_top, _,
  refine (divisor_lower_bound_log hε).mp _,
  filter_upwards [eventually_gt_at_top 0, h (eventually_gt_at_top 0),
    h $ l $ eventually_gt_at_top 0, h $ l $ l $ eventually_gt_at_top 0] with n hn hn₀ hn₁ hn₂ hn₃,
  dsimp at hn₀ hn₁ hn₂,
  simpa only [le_div_iff hn₁, ←div_le_iff hn₂, ←div_mul_eq_mul_div],
end
