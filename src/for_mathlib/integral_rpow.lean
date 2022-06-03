/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import analysis.special_functions.integrals
import analysis.special_functions.pow
import measure_theory.integral.integral_eq_improper

noncomputable theory

open_locale big_operators nnreal filter topological_space

open asymptotics filter set real measure_theory

lemma integral_Ioi_rpow_tendsto_aux {a r : ℝ} (hr : r < -1) (ha : 0 < a)
  {ι : Type*} {b : ι → ℝ} {l : filter ι} (hb : tendsto b l at_top) :
  tendsto (λ i, ∫ x in a..b i, x ^ r) l (nhds (-a ^ (r + 1) / (r + 1))) :=
begin
  suffices :
    tendsto (λ i, ∫ x in a..b i, x ^ r) l (nhds (0 / (r + 1) - a ^ (r + 1) / (r + 1))),
  { simpa [neg_div] using this },
  have : ∀ᶠ i in l, ∫ x in a..b i, x ^ r = (b i) ^ (r + 1) / (r + 1) - a ^ (r + 1) / (r + 1),
  { filter_upwards [hb.eventually (eventually_ge_at_top a)],
    intros i hi,
    rw [←sub_div, ←integral_rpow (or.inr ⟨hr.ne, not_mem_interval_of_lt ha (ha.trans_le hi)⟩)], },
  rw tendsto_congr' this,
  refine tendsto.sub_const _ (tendsto.div_const _),
  rw ←neg_neg (r+1),
  apply (tendsto_rpow_neg_at_top _).comp hb,
  simpa using hr
end

-- TODO: Move to mathlib
lemma integrable_on_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
  integrable_on (λ x, x ^ r) (Ioi a) :=
begin
  have hb : tendsto (λ (x : ℝ≥0), a + x) at_top at_top :=
    tendsto_at_top_add_const_left _ _ (nnreal.tendsto_coe_at_top.2 tendsto_id),
  have : tendsto (λ (i : ℝ≥0), ∫ x in a..(a + i), ∥x ^ r∥) at_top (nhds (-a ^ (r + 1) / (r + 1))),
  { refine (integral_Ioi_rpow_tendsto_aux hr ha hb).congr (λ x, _),
    refine interval_integral.integral_congr (λ i hi, _),
    apply (real.norm_of_nonneg (real.rpow_nonneg_of_nonneg _ _)).symm,
    exact ha.le.trans ((by simp : _ ≤ _).trans hi.1) },
  refine integrable_on_Ioi_of_interval_integral_norm_tendsto _ _ (λ i, _) hb this,
  refine (continuous_on.integrable_on_Icc _).mono_set Ioc_subset_Icc_self,
  exact continuous_on_id.rpow_const (λ x hx, or.inl (ha.trans_le hx.1).ne'),
end

-- TODO: Move to mathlib
lemma integral_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
  ∫ x in Ioi a, x ^ r = - a ^ (r + 1) / (r + 1) :=
tendsto_nhds_unique
  (interval_integral_tendsto_integral_Ioi _ (integrable_on_rpow_Ioi hr ha) tendsto_id)
  (integral_Ioi_rpow_tendsto_aux hr ha tendsto_id)

-- TODO: Move to mathlib
lemma integrable_on_rpow_inv_Ioi {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
  integrable_on (λ x, (x ^ r)⁻¹) (Ioi a) :=
(integrable_on_rpow_Ioi (neg_lt_neg hr) ha).congr_fun (λ x hx, rpow_neg (ha.trans hx).le _)
  measurable_set_Ioi

-- TODO: Move to mathlib
lemma integral_rpow_inv {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ r)⁻¹ = a ^ (1 - r) / (r - 1) :=
begin
  rw [←set_integral_congr, integral_rpow_Ioi (neg_lt_neg hr) ha, neg_div, ←div_neg, neg_add',
    neg_neg, neg_add_eq_sub],
  { apply measurable_set_Ioi },
  exact λ x hx, (rpow_neg (ha.trans hx).le _)
end

-- TODO: Move to mathlib
lemma integrable_on_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
  integrable_on (λ x, x ^ n) (Ioi a) :=
by exact_mod_cast integrable_on_rpow_Ioi (show (n : ℝ) < -1, by exact_mod_cast hn) ha

-- TODO: Move to mathlib
lemma integral_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
  ∫ x in Ioi a, x ^ n = - a ^ (n + 1) / (n + 1) :=
by exact_mod_cast integral_rpow_Ioi (show (n : ℝ) < -1, by exact_mod_cast hn) ha

-- TODO: Move to mathlib
lemma integrable_on_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
  integrable_on (λ x, (x ^ n)⁻¹) (Ioi a) :=
(integrable_on_zpow_Ioi (neg_lt_neg hn) ha).congr_fun (by simp) measurable_set_Ioi

-- TODO: Move to mathlib
lemma integral_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ n)⁻¹ = a ^ (1 - n) / (n - 1) :=
begin
  simp_rw [←zpow_neg, integral_zpow_Ioi (neg_lt_neg hn) ha, neg_div, ←div_neg, neg_add',
    int.cast_neg, neg_neg, neg_add_eq_sub],
end

-- TODO: Move to mathlib
lemma integrable_on_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
  integrable_on (λ x, (x ^ n)⁻¹) (Ioi a) :=
by exact_mod_cast integrable_on_zpow_inv_Ioi (show 1 < (n : ℤ), by exact_mod_cast hn) ha

-- TODO: Move to mathlib
lemma integral_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
  ∫ x in Ioi a, (x ^ n)⁻¹ = (a ^ (n - 1))⁻¹ / (n - 1) :=
by simp_rw [←zpow_coe_nat, integral_zpow_inv_Ioi (show 1 < (n : ℤ), by exact_mod_cast hn) ha,
  int.cast_coe_nat, ←zpow_neg, int.coe_nat_sub hn.le, neg_sub, int.coe_nat_one]
