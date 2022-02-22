/-
Copyright (c) 2022 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import defs
import for_mathlib.misc
import for_mathlib.basic_estimates
import algebra.group_power.order
import data.complex.exponential_bounds

open_locale big_operators classical real

noncomputable theory

open real finset

/-- Def 4.1 -/
def integer_count (A : finset ℕ) (k : ℕ) : ℕ :=
(A.powerset.filter (λ S, ∃ (d : ℤ), rec_sum S * k = d)).card

/-- Useful for def 4.2 and in other statements -/
def valid_sum_range (t : ℕ) : finset ℤ :=
finset.Ioc ((- (t : ℤ) / 2)) (t/2)

/-- implementation lemma -/
lemma dumb_subtraction_thing (t : ℕ) : ((t : ℤ) / 2 - -(t : ℤ) / 2) = t :=
begin
  have : (t : ℤ) - -(t : ℤ) = 2 * t,
  { simp [two_mul] },
  rw [←int.sub_div_of_dvd_sub, this, int.mul_div_cancel_left _ two_ne_zero],
  rw this,
  simp only [dvd_mul_right],
end

lemma card_valid_sum_range (t : ℕ) :
  (valid_sum_range t).card = t :=
by rw [valid_sum_range, int.card_Ioc, dumb_subtraction_thing, int.to_nat_coe_nat]

lemma mem_valid_sum_range (t : ℕ) (h : ℤ) :
  h ∈ valid_sum_range t ↔ (-↑t) / 2 < h ∧ h ≤ t / 2 :=
by simp [valid_sum_range]

lemma zero_mem_valid_sum_range {t : ℕ} (ht : t ≠ 0) : (0 : ℤ) ∈ valid_sum_range t :=
begin
  rw [mem_valid_sum_range],
  refine ⟨int.div_neg' _ zero_lt_two, int.div_nonneg _ zero_le_two⟩,
  { simpa only [right.neg_neg_iff, int.coe_nat_pos] using ht.bot_lt, },
  simp only [int.coe_nat_nonneg],
end

-- this is dangerous but I think I can get away with it in this file
local notation `[` A `]` := (A.lcm id : ℕ)

lemma lcm_ne_zero_of_zero_not_mem {A : finset ℕ} (hA : 0 ∉ A) : [A] ≠ 0 :=
by rwa [ne.def, finset.lcm_eq_zero_iff, set.image_id, finset.mem_coe]

/-- Def 4.2 (maybe has a better name?) -/
def j (A : finset ℕ) : finset ℤ :=
(valid_sum_range [A]).erase 0

/-- Def 4.3: types of `h`, `k` might need to change? -/
def cos_prod (B : finset ℕ) (t : ℤ) : ℝ :=
∏ n in B, |cos (π * t / n)|

lemma cos_prod_nonneg {B : finset ℕ} {t : ℤ} : 0 ≤ cos_prod B t :=
prod_nonneg (λ _ _, abs_nonneg _)

lemma cos_prod_le_one {B : finset ℕ} {t : ℤ} : cos_prod B t ≤ 1 :=
prod_le_one (λ _ _, abs_nonneg _) (λ _ _, abs_cos_le_one _)

/-- Def 4.4 part one -/
def major_arc_at (A : finset ℕ) (k : ℕ) (K : ℝ) (t : ℤ) : finset ℤ :=
(j A).filter (λ h, |(h : ℝ) - t * [A] / k| ≤ K / (2 * k))

lemma mem_major_arc_at {A : finset ℕ} {k : ℕ} {K : ℝ} {t : ℤ} (i : ℤ) :
  i ∈ major_arc_at A k K t ↔ i ∈ j A ∧ |(i : ℝ) - t * [A] / k| ≤ K / (2 * k) :=
finset.mem_filter

lemma mem_major_arc_at' {A : finset ℕ} {k : ℕ} {K : ℝ} {t : ℤ} (hk : k ≠ 0) (i : ℤ) :
  i ∈ major_arc_at A k K t ↔ i ∈ j A ∧ (|i * k - t * [A]| : ℝ) ≤ K / 2 :=
begin
  have hk' : (0 : ℝ) < k,
  { rwa [nat.cast_pos, pos_iff_ne_zero] },
  rw [mem_major_arc_at, and_congr_right'],
  rw [←div_div_eq_div_mul, le_div_iff hk'],
  congr' 2,
  rw [←abs_of_pos hk', ←abs_mul, abs_of_pos hk', sub_mul, div_mul_cancel],
  rwa nat.cast_ne_zero,
end

/-- Def 4.4 part two -/
def major_arc (A : finset ℕ) (k : ℕ) (K : ℝ) : finset ℤ :=
(j A).filter (λ h, ∀ t, h ∈ major_arc_at A k K t)

lemma major_arc_at_of_neg {A : finset ℕ} {k : ℕ} {K : ℝ} (hk : k ≠ 0) (hK : K < 0) (t : ℤ) :
  major_arc_at A k K t = ∅ :=
begin
  rw [major_arc_at, finset.filter_false_of_mem],
  intros i hi q,
  have : K / (2 * k) < 0,
  { refine div_neg_of_neg_of_pos hK (mul_pos zero_lt_two _),
    rwa [nat.cast_pos, pos_iff_ne_zero] },
  exact not_lt_of_le (abs_nonneg _) (q.trans_lt this),
end

def exp_circle (x : ℂ) : ℂ := complex.exp (x * (2 * π * complex.I))

lemma exp_circle_add {x y : ℂ} : exp_circle (x + y) = exp_circle x * exp_circle y :=
by { rw [exp_circle, add_mul, complex.exp_add], refl }

lemma exp_circle_int (z : ℤ) : exp_circle z = 1 :=
by rw [exp_circle, complex.exp_int_mul_two_pi_mul_I z]

lemma exp_circle_eq_one_iff (x : ℂ) :
  exp_circle x = 1 ↔ ∃ (z : ℤ), x = z :=
by simp [exp_circle, complex.exp_eq_one_iff, pi_ne_zero, complex.I_ne_zero]

@[simp] lemma exp_circle_nat (n : ℕ) : exp_circle n = 1 :=
by rw [←exp_circle_int n, int.cast_coe_nat]

@[simp] lemma exp_circle_zero : exp_circle 0 = 1 :=
by rw [←exp_circle_nat 0, nat.cast_zero]

lemma exp_circle_sum {ι : Type*} {s : finset ι} (f : ι → ℂ) :
  exp_circle (∑ i in s, f i) = ∏ i in s, exp_circle (f i) :=
by { rw [exp_circle, finset.sum_mul, complex.exp_sum], refl }

/-- Lemma 4.6. Note `r` in this statement is different to the `r` in the written proof -/
lemma orthogonality {n m : ℕ} {r s : ℤ} (hm : m ≠ 0) {I : finset ℤ} (hI : I = finset.Ioc r s)
  (hrs₁ : r < s) (hrs₂ : I.card = m) :
  (∑ h in I, exp_circle (h * n / m)) * (1 / m) =
    if m ∣ n then 1 else 0 :=
begin
  have hm' : (m : ℂ) ≠ 0, exact_mod_cast hm,
  split_ifs,
  { simp_rw [mul_div_assoc, ←nat.cast_dvd h hm', ←int.cast_coe_nat, ←int.cast_mul, exp_circle_int],
    rw [finset.sum_const, nat.smul_one_eq_coe, int.cast_coe_nat, one_div, hrs₂, mul_inv_cancel hm'] },
  rw [mul_eq_zero, one_div, inv_eq_zero, nat.cast_eq_zero],
  simp only [hm, or_false],
  set S := ∑ h in I, exp_circle (h * n / m),
  have : S * exp_circle (n / m) = ∑ h in (finset.Ioc (r + 1) (s + 1)), exp_circle (h * n / m),
  { simp only [←finset.image_add_right_Ioc, finset.sum_image, add_left_inj, imp_self,
      implies_true_iff, int.cast_add, add_mul, int.cast_one, one_mul, add_div, exp_circle_add,
      finset.sum_mul, hI] },
  rw [int.Ioc_succ_succ hrs₁.le, finset.sum_erase_eq_sub, finset.sum_insert, add_comm,
    add_sub_assoc, sub_eq_zero_of_eq, add_zero, ←hI] at this,
  { apply eq_zero_of_mul_eq_self_right _ this,
    rw [ne.def, exp_circle_eq_one_iff, not_exists],
    intros i hi,
    rw [div_eq_iff_mul_eq hm', ←int.cast_coe_nat, ←int.cast_coe_nat, ←int.cast_mul,
      int.cast_inj] at hi,
    rw [←int.coe_nat_dvd, ←hi] at h,
    simpa using h },
  { have : s = m + r,
    { rw [←hrs₂, hI, int.card_Ioc, int.to_nat_sub_of_le hrs₁.le, sub_add_cancel] },
    rw [this, add_assoc, int.cast_add, add_mul, add_div, exp_circle_add, int.cast_coe_nat,
      mul_div_cancel_left _ hm', exp_circle_nat, one_mul] },
  { simp },
  { simp [int.add_one_le_iff, hrs₁] },
end

theorem nat.lcm_smallest {a b d : ℕ} (hda : a ∣ d) (hdb : b ∣ d)
  (hd : ∀ e : ℕ, a ∣ e → b ∣ e → d ∣ e) : d = a.lcm b :=
nat.dvd_antisymm (hd _ (nat.dvd_lcm_left _ _) (nat.dvd_lcm_right _ _)) (nat.lcm_dvd hda hdb)

lemma factorization_lcm {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
  (x.lcm y).factorization = x.factorization ⊔ y.factorization :=
begin
  have l₂ : ∀ p ∈ (x.factorization ⊔ y.factorization).support, nat.prime p,
  { simp only [finsupp.support_sup, mem_union, nat.support_factorization, list.mem_to_finset,
      or_imp_distrib, forall_and_distrib],
    exact ⟨λ _, nat.prime_of_mem_factors, λ _, nat.prime_of_mem_factors⟩ },
  rw [eq_comm, nat.eq_factorization_iff (nat.lcm_ne_zero hx hy) l₂],
  let d := (x.factorization ⊔ y.factorization).prod pow,
  have d_pos : d ≠ 0 := (nat.factorization_equiv.inv_fun ⟨_, l₂⟩).2.ne.symm,
  apply nat.lcm_smallest,
  { rw [←nat.factorization_le_iff_dvd hx d_pos, nat.prod_pow_factorization_eq_self l₂],
    exact le_sup_left },
  { rw [←nat.factorization_le_iff_dvd hy d_pos, nat.prod_pow_factorization_eq_self l₂],
    exact le_sup_right },
  intros e hae hbe,
  rcases eq_or_ne e 0 with rfl | he,
  { simp },
  rw ←nat.factorization_le_iff_dvd hx he at hae,
  rw ←nat.factorization_le_iff_dvd hy he at hbe,
  rw [←nat.factorization_le_iff_dvd d_pos he, nat.prod_pow_factorization_eq_self l₂],
  simp [hae, hbe],
end

/-- Lemma 4.7 -/
lemma lcm_desc {A : finset ℕ} (hA : 0 ∉ A) :
  [A].factorization = A.sup nat.factorization :=
begin
  revert hA,
  apply finset.induction_on A,
  { simp },
  intros a s has ih has',
  simp only [mem_insert, not_or_distrib] at has',
  rw [lcm_insert, lcm_eq_nat_lcm, id.def, factorization_lcm (ne.symm has'.1), sup_insert,
    ih has'.2],
  rw [ne.def, finset.lcm_eq_zero_iff],
  simpa only [id.def, set.image_id', mem_coe] using has'.2,
end

lemma finset.support_sup {α β : Type*}
  {f : α → β →₀ ℕ} (s : finset α) :
  (s.sup f).support = s.sup (λ a, (f a).support) :=
finset.induction_on s (by simp) (by simp {contextual := tt})

lemma finset.sup_eq_mem {α β : Type*} {s : finset α} (f : α → β) [linear_order β] [order_bot β]
  (hs : s.nonempty) :
  ∃ x ∈ s, s.sup f = f x :=
begin
  revert hs,
  refine finset.induction_on s (by simp) _,
  intros a s has ih _,
  rcases s.eq_empty_or_nonempty with rfl | hs',
  { simp },
  obtain ⟨b, hb, hb'⟩ := ih hs',
  simp only [mem_insert, sup_insert, exists_prop, hb'],
  cases le_total (f a) (f b),
  { exact ⟨b, or.inr hb, sup_of_le_right h⟩ },
  { exact ⟨a, or.inl rfl, sup_of_le_left h⟩ },
end

lemma finset.finsupp_sup_apply {α β : Type*} {f : α → β →₀ ℕ} (s : finset α) (x : β) :
  s.sup f x = s.sup (λ a, f a x) :=
finset.induction_on s (by simp) (by simp {contextual := tt})

lemma smooth_lcm_aux {X : ℕ} {A : finset ℕ} (hX₀ : X ≠ 0)
  (hX : ∀ q ∈ ppowers_in_set A, q ≤ X) (hA : 0 ∉ A) :
  [A] ≤ X ^ X.prime_counting :=
begin
  have : [A].factorization.prod pow = (A.sup nat.factorization).prod pow,
  { rw lcm_desc hA },
  rw nat.factorization_prod_pow_eq_self (lcm_ne_zero_of_zero_not_mem hA) at this,
  rw [this, finsupp.prod],
  refine (finset.prod_le_of_forall_le _ _ X _).trans _,
  { intro p,
    rw finset.support_sup,
    rw finset.mem_sup,
    simp only [ne.def, exists_prop, forall_exists_index, and_imp],
    intros x hx hx',
    apply hX,
    rw mem_ppowers_in_set' _ (nat.prime_of_mem_factorization hx'),
    simp only [exists_prop],
    rw finset.finsupp_sup_apply,
    { obtain ⟨n, hn, hn'⟩ := finset.sup_eq_mem (λ a : ℕ, a.factorization p) ⟨_, hx⟩,
      exact ⟨n, hn, hn'.symm⟩ },
    rw [←finsupp.mem_support_iff, finset.support_sup, finset.mem_sup],
    exact ⟨_, hx, hx'⟩ },
  apply nat.pow_le_pow_of_le_right hX₀.bot_lt,
  rw [nat.prime_counting, nat.prime_counting', nat.count_eq_card_filter_range, range_eq_Ico,
    nat.Ico_succ_right],
  apply card_le_of_subset,
  rintro p hp,
  have pp : p.prime,
  { simp only [finset.support_sup, finset.mem_sup] at hp,
    obtain ⟨n, hn, hn'⟩ := hp,
    exact nat.prime_of_mem_factorization hn' },
  simp only [finset.mem_filter, pp, mem_Icc, zero_le', true_and, and_true],
  rw [finsupp.mem_support_iff] at hp,
  suffices : p ^ A.sup nat.factorization p ≤ X,
  { rw [←pos_iff_ne_zero, ←nat.succ_le_iff] at hp,
    apply le_trans _ this,
    simpa using nat.pow_le_pow_of_le_right pp.pos hp },
  apply hX,
  rw [mem_ppowers_in_set' _ pp hp, finset.finsupp_sup_apply],
  simp only [←finsupp.mem_support_iff, finset.support_sup, finset.mem_sup,
    list.mem_to_finset, exists_prop] at hp,
  obtain ⟨x, hx, -⟩ := hp,
  obtain ⟨n, hn, hn'⟩ := finset.sup_eq_mem (λ a : ℕ, a.factorization p) ⟨_, hx⟩,
  exact ⟨n, hn, hn'.symm⟩,
end

/-- Lemma 4.8 -/
lemma smooth_lcm :
  ∃ C : ℝ, ∀ᶠ X : ℝ in filter.at_top,
    ∀ (A : finset ℕ), 0 ∉ A → (∀ q ∈ ppowers_in_set A, ↑q ≤ X) →
      ↑[A] ≤ exp (C * X) :=
begin
  obtain ⟨c, hc⟩ := is_O_prime_counting_div_log.bound,
  refine ⟨c, _⟩,
  filter_upwards [hc, filter.eventually_gt_at_top (1 : ℝ)],
  intros X hX₁ hX A hA hAX,
  have : ⌊X⌋₊ ≠ 0 := by simp only [ne.def, nat.floor_eq_zero, not_lt, hX.le],
  refine (nat.cast_le.2 (smooth_lcm_aux this (λ q hq, nat.le_floor (hAX q hq)) hA)).trans _,
  simp only [nat.cast_pow],
  refine (pow_le_pow_of_le_left (nat.cast_nonneg _)
    (nat.floor_le (zero_le_one.trans hX.le)) _).trans _,
  simp only [norm_coe_nat, norm_div, norm_of_nonneg (zero_le_one.trans hX.le),
    norm_of_nonneg (log_pos hX).le] at hX₁,
  rwa [←log_le_iff_le_exp, log_pow, ←le_div_iff (log_pos hX), mul_div_assoc],
  exact pow_pos (zero_le_one.trans_lt hX) _,
end

lemma jordan_apply {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : 2 * x ≤ sin (π * x) :=
begin
  have : 2 * x ≤ 1,
  { rwa [le_div_iff'] at hx',
    exact zero_lt_two },
  have t := real.le_sin_mul (by linarith) this,
  rwa [←mul_assoc, div_mul_cancel] at t,
  exact two_ne_zero
end

/-- Lemma 4.9 -/
lemma cos_bound {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
  |cos (π * x)| ≤ exp (-(2 * x ^ 2)) :=
begin
  have i₁ : |cos (π * x)| ^ 2 ≤ 1 - (2 * x) ^ 2,
  { rw [sq_abs, cos_sq', sub_le_sub_iff_left],
    exact pow_le_pow_of_le_left (by linarith) (jordan_apply hx hx') _ },
  refine le_of_pow_le_pow 2 (exp_pos _).le zero_lt_two _,
  apply (i₁.trans (one_sub_le_exp_minus_of_pos (sq_nonneg (2 * x)))).trans,
  rw [←exp_nat_mul, nat.cast_two, ←neg_mul_eq_mul_neg, exp_le_exp],
  exact le_of_eq (by ring),
end

lemma cos_bound_abs {x : ℝ} (hx' : |x| ≤ 1/2) :
  |cos (π * x)| ≤ exp (-(2 * x ^ 2)) :=
begin
  rcases le_total x 0 with hx | hx,
  { rw abs_of_nonpos hx at hx',
    rw ←neg_nonneg at hx,
    simpa using cos_bound hx hx' },
  exact cos_bound hx (by rwa [abs_of_nonneg hx] at hx'),
end

lemma nat.coprime_prod {ι : Type*} (s : finset ι) (f : ι → ℕ) (n : ℕ) :
  n.coprime (∏ i in s, f i) ↔ ∀ i ∈ s, n.coprime (f i) :=
begin
  apply finset.induction_on s,
  { simp },
  intros a s has ih,
  simp [has, nat.coprime_mul_iff_right, ih],
end

lemma prod_dvd_of_dvd_of_pairwise_disjoint {ι : Type*} {s : finset ι} {f : ι → ℕ} {n : ℕ}
  (hn : ∀ i ∈ s, f i ∣ n) (h : (s : set ι).pairwise (nat.coprime on f)) :
  ∏ i in s, f i ∣ n :=
begin
  revert h hn,
  apply finset.induction_on s,
  { simp },
  intros a s has ih h hn,
  simp only [mem_insert, forall_eq_or_imp] at hn,
  rw [coe_insert, set.pairwise_insert_of_symmetric] at h,
  rw [prod_insert has],
  refine nat.coprime.mul_dvd_of_dvd_of_dvd _ hn.1 (ih h.1 hn.2),
  { rw [nat.coprime_prod],
    intros i hi,
    exact h.2 i hi (ne_of_mem_of_not_mem hi has).symm },
  intros i j t,
  exact t.symm,
end

/-- Lemma 4.10 -/
lemma triv_q_bound {A : finset ℕ} (hA : 0 ∉ A) (n : ℕ) :
  ↑((ppowers_in_set A).filter (λ q, n ∈ local_part A q)).card ≤ log n / log 2 :=
begin
  set Q := (ppowers_in_set A).filter (λ q, n ∈ local_part A q),
  have : ∏ q in Q, q ∣ n,
  { apply prod_dvd_of_dvd_of_pairwise_disjoint,
    { intros q hq,
      rw [mem_filter, mem_local_part] at hq,
      exact hq.2.2.1 },
    simp only [set.pairwise, mem_coe, mem_filter, mem_ppowers_in_set, mem_local_part,
      is_prime_pow_nat_iff, and_imp, forall_exists_index],
    rintro _ p₁ k₁ hp₁ hk₁ rfl - hn hpk₁ hpk₁' _ p₂ k₂ hp₂ hk₂ rfl - - hpk₂ hpk₂' i,
    rw [function.on_fun, nat.coprime_pow_left_iff hk₁, nat.coprime_pow_right_iff hk₂,
      nat.coprime_primes hp₁ hp₂],
    rintro rfl,
    apply i,
    rw [coprime_div_iff hp₁ hpk₁ hk₁.ne' hpk₁', coprime_div_iff hp₂ hpk₂ hk₂.ne' hpk₂'] },
  rcases eq_or_ne n 0 with rfl | hn,
  { simp [Q, zero_mem_local_part_iff hA] },
  have two_le : ∀ q ∈ Q, 2 ≤ q,
  { intros q hq,
    rw [mem_filter, mem_ppowers_in_set] at hq,
    exact hq.1.1.two_le },
  replace := (le_prod_of_forall_le Q _ _ two_le).trans (nat.le_of_dvd hn.bot_lt this),
  rw [←@nat.cast_le ℝ, nat.cast_pow, nat.cast_two] at this,
  rwa [le_div_iff (log_pos one_lt_two), ←log_pow, log_le_log],
  { exact pow_pos zero_lt_two _ },
  rwa [nat.cast_pos, pos_iff_ne_zero],
end

lemma sum_powerset_prod {ι : Type*} (I : finset ι) (x : ι → ℂ) :
  ∑ J in I.powerset, ∏ j in J, x j = ∏ i in I, (1 + x i) :=
begin
  refine finset.induction_on I (by simp) _,
  intros a s has ih,
  rw [finset.sum_powerset_insert has, finset.prod_insert has, ←ih, add_mul, one_mul,
    finset.mul_sum, add_right_inj, finset.sum_congr rfl],
  intros t ht,
  simp only [finset.mem_powerset] at ht,
  rw finset.prod_insert (λ i, has (ht i)),
end

/-- Lemma 4.11 -/
lemma orthog_rat {A : finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0) :
  (integer_count A k : ℂ) =
    1 / [A] * ∑ h in valid_sum_range [A], ∏ n in A, (1 + exp_circle (k * h / n)) :=
begin
  have hA' : ([A] : ℚ) ≠ 0 := nat.cast_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hA),
  have hk' : (k : ℚ) ≠ 0 := nat.cast_ne_zero.2 hk,
  have : ∀ S : finset ℕ, S ⊆ A →
          ((∃ (z : ℤ), rec_sum S * (k : ℚ) = z) ↔ [A] ∣ (k * ∑ n in S, [A] / n)),
  { intros S hS,
    rw [←int.coe_nat_dvd, dvd_iff_exists_eq_mul_left],
    apply exists_congr,
    intro z,
    rw [←@int.cast_inj ℚ, int.cast_coe_nat, int.cast_mul, int.cast_coe_nat, nat.cast_mul,
      nat.cast_sum, ←mul_left_inj' hA', eq.congr_left],
    rw [mul_assoc, mul_left_comm, mul_right_inj' hk', rec_sum, finset.sum_mul, sum_congr rfl],
    intros x hx,
    rw [mul_comm, mul_one_div, nat.cast_dvd_char_zero],
    exact finset.dvd_lcm (hS hx) },
  have : ∀ S : finset ℕ, S ∈ A.powerset →
    (if (∃ (z : ℤ), rec_sum S * (k : ℚ) = z) then (1 : ℕ) else 0 : ℂ) =
      1 / [A] * ∑ h in valid_sum_range [A], exp_circle (k * h * rec_sum S),
  { intros S hS,
    have ht : ((- ([A] : ℤ) / 2)) < ([A] / 2),
    { apply int.div_lt_of_lt_mul zero_lt_two,
      apply lt_of_lt_of_le,
      { rw [right.neg_neg_iff, int.coe_nat_pos, pos_iff_ne_zero],
        apply lcm_ne_zero_of_zero_not_mem hA },
      exact (mul_nonneg (int.div_nonneg (int.coe_nat_nonneg _) zero_le_two) zero_le_two) },
    rw finset.mem_powerset at hS,
    rw [nat.cast_one, if_congr (this S hS) rfl rfl, mul_comm (_ : ℂ),
      ←orthogonality (lcm_ne_zero_of_zero_not_mem hA) rfl ht (card_valid_sum_range _)],
    congr' 1,
    apply finset.sum_congr rfl,
    intros i hi,
    rw [nat.cast_mul, mul_div_assoc, mul_div_assoc, ←mul_assoc, mul_comm (i : ℂ)],
    congr' 2,
    rw [rec_sum, nat.cast_sum, finset.sum_div, rat.cast_sum],
    apply finset.sum_congr rfl,
    intros n hn,
    rw [nat.cast_dvd_char_zero, rat.cast_div, rat.cast_coe_nat, rat.cast_one, div_div_eq_div_mul,
      mul_comm, div_mul_right],
    { exact nat.cast_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hA) },
    exact finset.dvd_lcm (hS hn) },
  rw [integer_count, card_eq_sum_ones, nat.cast_sum, sum_filter, finset.sum_congr rfl this,
    ←mul_sum, sum_comm],
  simp_rw [←sum_powerset_prod, ←exp_circle_sum, rec_sum, rat.cast_sum, mul_sum,
    rat.cast_div, rat.cast_one, ←div_eq_mul_one_div, rat.cast_coe_nat],
end

lemma integer_bound_thing {d : ℤ} (hd₀ : 0 ≤ d) (hd₁ : d ≠ 1) (hd₂ : d < 2) :
  d = 0 :=
begin
  interval_cases using hd₀ hd₂,
  cases hd₁ rfl,
end

lemma orthog_simp_aux {A : finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
  (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
  ∑ h in valid_sum_range [A], (∏ n in A, (1 + exp_circle (k * h / n))) = [A] :=
begin
  have : integer_count A k = 1,
  { rw [integer_count, card_eq_one],
    refine ⟨∅, _⟩,
    ext S,
    simp only [mem_filter, mem_powerset, mem_singleton],
    split,
    { rintro ⟨h₁, d, h₂⟩,
      have : 0 ≤ d,
      { rw [←@int.cast_nonneg ℚ, ←h₂],
        exact mul_nonneg rec_sum_nonneg (nat.cast_nonneg _) },
      have : d < 2,
      { rw [←@int.cast_lt ℚ, ←h₂, int.cast_two, ←lt_div_iff],
        { exact (rec_sum_mono h₁).trans_lt hA' },
        exact nat.cast_pos.2 hk.bot_lt },
      have : d ≠ 1,
      { rw [ne.def, ←@int.cast_inj ℚ, ←h₂, int.cast_one, ←eq_div_iff],
        { exact hS S h₁ },
        rwa nat.cast_ne_zero, },
      rw integer_bound_thing ‹0 ≤ d› ‹d ≠ 1› ‹d < 2› at *,
      simp only [hk, int.cast_zero, mul_eq_zero, nat.cast_eq_zero, or_false] at h₂,
      have : 0 ∉ S := mt (λ i, h₁ i) hA,
      rwa ←rec_sum_eq_zero_iff this, },
    rintro rfl,
    exact ⟨by simp, 0, by simp⟩ },
  rw [←div_eq_one_iff_eq, div_eq_mul_one_div, mul_comm, ←orthog_rat hA hk, this, nat.cast_one],
  rw nat.cast_ne_zero,
  apply lcm_ne_zero_of_zero_not_mem hA,
end

/-- Lemma 4.12 -/
lemma orthog_simp {A : finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
  (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
  ∑ h in valid_sum_range [A], (∏ n in A, (1 + exp_circle (k * h / n))).re = [A] :=
begin
  have := congr_arg complex.re (orthog_simp_aux hA hk hS hA'),
  rwa [complex.nat_cast_re, complex.re_sum] at this,
end

/-- Lemma 4.13 -/
lemma orthog_simp2 {A : finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
  (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k)
  (hA'' : ([A] : ℝ) ≤ 2^(A.card - 1 : ℤ)) :
  ∑ h in j A, (∏ n in A, (1 + exp_circle (k * h / n))).re ≤ -2^(A.card - 1 : ℤ) :=
begin
  have hA''' := lcm_ne_zero_of_zero_not_mem hA,
  rw [j, finset.sum_erase_eq_sub (zero_mem_valid_sum_range hA'''), orthog_simp hA hk hS hA'],
  simp only [int.cast_zero, zero_div, mul_zero, exp_circle_zero, prod_const],
  rw [sub_le_iff_le_add, neg_add_eq_sub],
  apply hA''.trans,
  rw [le_sub_iff_add_le, ←mul_two, ←zpow_add_one₀ (@two_ne_zero ℝ _ _), sub_add_cancel],
  norm_cast,
end

/-- Lemma 4.14 -/
lemma majorarcs_disjoint {A : finset ℕ} {k : ℕ} {K : ℝ} (hk : k ≠ 0) (hA : K < [A]) :
  (set.univ : set ℤ).pairwise_disjoint (major_arc_at A k K) :=
begin
  rintro t₁ - t₂ - ht h hh,
  cases lt_or_le K 0 with hK hK,
  { rw major_arc_at_of_neg hk hK at hh,
    simpa using hh },
  simp only [inf_eq_inter, mem_inter, mem_major_arc_at' hk, and_and_and_comm, and_self] at hh,
  have : (|(t₁ - t₂) * [A]| : ℝ) ≤ K,
  { rw [sub_mul],
    refine le_trans (abs_sub_le _ (h * k) _) _,
    rw abs_sub_comm,
    apply le_trans (add_le_add hh.2.1 hh.2.2),
    simp only [add_halves'] },
  rw [abs_mul, nat.abs_cast, ←int.cast_sub, ←int.cast_abs] at this,
  apply not_lt_of_le this,
  have ht' : 1 ≤ |t₁ - t₂|,
  { rwa [←zero_add (1 : ℤ), int.add_one_le_iff, abs_pos, sub_ne_zero] },
  have ht'' : (1 : ℝ) ≤ (|t₁ - t₂| : ℤ) := by exact_mod_cast ht',
  rw ←one_mul K,
  apply mul_lt_mul' ht'' hA hK,
  rwa [int.cast_pos, abs_pos, sub_ne_zero],
end

lemma function.antiperiodic.abs_periodic {f : ℝ → ℝ} {c : ℝ} (h : function.antiperiodic f c) :
  function.periodic (abs ∘ f) c :=
λ x, by simp [h x]

lemma abs_cos_periodic : function.periodic (λ i, |cos i|) π :=
function.antiperiodic.abs_periodic cos_antiperiodic

lemma abs_cos_period {x y n : ℤ} (h : x % n = y % n) :
  |cos (π * (x / n))| = |cos (π * (y / n))| :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  have : n ∣ x - y,
  { rwa [int.dvd_iff_mod_eq_zero, ←int.mod_eq_mod_iff_mod_sub_eq_zero] },
  obtain ⟨k, hk⟩ := this,
  rw sub_eq_iff_eq_add' at hk,
  rw [hk, int.cast_add, int.cast_mul, add_div, mul_div_cancel_left, mul_add, mul_comm π k],
  exact abs_cos_periodic.int_mul k _,
  simpa using hn
end

/-- Lemma 4.18 -/
lemma cos_prod_bound {A : finset ℕ} {N : ℕ} (t : ℤ) (hA' : 0 ∉ A) (hA : ∀ n ∈ A, n ≤ N)
  (h' : ℕ → ℤ) (hh'₁ : ∀ n ∈ A, h' n % n = t % n) (hh'₂ : ∀ n ∈ A, (|h' n| : ℝ) ≤ n / 2) :
  cos_prod A t ≤ exp (- (2 / N^2) * ∑ n in A, h' n ^ 2) :=
begin
  rw [cos_prod, mul_sum, exp_sum],
  refine prod_le_prod (λ i hi, (abs_nonneg _)) _,
  intros n hn,
  have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA',
  rw [neg_mul, div_mul_comm', ←div_pow, ←mul_comm (2 : ℝ), mul_div_assoc,
    ←int.cast_coe_nat n, abs_cos_period (hh'₁ _ hn).symm, int.cast_coe_nat],
  apply (cos_bound_abs _).trans,
  { rw [exp_le_exp, neg_le_neg_iff, ←sq_abs, ←sq_abs (_ / _)],
    refine mul_le_mul_of_nonneg_left _ zero_le_two,
    refine pow_le_pow_of_le_left (abs_nonneg _) _ _,
    rw [abs_div, abs_div],
    refine div_le_div_of_le_left (abs_nonneg _) _ _,
    { simpa only [nat.abs_cast, nat.cast_pos, pos_iff_ne_zero] using hn' },
    simp only [nat.abs_cast, nat.cast_le],
    exact hA _ hn },
  rw [abs_div, nat.abs_cast, div_le_iff, mul_comm, ←div_eq_mul_one_div],
  { exact hh'₂ _ hn },
  simpa only [nat.abs_cast, nat.cast_pos, pos_iff_ne_zero] using hn',
end

lemma prod_rpow {ι : Type*} {s : finset ι} {f : ι → ℝ} (c : ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) :
  (∏ i in s, f i) ^ c = ∏ i in s, f i ^ c :=
begin
  revert hf,
  apply finset.induction_on s,
  { simp },
  intros a s has ih hf,
  simp only [mem_insert, forall_eq_or_imp] at hf,
  rw [prod_insert has, mul_rpow hf.1 (prod_nonneg hf.2), prod_insert has, ih hf.2],
end

lemma prod_swapping {A : finset ℕ} (x : ℕ → ℝ) :
  ∏ (n : ℕ) in A, ∏ (q : ℕ) in (ppowers_in_set A).filter (λ q, n ∈ local_part A q), x n =
  ∏ (q : ℕ) in ppowers_in_set A, ∏ (n : ℕ) in local_part A q, x n :=
begin
  simp only [prod_filter],
  rw finset.prod_comm,
  simp only [←prod_filter, filter_mem_eq_inter, (inter_eq_right_iff_subset _ _).2 local_part_subset]
end

lemma real.le_rpow_self_of {x : ℝ} {z : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
  (h_one_le : z ≤ 1) : x ≤ x ^ z :=
begin
  rcases eq_or_ne z 0 with rfl | hz,
  { simp [hx₁] },
  rcases eq_or_lt_of_le hx₀ with rfl | hx₀,
  { rw zero_rpow hz },
  simpa using rpow_le_rpow_of_exponent_ge hx₀ hx₁ h_one_le
end

lemma minor2_ind_bound_part_one {N : ℕ} {A : finset ℕ} {t : ℤ} {K L : ℝ} {I : finset ℤ}
  (hA : 0 ∉ A) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N)
  (hI : I = finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
  (hq : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N^2 * (log N)^2)) :
  cos_prod A t ≤ ∏ q in ppowers_in_set A, (cos_prod (local_part A q) t) ^ (2 * log N)⁻¹ :=
begin
  let Q_ : ℕ → finset ℕ := λ n, (ppowers_in_set A).filter (λ q, n ∈ local_part A q),
  have hq : ∀ n ∈ A, ↑(Q_ n).card ≤ 2 * log N,
  { intros n hn,
    have : 0 < n := (ne_of_mem_of_not_mem hn hA).bot_lt,
    refine (triv_q_bound hA n).trans _,
    rw [div_eq_mul_one_div, mul_comm],
    refine mul_le_mul _ ((log_le_log _ _).2 _) (log_nonneg _) zero_le_two,
    { rw one_div_le (log_pos one_lt_two) zero_lt_two,
      exact le_trans (by norm_num1) log_two_gt_d9.le },
    { rwa [nat.cast_pos] },
    { rw nat.cast_pos,
      exact lt_of_lt_of_le (by norm_num1) hN },
    { exact nat.cast_le.2 (hA' n hn) },
    rwa [nat.one_le_cast, nat.succ_le_iff] },
  simp only [cos_prod],
  have : ∀ x ∈ ppowers_in_set A,
    (∏ (n : ℕ) in local_part A x, |cos (π * ↑t / ↑n)|) ^ (2 * log ↑N)⁻¹ =
    ∏ (n : ℕ) in local_part A x, |cos (π * ↑t / ↑n)| ^ (2 * log ↑N)⁻¹,
  { intros x hx,
    exact prod_rpow _ (λ n hn, abs_nonneg _) },
  simp_rw [finset.prod_congr rfl this, ←prod_swapping, prod_const],
  refine prod_le_prod (λ _ _, abs_nonneg _) _,
  intros n hn,
  rw [←rpow_nat_cast, ←rpow_mul (abs_nonneg _)],
  refine real.le_rpow_self_of (abs_nonneg _) (abs_cos_le_one _) _,
  rw [←div_eq_inv_mul, div_le_one],
  { exact hq n hn },
  refine mul_pos zero_lt_two (log_pos _),
  rw nat.one_lt_cast,
  exact lt_of_lt_of_le (by norm_num1) hN,
end

lemma exists_representative (t : ℤ) {n : ℕ} (hn : n ≠ 0) :
  ∃ tn : ℤ, tn % n = t % n ∧ |tn| ≤ n / 2 :=
begin
  cases le_or_lt (t % n) (n / 2),
  { refine ⟨t % n, int.mod_mod _ _, _⟩,
    rwa abs_of_nonneg,
    apply int.mod_nonneg,
    rwa int.coe_nat_ne_zero },
  refine ⟨t % n - n, _, _⟩,
  { simp [int.sub_mod] },
  rw [abs_of_nonpos, neg_sub, tsub_le_iff_right],
  { rw ←int.add_one_le_iff at h,
    apply le_trans _ (add_le_add_left h (n / 2)),
    rw [←add_assoc, ←two_mul, eq_sub_of_add_eq' (int.mod_add_div n 2), sub_add_eq_add_sub,
      le_sub_iff_add_le, add_le_add_iff_left, ←int.lt_add_one_iff],
    exact int.mod_lt n two_ne_zero },
  rw [sub_nonpos],
  apply (t.mod_lt (int.coe_nat_ne_zero.2 hn)).le.trans _,
  simp,
end

lemma minor2_ind_bound_sum {N : ℕ} {A : finset ℕ} {t : ℤ} {K L : ℝ} {I : finset ℤ} {q : ℕ}
  {tn : ℕ → ℤ} (hK : 0 < K) (hA : 0 ∉ A) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N)
  (hI : I = finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
  (htn₁ : ∀ (n : ℕ), n ∈ A → tn n % ↑n = t % ↑n)
  (htn₂ : ∀ (n : ℕ), n ∈ A → |tn n| ≤ ↑n / 2)
  (hq₁ : q ∈ ppowers_in_set A)
  (hq₂ : L / q ≤ (((local_part A q).filter (λ (n : ℕ), ∀ (x : ℤ), x ∈ I → ¬↑n ∣ x)).card)) :
  L / q * (K^2 / 4) ≤ ∑ (n : ℕ) in local_part A q, (tn n : ℝ) ^ 2 :=
begin
  let Aq' := ((local_part A q).filter (λ (n : ℕ), ∀ (x : ℤ), x ∈ I → ¬↑n ∣ x)),
  have : Aq' ⊆ local_part A q := filter_subset _ _,
  refine le_trans _ (sum_le_sum_of_subset_of_nonneg this (λ _ _ _, sq_nonneg _)),
  have : L / q * (K^2 / 4) ≤ Aq'.card * (K / 2)^2 :=
    mul_le_mul hq₂ (by norm_num) (div_nonneg (sq_nonneg _) (by norm_num)) (nat.cast_nonneg _),
  apply this.trans _,
  rw ←nsmul_eq_mul,
  apply finset.le_sum_of_forall_le,
  intros n hn,
  simp only [mem_filter] at hn,
  apply sq_le_sq,
  rw abs_of_pos (div_pos hK zero_lt_two),
  apply le_of_not_lt,
  intro i,
  have : t - tn n ∈ I,
  { rw [hI, mem_Icc, int.le_floor, int.ceil_le, int.cast_sub, sub_le_sub_iff_left, sub_eq_add_neg,
      add_le_add_iff_left, neg_le, and_comm, ←abs_le],
    apply i.le },
  have := hn.2 _ this,
  rw [int.dvd_iff_mod_eq_zero, ←int.mod_eq_mod_iff_mod_sub_eq_zero, eq_comm] at this,
  exact this (htn₁ _ (local_part_subset hn.1)),
end

lemma minor2_ind_bound {N : ℕ} {A : finset ℕ} {t : ℤ} {K L : ℝ} (I : finset ℤ)
  (hA : 0 ∉ A) (hK : 0 < K) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N)
  (hI : I = finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
  (hq : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N^2 * (log N)^2)) :
  cos_prod A t ≤ N ^ (-4 * finset.card (ppowers_in_set A \ interval_rare_ppowers I A L) : ℝ) :=
begin
  apply (minor2_ind_bound_part_one hA hA' hN hI hq).trans _,
  rw ←prod_sdiff (interval_rare_ppowers_subset I L),
  suffices : ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
              cos_prod (local_part A q) t ≤ N ^ (-8 * log N),
  { have hq : ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
              cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ N ^ (-4 : ℝ),
    { intros q hq,
      refine (rpow_le_rpow cos_prod_nonneg (this q hq) (inv_nonneg.2 _)).trans _,
      { exact mul_nonneg zero_le_two (log_nonneg (nat.one_le_cast.2 (one_le_two.trans hN))) },
      rw [←rpow_mul (nat.cast_nonneg _), ←div_eq_mul_inv, mul_comm (2 : ℝ),
        ←div_div_eq_div_mul, mul_div_cancel _ (log_pos _).ne'],
      { norm_num },
      rwa nat.one_lt_cast },
    have hq' : ∀ q ∈ interval_rare_ppowers I A L,
              cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ 1,
    { intros q hq,
      apply rpow_le_one cos_prod_nonneg cos_prod_le_one,
      rw inv_nonneg,
      refine mul_nonneg zero_le_two (log_nonneg _),
      rw nat.one_le_cast,
      apply one_le_two.trans hN },
    refine (mul_le_mul (prod_le_prod _ hq) (prod_le_prod _ hq') _ _).trans _,
    { exact λ i hi, rpow_nonneg_of_nonneg cos_prod_nonneg _ },
    { exact λ i hi, rpow_nonneg_of_nonneg cos_prod_nonneg _ },
    { exact prod_nonneg (λ i hi, rpow_nonneg_of_nonneg cos_prod_nonneg _) },
    { exact prod_nonneg (λ i hi, rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) },
    { rw [prod_const, prod_const_one, mul_one, ←rpow_nat_cast, ←rpow_mul (nat.cast_nonneg _)] } },
  intros q hq',
  have : ∀ n : ℕ, ∃ (tn : ℤ), n ∈ A → tn % n = t % n ∧ |tn| ≤ n / 2,
  { intro n,
    by_cases n ∈ A,
    { have hn' : n ≠ 0 := ne_of_mem_of_not_mem h hA,
      obtain ⟨tn, htn⟩ := exists_representative t hn',
      exact ⟨tn, λ _, htn⟩ },
    simp [h] },
  choose tn htn₁ htn₂ using this,
  refine (cos_prod_bound t (zero_mem_local_part_iff hA) (λ _ n, hA' _ (filter_subset _ _ n)) tn
    (λ _ n, htn₁ _ (filter_subset _ _ n)) _).trans _,
  { intros n hn,
    have z := htn₂ _ (filter_subset _ _ hn),
    rw [←int.coe_nat_one, ←int.coe_nat_bit0, ←int.coe_nat_div, ←@int.cast_le ℝ, int.cast_abs,
      int.cast_coe_nat] at z,
    exact z.trans (nat.cast_div_le.trans (by simp)) },
  simp only [interval_rare_ppowers, mem_sdiff, mem_filter, not_and, not_lt] at hq',
  replace hq' := and.intro hq'.1 (hq'.2 hq'.1),
  have := minor2_ind_bound_sum hK hA hA' hN hI htn₁ htn₂ hq'.1 hq'.2,
  apply le_trans (exp_le_exp.2 (mul_le_mul_of_nonpos_left this _)) _,
  { exact neg_nonpos.2 (div_nonneg zero_le_two (sq_nonneg _)) },
  have : 0 < (N : ℝ) := nat.cast_pos.2 (zero_lt_two.trans_le hN),
  rw [←le_log_iff_exp_le (rpow_pos_of_pos this _), log_rpow this, neg_mul, neg_mul, neg_mul,
    neg_le_neg_iff, div_mul_div, div_mul_div, mul_assoc, ←sq, ←one_le_div, div_div_eq_div_mul,
    ←inv_inv (2 : ℝ), mul_comm, ←div_eq_mul_inv, div_div_eq_div_mul, inv_inv (2 : ℝ), ←mul_assoc,
    ←mul_assoc, ←mul_assoc, ←mul_assoc, mul_right_comm _ (q : ℝ), mul_right_comm _ (q : ℝ),
    mul_right_comm _ (q : ℝ), ←div_div_eq_div_mul, one_le_div, mul_right_comm _ (N^2 : ℝ),
    mul_right_comm _ (N^2 : ℝ)],
  { norm_num,
    exact hq q hq'.1 },
  { rw nat.cast_pos,
    have : is_prime_pow q,
    { rw [mem_ppowers_in_set] at hq',
      apply hq'.1.1 },
    exact this.pos },
  refine mul_pos (by norm_num1) (pow_pos (log_pos _) _),
  rwa [nat.one_lt_cast, ←nat.succ_le_iff],
end

-- Proposition 2
theorem circle_method_prop : ∃ c : ℝ,
  ∀ᶠ (N : ℕ) in filter.at_top, ∀ k : ℕ, ∀ K L M: ℝ,  ∀ A ⊆ finset.range (N+1),
  (M ≤ N) → (K < M) → (1 ≤ k) → (2*k ≤ N) →
  (∀ n ∈ A, M ≤ (n:ℝ)) →
  (rec_sum A < 2/k) → ((2:ℝ)/k - 1/M ≤ rec_sum A ) →
  (k ∣ A.lcm id) →
  (∀ q ∈ ppowers_in_set A, ((q:ℝ) ≤ c*A.card) ∧
  ((q:ℝ) ≤ c*L*K^2 / (N*log N)^2)) →
  (∀ (a : ℤ), let I : finset ℤ := (finset.Icc a ⌊(a:ℝ)+K⌋) in
  (((M:ℝ)/log N ≤ ((A.filter (λ (n : ℕ), ∀ x ∈ I, ¬ (↑n ∣ x))).card : ℝ)) ∨
    (∃ x ∈ I, ∀ q : ℕ, (q ∈ interval_rare_ppowers I A L) → ↑q ∣ x)
  ))
  → ∃ S ⊆ A, rec_sum S = 1/k
  :=
sorry
