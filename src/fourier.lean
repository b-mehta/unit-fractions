/-
Copyright (c) 2022 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import defs
import for_mathlib.misc

open_locale big_operators classical real

noncomputable theory

open filter real finset

def integer_count (A : finset ℕ) (k : ℕ) : ℕ :=
(A.powerset.filter (λ S, ∃ (d : ℤ), rec_sum S * k = d)).card

def valid_sum_range (t : ℕ) : finset ℤ :=
finset.Ioc ((- (t : ℤ) / 2)) (t/2)

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

def j (A : finset ℕ) : finset ℤ :=
(valid_sum_range [A]).erase 0

-- types of `h`, `k` might need to change?
def cos_prod (B : finset ℕ) (h : ℤ) (k : ℕ) : ℝ :=
∏ n in B, |cos (π * k * h / n)|

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

lemma jordan_apply {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : 2 * x ≤ sin (π * x) :=
begin
  have : 2 * x ≤ 1,
  { rwa [le_div_iff'] at hx',
    exact zero_lt_two },
  have t := le_sin_mul (by linarith) this,
  rwa [←mul_assoc, div_mul_cancel] at t,
  exact two_ne_zero
end

lemma cos_bound {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
  cos (π * x) ≤ exp (-(2 * x ^ 2)) :=
begin
  have i₁ : cos (π * x) ^ 2 ≤ 1 - (2 * x) ^ 2,
  { rw [cos_sq', sub_le_sub_iff_left],
    exact pow_le_pow_of_le_left (by linarith) (jordan_apply hx hx') _ },
  refine le_of_pow_le_pow 2 (exp_pos _).le zero_lt_two _,
  apply (i₁.trans (one_sub_le_exp_minus_of_pos (sq_nonneg (2 * x)))).trans,
  rw [←exp_nat_mul, nat.cast_two, ←neg_mul_eq_mul_neg, exp_le_exp],
  exact le_of_eq (by ring),
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

lemma int.Ico_succ_right {a b : ℤ} : finset.Ico a (b+1) = finset.Icc a b :=
by { ext x, simp only [finset.mem_Icc, finset.mem_Ico, int.lt_add_one_iff] }

lemma int.Ioc_succ_right {a b : ℤ} (h : a ≤ b) :
  finset.Ioc a (b+1) = insert (b+1) (finset.Ioc a b) :=
begin
  ext x,
  simp only [finset.mem_Ioc, finset.mem_insert],
  rw [le_iff_lt_or_eq, int.lt_add_one_iff, or_comm, and_or_distrib_left, or_congr_left],
  rw and_iff_right_of_imp,
  rintro rfl,
  exact int.lt_add_one_iff.2 h
end

lemma int.insert_Ioc_succ_left {a b : ℤ} (h : a < b) :
  insert (a+1) (finset.Ioc (a+1) b) = finset.Ioc a b :=
begin
  ext x,
  simp only [finset.mem_Ioc, finset.mem_insert],
  rw [or_and_distrib_left, eq_comm, ←le_iff_eq_or_lt, int.add_one_le_iff, and_congr_right'],
  rw or_iff_right_of_imp,
  rintro rfl,
  rwa int.add_one_le_iff,
end

lemma int.Ioc_succ_left {a b : ℤ} (h : a < b) :
  finset.Ioc (a+1) b = (finset.Ioc a b).erase (a+1) :=
begin
  rw [←@int.insert_Ioc_succ_left a b h, finset.erase_insert],
  simp only [finset.left_not_mem_Ioc, not_false_iff],
end

lemma int.Ioc_succ_succ {a b : ℤ} (h : a ≤ b) :
  finset.Ioc (a+1) (b+1) = (insert (b+1) (finset.Ioc a b)).erase (a+1) :=
begin
  rw [int.Ioc_succ_left, int.Ioc_succ_right h],
  rwa int.lt_add_one_iff,
end

lemma finset.sum_erase_eq_sub {α β : Type*} [decidable_eq α] [add_comm_group β]
  {f : α → β} {s : finset α} {a : α} (ha : a ∈ s) :
  ∑ x in s.erase a, f x = (∑ x in s, f x) - f a :=
by rw [←finset.sum_erase_add _ _ ha, add_sub_cancel]

-- note `r` here is different to the `r` in the proof
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

-- shows up in Lemma 4.10
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

lemma lcm_ne_zero_of_zero_not_mem {A : finset ℕ} (hA : 0 ∉ A) : [A] ≠ 0 :=
by rwa [ne.def, finset.lcm_eq_zero_iff, set.image_id, finset.mem_coe]

-- example {a b : ℚ} (ha : a ≠ 0) : a / (b * a) = b⁻¹ :=
-- begin
--   rw [div_eq_mul_inv, mul_inv₀],
-- end

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

lemma orthog_simp {A : finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
  (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
  ∑ h in valid_sum_range [A], (∏ n in A, (1 + exp_circle (k * h / n))).re = [A] :=
begin
  have := congr_arg complex.re (orthog_simp_aux hA hk hS hA'),
  rwa [complex.nat_cast_re, complex.re_sum] at this,
end

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

-- Proposition 2
theorem circle_method_prop : ∃ c : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ k : ℕ, ∀ K L M: ℝ,  ∀ A ⊆ finset.range (N+1),
  (M ≤ N) → (K < M) → (1 ≤ k) → (2*k ≤ N) →
  (∀ n ∈ A, M ≤ (n:ℝ)) →
  (rec_sum A < 2/k) → ((2:ℝ)/k - 1/M ≤ rec_sum A ) →
  (k ∣ A.lcm id) →
  (∀ q ∈ ppowers_in_set A, ((q:ℝ) ≤ c*A.card) ∧
  ((q:ℝ) ≤ c*L*K^2 / (N*log N)^2)) →
  (∀ (a : ℕ), let I : finset ℕ := (finset.Icc a ⌊(a:ℝ)+K⌋₊)
  in
  ( ((M:ℝ)/log N ≤ ((A.filter (λ n, ∀ x ∈ I, ¬ (n ∣ x))).card : ℝ)) ∨
    (∃ x ∈ I, ∀ q : ℕ, (q ∈ interval_rare_ppowers I A L) → q ∣ x)
  ))
  → ∃ S ⊆ A, rec_sum S = 1/k
  :=
sorry
