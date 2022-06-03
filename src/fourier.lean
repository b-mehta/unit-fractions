/-
Copyright (c) 2022 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import defs
import aux_lemmas
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

lemma of_mem_valid_sum_range {t : ℕ} {h : ℤ} :
  h ∈ valid_sum_range t → |(h : ℝ)| ≤ t / 2 :=
begin
  rw [mem_valid_sum_range, and_imp, int.div_lt_iff_lt_mul zero_lt_two,
    int.le_div_iff_mul_le zero_lt_two, le_div_iff (zero_lt_two : (0 : ℝ) < 2), ←int.cast_abs],
  intros h₁ h₂,
  rw [←int.cast_two, ←int.cast_mul, ←abs_two, ←abs_mul, ←int.cast_coe_nat, int.cast_le,
    abs_le],
  exact ⟨h₁.le, h₂⟩
end

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

lemma mem_j (A : finset ℕ) (h : ℤ) :
  h ∈ j A ↔ h ≠ 0 ∧ (-↑[A]) / 2 < h ∧ h ≤ [A]/2 :=
by rw [j, mem_erase, mem_valid_sum_range]

lemma bound_of_mem_j (A : finset ℕ) (h : ℤ) (h' : h ∈ j A) :
  |(h : ℝ)| ≤ [A] / 2 :=
begin
  rw [j, mem_erase] at h',
  exact of_mem_valid_sum_range h'.2,
end

/-- Def 4.3 -/
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
  rw [←div_div, le_div_iff hk'],
  congr' 2,
  rw [←abs_of_pos hk', ←abs_mul, abs_of_pos hk', sub_mul, div_mul_cancel],
  rwa nat.cast_ne_zero,
end

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

/-- Def 4.4 part two -/
def major_arc (A : finset ℕ) (k : ℕ) (K : ℝ) : finset ℤ :=
(j A).filter (λ h, ∃ t, h ∈ major_arc_at A k K t)

lemma j_sdiff_major_arc {A k K} :
  j A \ major_arc A k K = (j A).filter (λ h, ∀ t, h ∉ major_arc_at A k K t) :=
begin
  rw [major_arc, ←filter_not],
  simp
end

/-- Centred at x, width 2 * y -/
def integer_range (x y : ℝ) : finset ℤ := Icc ⌈x - y⌉ ⌊x + y⌋

lemma mem_integer_range_iff {x y : ℝ} {z : ℤ} :
  z ∈ integer_range x y ↔ |x - z| ≤ y :=
by rw [integer_range, mem_Icc, int.le_floor, int.ceil_le, sub_le, ←sub_le_iff_le_add',
  abs_le', neg_sub]

lemma card_integer_range_le {x y : ℝ} (hy : 0 ≤ y) :
  ↑(integer_range x y).card ≤ 2 * y + 1 :=
begin
  rw [integer_range, ←int.cast_coe_nat, int.card_Icc_of_le, int.cast_sub, int.cast_add,
    ←sub_add_eq_add_sub, int.cast_one, add_le_add_iff_right],
  { linarith only [int.le_ceil (x - y), int.floor_le (x + y)] },
  exact (int.ceil_mono (by linarith only [hy])).trans (int.ceil_le_floor_add_one _),
end

-- meaningless
def my_range (x : ℝ) : finset ℤ := integer_range 0 x

lemma mem_my_range_iff {x : ℝ} {y : ℤ} :
  y ∈ my_range x ↔ |(y : ℝ)| ≤ x :=
by rw [my_range, mem_integer_range_iff, abs_sub_comm, sub_zero]

-- meaningless
def my_range' (A : finset ℕ) (k : ℕ) (K : ℝ) : finset ℤ :=
my_range ((K / (2 * ↑k) + ↑(A.lcm id) / 2) / |↑(A.lcm id) / ↑k|)

def I (h : ℤ) (K : ℝ) (k : ℕ) : finset ℤ := integer_range (h * k) (K / 2)

lemma mem_I' {h : ℤ} {K : ℝ} {k : ℕ} {z : ℤ} :
  z ∈ I h K k ↔ |(h * k : ℝ) - z| ≤ K / 2 :=
by rw [I, mem_integer_range_iff]

lemma card_I_le {h K k} (hK : (0 : ℝ) ≤ K) : ↑(I h K k).card ≤ K + 1 :=
(card_integer_range_le (by linarith)).trans (by linarith)

/-- Def 4.5 -/
def minor_arc₁ (A : finset ℕ) (k : ℕ) (K : ℝ) (δ : ℝ) : finset ℤ :=
(j A \ major_arc A k K).filter $
  λ h, δ ≤ (A.filter (λ n, ∀ z ∈ I h K k, ¬↑n ∣ z)).card

def minor_arc₂ (A : finset ℕ) (k : ℕ) (K : ℝ) (δ : ℝ) : finset ℤ :=
(j A \ major_arc A k K) \ minor_arc₁ A k K δ

-- major arc is actually a finite union
lemma major_arc_eq_union {A k K} (hA : 0 ∉ A) (hk : k ≠ 0) :
  major_arc A k K = (my_range' A k K).bUnion (major_arc_at A k K) :=
begin
  ext h,
  simp only [major_arc, mem_bUnion, mem_filter, mem_major_arc_at, exists_prop,
    exists_and_distrib_left, and_self_left, and.congr_right_iff, and_imp, j, mem_erase],
  intros h₁ h₂,
  refine ⟨_, λ ⟨i, _, j⟩, ⟨i, j⟩⟩,
  rintro ⟨i, z⟩,
  refine ⟨i, _, z⟩,
  rw abs_sub_comm at z,
  replace z := (abs_sub_abs_le_abs_sub _ _).trans z,
  rw [sub_le_iff_le_add, mul_div_assoc, abs_mul] at z,
  replace z := z.trans (add_le_add_left (of_mem_valid_sum_range h₂) _),
  rw [←le_div_iff] at z,
  { rwa [my_range', mem_my_range_iff] },
  rw [abs_pos, div_ne_zero_iff, nat.cast_ne_zero, nat.cast_ne_zero],
  exact ⟨lcm_ne_zero_of_zero_not_mem hA, hk⟩,
end

lemma minor_arc₂_eq {A k K δ} :
  minor_arc₂ A k K δ =
    ((j A \ major_arc A k K).filter $ λ h, ↑(A.filter (λ n, ∀ z ∈ I h K k, ¬↑n ∣ z)).card < δ) :=
begin
  ext z,
  simp only [minor_arc₂, minor_arc₁, mem_filter, mem_sdiff, not_and, not_le, and_imp,
    and.congr_right_iff, not_false_iff, forall_true_left, iff_self, implies_true_iff]
  {contextual := tt},
end

def e (x : ℝ) : ℂ := complex.exp (x * (2 * π * complex.I))

lemma e_add {x y : ℝ} : e (x + y) = e x * e y :=
by { rw [e, complex.of_real_add, add_mul, complex.exp_add], refl }

lemma e_int (z : ℤ) : e z = 1 :=
by rw [e, complex.of_real_int_cast, complex.exp_int_mul_two_pi_mul_I]

lemma e_eq_one_iff (x : ℝ) :
  e x = 1 ↔ ∃ (z : ℤ), x = z :=
by simp only [e, complex.exp_eq_one_iff, mul_eq_mul_right_iff, mul_eq_zero, bit0_eq_zero,
    one_ne_zero, complex.of_real_eq_zero, pi_ne_zero, complex.I_ne_zero, ←complex.of_real_int_cast,
    complex.of_real_inj, or_false]

@[simp] lemma e_nat (n : ℕ) : e n = 1 :=
by rw [←e_int n, int.cast_coe_nat]

@[simp] lemma e_zero : e 0 = 1 :=
by rw [←e_nat 0, nat.cast_zero]

lemma e_sum {ι : Type*} {s : finset ι} (f : ι → ℝ) :
  e (∑ i in s, f i) = ∏ i in s, e (f i) :=
by { rw [e, complex.of_real_sum, finset.sum_mul, complex.exp_sum], refl }

lemma e_half_re {x : ℝ} : (e (x / 2)).re = cos (x * π) :=
begin
  rw [←complex.exp_of_real_mul_I_re, e, complex.of_real_div, complex.of_real_bit0,
    complex.of_real_one, complex.of_real_mul],
  ring_nf,
end

lemma abs_e {x : ℝ} : complex.abs (e x) = 1 :=
begin
  rw [e, ←mul_assoc],
  convert complex.abs_exp_of_real_mul_I (x * (2 * π)),
  simp,
end

lemma one_add_e (x : ℝ) : 1 + e x = 2 * e (x / 2) * cos (π * x) :=
begin
  rw [mul_right_comm, complex.of_real_cos, complex.two_cos, e, e, mul_assoc,
    complex.of_real_div, complex.of_real_bit0, complex.of_real_one, ←mul_assoc (x / 2 : ℂ),
    div_mul_cancel (x : ℂ) two_ne_zero', mul_left_comm, mul_comm π, complex.of_real_mul, neg_mul,
    mul_assoc, add_mul, ←complex.exp_add, ←two_mul, ←complex.exp_add, add_left_neg,
    complex.exp_zero, add_comm]
end

lemma abs_one_add_e (x : ℝ) :
  complex.abs (1 + e x) = 2 * |cos (π * x)| :=
by rw [one_add_e, complex.abs_mul, complex.abs_mul, complex.abs_two, abs_e,
    complex.abs_of_real, mul_one]

/-- Lemma 4.6. Note `r` in this statement is different to the `r` in the written proof -/
lemma orthogonality {n m : ℕ} {r s : ℤ} (hm : m ≠ 0) {I : finset ℤ} (hI : I = finset.Ioc r s)
  (hrs₁ : r < s) (hrs₂ : I.card = m) :
  (∑ h in I, e (h * n / m)) * (1 / m) =
    if m ∣ n then 1 else 0 :=
begin
  have hm' : (m : ℝ) ≠ 0, exact_mod_cast hm,
  have hm'' : (m : ℂ) ≠ 0, exact_mod_cast hm',
  split_ifs,
  { simp_rw [mul_div_assoc, ←nat.cast_div h hm', ←int.cast_coe_nat, ←int.cast_mul, e_int],
    rw [sum_const, nat.smul_one_eq_coe, int.cast_coe_nat, one_div, hrs₂, mul_inv_cancel hm''] },
  rw [mul_eq_zero, one_div, inv_eq_zero, nat.cast_eq_zero],
  simp only [hm, or_false],
  set S := ∑ h in I, e (h * n / m),
  have : S * e (n / m) = ∑ h in (finset.Ioc (r + 1) (s + 1)), e (h * n / m),
  { simp only [←finset.image_add_right_Ioc, finset.sum_image, add_left_inj, imp_self,
      implies_true_iff, int.cast_add, add_mul, int.cast_one, one_mul, add_div, e_add,
      finset.sum_mul, hI] },
  rw [int.Ioc_succ_succ hrs₁.le, finset.sum_erase_eq_sub, finset.sum_insert, add_comm,
    add_sub_assoc, sub_eq_zero_of_eq, add_zero, ←hI] at this,
  { apply eq_zero_of_mul_eq_self_right _ this,
    rw [ne.def, e_eq_one_iff, not_exists],
    intros i hi,
    rw [div_eq_iff_mul_eq hm', ←int.cast_coe_nat, ←int.cast_coe_nat, ←int.cast_mul,
      int.cast_inj] at hi,
    rw [←int.coe_nat_dvd, ←hi] at h,
    simpa using h },
  { have : s = m + r,
    { rw [←hrs₂, hI, int.card_Ioc, int.to_nat_sub_of_le hrs₁.le, sub_add_cancel] },
    rw [this, add_assoc, int.cast_add, add_mul, add_div, e_add, int.cast_coe_nat,
      mul_div_cancel_left _ hm', e_nat, one_mul] },
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
  refine (finset.prod_le_pow_card _ _ X _).trans _,
  { intro p,
    rw finset.support_sup,
    rw finset.mem_sup,
    simp only [ne.def, exists_prop, forall_exists_index, and_imp],
    intros x hx hx',
    apply hX,
    rw mem_ppowers_in_set' (nat.prime_of_mem_factorization hx'),
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
  rw [mem_ppowers_in_set' pp hp, finset.finsupp_sup_apply],
  simp only [←finsupp.mem_support_iff, finset.support_sup, finset.mem_sup,
    list.mem_to_finset, exists_prop] at hp,
  obtain ⟨x, hx, -⟩ := hp,
  obtain ⟨n, hn, hn'⟩ := finset.sup_eq_mem (λ a : ℕ, a.factorization p) ⟨_, hx⟩,
  exact ⟨n, hn, hn'.symm⟩,
end

/-- Lemma 4.8 -/
lemma smooth_lcm :
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 ≤ X →
    ∀ (A : finset ℕ), 0 ∉ A → (∀ q ∈ ppowers_in_set A, ↑q ≤ X) →
      ↑[A] ≤ exp (C * X) :=
begin
  obtain ⟨c, hc', hc⟩ := prime_counting_le_const_mul_div_log,
  refine ⟨c, hc', λ X hX₀ A hA hAX, _⟩,
  rcases le_or_lt X 1 with hX | hX,
  { have : ppowers_in_set A = ∅,
    { apply finset.eq_empty_of_forall_not_mem,
      intros q hq,
      have := (hAX q hq).trans hX,
      rw mem_ppowers_in_set at hq,
      apply not_le_of_lt hq.1.one_lt,
      simpa only [nat.cast_le_one] using this },
    rw [ppowers_in_set_eq_empty' this hA, nat.cast_one],
    exact one_le_exp (mul_nonneg hc'.le hX₀) },
  have : ⌊X⌋₊ ≠ 0 := by simp only [ne.def, nat.floor_eq_zero, not_lt, hX.le],
  refine (nat.cast_le.2 (smooth_lcm_aux this (λ q hq, nat.le_floor (hAX q hq)) hA)).trans _,
  simp only [nat.cast_pow],
  refine (pow_le_pow_of_le_left (nat.cast_nonneg _)
    (nat.floor_le (zero_le_one.trans hX.le)) _).trans _,
  have hX₁ := hc X,
  simp only [norm_coe_nat, norm_div, norm_of_nonneg (zero_le_one.trans hX.le),
    norm_of_nonneg (log_nonneg hX.le)] at hX₁,
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
  replace := (pow_card_le_prod Q _ _ two_le).trans (nat.le_of_dvd hn.bot_lt this),
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
    1 / [A] * ∑ h in valid_sum_range [A], ∏ n in A, (1 + e (k * h / n)) :=
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
    rw [mul_comm, mul_one_div, nat.cast_div_char_zero],
    exact finset.dvd_lcm (hS hx) },
  have : ∀ S : finset ℕ, S ∈ A.powerset →
    (if (∃ (z : ℤ), rec_sum S * (k : ℚ) = z) then (1 : ℕ) else 0 : ℂ) =
      1 / [A] * ∑ h in valid_sum_range [A], e (k * h * rec_sum S),
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
    rw [nat.cast_mul, mul_div_assoc, mul_div_assoc, ←mul_assoc, mul_comm (i : ℝ)],
    congr' 2,
    rw [rec_sum, nat.cast_sum, finset.sum_div, rat.cast_sum],
    apply finset.sum_congr rfl,
    intros n hn,
    rw [nat.cast_div_char_zero, rat.cast_div, rat.cast_coe_nat, rat.cast_one, div_div,
      mul_comm, div_mul_right],
    { exact nat.cast_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hA) },
    exact finset.dvd_lcm (hS hn) },
  rw [integer_count, card_eq_sum_ones, nat.cast_sum, sum_filter, finset.sum_congr rfl this,
    ←mul_sum, sum_comm],
  simp_rw [←sum_powerset_prod, ←e_sum, rec_sum, rat.cast_sum, mul_sum,
    rat.cast_div, rat.cast_one, ←div_eq_mul_one_div, rat.cast_coe_nat],
end

lemma integer_bound_thing {d : ℤ} (hd₀ : 0 ≤ d) (hd₁ : d ≠ 1) (hd₂ : d < 2) :
  d = 0 :=
begin
  refine le_antisymm (int.lt_add_one_iff.1 (lt_of_le_of_ne _ hd₁)) hd₀,
  rwa ←int.lt_add_one_iff,
end

lemma orthog_simp_aux {A : finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
  (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
  ∑ h in valid_sum_range [A], (∏ n in A, (1 + e (k * h / n))) = [A] :=
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
  ∑ h in valid_sum_range [A], (∏ n in A, (1 + e (k * h / n))).re = [A] :=
begin
  have := congr_arg complex.re (orthog_simp_aux hA hk hS hA'),
  rwa [complex.nat_cast_re, complex.re_sum] at this,
end

/-- Lemma 4.13 -/
lemma orthog_simp2 {A : finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
  (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k)
  (hA'' : ([A] : ℝ) ≤ 2^(A.card - 1 : ℤ)) :
  ∑ h in j A, (∏ n in A, (1 + e (k * h / n))).re ≤ -2^(A.card - 1 : ℤ) :=
begin
  have hA''' := lcm_ne_zero_of_zero_not_mem hA,
  rw [j, finset.sum_erase_eq_sub (zero_mem_valid_sum_range hA'''), orthog_simp hA hk hS hA'],
  simp only [int.cast_zero, zero_div, mul_zero, e_zero, prod_const],
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
end.

/-- Lemma 4.15 -/
lemma useful_rewrite {A : finset ℕ} {θ : ℝ} :
  (∏ n in A, (1 + e (θ / n))).re =
    2 ^ A.card * cos (π * θ * rec_sum A) * ∏ n in A, cos (π * θ / n) :=
begin
  simp only [←complex.of_real_nat_cast, ←complex.of_real_div, one_add_e,
    finset.prod_mul_distrib, ←mul_div_assoc],
  rw [prod_const, ←nat.cast_two, ←nat.cast_pow, ←complex.of_real_prod, mul_comm,
    complex.of_real_mul_re, ←complex.of_real_nat_cast, complex.of_real_mul_re, ←e_sum,
    nat.cast_pow, ←finset.sum_div, nat.cast_two, e_half_re, mul_comm, rec_sum, mul_assoc π,
    rat.cast_sum, mul_sum, ←mul_comm π],
  simp only [rat.cast_div, rat.cast_one, rat.cast_coe_nat, mul_one_div],
end

@[to_additive]
lemma prod_major_arc_eq {α : Type*} [comm_monoid α] {A : finset ℕ} {k : ℕ} {K : ℝ}
  (hA : 0 ∉ A) (hk : k ≠ 0) (hA' : K < [A]) {f : ℤ → α} :
  ∏ h in major_arc A k K, f h = ∏ t in my_range' A k K, ∏ h in major_arc_at A k K t, f h :=
begin
  rw [←finset.prod_bUnion, ←major_arc_eq_union hA hk],
  refine (majorarcs_disjoint hk hA').subset (set.subset_univ _),
end

def jt (A : finset ℕ) (k : ℕ) (K : ℝ) (t : ℝ) : finset ℤ :=
(my_range (K / (2 * k))).filter (λ h, ∃ i ∈ j A, ↑i - t * [A] / k = h)

@[to_additive]
lemma prod_major_arc_at_eq {α : Type*} [comm_monoid α] {A : finset ℕ} {k : ℕ} {K : ℝ} {t}
  {f : ℤ → α} (hk : k ∣ [A]) :
  ∏ h in major_arc_at A k K t, f h = ∏ r in jt A k K t, f (t * [A] / k + r) :=
begin
  have : (k : ℤ) ∣ t * [A],
  { apply dvd_mul_of_dvd_right,
    rwa int.coe_nat_dvd },
  symmetry,
  refine prod_bij (λ h _, t * [A] / k + h) _ (λ _ _, rfl) _ _,
  { simp only [jt, mem_filter, and_imp, forall_exists_index, and_imp, exists_prop, int.cast_add,
      mem_major_arc_at, mem_my_range_iff, ←int.cast_mul, ←int.cast_coe_nat,
      ←int.cast_div_char_zero this, ←int.cast_sub, int.cast_inj, add_tsub_cancel_left],
    rintro a ha b hb rfl,
    simp [ha, hb, -int.cast_sub, ←int.cast_coe_nat] },
  { simp only [add_right_inj, imp_self, implies_true_iff, forall_const] },
  simp only [mem_major_arc_at, exists_prop, and_imp, jt, mem_filter, mem_my_range_iff, and_self,
    ←int.cast_div_char_zero this, ←int.cast_coe_nat, ←int.cast_mul, ←int.cast_sub, implies_true_iff,
    ←sub_eq_iff_eq_add', int.cast_inj, exists_eq_right, exists_eq_right', sub_left_inj]
    {contextual := tt},
end

lemma majorarcs_at {K : ℝ} {A : finset ℕ} {k : ℕ} (hk : k ≠ 0) (hk' : k ∣ [A]) {t : ℤ} :
  ∑ (h : ℤ) in major_arc_at A k K t, (∏ (n : ℕ) in A, (1 + e (↑k * ↑h / ↑n))).re =
    2 ^ A.card * ∑ r in jt A k K t, cos (π * k * r * rec_sum A) * ∏ n in A, cos (π * (k * r) / n) :=
begin
  have : (k : ℤ) ∣ t * [A],
  { apply dvd_mul_of_dvd_right,
    rwa int.coe_nat_dvd },
  have hk'' : (k : ℝ) ≠ 0 := nat.cast_ne_zero.2 hk,
  rw sum_major_arc_at_eq hk',
  simp only [int.cast_add, int.cast_div_char_zero this, mul_add, int.cast_coe_nat, mul_div_assoc',
    mul_div_cancel_left _ hk'', add_div, e_add],
  have : ∀ n ∈ A, (n : ℤ) ∣ t * [A],
  { intros n hn,
    apply dvd_mul_of_dvd_right,
    rw int.coe_nat_dvd,
    apply dvd_lcm hn },
  conv in (_ / _) { rw [←int.cast_coe_nat, ←@int.cast_div_char_zero ℝ _ _ _ _ (this _ H)] },
  simp only [e_int, one_mul, ←int.cast_coe_nat k, ←int.cast_mul, useful_rewrite,
    mul_assoc, ←finset.mul_sum],
end

lemma cos_nonneg_of_abs_le {x : ℝ} (hx : |x| ≤ π / 2) : 0 ≤ cos x :=
cos_nonneg_of_neg_pi_div_two_le_of_le (neg_le_of_abs_le hx) (le_of_abs_le hx)

/-- Lemma 4.16 -/
lemma majorarcs {M K : ℝ} {A : finset ℕ} (hM : ∀ n : ℕ, n ∈ A → M ≤ n) (hK : 0 < K)
  (hKM : K < M) {k : ℕ} (hk' : k ∣ [A]) (hA₁ : (2 : ℝ) - k / M ≤ k * rec_sum A)
  (hA₂ : (k : ℝ) * rec_sum A ≤ 2) (hA₃ : A.nonempty) :
  (0 : ℝ) ≤ ∑ h in major_arc A k K, (∏ n in A, (1 + e (k * h / n))).re :=
begin
  have hA : 0 ∉ A, -- is it easier to allow this as an input?
  { intro hA, simpa using (hKM.trans_le (hM 0 hA)).trans hK },
  have : K < [A],
  { apply hKM.trans_le,
    obtain ⟨n, hn⟩ := hA₃,
    refine (hM n hn).trans (nat.cast_le.2 _),
    exact nat.le_of_dvd (lcm_ne_zero_of_zero_not_mem hA).bot_lt (dvd_lcm hn) },
  have hk : k ≠ 0 := ne_zero_of_dvd_ne_zero (lcm_ne_zero_of_zero_not_mem hA) hk',
  rw sum_major_arc_eq hA hk this,
  simp only [majorarcs_at hk hk', ←finset.mul_sum, jt, sum_filter],
  rw sum_comm,
  simp only [←sum_filter, sum_const, nsmul_eq_mul],
  refine mul_nonneg (pow_nonneg zero_le_two _) (sum_nonneg _),
  intros r hr,
  rw [mem_my_range_iff] at hr,
  refine mul_nonneg (nat.cast_nonneg _) (mul_nonneg _ _),
  { have : cos (π * k * r * rec_sum A) = cos (π * r * (k * rec_sum A - 2)),
    { rw [mul_sub, mul_mul_mul_comm, ←mul_assoc, mul_comm π r, mul_assoc ↑r π, mul_comm π 2,
        cos_sub_int_mul_two_pi] },
    rw [this, ←cos_neg, ←mul_neg, neg_sub],
    apply cos_nonneg_of_abs_le,
    rw sub_le at hA₁,
    rw ←sub_nonneg at hA₂,
    rw [abs_mul, abs_mul, abs_of_nonneg pi_pos.le, abs_of_nonneg hA₂],
    refine (mul_le_mul_of_nonneg_left hA₁ (mul_nonneg pi_pos.le (abs_nonneg _))).trans _,
    rw mul_right_comm,
    have hM' : 0 < M := hK.trans hKM,
    refine (mul_le_mul_of_nonneg_left hr (mul_nonneg pi_pos.le
      (div_nonneg (nat.cast_nonneg _) hM'.le))).trans _,
    have : 0 < (k : ℝ) := by simpa using hk.bot_lt,
    simp only [div_div, div_mul_eq_mul_div, mul_div_assoc', this, div_le_div_iff,
      hM', mul_pos, zero_lt_two],
    convert mul_le_mul_of_nonneg_left hKM.le
      (mul_nonneg zero_le_two (mul_nonneg pi_pos.le (nat.cast_nonneg k))) using 1;
    ring_nf },
  { apply prod_nonneg,
    intros n hn,
    apply cos_nonneg_of_abs_le,
    have : 0 < 2 * (k : ℝ) := mul_pos zero_lt_two (by simpa using hk.bot_lt),
    replace hr := ((le_div_iff this).1 hr).trans (hKM.le.trans (hM _ hn)),
    have : 0 < |(n : ℝ)| := abs_pos_of_pos (hK.trans (hKM.trans_le (hM n hn))),
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg pi_pos.le, div_le_div_iff this zero_lt_two,
      nat.abs_cast k, nat.abs_cast n, mul_assoc],
    apply mul_le_mul_of_nonneg_left _ pi_pos.le,
    convert hr using 1,
    ring_nf }
end

@[to_additive]
lemma prod_sdiff' {α M : Type*} [decidable_eq α] [comm_group M] (f : α → M) (s₁ s₂ : finset α)
  (h : s₁ ⊆ s₂) :
  ∏ x in (s₂ \ s₁), f x = (∏ x in s₂, f x) / ∏ x in s₁, f x :=
by rw [eq_div_iff_mul_eq', prod_sdiff h]

/-- Lemma 4.17 -/
lemma minor_lbound {M : ℝ} {A : finset ℕ} {K : ℝ} {k : ℕ}
  (hM : ∀ n ∈ A, M ≤ ↑n) (hK : 0 < K) (hKM : K < M) (hkA : k ∣ [A]) (hk : k ≠ 0)
  (hA₁ : (2 : ℝ) - k / M ≤ k * rec_sum A) (hA₂ : (k : ℝ) * rec_sum A < 2)
  (hA₃ : A.nonempty) (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA₄ : ([A] : ℝ) ≤ 2^(A.card - 1 : ℤ)) :
  1 / 2 ≤ ∑ h in j A \ major_arc A k K, cos_prod A (h * k) :=
begin
  have hA : 0 ∉ A,
  { intro hA, simpa using (hKM.trans_le (hM 0 hA)).trans hK },
  suffices :
    (2 : ℝ) ^ (A.card - 1 : ℤ) ≤
      |∑ h in j A \ major_arc A k K, (∏ n in A, (1 + e (k * h / n))).re|,
  { rw ←complex.re_sum at this,
    replace := (this.trans (complex.abs_re_le_abs _)).trans (abv_sum_le_sum_abv _ _),
    simp only [complex.abs_prod, abs_one_add_e, prod_mul_distrib, mul_div_assoc',
      prod_const, ←finset.mul_sum, ←int.cast_coe_nat k, ←int.cast_mul, mul_comm (k : ℤ)] at this,
    rwa [←div_le_iff', ←zpow_coe_nat, ←zpow_sub₀, sub_sub_cancel_left, zpow_neg, zpow_one,
      ←one_div] at this,
    { exact two_ne_zero },
    exact pow_pos zero_lt_two _ },
  have hA₂' : rec_sum A < 2 / ↑k,
  { rw [lt_div_iff'],
    { exact_mod_cast hA₂ },
    rwa [nat.cast_pos, pos_iff_ne_zero] },
  rw [le_abs', sum_sdiff'],
  { left,
    linarith [majorarcs hM hK hKM hkA hA₁ hA₂.le hA₃, orthog_simp2 hA hk hS hA₂' hA₄] },
  apply filter_subset,
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
  rw [neg_mul, div_mul_comm, ←div_pow, ←mul_comm (2 : ℝ), mul_div_assoc,
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

lemma minor1_bound_aux :
  ∀ᶠ N : ℕ in filter.at_top,
    ∀ {K M T : ℝ} {A : finset ℕ},
    8 ≤ M → 0 ∉ A → 0 < T →
    (∀ q ∈ ppowers_in_set A, ↑q ≤ (T * K^2) / (N^2 * log N)) →
      ↑[A] ≤ exp ((T * K^2) / (4 * N^2)) :=
begin
  obtain ⟨C, hC₀, hC⟩ := smooth_lcm,
  filter_upwards [filter.eventually_gt_at_top 1,
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top) (filter.eventually_ge_at_top (4 * C))]
    with N hN₁ hN' K M T A hM hA hT hA₄,
  change 4 * C ≤ log N at hN',
  have hN₁' : (1 : ℝ) < N := nat.one_lt_cast.2 hN₁,
  have h₁ : (0 : ℝ) < N ^ 2 := pow_pos (zero_lt_one.trans hN₁') _,
  have : 0 < (N : ℝ) ^ 2 * log N := mul_pos h₁ (log_pos hN₁'),
  refine (hC _ (div_nonneg _ _) _ hA hA₄).trans _,
  { exact mul_nonneg (by linarith) (sq_nonneg _) },
  { exact mul_nonneg (sq_nonneg _) (log_nonneg hN₁'.le) },
  rw [exp_le_exp, mul_div_assoc', div_le_div_iff this (mul_pos (show (0 : ℝ) < 4, by norm_num) h₁),
    mul_right_comm, mul_comm (T * K ^ 2), mul_comm _ (log _), ←mul_assoc C, mul_assoc,
    mul_assoc (log _), mul_comm C],
  exact mul_le_mul_of_nonneg_right hN' (mul_nonneg (sq_nonneg _) (mul_nonneg hT.le (sq_nonneg _))),
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

lemma missing_bridge_sum {A : finset ℕ} {t : ℤ} {K M : ℝ} {I : finset ℤ} {tn : ℕ → ℤ} (hK : 0 < K)
  (hI : I = finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
  (htn₁ : ∀ (n : ℕ), n ∈ A → tn n % ↑n = t % ↑n)
  (hI' : M ≤ ((A.filter (λ (n : ℕ), ∀ x ∈ I, ¬ (↑n ∣ x))).card : ℝ)) :
  M * (K^2 / 4) ≤ ∑ n in A, (tn n : ℝ) ^ 2 :=
begin
  let A' := (A.filter (λ (n : ℕ), ∀ (x : ℤ), x ∈ I → ¬↑n ∣ x)),
  have : A' ⊆ A := filter_subset _ _,
  refine le_trans _ (sum_le_sum_of_subset_of_nonneg this (λ _ _ _, sq_nonneg _)),
  have : M * (K^2 / 4) ≤ A'.card * (K / 2)^2 :=
    mul_le_mul hI' (by norm_num) (div_nonneg (sq_nonneg _) (by norm_num)) (nat.cast_nonneg _),
  apply this.trans _,
  rw ←nsmul_eq_mul,
  apply finset.card_nsmul_le_sum,
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
  exact this (htn₁ _ hn.1),
end

lemma missing_bridge (A : finset ℕ) {N : ℕ} {t : ℤ} {K M : ℝ} (hA' : 0 ∉ A) (hA : ∀ n ∈ A, n ≤ N)
  {I : finset ℤ} (hK : 0 < K) (hI : I = finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
  (hI' : M ≤ ((A.filter (λ (n : ℕ), ∀ x ∈ I, ¬ (↑n ∣ x))).card : ℝ)) :
  cos_prod A t ≤ exp (- (M * K^2 / (2 * N^2))) :=
begin
  have : ∀ n : ℕ, ∃ (tn : ℤ), n ∈ A → tn % n = t % n ∧ |tn| ≤ n / 2,
  { intro n,
    by_cases n ∈ A,
    { have hn' : n ≠ 0 := ne_of_mem_of_not_mem h hA',
      obtain ⟨tn, htn⟩ := exists_representative t hn',
      exact ⟨tn, λ _, htn⟩ },
    simp [h] },
  choose tn htn₁ htn₂ using this,
  refine (cos_prod_bound t hA' hA tn htn₁ _).trans _,
  { intros n hn,
    have z := htn₂ _ hn,
    rw [←int.coe_nat_one, ←int.coe_nat_bit0, ←int.coe_nat_div, ←@int.cast_le ℝ, int.cast_abs,
      int.cast_coe_nat] at z,
    exact z.trans (nat.cast_div_le.trans (by simp)) },
  set A' := A.filter (λ (n : ℕ), ∀ x ∈ my_range (K / 2), ¬ (↑n ∣ (x - t))),
  have := missing_bridge_sum hK hI htn₁ hI',
  apply le_trans (exp_le_exp.2 (mul_le_mul_of_nonpos_left this _)) _,
  { exact neg_nonpos.2 (div_nonneg zero_le_two (sq_nonneg _)) },
  apply le_of_eq,
  rw [neg_mul, mul_div_assoc', div_mul_div_comm, mul_comm _ (4 : ℝ), ←div_mul_div_comm,
    mul_comm (2 : ℝ), ←div_div, div_eq_mul_inv _ (2 : ℝ), mul_comm _ (2⁻¹ : ℝ)],
  norm_num,
end

/-- Lemma 4.19 -/
lemma minor1_bound :
  ∀ᶠ N : ℕ in filter.at_top,
    ∀ {K M T : ℝ} (k : ℕ) {A : finset ℕ},
    8 ≤ M → A.nonempty → (∀ n ∈ A, M ≤ ↑n) → 0 < K → 0 < T →
    (∀ n ∈ A, n ≤ N) →
    (∀ q ∈ ppowers_in_set A, ↑q ≤ (T * K^2) / (N^2 * log N)) →
      ∑ h in minor_arc₁ A k K T, cos_prod A (h * k) ≤ 8⁻¹ :=
begin
  filter_upwards [minor1_bound_aux] with N hN K M T k A hM hA₁ hA₃ hK hT hA₂ hA₄,
  have hA : 0 ∉ A,
  { intro hA,
    have z := hM.trans (hA₃ _ hA),
    norm_num at z },
  suffices : ∀ h ∈ minor_arc₁ A k K T, cos_prod A (h * k) ≤ ([A] ^ 2)⁻¹,
  { apply (sum_le_card_nsmul _ _ _ this).trans _,
    have h₁ : (minor_arc₁ A k K T).card ≤ [A],
    { refine (card_le_of_subset ((filter_subset _ _).trans (sdiff_subset _ _))).trans _,
      refine (card_le_of_subset (erase_subset _ _)).trans _,
      rw card_valid_sum_range },
    rw ←@nat.cast_le ℝ at h₁,
    have h₂ : (8 : ℝ) ≤ [A],
    { obtain ⟨n, hn⟩ := hA₁,
      refine (hM.trans (hA₃ n hn)).trans _,
      exact_mod_cast (nat.le_of_dvd (lcm_ne_zero_of_zero_not_mem hA).bot_lt (dvd_lcm hn)) },
    rw [nsmul_eq_mul, ←one_div (8 : ℝ), le_div_iff, mul_right_comm, ←le_div_iff, one_div,
      inv_inv, sq],
    { exact mul_le_mul h₁ h₂ (by norm_num1) (nat.cast_nonneg _) },
    { rw [inv_pos, sq_pos_iff, nat.cast_ne_zero],
      exact lcm_ne_zero_of_zero_not_mem hA },
    norm_num1 },
  have z : 0 < ([A] : ℝ),
  { rw [nat.cast_pos, pos_iff_ne_zero],
    apply lcm_ne_zero_of_zero_not_mem hA },
  have : 0 < N,
  { obtain ⟨n, hn⟩ := hA₁,
    refine (show 0 < 8, by norm_num1).trans_le _,
    exact_mod_cast (hM.trans (hA₃ _ hn)).trans (nat.cast_le.2 (hA₂ _ hn)) },
  intros h hh,
  rw [minor_arc₁, mem_filter] at hh,
  let I : finset ℤ := finset.Icc ⌈(h : ℝ) * k - K / 2⌉ ⌊(h : ℝ) * k + K / 2⌋,
  have hI : finset.Icc ⌈(h : ℝ) * k - K / 2⌉ ⌊(h : ℝ) * k + K / 2⌋ =
    Icc ⌈↑(h * k) - K / 2⌉ ⌊↑(h * k) + K / 2⌋,
  { simp },
  refine (missing_bridge A hA hA₂ hK hI hh.2).trans _,
  rw [exp_neg, inv_le_inv (exp_pos _) (pow_pos z _)],
  refine (pow_le_pow_of_le_left z.le (hN hM hA hT hA₄) _).trans _,
  rw [←rpow_nat_cast, ←exp_mul, exp_le_exp, nat.cast_two, mul_comm, mul_div_assoc',
    ←div_mul_div_comm, mul_comm (2 : ℝ), ←div_div, div_eq_mul_inv _ (2 : ℝ), ←mul_comm (2 : ℝ)⁻¹],
  norm_num,
end

lemma prod_swapping {A : finset ℕ} (x : ℕ → ℝ) :
  ∏ (n : ℕ) in A, ∏ (q : ℕ) in (ppowers_in_set A).filter (λ q, n ∈ local_part A q), x n =
  ∏ (q : ℕ) in ppowers_in_set A, ∏ (n : ℕ) in local_part A q, x n :=
begin
  simp only [prod_filter],
  rw finset.prod_comm,
  simp only [←prod_filter, filter_mem_eq_inter, (inter_eq_right_iff_subset _ _).2 local_part_subset]
end

lemma minor2_ind_bound_part_one {N : ℕ} {A : finset ℕ} {t : ℤ}
  (hA : 0 ∉ A) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N) :
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
    exact finset.prod_rpow _ (λ n hn, abs_nonneg _) },
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

/-- Lemma 4.20 -/
lemma minor2_ind_bound {N : ℕ} {A : finset ℕ} {t : ℤ} {K L : ℝ} (I : finset ℤ)
  (hA : 0 ∉ A) (hK : 0 < K) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N)
  (hI : I = finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
  (hq : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N^2 * (log N)^2)) :
  cos_prod A t ≤ N ^ (-4 * (ppowers_in_set A \ interval_rare_ppowers I A L).card : ℝ) :=
begin
  apply (minor2_ind_bound_part_one hA hA' hN).trans _,
  rw ←prod_sdiff (interval_rare_ppowers_subset I L),
  suffices : ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
              cos_prod (local_part A q) t ≤ N ^ (-8 * log N),
  { have hq : ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
              cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ N ^ (-4 : ℝ),
    { intros q hq,
      refine (rpow_le_rpow cos_prod_nonneg (this q hq) (inv_nonneg.2 _)).trans _,
      { exact mul_nonneg zero_le_two (log_nonneg (nat.one_le_cast.2 (one_le_two.trans hN))) },
      rw [←rpow_mul (nat.cast_nonneg _), ←div_eq_mul_inv, mul_comm (2 : ℝ),
        ←div_div, mul_div_cancel _ (log_pos _).ne'],
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
  simp only [interval_rare_ppowers, mem_sdiff, mem_filter, not_and, not_lt] at hq',
  replace hq' := and.intro hq'.1 (hq'.2 hq'.1),
  refine (missing_bridge (local_part A q) (zero_mem_local_part_iff hA)
    (λ _ n, hA' _ (filter_subset _ _ n)) hK hI hq'.2).trans _,
  have : 0 < (N : ℝ) := nat.cast_pos.2 (zero_lt_two.trans_le hN),
  rw [←le_log_iff_exp_le (rpow_pos_of_pos this _), log_rpow this, neg_mul, neg_mul, neg_le_neg_iff,
    div_mul_eq_mul_div, div_div, mul_comm (q : ℝ), ←div_div, le_div_iff,
    mul_comm, mul_assoc, ←sq, ←le_div_iff, div_div, mul_mul_mul_comm, ←mul_assoc],
  { norm_num,
    exact hq q hq'.1 },
  { refine mul_pos (by norm_num1) (pow_pos (log_pos _) _),
    rwa [nat.one_lt_cast, ←nat.succ_le_iff] },
  rw nat.cast_pos,
  rw [mem_ppowers_in_set] at hq',
  exact hq'.1.1.pos,
end

-- lemma counting_lemma {K L M : ℝ} {k : ℕ} {A : finset ℕ} {m₂ : finset ℤ}
--   (D : finset ℕ) (hA : 0 ∉ A)
--   (hK : 0 < K) (hKM : K < M) (hL : 0 < L) (hk : k ≠ 0)
--   (z : ∀ h ∈ m₂, ∃ x ∈ I h K k, ∀ q ∈ interval_rare_ppowers (I h K k) A L, ↑q ∣ x) :
--   ((m₂.filter (λ h, interval_rare_ppowers (I h K k) A L = D)).card : ℝ) ≤
--     M * (k * [A]) / [D] :=
-- begin
--   sorry
-- end

lemma powerset_sum_pow {α : Type*} {s : finset α} {x : ℝ} :
  ∑ t in s.powerset, x ^ t.card = (1 + x) ^ s.card :=
begin
  refine finset.induction_on s (by simp) (λ a s has ih, _),
  rw [sum_powerset_insert has, ←sum_add_distrib, card_insert_of_not_mem has, pow_succ, ←ih,
    mul_sum],
  refine sum_congr rfl _,
  intros y hy,
  rw [card_insert_of_not_mem (λ z, has (mem_powerset.1 hy z)), pow_succ, add_mul, one_mul],
end

lemma powerset_sum_pow' {α : Type*} [decidable_eq α] {s : finset α} {x : ℝ} :
  ∑ t in s.powerset, x ^ (s \ t).card = (1 + x) ^ s.card :=
begin
  convert powerset_sum_pow using 1,
  have : ∀ t ∈ s.powerset, s \ (s \ t) = t,
  { simp [inter_eq_right_iff_subset] },
  exact sum_bij' (λ t _, s \ t) (by simp) (λ _ _, rfl) (λ t _, s \ t) (by simp) this this,
end

lemma lcm_Q {A : finset ℕ} (hA : 0 ∉ A) : [ppowers_in_set A] = [A] :=
begin
  apply nat.dvd_antisymm,
  { refine finset.lcm_dvd_iff.2 (λ i hi, _),
    obtain ⟨p, k, hp, hk, rfl⟩ := (is_prime_pow_nat_iff _).1 (mem_ppowers_in_set.1 hi).1,
    simp only [mem_ppowers_in_set' hp hk.ne', mem_singleton, exists_prop, exists_eq_left] at hi,
    obtain ⟨n, hn, rfl⟩ := hi,
    apply (nat.pow_factorization_dvd _ _).trans (finset.dvd_lcm hn) },
  refine finset.lcm_dvd_iff.2 (λ n hn, _),
  have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA,
  have h : [ppowers_in_set A] ≠ 0 := lcm_ne_zero_of_zero_not_mem zero_not_mem_ppowers_in_set,
  rw [id.def, nat.dvd_iff_prime_pow_dvd_dvd],
  intros p k hp z,
  rw hp.pow_dvd_iff_le_factorization hn' at z,
  have : p ^ n.factorization p ∣ [ppowers_in_set A],
  { rcases eq_or_ne (n.factorization p) 0 with hnp | hnp,
    { simp [hnp] },
    apply finset.dvd_lcm,
    rw mem_ppowers_in_set' hp hnp,
    exact ⟨_, hn, rfl⟩ },
  exact (pow_dvd_pow _ z).trans this,
end

lemma d_strict_subset {K L δ : ℝ} {k : ℕ} {A : finset ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
  (z : ∀ h ∈ minor_arc₂ A k K δ,
    ∃ x ∈ I h K k, ↑[interval_rare_ppowers (I h K k) A L] ∣ x) :
  (minor_arc₂ A k K δ).filter (λ h, interval_rare_ppowers (I h K k) A L ⊂ ppowers_in_set A)
    = minor_arc₂ A k K δ :=
begin
  rw filter_true_of_mem,
  intros h hh,
  simp only [filter_subset, finset.ssubset_iff_subset_ne, interval_rare_ppowers_subset, true_and],
  intro hD,
  obtain ⟨x, hx, hx'⟩ := z h hh,
  simp only [mem_I'] at hx,
  simp only [minor_arc₂_eq, mem_filter, j_sdiff_major_arc, mem_major_arc_at' hk, not_and_distrib,
    forall_or_distrib_left, and_or_distrib_left, and_not_self, false_or, not_le] at hh,
  have := hh.1.2 (x / [interval_rare_ppowers (I h K k) A L]),
  rw [←lcm_Q hA, ←hD, ←int.cast_coe_nat [interval_rare_ppowers (I h K k) A L],
    ←int.cast_mul, mul_comm (x / _), int.mul_div_cancel' hx'] at this,
  apply not_lt_of_le hx this,
end

lemma cast_lcm {x y : ℕ} : (lcm x y : ℤ) = lcm (x : ℤ) y :=
by rw [←int.coe_lcm, int.coe_nat_lcm, lcm_eq_nat_lcm]

lemma finset.cast_lcm {x : finset ℕ} : ((x.lcm id : ℕ) : ℤ) = x.lcm coe :=
(fold_hom (λ y z, cast_lcm)).symm

lemma cast_lcm_dvd {x : finset ℕ} {z : ℤ} (h : ∀ i ∈ x, ↑i ∣ z) : ↑[x] ∣ z :=
by { rw finset.cast_lcm, apply finset.lcm_dvd h }

lemma ssubsets_subset_powerset {α : Type*} [decidable_eq α] {s : finset α} :
  s.ssubsets ⊆ s.powerset :=
finset.erase_subset _ _

lemma thing_le_four {N : ℕ} : ((N : ℝ)⁻¹ + 1) ^ N ≤ 4 :=
begin
  rcases eq_or_ne N 0 with rfl | hN,
  { norm_num },
  refine le_trans _ (exp_one_lt_d9.le.trans (by norm_num)),
  refine (pow_le_pow_of_le_left _ (add_one_le_exp _) _).trans _,
  { simp [add_nonneg] },
  rw [←rpow_nat_cast, ←exp_mul, inv_mul_cancel],
  simpa
end

lemma ppowers_in_set_le {N : ℕ} {A : finset ℕ} (hA' : ∀ (n : ℕ), n ∈ A → n ≤ N) :
  ∀ q ∈ ppowers_in_set A, 1 ≤ q ∧ q ≤ N :=
begin
  intros x hx,
  simp only [ppowers_in_set, mem_bUnion, nat.mem_divisors, mem_filter, and_assoc] at hx,
  obtain ⟨n, hn, hx, hn', hx', -⟩ := hx,
  simp only [hx'.one_lt.le, true_and],
  apply le_trans (nat.le_of_dvd hn'.bot_lt hx) (hA' _ hn)
end

lemma minor2_bound_end {k : ℕ} {A : finset ℕ} (N : ℕ)
  (hN : 2 ≤ N)
  (hkN : k ≤ N / 192)
  (hA' : ∀ (n : ℕ), n ∈ A → n ≤ N) :
  6 * (k : ℝ) * N⁻¹ * ∑ x in (ppowers_in_set A).ssubsets, N⁻¹ ^ (ppowers_in_set A \ x).card ≤ 8⁻¹ :=
begin
  have : (ppowers_in_set A).card ≤ N,
  { suffices : ppowers_in_set A ⊆ finset.Icc 1 N,
    { simpa using finset.card_le_of_subset this },
    intros x hx,
    simp [mem_Icc, ppowers_in_set_le hA' x hx] },
  refine le_trans (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
    ssubsets_subset_powerset (by simp [rpow_nonneg_of_nonneg]))
      (by simp [mul_nonneg, show (0 : ℝ) ≤ 6, by norm_num])) _,
  rw [powerset_sum_pow', add_comm],
  refine le_trans (mul_le_mul_of_nonneg_left ((pow_le_pow (by simp) this).trans thing_le_four)
    (by simp [mul_nonneg, show (0 : ℝ) ≤ 6, by norm_num])) _,
  rw nat.le_div_iff_mul_le' (by norm_num : 0 < 192) at hkN,
  rw [mul_right_comm, ←div_eq_mul_inv, ←one_div, div_le_div_iff _ (show (0 : ℝ) < 8, by norm_num)],
  { norm_cast,
    linarith only [hkN] },
  rw nat.cast_pos,
  linarith
end.

lemma count_multiples {m n : ℕ} (hm : 1 ≤ m) :
  ((finset.Icc 1 n).filter (λ k, m ∣ k)).card = n / m :=
begin
  have : (finset.Icc 1 (n / m)).card = n / m,
  { simp only [nat.card_Icc, nat.add_succ_sub_one, add_zero] },
  rw ←this,
  refine (card_congr (λ i _, i * m) _ _ _).symm,
  { intros i hi,
    refine mem_filter.2 ⟨mem_Icc.2 ⟨one_le_mul (mem_Icc.1 hi).1 hm, _⟩, dvd_mul_left _ _⟩,
    exact (nat.le_div_iff_mul_le i n hm).1 (mem_Icc.1 hi).2 },
  { simp [(zero_lt_one.trans_le hm).ne'] },
  simp only [mem_filter, mem_Icc, exists_prop, and_imp, nat.le_div_iff_mul_le _ _ hm,
    mul_comm _ m],
  rintro _ h₁ h₂ ⟨z, rfl⟩,
  refine ⟨z, ⟨_, h₂⟩, rfl⟩,
  rw [nat.succ_le_iff] at h₁ ⊢,
  exact pos_of_mul_pos_left h₁ zero_le',
end

lemma count_multiples' {m : ℕ} {n : ℝ} (hm : 1 ≤ m) (hn : 0 ≤ n) :
  ↑((finset.Icc 1 ⌊n⌋₊).filter (λ k, m ∣ k)).card ≤ n / m :=
begin
  rw [count_multiples hm],
  exact nat.cast_div_le.trans (div_le_div_of_le_of_nonneg (nat.floor_le hn) (nat.cast_nonneg _)),
end

lemma count_real_multiples' {m : ℕ} {x y : ℝ} (hxy : x ≤ y) (hm : 1 ≤ m) :
  ↑((finset.Icc ⌈x⌉ ⌊y⌋).filter (λ k, ↑m ∣ k)).card ≤ (y - x) / m + 1 :=
begin
  have hm' : 0 < (m : ℝ), { rwa [nat.cast_pos] },
  have hm'' : 0 < ((m : ℤ) : ℝ), { rwa [int.cast_coe_nat] },
  have : ((finset.Icc ⌈x⌉ ⌊y⌋).filter (λ k, ↑m ∣ k)).card ≤ ((finset.Icc ⌈x / m⌉ ⌊y / m⌋)).card,
  { refine finset.card_le_card_of_inj_on (λ i, i / m) _ _,
    { simp only [mem_filter, mem_Icc, and_imp, int.ceil_le, int.le_floor, le_div_iff, hm'',
        div_le_iff, ←int.cast_coe_nat, ←int.cast_mul, int.div_mul_cancel, implies_true_iff,
        and_self] {contextual := tt} },
    simp only [mem_filter, and_imp],
    rintro a₁ - ha₁ a₂ - ha₂ h,
    rw [←int.div_mul_cancel ha₁, h, int.div_mul_cancel ha₂] },
  refine (nat.cast_le.2 this).trans _,
  rw [←int.cast_coe_nat, int.card_Icc_of_le, int.cast_sub, int.cast_add, int.cast_one],
  { rw sub_div,
    linarith [int.floor_le (y / m), int.le_ceil (x / m)] },
  exact (int.ceil_mono (by rwa div_le_div_right hm')).trans (int.ceil_le_floor_add_one _),
end

lemma count_real_multiples {m : ℕ} {K : ℝ} {t : ℤ} (hK : 0 < K) (hm : 1 ≤ m) :
  ↑((integer_range t K).filter (λ k, ↑m ∣ k)).card ≤ (2 * K) / m + 1 :=
begin
  apply (count_real_multiples' _ hm).trans _,
  rw [sub_le_iff_le_add, add_assoc], refine le_add_of_nonneg_right (le_of_lt _),
  refine add_pos hK hK,
  rw [← sub_add, add_sub_right_comm, sub_self, zero_add, ← two_mul],
end

lemma candidate_count_one {N : ℕ} {K L T : ℝ} {k : ℕ} {A : finset ℕ} {D : finset ℕ}
  (hN : 2 ≤ N) (hA : 0 ∉ A) (hK : 1 ≤ K) (hL : 0 < L) (hk : k ≠ 0) (hKN : K ≤ ↑N)
  (hq : ∀ (q : ℕ), q ∈ ppowers_in_set A → ↑q ≤ L * K ^ 2 / (16 * ↑N ^ 2 * log ↑N ^ 2))
  (z : ∀ h ∈ minor_arc₂ A k K T, (∃ x ∈ I h K k,
            ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x))
  (hD : D ∈ (ppowers_in_set A).ssubsets) :
  (((minor_arc₂ A k K T).filter (λ h, interval_rare_ppowers (I h K k) A L = D)).card : ℝ) ≤
      (K + 1) * ((k * [A] + K) / [D] + 1) :=
begin
  have : ((minor_arc₂ A k K T).filter (λ h, interval_rare_ppowers (I h K k) A L = D)).card ≤
    (((finset.Icc (-⌊((k : ℝ) * [A] + K) / 2⌋) ⌊((k : ℝ) * [A] + K) / 2⌋).filter
      (λ m, ↑[D] ∣ m)).bUnion (λ m, integer_range m (K / 2))).card,
  { refine card_le_card_of_inj_on (λ h, h * k) _ _,
    swap,
    { intros _ _ _ _ z,
      rw mul_eq_mul_right_iff at z,
      apply z.resolve_right,
      simpa using hk },
    intros h h',
    rw [mem_filter] at h',
    simp only [mem_bUnion, mem_filter, exists_prop, and_assoc],
    obtain ⟨r, hr₁, hr₂⟩ := z _ h'.1,
    refine ⟨r, _, _, _⟩,
    { rw [mem_I', abs_sub_comm] at hr₁,
      rw [mem_Icc, ←abs_le, int.le_floor, add_div, mul_div_assoc],
      have := (abs_sub_abs_le_abs_sub _ _).trans hr₁,
      rw [tsub_le_iff_right, add_comm, ←int.cast_abs, mul_comm, abs_mul, nat.abs_cast] at this,
      apply this.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _)) _),
      rw [minor_arc₂, mem_sdiff, mem_sdiff] at h',
      apply bound_of_mem_j _ _ h'.1.1.1 },
    { rwa ←h'.2 },
    rw [I, mem_integer_range_iff, abs_sub_comm] at hr₁,
    rwa [mem_integer_range_iff, int.cast_mul, int.cast_coe_nat] },
  rw ←@nat.cast_le ℝ at this,
  apply this.trans _,
  refine (nat.cast_le.2 card_bUnion_le).trans _,
  rw nat.cast_sum,
  refine (finset.sum_le_card_nsmul _ _ (K+1) _).trans _,
  { intros x hx,
    exact (card_integer_range_le (by linarith)).trans (by linarith) },
  rw [nsmul_eq_mul, mul_comm],
  refine mul_le_mul_of_nonneg_left _ (by linarith),
  rw ←int.ceil_neg,
  apply (count_real_multiples' _ _).trans _,
  { refine neg_le_self (div_nonneg _ _),
    refine add_nonneg (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) (by linarith),
    norm_num },
  { change 0 < D.lcm id,
    rw pos_iff_ne_zero,
    apply lcm_ne_zero_of_zero_not_mem,
    intro i,
    rw [mem_ssubsets] at hD,
    exact zero_not_mem_ppowers_in_set (hD.1 i) },
  rw [sub_neg_eq_add, add_halves]
end

lemma candidate_count {N : ℕ} {K L T : ℝ} {k : ℕ} {A : finset ℕ} {D : finset ℕ}
  (hN : 2 ≤ N) (hA : 0 ∉ A) (hK : 1 ≤ K) (hL : 0 < L) (hk : k ≠ 0) (hKN : K ≤ ↑N)
  (hA' : ∀ n ∈ A, n ≤ N)
  (hq : ∀ (q : ℕ), q ∈ ppowers_in_set A → ↑q ≤ L * K ^ 2 / (16 * ↑N ^ 2 * log ↑N ^ 2))
  (z : ∀ h ∈ minor_arc₂ A k K T, (∃ x ∈ I h K k,
            ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x))
  (hD : D ∈ (ppowers_in_set A).ssubsets) :
  ((filter (λ h, interval_rare_ppowers (I h K k) A L = D) (minor_arc₂ A k K T)).card : ℝ) ≤
      6 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) :=
begin
  refine (candidate_count_one hN hA hK hL hk hKN hq z hD).trans _,
  rw [mem_ssubsets] at hD,
  have h₃' : 0 < [D],
  { rw [pos_iff_ne_zero],
    exact lcm_ne_zero_of_zero_not_mem (λ i, zero_not_mem_ppowers_in_set (hD.1 i)) },
  suffices h₁ : ([A] : ℝ) ≤ N ^ (ppowers_in_set A \ D).card * [D],
  { have h₂ : K + 1 ≤ 2 * N, { linarith only [hK, hKN] },
    have h₃ : (1 : ℝ) ≤ [D], { rwa [nat.one_le_cast, nat.succ_le_iff] },
    have h₄ : (1 : ℝ) ≤ k, { rwa [nat.one_le_cast, nat.succ_le_iff, pos_iff_ne_zero] },
    have h₅ : (N : ℝ) ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card,
    { rw [←pow_one (N : ℝ), ←pow_mul, one_mul],
      apply pow_mono (hK.trans hKN),
      rw [nat.succ_le_iff, card_pos, sdiff_nonempty],
      exact hD.2 },
    calc _ ≤ 4 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) + 2*N :_
       ... ≤ _ :_,
    rw mul_add, refine add_le_add _ _,
    { rw [mul_div_assoc', div_le_iff (zero_lt_one.trans_le h₃), ←nat.cast_add_one, rpow_nat_cast,
        pow_succ],
      transitivity ((2 : ℝ) * N) * (2 * (k * N ^ (ppowers_in_set A \ D).card * [D])),
      { rw [two_mul (_ * _ : ℝ)],
        refine mul_le_mul h₂ (add_le_add (by nlinarith only [h₁, h₄]) _) _ (by simp),
        { apply (hKN.trans h₅).trans,
          rw mul_right_comm,
          exact le_mul_of_one_le_left (by simp) (by nlinarith only [h₃, h₄]) },
        exact add_nonneg (by simp [mul_nonneg]) (by linarith only [hK]) },
      exact (le_of_eq (by ring)) },
    { rwa mul_one },
    have : (N : ℝ) ≤ ↑k * ↑N ^ (((ppowers_in_set A \ D).card : ℝ) + 1),
    { rw [rpow_add_one, ←mul_assoc, rpow_nat_cast],
      refine le_mul_of_one_le_left (nat.cast_nonneg _) _,
      refine one_le_mul_of_one_le_of_one_le h₄ _,
      apply le_trans _ h₅,
      { rw nat.one_le_cast, linarith },
      linarith },
    linarith only [this, h₄] },
  rw [←nat.cast_pow, ←nat.cast_mul, nat.cast_le],
  have : ∏ q in ppowers_in_set A \ D, q ≤ N ^ (ppowers_in_set A \ D).card,
  { refine prod_le_pow_card _ _ _ _,
    intros x hx,
    rw [mem_sdiff] at hx,
    exact (ppowers_in_set_le hA' _ hx.1).2 },
  refine le_trans _ (nat.mul_le_mul_right _ this),
  have hd : 0 < (∏ q in ppowers_in_set A \ D, q) * D.lcm id,
  { refine mul_pos (prod_pos (λ x hx, _)) h₃',
    rw [mem_sdiff] at hx,
    exact (ppowers_in_set_le hA' _ hx.1).1 },
  refine nat.le_of_dvd hd _,
  rw ←nat.factorization_le_iff_dvd (lcm_ne_zero_of_zero_not_mem hA) hd.ne',
  intro p,
  rcases eq_or_ne ([A].factorization p) 0 with hAp | hAp,
  { simp only [hAp, zero_le'] },
  rcases A.eq_empty_or_nonempty with rfl | hA'',
  { simp only [lcm_empty, nat.factorization_one, finsupp.coe_zero, pi.zero_apply, ne.def,
      eq_self_iff_true, not_true] at hAp,
    exact hAp.elim },
  obtain ⟨n, hn, hn' : _ = n.factorization p⟩ :=
    finset.sup_eq_mem (λ a : ℕ, a.factorization p) hA'',
  rw [lcm_desc hA, finset.finsupp_sup_apply, hn'] at hAp ⊢,
  have hp : p.prime,
  { by_contra pp,
    exact hAp (nat.factorization_eq_zero_of_non_prime _ pp) },
  have : p ^ n.factorization p ∈ ppowers_in_set A,
  { rw mem_ppowers_in_set' hp hAp,
    exact ⟨_, hn, rfl⟩ },
  rw ←hp.pow_dvd_iff_le_factorization hd.ne',
  by_cases p ^ n.factorization p ∈ D,
  { exact dvd_mul_of_dvd_right (dvd_lcm h) _ },
  { refine dvd_mul_of_dvd_left _ _,
    apply dvd_prod_of_mem,
    simp [this, h] },
end

/-- Lemma 4.21 -/
lemma minor2_bound :
  ∀ᶠ N : ℕ in filter.at_top,
    ∀ {K L T : ℝ} {k : ℕ} {A : finset ℕ},
    0 ∉ A → 1 ≤ K → 0 < L → k ≠ 0 → k ≤ N / 192 → K ≤ N → (∀ n ∈ A, n ≤ N) →
    (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N^2 * (log N)^2)) →
    (∀ (t : ℝ) (I : finset ℤ), I = Icc ⌈t - K / 2⌉ ⌊t + K / 2⌋ →
      T ≤ (A.filter (λ n, ∀ x ∈ I, ¬ ↑n ∣ x)).card ∨
      ∃ x ∈ I, ∀ q ∈ interval_rare_ppowers I A L, ↑q ∣ x) →
    ∑ h in minor_arc₂ A k K T, cos_prod A (h * k) ≤ 8⁻¹  :=
begin
  filter_upwards [filter.eventually_ge_at_top (2 : ℕ)] with
    N hN K L T k A hA hK hL hk hkN hKN hA' hq hI,
  have : ∀ h ∈ minor_arc₂ A k K T,
    ∃ x ∈ I h K k, ∀ q ∈ interval_rare_ppowers (I h K k) A L, ↑q ∣ x,
  { intros h hh,
    apply (hI _ _ rfl).resolve_left _,
    rw [minor_arc₂_eq, mem_filter] at hh,
    rw not_le,
    apply hh.2 },
  have z : ∀ h ∈ minor_arc₂ A k K T, ∃ x ∈ I h K k, ↑[interval_rare_ppowers (I h K k) A L] ∣ x,
  { intros h hh,
    obtain ⟨x, hx, hx'⟩ := this h hh,
    exact ⟨x, hx, cast_lcm_dvd hx'⟩ },
  have : ∀ D ∈ (ppowers_in_set A).ssubsets,
    (((minor_arc₂ A k K T).filter (λ h, interval_rare_ppowers (I h K k) A L = D)).card : ℝ) ≤
      6 * k * N ^ ((ppowers_in_set A \ D).card + 1 : ℝ),
  { intros D hD, exact candidate_count hN hA hK hL hk hKN hA' hq z hD },
  have : ∀ D ∈ (ppowers_in_set A).ssubsets,
    ∑ h in (minor_arc₂ A k K T).filter (λ h, interval_rare_ppowers (I h K k) A L = D),
        cos_prod A (h * k) ≤
      6 * k * N⁻¹ * N⁻¹ ^ ((ppowers_in_set A \ D).card),
  { intros D hD,
    refine (sum_le_card_nsmul _ _ (↑N ^ (-4 * (ppowers_in_set A \ D).card : ℝ)) _).trans _,
    { intros h hh,
      rw mem_filter at hh,
      rw ←hh.2,
      refine minor2_ind_bound _ hA (by linarith) hA' hN _ hq,
      rw [I, integer_range],
      simp },
    rw nsmul_eq_mul,
    refine (mul_le_mul_of_nonneg_right (this D hD)
      (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _)).trans _,
    have : 0 < (N : ℝ), { rw nat.cast_pos, linarith only [hN] },
    rw [mul_assoc, ←rpow_add this, mul_assoc (6 * k : ℝ), ←rpow_neg_one, ←rpow_nat_cast,
      ←rpow_mul this.le, ←rpow_add this],
    refine mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (nat.cast_nonneg _)),
    refine rpow_le_rpow_of_exponent_le _ _,
    { rw [nat.one_le_cast],
      apply one_le_two.trans hN },
    have : (1 : ℝ) ≤ (ppowers_in_set A \ D).card,
    { rw [nat.one_le_cast, nat.succ_le_iff, card_pos, finset.sdiff_nonempty],
      rw [mem_ssubsets] at hD,
      exact hD.2 },
    linarith only [this] },
  have r := sum_le_sum this,
  simp only [sum_filter] at r,
  rw [sum_comm] at r,
  simp only [sum_ite_eq, mem_ssubsets] at r,
  rw [←sum_filter, d_strict_subset hA hk z, ←mul_sum] at r,
  refine r.trans _,
  exact minor2_bound_end N hN hkN hA',
end

/-- Lemma 4.22 -/
theorem circle_method_prop2 :
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ (N : ℕ) in filter.at_top,
    ∀ {K L M T : ℝ} {k : ℕ} {A : finset ℕ},
    0 < T → 0 < L → 8 ≤ K → K < M → M ≤ N → k ≠ 0 → (k : ℝ) ≤ M / 192 → (∀ n ∈ A, M ≤ ↑n) →
    (∀ n ∈ A, n ≤ N) →
    rec_sum A < 2 / k → (2 : ℝ) / k - 1 / M ≤ rec_sum A →
    k ∣ (A.lcm id : ℕ) →
    (∀ q ∈ ppowers_in_set A, ↑q ≤ min (L * K^2 / (16 * N^2 * (log N)^2)) (min (c * M / k) (T * K^2 / (N^2 * log N)))) →
    good_condition A K T L →
    ∃ S ⊆ A, rec_sum S = 1 / k :=
begin
  rcases smooth_lcm with ⟨C,h0C,hClcm⟩,
  let C' := max C 1,
  let c : ℝ := (log 2)/C',
  have hc₀ : 0 < c, {
    refine div_pos (log_pos one_lt_two) (lt_of_lt_of_le h0C (le_max_left _ _)),
  },

  have hc₁ : c ≤ 1, { rw div_le_one, refine le_trans _ (le_max_right _ _),
    refine le_trans (le_of_lt log_two_lt_d9) _, norm_num1,
    refine lt_of_lt_of_le h0C (le_max_left _ _), },
  refine ⟨c, hc₀, _⟩,
  filter_upwards [minor1_bound, minor2_bound] with
    N m1 m2 K L M T k A hT hL hK hKM hMN hk hkM hA₁ hA₂ hA₃ hA₄ hkA hq hI,
  have hM₀ : 0 < M := by linarith only [hK, hKM],
  have hk₀ : 0 < (k : ℝ) := by rwa [nat.cast_pos, pos_iff_ne_zero],
  have hcCkM : C * (c * M / k) / log 2 / M + 1 / M + 1 / M ≤ 2 / k, {
    rw add_assoc,
    calc _ ≤ C' * (c * M / k) / log 2 / M + 1 / M + 1 / M :_
       ... ≤ (1:ℝ)/k + (1 / M + 1 / M) :_
       ... ≤ (1:ℝ)/k + (1 /k) :_
       ... = _ :_,
    rw [add_assoc, add_le_add_iff_right, div_le_div_right hM₀, div_le_div_right (log_pos one_lt_two),
        mul_le_mul_right], refine le_max_left _ _, refine mul_pos (mul_pos hc₀ hM₀) _,
    rw inv_pos, exact hk₀,
    rw [div_div, mul_div, div_div, mul_comm (k:ℝ), ← div_div, ← mul_assoc, mul_div_mul_right,
        mul_div_cancel', div_self, add_assoc], exact ne_of_gt (log_pos one_lt_two),
        refine ne_of_gt (lt_of_lt_of_le zero_lt_one _), refine le_max_right _ _,
    exact ne_of_gt hM₀, rw [add_le_add_iff_left, ← two_mul, ← div_eq_mul_one_div, div_le_div_iff,
      one_mul, ← le_div_iff'], refine le_trans hkM _, rw [div_le_div_left hM₀], norm_num1,
    norm_num1, exact zero_lt_two, exact zero_lt_two, exact hM₀, exact hk₀,
    rw [← two_mul, ← div_eq_mul_one_div],
   },
  have hA₅ : A.nonempty,
  { rw nonempty_iff_ne_empty,
    rintro rfl,
    simp only [rec_sum_empty, rat.cast_zero, sub_nonpos, div_le_div_iff hk₀ hM₀, one_mul] at hA₄,
    have := hA₄.trans hkM,
    rw [le_div_iff', ←mul_assoc] at this,
    { linarith only [this, hM₀] },
    { norm_num1 } },
  simp only [le_min_iff, imp_and_distrib, forall_and_distrib] at hq,
  specialize m1 k (hK.trans hKM.le) hA₅ hA₁ (show 0 < K, by linarith only [hK]) hT hA₂ hq.2.2,
  have hA₆ : 0 ∉ A := λ t, hM₀.not_le (hA₁ _ t),
  have hkN : k ≤ N / 192,
  { rw nat.le_div_iff_mul_le' (show 0 < 192, by norm_num),
    rw le_div_iff (show (0 : ℝ) < 192, by norm_num) at hkM,
    exact_mod_cast hkM.trans hMN },
  have h0K : 0 < K, { refine lt_of_lt_of_le _ hK, norm_num1, },
  have hA₄' : (2 : ℝ) - k / M ≤ k*rec_sum A, {
    rw ← pos_iff_ne_zero at hk,
    rw [← mul_le_mul_left hk₀, mul_sub, ← div_eq_mul_one_div, mul_div_cancel'] at hA₄,
    exact hA₄, exact ne_of_gt hk₀,
  },
  have hA₃': (k:ℝ)*rec_sum A < 2, {
    rw ← pos_iff_ne_zero at hk,
    rw ← lt_div_iff' hk₀,
    have : ((2/k : ℚ):ℝ) = 2/k, { push_cast, },
    rw ← this, exact_mod_cast hA₃,
   },
  have hAlcm : ([A] : ℝ) ≤ 2^(A.card - 1 : ℤ), {
    have hClcmnec : 0 ≤ (c * M / k), { refine div_nonneg _ _,
      refine mul_nonneg (le_of_lt hc₀) (le_of_lt hM₀), exact nat.cast_nonneg k, },
    have hClcmnec2 : (∀ q ∈ ppowers_in_set A, (q:ℝ) ≤ (c * M / k)), {
      intros q hqpp, refine hq.2.1 q hqpp,
     },
    specialize hClcm (c * M / k) hClcmnec A hA₆ hClcmnec2,
    refine le_trans hClcm _, rw [← real.log_le_log, log_exp, log_zpow, ← div_le_iff],
    push_cast, rw [le_sub_iff_add_le, ← div_le_div_right hM₀],
    refine le_trans _ (rec_sum_le_card_div hM₀ hA₁), refine le_trans _ hA₄,
    rw [add_div, le_sub_iff_add_le], exact hcCkM, refine log_pos one_lt_two,
    refine exp_pos _, rw ← rpow_int_cast, refine rpow_pos_of_pos _ _, exact zero_lt_two,
  },
  specialize m2 hA₆ ((by norm_num : (1 : ℝ) ≤ 8).trans hK) hL hk hkN (hKM.le.trans hMN) hA₂ hq.1 hI,
  by_contra' i,
  have hminorl := minor_lbound hA₁ h0K hKM hkA hk hA₄' hA₃' hA₅ i hAlcm,
  have hminors : (minor_arc₂ A k K T) ∪ (minor_arc₁ A k K T) = j A \ major_arc A k K, {
    rw minor_arc₂, refine finset.sdiff_union_of_subset _, rw minor_arc₁,
    refine filter_subset _ _,
   },
  rw [← hminors, sum_union, ← not_lt] at hminorl, refine hminorl _,
  calc _ ≤ 8⁻¹ + 8⁻¹ :_
     ... < _ :_,
  refine add_le_add m2 m1, norm_num1, rw minor_arc₂, refine sdiff_disjoint,
end
