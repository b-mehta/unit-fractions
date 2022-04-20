/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import data.real.basic
import analysis.special_functions.log
import analysis.special_functions.pow
import order.filter.at_top_bot
import number_theory.arithmetic_function
import algebra.is_prime_pow

/-!
# Title

This file should contain a formal proof of https://arxiv.org/pdf/2112.03726.pdf, but for now it
contains associated results useful for that paper.
-/

open_locale big_operators -- this lets me use ∑ and ∏ notation
open filter real finset
open nat (coprime)

open_locale arithmetic_function
open_locale classical
noncomputable theory

def upper_density (A : set ℕ) : ℝ :=
  limsup at_top (λ N : ℕ, (((range N).filter (λ n, n ∈ A)).card : ℝ) / N)

lemma frequently_nat_of {A : set ℕ} {ε : ℝ} (hA : ε < upper_density A) :
  ∃ᶠ (N : ℕ) in at_top, ε < ((range N).filter (λ n, n ∈ A)).card / N :=
begin
  refine frequently_lt_of_lt_limsup _ hA,
  apply is_bounded.is_cobounded_le,
  exact is_bounded_under_of ⟨0, λ x, div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)⟩,
end

lemma exists_nat_of {A : set ℕ} {ε : ℝ} (hA : ε < upper_density A) :
  ∃ (N : ℕ), 0 < N ∧ ε < ((range N).filter (λ n, n ∈ A)).card / N :=
by simpa using frequently_at_top'.1 (frequently_nat_of hA) 0

lemma exists_density_of {A : set ℕ} {ε : ℝ} (hA : ε < upper_density A) :
  ∃ (N : ℕ), 0 < N ∧ ε * N < ((range N).filter (λ n, n ∈ A)).card :=
begin
  obtain ⟨N, hN, hN'⟩ := exists_nat_of hA,
  refine ⟨N, hN, _⟩,
  rwa lt_div_iff at hN',
  rwa nat.cast_pos
end

lemma upper_density_nonneg {A : set ℕ} :
  0 ≤ upper_density A :=
begin
  refine le_limsup_of_frequently_le _ _,
  { exact frequently_of_forall (λ x, div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) },
  refine is_bounded_under_of ⟨1, λ x, _⟩,
  refine div_le_one_of_le (nat.cast_le.2 _) (nat.cast_nonneg _),
  exact (card_le_of_subset (filter_subset _ _)).trans (by simp),
end

-- This is R(A) in the paper.
def rec_sum (A : finset ℕ) : ℚ := ∑ n in A, 1/n

lemma rec_sum_bUnion_disjoint {A : finset (finset ℕ)}
  (hA : (A : set (finset ℕ)).pairwise_disjoint id) : rec_sum (A.bUnion id) = ∑ s in A, rec_sum s :=
by simp only [rec_sum, sum_bUnion hA, id.def]

lemma rec_sum_disjoint {A B : finset ℕ} (h : disjoint A B) :
   rec_sum (A ∪ B) = rec_sum A + rec_sum B :=
by simp only [rec_sum, sum_union h]

@[simp] lemma rec_sum_empty : rec_sum ∅ = 0 := by simp [rec_sum]

lemma rec_sum_nonneg {A : finset ℕ} : 0 ≤ rec_sum A :=
sum_nonneg (λ i hi, div_nonneg zero_le_one (nat.cast_nonneg _))

lemma rec_sum_mono {A₁ A₂ : finset ℕ} (h : A₁ ⊆ A₂) : rec_sum A₁ ≤ rec_sum A₂ :=
sum_le_sum_of_subset_of_nonneg h (λ _ _ _, div_nonneg zero_le_one (nat.cast_nonneg _))

-- can make this stronger without 0 ∉ A but we never care about that case
lemma rec_sum_eq_zero_iff {A : finset ℕ} (hA : 0 ∉ A) : rec_sum A = 0 ↔ A = ∅ :=
begin
  symmetry,
  split,
  { rintro rfl,
    simp },
  simp_rw [rec_sum, one_div],
  rw [sum_eq_zero_iff_of_nonneg (λ i hi, _)],
  { intro h,
    simp only [one_div, inv_eq_zero, nat.cast_eq_zero] at h,
    apply eq_empty_of_forall_not_mem,
    intros x hx,
    cases h x hx,
    apply hA hx },
  exact inv_nonneg.2 (nat.cast_nonneg _),
end

lemma nonempty_of_rec_sum_recip {A : finset ℕ} {d : ℕ} (hd : 1 ≤ d) :
  rec_sum A = 1 / d → A.nonempty :=
begin -- should be able to simplify this
  intro h,
  rw [nonempty_iff_ne_empty],
  rintro rfl,
  simp only [one_div, zero_eq_inv, rec_sum_empty] at h,
  have : 0 < d := hd,
  exact this.ne (by exact_mod_cast h),
end

/--
This is A_q in the paper.
-/
def local_part (A : finset ℕ) (q : ℕ) : finset ℕ := A.filter (λ n, q ∣ n ∧ coprime q (n / q))

lemma mem_local_part {A : finset ℕ} {q : ℕ} (n : ℕ) :
  n ∈ local_part A q ↔ n ∈ A ∧ q ∣ n ∧ coprime q (n / q) :=
by rw [local_part, mem_filter]

lemma local_part_subset {A : finset ℕ} {q : ℕ} :
  local_part A q ⊆ A :=
filter_subset _ _

lemma zero_mem_local_part_iff {A : finset ℕ} {q : ℕ} (hA : 0 ∉ A) :
  0 ∉ local_part A q :=
λ i, hA (local_part_subset i)

/--
This is Q_A in the paper. The definition looks a bit different, but `mem_ppowers_in_set` shows
it's the same thing.
-/
def ppowers_in_set (A : finset ℕ) : finset ℕ :=
A.bUnion (λ n, n.divisors.filter (λ q, is_prime_pow q ∧ coprime q (n / q)))

@[simp] lemma ppowers_in_set_empty : ppowers_in_set ∅ = ∅ := bUnion_empty

lemma mem_ppowers_in_set {A : finset ℕ} {q : ℕ} :
  q ∈ ppowers_in_set A ↔ is_prime_pow q ∧ (local_part A q).nonempty :=
begin
  simp only [ppowers_in_set, mem_bUnion, mem_filter, exists_prop, nat.mem_divisors,
    finset.nonempty, mem_local_part, ←exists_and_distrib_left],
  refine exists_congr (λ i, _),
  split,
  { rintro ⟨h₁, h₂, h₃, h₄⟩,
    exact ⟨h₃, h₁, h₂.1, h₄⟩ },
  { rintro ⟨h₁, h₂, h₃, h₄⟩,
    refine ⟨h₂, ⟨h₃, _⟩, h₁, h₄⟩,
    rintro rfl,
    simp only [nat.zero_div, nat.coprime_zero_right] at h₄,
    exact h₁.ne_one h₄ },
end

lemma zero_not_mem_ppowers_in_set {A : finset ℕ} : 0 ∉ ppowers_in_set A :=
λ t, not_is_prime_pow_zero (mem_ppowers_in_set.1 t).1

lemma nat.pow_eq_one_iff {n k : ℕ} : n ^ k = 1 ↔ n = 1 ∨ k = 0 :=
begin
  rcases eq_or_ne k 0 with rfl | hk,
  { simp },
  { simp [pow_eq_one_iff, hk] },
end

lemma coprime_div_iff {n p k : ℕ} (hp : p.prime) (hn : p ^ k ∣ n) (hk : k ≠ 0) :
  nat.coprime (p^k) (n / p^k) → k = n.factorization p :=
begin
  rcases eq_or_ne n 0 with rfl | hn',
  { simp [nat.pow_eq_one_iff, hp.ne_one] },
  intro h,
  have := nat.factorization_mul_of_coprime h,
  rw [nat.mul_div_cancel' hn] at this,
  rw [this, hp.factorization_pow, finsupp.coe_add, pi.add_apply, finsupp.single_eq_same,
    self_eq_add_right, ←finsupp.not_mem_support_iff],
  intro i,
  apply nat.factorization_disjoint_of_coprime h,
  simp only [inf_eq_inter, mem_inter],
  refine ⟨_, i⟩,
  simp only [nat.support_factorization],
  rw [nat.prime_pow_prime_divisor hk hp, finset.mem_singleton],
end

lemma factorization_disjoint_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  disjoint a.factorization.support b.factorization.support ↔ a.coprime b :=
begin
  rw ←@not_not (a.coprime b),
  simp [disjoint_left, nat.prime.not_coprime_iff_dvd, nat.mem_factors ha, nat.mem_factors hb]
    {contextual := tt},
end

lemma factorization_eq_iff {n p k : ℕ} (hp : p.prime) (hk : k ≠ 0) :
  p ^ k ∣ n ∧ (p ^ k).coprime (n / p ^ k) ↔ n.factorization p = k :=
begin
  split,
  { rintro ⟨h₁, h₂⟩,
    rw ←coprime_div_iff hp h₁ hk h₂ },
  intro hk',
  have : p ^ k ∣ n,
  { rw ←hk',
    exact nat.pow_factorization_dvd n p },
  have hn : n ≠ 0,
  { rintro rfl,
    apply hk,
    simpa using hk'.symm },
  refine ⟨this, _⟩,
  rw ←factorization_disjoint_iff (pow_ne_zero _ hp.ne_zero),
  { rw [nat.factorization_div this, hp.factorization_pow, finsupp.support_single_ne_zero hk,
      disjoint_singleton_left, finsupp.mem_support_iff, finsupp.coe_tsub, pi.sub_apply, ne.def,
      tsub_eq_zero_iff_le, not_not, finsupp.single_eq_same, hk'] },
  rw [ne.def, nat.div_eq_zero_iff (pow_pos hp.pos _), not_lt],
  apply nat.le_of_dvd hn.bot_lt this,
end

lemma mem_ppowers_in_set' {A : finset ℕ} {p k : ℕ} (hp : p.prime) (hk : k ≠ 0) :
  p ^ k ∈ ppowers_in_set A ↔ ∃ n ∈ A, nat.factorization n p = k :=
begin
  rw [mem_ppowers_in_set, and_iff_right (hp.is_prime_pow.pow hk)],
  simp only [finset.nonempty, mem_local_part, exists_prop],
  refine exists_congr (λ n, and_congr_right' _),
  rw factorization_eq_iff hp hk,
end

-- TB - this lemma will frequently be useful
lemma ppowers_in_set_subset { A B : finset ℕ} (hAB : A ⊆ B) :
  ppowers_in_set A ⊆ ppowers_in_set B :=
sorry

lemma ppowers_in_set_nonempty {A : finset ℕ} (hA : ∃ n ∈ A, 2 ≤ n) :
  (ppowers_in_set A).nonempty :=
begin
  obtain ⟨n, hn, hn'⟩ := hA,
  have : n ≠ 1,
  { linarith },
  rw nat.ne_one_iff_exists_prime_dvd at this,
  obtain ⟨p, hp₁, hp₂⟩ := this,
  refine ⟨p ^ _, (mem_ppowers_in_set' hp₁ _).2 ⟨n, hn, rfl⟩⟩,
  rwa [←finsupp.mem_support_iff, nat.support_factorization, list.mem_to_finset,
    nat.mem_factors_iff_dvd _ hp₁],
  linarith
end

lemma ppowers_in_set_eq_empty {A : finset ℕ} (hA : ppowers_in_set A = ∅) :
  ∀ n ∈ A, n < 2 :=
begin
  contrapose hA,
  rw [←ne.def, ←finset.nonempty_iff_ne_empty],
  apply ppowers_in_set_nonempty,
  simpa using hA
end

lemma ppowers_in_set_eq_empty' {A : finset ℕ} (hA : ppowers_in_set A = ∅) (hA' : 0 ∉ A):
  A.lcm id = 1 :=
begin
  have : A ⊆ {1},
  { intros n hn,
    have := ppowers_in_set_eq_empty hA n hn,
    interval_cases n,
    { trivial },
    simp },
  rw finset.subset_singleton_iff at this,
  rcases this with rfl | rfl;
  simp,
end

-- This is R(A;q) in the paper.
def rec_sum_local (A : finset ℕ) (q : ℕ) : ℚ := ∑ n in local_part A q, q / n

lemma rec_sum_local_disjoint {A B : finset ℕ} {q : ℕ} (h : disjoint A B) :
   rec_sum_local (A ∪ B) q = rec_sum_local A q + rec_sum_local B q :=
by { rw [rec_sum_local, local_part, filter_union, sum_union (disjoint_filter_filter h)], refl }

lemma rec_sum_local_mono {A₁ A₂ : finset ℕ} {q : ℕ} (h : A₁ ⊆ A₂) :
  rec_sum_local A₁ q ≤ rec_sum_local A₂ q :=
sorry

def ppower_rec_sum (A : finset ℕ) : ℚ :=
∑ q in ppowers_in_set A, 1 / q

-- Replace nat.prime here with prime_power
def is_smooth (y : ℝ) (n : ℕ) : Prop := ∀ q : ℕ, is_prime_pow q → q ∣ n → (q : ℝ) ≤ y

def arith_regular (N : ℕ) (A : finset ℕ) : Prop :=
∀ n ∈ A, ((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)

lemma arith_regular.subset {N : ℕ} {A A' : finset ℕ} (hA : arith_regular N A) (hA' : A' ⊆ A) :
  arith_regular N A' :=
λ n hn, hA n (hA' hn)

-- This is the set D_I
def interval_rare_ppowers (I : finset ℤ) (A : finset ℕ) (K : ℝ) : finset ℕ :=
(ppowers_in_set A).filter $ λ q, ↑((local_part A q).filter (λ n, ∀ x ∈ I, ¬ ↑n ∣ x)).card < K / q

lemma interval_rare_ppowers_subset (I : finset ℤ) {A : finset ℕ} (K : ℝ) :
  interval_rare_ppowers I A K ⊆ ppowers_in_set A :=
filter_subset _ _
