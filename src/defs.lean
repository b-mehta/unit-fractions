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
open filter real
open nat (coprime)

open_locale arithmetic_function
open_locale classical
noncomputable theory

def upper_density (A : set ℕ) : ℝ := limsup at_top
   (λ N : ℕ, (((finset.range(N+1)).filter (λ n, n ∈ A)).card : ℝ) / N)

-- This is R(A) in the paper.
def rec_sum (A : finset ℕ) : ℚ := ∑ n in A, 1/n

lemma rec_sum_bUnion_disjoint {A : finset (finset ℕ)}
  (hA : (A : set (finset ℕ)).pairwise_disjoint id) : rec_sum (A.bUnion id) = ∑ s in A, rec_sum s :=
by simp only [rec_sum, finset.sum_bUnion hA, id.def]

lemma rec_sum_disjoint {A B : finset ℕ} (h : disjoint A B) :
   rec_sum (A ∪ B) = rec_sum A + rec_sum B :=
by simp only [rec_sum, finset.sum_union h]

@[simp] lemma rec_sum_empty : rec_sum ∅ = 0 := by simp [rec_sum]

lemma rec_sum_nonneg {A : finset ℕ} : 0 ≤ rec_sum A :=
finset.sum_nonneg (λ i hi, div_nonneg zero_le_one (nat.cast_nonneg _))

lemma rec_sum_mono {A₁ A₂ : finset ℕ} (h : A₁ ⊆ A₂) : rec_sum A₁ ≤ rec_sum A₂ :=
finset.sum_le_sum_of_subset_of_nonneg h (λ _ _ _, div_nonneg zero_le_one (nat.cast_nonneg _))

-- can make this stronger without 0 ∉ A but we never care about that case
lemma rec_sum_eq_zero_iff {A : finset ℕ} (hA : 0 ∉ A) : rec_sum A = 0 ↔ A = ∅ :=
begin
  symmetry,
  split,
  { rintro rfl,
    simp },
  simp_rw [rec_sum, one_div],
  rw [finset.sum_eq_zero_iff_of_nonneg (λ i hi, _)],
  { intro h,
    simp only [one_div, inv_eq_zero, nat.cast_eq_zero] at h,
    apply finset.eq_empty_of_forall_not_mem,
    intros x hx,
    cases h x hx,
    apply hA hx },
  exact inv_nonneg.2 (nat.cast_nonneg _),
end

lemma nonempty_of_rec_sum_recip {A : finset ℕ} {d : ℕ} (hd : 1 ≤ d) :
  rec_sum A = 1 / d → A.nonempty :=
begin -- should be able to simplify this
  intro h,
  rw [finset.nonempty_iff_ne_empty],
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
by rw [local_part, finset.mem_filter]

lemma zero_mem_local_part_iff {A : finset ℕ} {q : ℕ} (hA : 0 ∉ A) :
  0 ∉ local_part A q :=
λ i, hA (finset.filter_subset _ _ i)

/--
This is Q_A in the paper. The definition looks a bit different, but `mem_ppowers_in_set` shows
it's the same thing.
-/
def ppowers_in_set (A : finset ℕ) : finset ℕ :=
A.bUnion (λ n, n.divisors.filter (λ q, is_prime_pow q ∧ coprime q (n / q)))

lemma mem_ppowers_in_set (A : finset ℕ) (q : ℕ) :
  q ∈ ppowers_in_set A ↔ is_prime_pow q ∧ (local_part A q).nonempty :=
begin
  simp only [ppowers_in_set, finset.mem_bUnion, finset.mem_filter, exists_prop, nat.mem_divisors,
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

-- This is R(A;q) in the paper.
def rec_sum_local (A : finset ℕ) (q : ℕ) : ℚ := ∑ n in local_part A q, q / n

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
def interval_rare_ppowers (I : finset ℕ) (A : finset ℕ) (K : ℝ) : set ℕ :=
(ppowers_in_set A).filter $ λ q, ↑((local_part A q).filter (λ n, ∀ x ∈ I, ¬ n ∣ x)).card < K / q
