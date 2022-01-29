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

-- This is A_q in the paper.
def local_part (A : finset ℕ) (q : ℕ) : finset ℕ := A.filter (λ n, q ∣ n ∧ coprime q (n/q))

-- This is Q_A in the paper.
-- Replace nat.prime here with prime_power
def ppowers_in_set (A : finset ℕ) : set ℕ := { q | nat.prime q ∧ local_part A q ≠ ∅ }

-- For summing over 1/q for q in Q_A, need to know this is a finite set, so
-- I've put the below for now - actually should be ppowers_in_set? Prove this is
-- finite as a lemma?
def fin_ppowers_in_set (A : finset ℕ) : finset ℕ := sorry

-- This is R(A;q) in the paper.
def rec_sum_local (A : finset ℕ) (q : ℕ) : ℚ := ∑ n in local_part A q, q/n

def ppower_rec_sum (A : finset ℕ) : ℚ :=
∑ q in fin_ppowers_in_set A, 1/q

-- Replace nat.prime here with prime_power
def is_smooth (y : ℝ) (n : ℕ) : Prop := ∀ q : ℕ, nat.prime q → q ∣ n → (q : ℝ) ≤ y

def arith_regular (N : ℕ) (A : finset ℕ) : Prop :=
∀ n ∈ A, ((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)

lemma arith_regular.subset {N : ℕ} {A A' : finset ℕ} (hA : arith_regular N A) (hA' : A' ⊆ A) :
  arith_regular N A' :=
λ n hn, hA n (hA' hn)

-- This is the set D_I
def interval_rare_ppowers (I : finset ℕ) (A : finset ℕ) (K : ℝ) : set ℕ :=
{ q in ppowers_in_set A | (((local_part A q).filter (λ n, ∀ x ∈ I, ¬ n ∣ x)).card : ℝ) < K / q }
