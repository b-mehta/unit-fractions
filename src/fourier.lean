/-
Copyright (c) 2022 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import defs
import for_mathlib.misc

open_locale big_operators classical real

noncomputable theory

open filter real
open nat (coprime)

def integer_count (A : finset ℕ) (k : ℕ) : ℕ :=
(A.powerset.filter (λ S, ∃ (d : ℕ), rec_sum S * k = d)).card

def j (A : finset ℕ) : finset ℤ :=
(finset.Ioo ⌈((- (A.lcm id : ℕ) / 2) : ℚ)⌉ ⌊(((A.lcm id : ℕ) / 2) : ℚ)⌋).erase (0 : ℤ)

-- types of `h`, `k` might need to change?
def cos_prod (B : finset ℕ) (h : ℤ) (k : ℕ) : ℝ :=
∏ n in B, |cos (π * k * h / n)|

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
  rw [sq (exp _), ←exp_add],
  rw exp_le_exp,
  apply le_of_eq,
  ring,
end

-- Proposition 2
theorem circle_method_prop : ∃ c : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ k M : ℕ, ∀ η K : ℝ,  ∀ A ⊆ finset.range (N+1),
  (M ≤ N) → ((N:ℝ)^(3/4 : ℝ) ≤ M) → (1 ≤ k) → ((k:ℝ) ≤ c*M) →
  (0 < η) → (η < 1) → (2*K ≤ M) → ((N:ℝ)^(3/4:ℝ) ≤ K) →
  (∀ n ∈ A, M ≤ n) →
  (rec_sum A ≤ 2/k) → ((2:ℚ)/k - 1 ≤ rec_sum A ) →
  (k ∣ A.lcm id) →
  (∀ q ∈ ppowers_in_set A, ((q:ℝ) ≤ c*M/k) ∧
  ((q:ℝ) ≤ c*η*M*K^2 / (N*log N)^2)) →
  (∀ (a : ℕ), let I : finset ℕ := (finset.Icc a ⌊(a:ℝ)+K⌋₊)
  in
  ( ((M:ℝ)/log N ≤ ((A.filter (λ n, ∀ x ∈ I, ¬ (n ∣ x))).card : ℝ)) ∨
    (∃ x ∈ I, ∀ q : ℕ, (q ∈ interval_rare_ppowers I A (η*M)) → q ∣ x)
  ))
  → ∃ S ⊆ A, rec_sum S = 1/k
  :=
sorry
