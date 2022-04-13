/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import for_mathlib.misc
import defs

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

theorem unit_fractions_upper_density (A : set ℕ) (hA : upper_density A > 0):
   ∃ (S : finset ℕ), (S : set ℕ) ⊆ A ∧ ∑ n in S, (1 / n : ℝ) = 1 :=
sorry

theorem unit_fractions_upper_log_density :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range (N+1),
    25 * log (log (log N)) * log N / log (log N) ≤ ∑ n in A, (1 / n : ℝ) →
      ∃ S ⊆ A, ∑ n in S, (1 / n : ℝ) = 1 :=
sorry

-- * sorry is used as a placeholder for things we haven't filled in yet, a finished formal proof
--   would be "sorry-free"
-- * it's easier to write all inequalities as < or ≤ for essentially technical reasons, and it's
--   not too unreadable
-- * `finset.range (N+1)` is the finite set `{0, 1, ..., N}`. Oddly enough, 1/0 is defined to be 0
--   in Lean, so it's actually safe for me to include `0` in the set (in fact equivalent).
--     * the alternative is to have division only defined when the denominator is non-zero, but
--       that turns out to be more inconvenient; instead we allow division by zero but many
--       lemmas about division insist the denominator is non-zero instead
--     * for instance, to divide by `log (log N)` above I'd need to show that it's non-zero, which
--       is obvious but still requires work. Essentially the tradeoff is that the statement doesn't
--       need these proofs, but the proof will; and it's more important for the statement to be
--       readable
-- * I had to write `(1 / n : ℝ)` rather than just `(1 / n)` because otherwise Lean tries to work
--   with `1 / n` as a natural, which means floor division. So I instead say "treat this as a real
--   number" to make the division act sensibly. I could instead talk about rationals, but for
--   the inequality part I've got a real on the LHS anyway, so it would convert to rationals and
--   then to reals, so might as well go straight to ℝ.

-- Prop 1
theorem technical_prop :
  ∀ᶠ (N : ℕ) in at_top, ∀ (A ⊆ finset.range (N+1)) (y z : ℝ),
  (1 ≤ y) → (y ≤ z) → (z ≤ (log N)^((1/500 : ℝ)))
  → (∀ n ∈ A, ( (N:ℝ)^(1-(1:ℝ)/(log(log N))) ≤ n ))
  → 2 / y + (log N)^(-(1/200 : ℝ)) ≤ (rec_sum A : ℝ)
  → (∀ n ∈ A, ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧ (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z) )
  → (∀ n ∈ A, is_smooth ((N:ℝ)^(1-(6:ℝ)/(log(log N)))) n)
  → arith_regular N A
  → ∃ S ⊆ A, ∃ d : ℕ, (y ≤ d) ∧ ((d:ℝ) ≤ z) ∧
    rec_sum S = 1/d
  :=
sorry

-- (written before getting anywhere)
-- I have a suspicion that an alternative phrasing might be nicer
-- The ordering of the Sᵢ doesn't actually matter...
-- the idea is that we pick a collection of subsets which has maximum size

-- (written later)
-- the above wasn't really true, I forgot about `nat.find_greatest` which does what's needed
-- but it's still helpful to forget about the ordering of the S_i both here and in general
-- imo it's almost always easier without, and oftentimes the argument never needed the ordering
-- in the first place
-- also `finset.exists_smaller_set` and `finset.exists_intermediate_set` are good to know about

-- This shows up often enough here that it's worth having separately
lemma tendsto_coe_log_pow_at_top (c : ℝ) (hc : 0 < c) :
  tendsto (λ (x : ℕ), (log x)^c) at_top at_top :=
(tendsto_rpow_at_top hc).comp (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top)

lemma prop_one_specialise :
  ∀ᶠ (N : ℕ) in at_top, ∀ (A ⊆ finset.range (N+1)),
    (∀ n ∈ A, ( (N:ℝ)^(1-(1:ℝ)/(log(log N))) ≤ n ))
  → (log N)^((1/500 : ℝ)) ≤ (rec_sum A : ℝ)
  → (∀ n ∈ A, ∃ d₂ : ℕ, (d₂ ∣ n) ∧ 4 ≤ d₂ ∧ ((d₂ : ℝ) ≤ (log N)^(1/500 : ℝ)))
  → (∀ n ∈ A, is_smooth ((N:ℝ)^(1-(6:ℝ)/(log(log N)))) n)
  → arith_regular N A
  → ∃ S ⊆ A, ∃ d : ℕ, (1 ≤ d) ∧ ((d:ℝ) ≤ (log N)^(1/500 : ℝ)) ∧
    rec_sum S = 1/d :=
begin
  have hf : tendsto (λ (x : ℕ), (log x)^(1/500 : ℝ)) at_top at_top :=
    tendsto_coe_log_pow_at_top _ (by norm_num1),
  have hf' : tendsto (λ (x : ℕ), (log x)^(1/200 : ℝ)) at_top at_top :=
    tendsto_coe_log_pow_at_top _ (by norm_num1),
  filter_upwards [technical_prop, hf (eventually_ge_at_top 3), hf' (eventually_ge_at_top 1),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top) (eventually_ge_at_top 0)],
  intros N hN hN' hN'' hN''' A A_upper_bound A_lower_bound hA₁ hA₂ hA₃ hA₄,
  simp only [set.mem_set_of_eq, set.preimage_set_of_eq] at hN' hN'' hN''',
  exact_mod_cast hN A A_upper_bound 1 _ le_rfl _ le_rfl A_lower_bound _ _ hA₃ hA₄,
  { exact le_trans (by norm_num1) hN' },
  { apply le_trans _ hA₁,
    apply le_trans _ hN',
    rw ←le_sub_iff_add_le',
    norm_num1,
    rw rpow_neg,
    apply inv_le_one hN'',
    apply hN''' },
  intros n hn,
  obtain ⟨d₂, hd₂, hd₂', hd₂''⟩ := hA₂ n hn,
  exact ⟨1, d₂, one_dvd _, hd₂, by simp, by simpa, hd₂''⟩,
end

-- Corollary 1
theorem corollary_one :
  ∀ᶠ (N : ℕ) in at_top, ∀ (A ⊆ finset.range (N+1)),
  (∀ n ∈ A, ( (N:ℝ)^(1-(1:ℝ)/(log(log N))) ≤ n ))
  → 2*(log N)^((1/500 : ℝ)) ≤ (rec_sum A : ℝ)
  → (∀ n ∈ A, ∃ p : ℕ, ((p ∣ n) ∧ (4 ≤ p) ∧ ((p:ℝ) ≤ (log N)^((1/500 : ℝ))) ))
  → (∀ n ∈ A, is_smooth ((N:ℝ)^(1-(6:ℝ)/(log(log N)))) n)
  → arith_regular N A
  → ∃ S ⊆ A, rec_sum S = 1 :=
begin
  filter_upwards [prop_one_specialise, eventually_ge_at_top 1],
  intros N p1 hN₁ A A_upper_bound A_lower_bound hA₁ hA₂ hA₃ hA₄,
  -- `good_set` expresses the families of subsets that we like
  -- instead of saying we have S_1, ..., S_k, I'll say we have k-many subsets (+ same conditions)
  let good_set : finset (finset ℕ) → Prop :=
    λ S, (∀ s ∈ S, s ⊆ A) ∧ (S : set (finset ℕ)).pairwise_disjoint id ∧
      ∀ s, ∃ (d : ℕ), s ∈ S → 1 ≤ d ∧ (d : ℝ) ≤ (log N)^(1/500 : ℝ) ∧ rec_sum s = 1 / d,
    -- the last condition involving `d` is chosen weirdly so that `choose` later gives a more
    -- convenient function
  let P : ℕ → Prop := λ k, ∃ S : finset (finset ℕ), S.card = k ∧ good_set S,
  let k : ℕ := nat.find_greatest P (A.card + 1), -- A.card is a trivial upper bound
  have P0 : P 0 := ⟨∅, by simp [good_set]⟩, -- we clearly have that 0 satisfies p by using ∅
  have Pk : P k := nat.find_greatest_spec (nat.zero_le _) P0,
  obtain ⟨S, hk, hS₁, hS₂, hS₃⟩ := Pk,
  choose d' hd'₁ hd'₂ hd'₃ using hS₃,
  let t : ℕ → ℕ := λ d, (S.filter (λ s, d' s = d)).card,
  -- If we do have an appropriate d, take it
  by_cases h : ∃ d : ℕ, 0 < d ∧ d ≤ t d,
  { obtain ⟨d, d_pos, ht⟩ := h,
    -- there are ≥ d things with R(s) = 1/d, pick a subset so we have exactly d
    obtain ⟨T', hT', hd₂⟩ := finset.exists_smaller_set _ _ ht,
    have hT'S := hT'.trans (finset.filter_subset _ _),
    refine ⟨T'.bUnion id, _, _⟩,
    { refine (finset.bUnion_subset_bUnion_of_subset_left _ hT'S).trans _,
      rwa finset.bUnion_subset },
    rw [rec_sum_bUnion_disjoint (hS₂.subset hT'S), finset.sum_congr rfl, finset.sum_const, hd₂,
      nsmul_eq_mul, mul_div_cancel'],
    { rw nat.cast_ne_zero, exact d_pos.ne' },
    intros i hi,
    rw [hd'₃ _ (hT'S hi), (finset.mem_filter.1 (hT' hi)).2] },
  push_neg at h,
  exfalso,
  -- otherwise make A' as in the paper
  let A' := A \ S.bUnion id,
  have hS : (∑ s in S, rec_sum s : ℝ) ≤ (log N)^(1/500 : ℝ),
  { transitivity (∑ d in finset.Icc 1 ⌊(log N)^(1/500 : ℝ)⌋₊, t d / d : ℝ),
    { have : ∀ s ∈ S, d' s ∈ finset.Icc 1 ⌊(log N)^(1/500 : ℝ)⌋₊,
      { intros s hs,
        simp only [finset.mem_Icc, hd'₁ s hs, nat.le_floor (hd'₂ s hs), and_self] },
      rw ←finset.sum_fiberwise_of_maps_to this,
      apply finset.sum_le_sum,
      intros d hd,
      rw [div_eq_mul_one_div, ←nsmul_eq_mul],
      apply finset.sum_le_card_nsmul,
      intros s hs,
      simp only [finset.mem_filter] at hs,
      rw [hd'₃ _ hs.1, hs.2, rat.cast_div, rat.cast_one, rat.cast_coe_nat] },
    refine (finset.sum_le_card_nsmul _ _ 1 _).trans _,
    { simp only [one_div, and_imp, finset.mem_Icc],
      rintro d hd -,
      exact div_le_one_of_le (nat.cast_le.2 ((h d hd).le)) (nat.cast_nonneg _) },
    { simp only [nat.add_succ_sub_one, add_zero, nat.card_Icc, nat.smul_one_eq_coe],
      exact nat.floor_le (rpow_nonneg_of_nonneg (log_nonneg (nat.one_le_cast.2 hN₁)) _) } },
  have hAS : disjoint A' (S.bUnion id) := finset.sdiff_disjoint,
  have RA'_ineq : (log N)^(1/500 : ℝ) ≤ rec_sum A',
  { have : rec_sum A = rec_sum A' + rec_sum (S.bUnion id),
    { rw [←rec_sum_disjoint hAS, finset.sdiff_union_of_subset],
      rwa finset.bUnion_subset },
    rw [this] at hA₁,
    simp only [rat.cast_add] at hA₁,
    rw ←sub_le_iff_le_add at hA₁,
    apply le_trans _ hA₁,
    rw [rec_sum_bUnion_disjoint hS₂, rat.cast_sum],
    linarith [hS] },
  have hA' : A' ⊆ A := finset.sdiff_subset _ _,
  obtain ⟨S', hS', d, hd, hd', hS'₂⟩ :=
    p1 A' (hA'.trans A_upper_bound) (λ n hn, A_lower_bound n (hA' hn))
      RA'_ineq (λ n hn, hA₂ n (hA' hn)) (λ n hn, hA₃ n (hA' hn)) (hA₄.subset hA'),
  have hS'' : ∀ s ∈ S, disjoint S' s :=
    λ s hs, disjoint.mono hS' (finset.subset_bUnion_of_mem id hs) hAS,
  have hS''' : S' ∉ S,
  { intro t,
    exact (nonempty_of_rec_sum_recip hd hS'₂).ne_empty (disjoint_self.1 (hS'' _ t)) },
  have : P (k+1),
  { refine ⟨insert S' S, _, _⟩,
    { rw [finset.card_insert_of_not_mem hS''', hk] },
    refine ⟨_, _, _⟩,
    { simpa [hS'.trans hA'] using hS₁ },
    { simpa [set.pairwise_disjoint_insert, hS₂] using λ s hs _, hS'' _ hs },
    intros s,
    rcases eq_or_ne s S' with rfl | hs,
    { exact ⟨d, λ _, ⟨hd, hd', hS'₂⟩⟩ },
    refine ⟨d' s, λ i, _⟩,
    have : s ∈ S := finset.mem_of_mem_insert_of_ne i hs,
    exact ⟨hd'₁ _ this, hd'₂ _ this, hd'₃ _ this⟩ },
  have hk_bound : k + 1 ≤ A.card + 1,
  { rw [←hk, add_le_add_iff_right],
    apply le_trans _ (finset.card_le_of_subset (finset.bUnion_subset.2 hS₁)),
    apply finset.card_le_card_bUnion hS₂,
    intros s hs,
    exact nonempty_of_rec_sum_recip (hd'₁ s hs) (hd'₃ s hs) },
  have : k + 1 ≤ k := nat.le_find_greatest hk_bound this,
  simpa using this,
end

-- define the X in Lemma 1 as a separate definition?
def X (y z : ℝ) : set ℕ := sorry

-- Sieve of Eratosthenes-Legendre, again belongs in basic_estimates
-- Bhavik, this is clumsily expressed, condensed form?
lemma sieve_eratosthenes (x y u v : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu: 2 ≤ u)
  -- BM: hu isn't in the paper? also the ordering looks weird to me
(huv : u ≤ v) :
|(((finset.Icc ⌈x⌉₊ ⌊x+y⌋₊).filter (λ n : ℕ, (∀ p : ℕ, (p ∣ n)
   → (prime p) → ( (p:ℝ) < u ∨ v < p ) ))).card : ℝ)-
   (∏ p in (finset.range(⌊v⌋₊+1)).filter (λ n, (prime n) ∧ (u ≤ n)), (1-(1/p:ℝ)))
   * y|
   ≤ (2:ℝ)^(v+1)
:=
sorry
-- (Proof: write the filtered cardinality as a sum, using the Mobius function
-- to detect the divisibility constraint, then rearrange. Uses the trivial bound
-- of v for number of primes in [u,v])

-- Lemma 1
lemma sieve_lemma_one  : ∃ C : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ y z : ℝ, (3 ≤ y) → (y < z) → (z ≤ log N) →
   let X : set ℕ := { n : ℕ | ∀ p:ℕ, (prime p) → (p ∣ n) →
   ( ((p:ℝ) < y) ∨ (z < p)) } in
   (((finset.range(2*N)).filter (λ n, n ∈ X ∧ N ≤ n)).card : ℝ) ≤
   C * (log y / log z) * N
    :=
sorry

-- This is Turan's estimate, belongs in basic_estimates probably
lemma turan_primes_estimate : ∃ (C : ℝ), ∀ x : ℝ, (x ≥ 25) →
  (∑ n in finset.Icc 1 ⌊x⌋₊, ((ω n : ℝ) - log(log n))^2
  ≤  C * x * log(log x)  ) :=
 --
--  ≤  ):=
sorry
-- Textbook proof is to expand square, rearrnage sum, write ω n as
-- ∑ p ≤ x, 1_(p∣n)

-- Sieve of Eratosthenes-Legendre, again belongs in basic_estimates
--lemma sieve_eratosthenes :

-- Lemma 2
lemma sieve_lemma_two : ∃ C : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ y z : ℝ, (2 ≤ y) → (4*y < z) → (z^2 ≤ log N) →
   let Y : set ℕ := { n : ℕ | ∃ p₁ p₂ : ℕ, (p₁ ≠ p₂) ∧ (prime p₁)
   ∧ (prime p₂) ∧ (p₁ ∣ n) ∧ (p₂ ∣ n) ∧ (y ≤ p₁) ∧ (4*p₁ ≤ p₂)
   ∧ ((p₂:ℝ) ≤ z) } in
   (((finset.range(N+1)).filter (λ n, ¬(n ∈ Y))).card : ℝ) ≤
   C * (log y / log z)^(1/2) * N
    :=
sorry

-- Lemma 3
-- TODO: Replace nat.divisors with just the prime power divisors
lemma rest_recip_ppowers : ∃ C : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ n₁ n₂ : ℕ, (n₁ < n₂) → (n₂ ≤ N+n₁) →
  ∑ q in (nat.divisors (int.gcd n₁ n₂)), (1/q : ℝ) ≤
  C * log(log(log N))
 :=
sorry

-- Lemma 4
lemma rec_qsum_lower_bound (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1/2) :
  ∀ᶠ (N : ℕ) in at_top, ∀ A : finset ℕ,
  ((log N)^(-ε/2) ≤ rec_sum A )
  → (∀ n ∈ A, ((1-ε)*log(log N) ≤ ω n ) ∧ ( (ω n : ℝ) ≤ 2*(log (log N))))
  → (1-2*ε)*log(log N) *real.exp(-1) ≤ ∑ q in ppowers_in_set A, (1/q : ℝ)
:=
sorry

-- Lemma 5
lemma find_good_d : ∃ c C : ℝ, ∀ᶠ (N : ℕ) in at_top, ∀ M k : ℝ,
  ∀ A ⊆ finset.range(N+1),
  (M ≤ N) → ((N:ℝ) ≤ M^2) → ((4:ℝ) ≤ k) → (k ≤ c* log(log N))
  → (∀ n ∈ A, M ≤ (n:ℝ) ∧ ((ω n) : ℝ) ≤ (log N)^(1/k)) →
    (∀ q ∈ ppowers_in_set A,
    ((log N)^(-(1/2 : ℝ)) ≤ rec_sum_local A q) →
    (∃ d : ℕ,
    ( M*real.exp(-(log N)^(1-1/k)) < q*d ) ∧
    ( (ω d : ℝ) ≤ (5/log k) * log(log N) ) ∧
    ( C*(rec_sum_local A q) / (log N)^(2/k) ≤
      ∑ n in (local_part A q).filter(λ n, (q*d ∣ n) ∧
        (coprime (q*d) (n/q*d))), (q*d/n : ℝ)  ) ) )
  :=
sorry

lemma good_d (N : ℕ) (M δ : ℝ) (A : finset ℕ) (hA₁ : A ⊆ finset.range (N + 1)) (hM : 0 < M)
  (hAM : ∀ n ∈ A, M ≤ (n : ℝ)) (hAq : ∀ q ∈ ppowers_in_set A, (2 : ℝ) * δ ≤ rec_sum_local A q)
  (I : finset ℤ) (q : ℕ) (hq : q ∈ interval_rare_ppowers I A (M * δ)) :
  δ ≤ rec_sum_local (A.filter (λ n, ∃ x ∈ I, ↑n ∣ x)) q :=
begin
  rw [interval_rare_ppowers, finset.mem_filter] at hq,
  set nA : finset ℕ := A.filter (λ n, ∀ x ∈ I, ¬ (↑n ∣ x)),
  have hnA : nA = A.filter (λ n, ¬ ∃ x ∈ I, ↑n ∣ x),
  { apply finset.filter_congr,
    simp },
  have h1 : (rec_sum_local nA q : ℝ) ≤ δ,
  { rw [rec_sum_local, local_part, finset.filter_comm, ←local_part, rat.cast_sum],
    refine (finset.sum_le_card_nsmul _ _ ((q : ℝ) / M) _).trans _,
    { intros i hi,
      simp only [finset.mem_filter, mem_local_part, and_assoc] at hi,
      simp only [rat.cast_div, rat.cast_coe_nat],
      exact div_le_div_of_le_left (nat.cast_nonneg _) hM (hAM _ hi.1) },
    rw nsmul_eq_mul,
    refine (mul_le_mul_of_nonneg_right hq.2.le (div_nonneg (nat.cast_nonneg _) hM.le)).trans _,
    rw [mul_comm M, mul_div_assoc, mul_assoc, div_mul_div_comm₀, mul_comm M, div_self, mul_one],
    simp only [mul_eq_zero, nat.cast_eq_zero, hM.ne', ne.def, or_false],
    rw [mem_ppowers_in_set, and_assoc] at hq,
    exact hq.1.ne_zero },
  have h2 : rec_sum_local A q =
    rec_sum_local (A.filter (λ n, ∃ x ∈ I, ↑n ∣ x)) q + rec_sum_local nA q,
  { rw [hnA, ←rec_sum_local_disjoint (finset.disjoint_filter_filter_neg _ _),
      finset.filter_union_filter_neg_eq] },
  have h4 : 2 * δ ≤ (rec_sum_local (A.filter (λ n, ∃ x ∈ I, ↑n ∣ x)) q) + (rec_sum_local nA q),
  { rw_mod_cast ← h2, exact hAq _ hq.1, },
  linarith,
end

-- Proposition 3
theorem force_good_properties :
  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  ((N:ℝ)^2 ≤ M) →
  (∀ n ∈ A, M ≤ (n:ℝ) ∧
    (((99:ℝ)/100)*log(log N) ≤ ω n ) ∧
    ( (ω n : ℝ) ≤ 2*(log (log N)))) →
  ( (log N)^(-(1/101 : ℝ)) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A,
    ((log N)^(-(1/100 : ℝ)) ≤ rec_sum_local A q )) → (
  (∃ B ⊆ A, ((rec_sum A) ≤ 3*rec_sum B) ∧
  ((ppower_rec_sum B : ℝ) ≤ (2/3)* log(log N)))
  ∨
  (∀ (a : ℕ), let I : finset ℤ := (finset.Icc a
       ⌊(a:ℝ)+M*(N:ℝ)^(-(2:ℝ)/log(log N))⌋) in
  ( ((M:ℝ)/log N ≤ ((A.filter (λ n, ∀ x ∈ I, ¬ (↑n ∣ x))).card : ℝ)) ∨
    (∃ x ∈ I, ∀ q : ℕ, (q ∈ interval_rare_ppowers I A
       (M / (2*q*(log N)^(1/100 : ℝ)))) → ↑q ∣ x)
  ))) :=
sorry

-- The inductive heart of Lemma 5.5

lemma pruning_lemma_one_prec (A : finset ℕ) (ε : ℝ) (i: ℕ):
  ∃ A_i ⊆ A, ∃ Q_i ⊆ ppowers_in_set A,
  ( disjoint Q_i (ppowers_in_set A_i) ) ∧
  ( (rec_sum A : ℝ) - ε * (rec_sum Q_i) ≤ rec_sum A_i ) ∧
  (( i ≤ (A.filter( λ n, ¬ n ∈ A_i)).card ) ∨
  (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q))
  :=
begin
  induction i,
  use A,
  split,
  simp only [finset.subset.refl],
  use ∅,
  simp only [finset.empty_subset, finset.disjoint_empty_left,
   le_refl, nat.nat_zero_eq_zero, true_or, sub_zero, and_self,
   zero_le', rat.cast_le, mul_zero, rec_sum_empty, rat.cast_zero],
  cases i_ih with A' i_ih,
  cases i_ih with hA' i_ih,
  cases i_ih with Q' i_ih,
  cases i_ih with hQ' i_ih,
  by_cases hq : ∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q,
  use A',
  split,
  exact hA',
  use Q',
  split,
  exact hQ',
  split,
  exact i_ih.1,
  split,
  exact i_ih.2.1,
  right,
  exact hq,
  have h4: ∃ q ∈ ppowers_in_set A', ¬ ε < rec_sum_local A' q,
  { exact not_ball.mp hq, },
  cases h4 with q' h4,
  cases h4 with hq' h4,
  let A'' := A'.filter(λ n,  (q'∣n) ∧ coprime q' (n/q')),
  use A'',
  split,
  have h6 : A'' ⊆ A', {simp only [finset.filter_subset],},
  exact finset.subset.trans h6 hA',
  let Q'' := insert q' Q',
  use Q'',
  split,
  -- Pausing proof here
  sorry,
  sorry,
end

-- Lemma 5.5
lemma pruning_lemma_one :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range(N+1), ∀ ε : ℝ,
  ∃ B ⊆ A,
  ( (rec_sum A : ℝ) - 2*ε*log(log N) ≤ (rec_sum B : ℝ) ) ∧
  (∀ q ∈ ppowers_in_set B,
  ε < rec_sum_local B q )
  :=
begin
  -- Not actually the right filter, just a placeholder - see use of Mertens below.
  filter_upwards [eventually_ge_at_top 1],
  intros  N hN A hA ε,
  let i := A.card + 1,
  obtain ⟨B, haux⟩ :=  pruning_lemma_one_prec A ε i,
  cases haux with hB haux,
  cases haux with Q haux,
  cases haux with hQ haux,
  have h_recsums := haux.2.1,
  have h_local := haux.2.2,
  clear haux,
  use B,
  split,
  exact hB,
  split,
  -- For the below, first show rec_sum Q is at most the sum of 1/q over all prime
  -- powers q ≤ N, then use Mertens estimate and N chosen large enough such that
  -- this is ≤ 2*loglog N.
  have hQs : ε * (rec_sum Q : ℝ) ≤ 2*ε*(log(log N)) := sorry,
  linarith,
  cases h_local,
  exfalso,
  have hi : (A.filter( λ n, ¬ n ∈ B)).card ≤ A.card,
  { apply finset.card_filter_le, },
  linarith,
  exact h_local,
end

-- Lemma 7
lemma pruning_lemma_two :
  ∀ᶠ (N : ℕ) in at_top, ∀ M α : ℝ, ∀ A ⊆ finset.range(N+1),
  ((N:ℝ)^2 ≤ M) → ((2:ℝ)*(log N)^(-(1/200:ℝ)) < α ) →
  (∀ n ∈ A, M ≤ (n:ℝ)) →
  (α + (log N)^(-(1/200:ℝ)) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ M*(log N)^(-(1/100:ℝ))) →
  ∃ B ⊆ A, ( (rec_sum B : ℝ) < α) ∧ ( α - 1/M ≤ rec_sum B) ∧
  (∀ q ∈ ppowers_in_set B, (log N)^(-(1/100:ℝ)) ≤
    rec_sum_local B q)
  :=
sorry
