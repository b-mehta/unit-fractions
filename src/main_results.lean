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
  have hq'zero : q' ≠ 0,
  { intro hnq,
    apply @zero_not_mem_ppowers_in_set A',
    rw ← hnq,
    exact hq', },
  let A'' := A'.filter(λ n,  ¬ ((q'∣n) ∧ coprime q' (n/q'))),
  use A'',
  split,
  have h6 : A'' ⊆ A', {simp only [finset.filter_subset],},
  exact finset.subset.trans h6 hA',
  let Q'' := insert q' Q',
  use Q'',
  split,
  intros x hx,
  rw finset.mem_insert at hx,
  cases hx with hx1 hx2,
  rw hx1,
  have hApp : ppowers_in_set A' ⊆ ppowers_in_set A,
  { apply ppowers_in_set_subset, exact hA', },
  exact hApp hq',
  exact hQ' hx2,
  split,
  rw finset.disjoint_left,
  intros x hx,
  rw finset.mem_insert at hx,
  cases hx with hx1 hx2,
  rw ppowers_in_set,
  rw hx1,
  rw finset.mem_bUnion,
  intro ha,
  cases ha with a ha,
  cases ha with ha2 ha,
  rw finset.mem_filter at ha,
  rw finset.mem_filter at ha2,
  apply ha2.2,
  split,
  apply nat.dvd_of_mem_divisors,
  exact ha.1,
  exact ha.2.2,
  intro hx3,
  have hdis : disjoint Q' (ppowers_in_set A'), { exact i_ih.1,},
  rw finset.disjoint_left at hdis,
  specialize hdis hx2,
  apply hdis,
  have hA'' : A'' ⊆ A', { simp only [finset.filter_subset], },
  have hApp : ppowers_in_set A'' ⊆ ppowers_in_set A',
  { apply ppowers_in_set_subset, exact hA'', },
  exact hApp hx3,
  split,
  have hrs : (rec_sum Q'':ℝ) = rec_sum Q' + 1/q',
  { rw rec_sum,
    rw rec_sum,
    rw finset.sum_insert,
    rw add_comm,
    simp only [one_div, rat.cast_coe_nat, rat.cast_inv, add_left_inj,
    rat.cast_add, eq_self_iff_true, rat.cast_sum, finset.sum_congr],
    intro hn,
    have hdis : disjoint Q' (ppowers_in_set A') := i_ih.1,
    rw finset.disjoint_left at hdis,
    apply @hdis q',
    exact hn,
    exact hq',
    },
    have hrs2a : rec_sum A'' + (rec_sum_local A' q')/q' = rec_sum A' ,
  { rw rec_sum,
    rw rec_sum,
    rw rec_sum_local,
    rw finset.sum_div,
    have hrs2b : ∑ (x : ℕ) in local_part A' q', (q':ℚ) / x / q' = ∑ (x : ℕ) in local_part A' q', 1 / ↑x,
    { refine finset.sum_congr rfl _,
      intros x hx,
      rw div_div_eq_div_mul,
      apply div_mul_left,
      exact_mod_cast hq'zero,},

    rw hrs2b,
    rw ← finset.sum_union,
    have hun :  A'' ∪ local_part A' q' = A',
    { ext,
      split,
      intro ha,
      rw finset.mem_union at ha,
      cases ha with ha1 ha2,
      rw finset.mem_filter at ha1,
      exact ha1.1,
      rw local_part at ha2,
      rw finset.mem_filter at ha2,
      exact ha2.1,
      intro ha,
      rw finset.mem_union,
      by_cases hcas : q' ∣ a ∧ q'.coprime (a / q'),
      right,
      rw local_part,
      rw finset.mem_filter,
      refine ⟨ha, hcas⟩,
      left,
      rw finset.mem_filter,
      refine ⟨ha, hcas⟩,
       },
    rw hun,
    rw finset.disjoint_left,
    intros a ha ha2,
    rw finset.mem_filter at ha,
    apply ha.2,
    rw local_part at ha2,
    rw finset.mem_filter at ha2,
    exact ha2.2,
     },
  have hrs2 : rec_sum A'' = rec_sum A' - (rec_sum_local A' q')/q',
  { rw ← hrs2a,
  simp only [eq_self_iff_true, add_tsub_cancel_right], },
  have hrs3 : (rec_sum A' : ℝ)  ≤ rec_sum A'' + ε*(1/q'),
  { rw hrs2,
    rw not_lt at h4,
    simp only [rat.cast_coe_nat, rat.cast_div, rat.cast_sub],
    have hrsa : ↑(rec_sum_local A' q') / ↑q' ≤ ε * (1 / ↑q'),
    { rw mul_one_div,
      apply (div_le_div_right _).mpr,
      exact h4,
      rw ppowers_in_set at hq',
      rw finset.mem_bUnion at hq',
      cases hq' with a hq',
      cases hq' with ha hq',
      rw finset.mem_filter at hq',
      rw nat.cast_pos,
      refine @nat.pos_of_mem_divisors a q' _,
      exact hq'.1,
     },
    linarith,
     },
  rw hrs,
  have hrs4 : (rec_sum A : ℝ)  ≤ rec_sum A' + ε*(rec_sum Q'),
  { apply tsub_le_iff_right.mp,
    exact i_ih.2.1,
    exact add_group.to_has_ordered_sub,
    },
  simp only [tsub_le_iff_right],
  rw mul_add,
  linarith,
  left,
  have h3 : i_n ≤ (finset.filter (λ (n : ℕ), n ∉ A') A).card,
  { cases i_ih.2.2 with ha1 ha2,
    exact ha1,
    exfalso,
    apply hq,
    exact ha2,
    },
  have h4 : (finset.filter (λ (n : ℕ), n ∉ A') A).card <
     (finset.filter (λ (n : ℕ), n ∉ A'') A).card,
  { apply finset.card_lt_card,
    rw finset.ssubset_iff_of_subset,
    rw ppowers_in_set at hq',
    rw finset.mem_bUnion at hq',
    cases hq' with a' hq',
    cases hq' with ha' hq',
    use a',
    split,
    rw finset.mem_filter,
    split,
    exact hA' ha',
    intro ha'n,
    rw finset.mem_filter at ha'n,
    apply ha'n.2,
    rw finset.mem_filter at hq',
    split,
    apply nat.dvd_of_mem_divisors,
    exact hq'.1,
    exact hq'.2.2,
    intro hn1,
    rw finset.mem_filter at hn1,
    apply hn1.2,
    exact ha',
    refine finset.subset_iff.mpr _,
    intros x hx,
    rw finset.mem_filter,
    rw finset.mem_filter at hx,
    split,
    exact hx.1,
    intro hx2,
    rw finset.mem_filter at hx2,
    apply hx.2,
    exact hx2.1,
   },
  have h5 : (finset.filter (λ (n : ℕ), n ∉ A') A).card + 1 ≤
     (finset.filter (λ (n : ℕ), n ∉ A'') A).card,
  { exact nat.succ_le_iff.mpr h4, },
  rw nat.succ_eq_add_one,
  linarith,
end

lemma explicit_mertens :
  ∀ᶠ (N : ℕ) in at_top,
  ((∑ q in (finset.range(N+1)).filter(λ q, is_prime_pow q), (1:ℚ)/q):ℝ) ≤ 2*log(log N) :=
sorry

-- Lemma 5.5
lemma pruning_lemma_one :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range(N+1), ∀ ε : ℝ,
  ( 0 < ε ) →
  (∃ B ⊆ A,
  ( (rec_sum A : ℝ) - ε*2*log(log N) ≤ (rec_sum B : ℝ) ) ∧
  (∀ q ∈ ppowers_in_set B,
  ε < rec_sum_local B q ))
  :=
begin
  filter_upwards [explicit_mertens],
  intros  N hN A hA ε hε,
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
  have hQu : Q ⊆ (finset.range(N+1)).filter(λ q, is_prime_pow q),
  { intros q hq,
    rw finset.mem_filter,
    have hqA : q ∈ ppowers_in_set A, { exact hQ hq, },
    rw [ppowers_in_set,finset.mem_bUnion] at hqA,
    cases hqA with a hqA,
    cases hqA with ha hqA,
    rw finset.mem_filter at hqA,
    rw finset.mem_range,
    split,
    have hq2 : q ≤ a, { apply nat.divisor_le, exact hqA.1, },
    have ha2 : a ∈ finset.range(N+1), { exact hA ha, },
    rw finset.mem_range at ha2,
    linarith,
    exact hqA.2.1,
     },
  have hQr : rec_sum Q ≤ ∑ q in (finset.range(N+1)).filter(λ q, is_prime_pow q), (1:ℚ)/q,
  { rw rec_sum,
    apply finset.sum_le_sum_of_subset_of_nonneg,
    exact hQu,
    intros i hi1 hi2,
    simp only [one_div, inv_nonneg, nat.cast_nonneg],},
  have hQt : (rec_sum Q : ℝ) ≤ (∑ q in (finset.range(N+1)).filter(λ q, is_prime_pow q), (1:ℚ) /q),
  { exact_mod_cast hQr, },
  have hQs : (rec_sum Q : ℝ) ≤ 2*(log(log N)),
  { exact_mod_cast le_trans hQt hN, },
  have hQu : ε * (rec_sum Q : ℝ) ≤ ε*(2*(log(log N))),
  { exact (mul_le_mul_left hε).mpr hQs, },
  linarith,
  cases h_local,
  exfalso,
  have hi : (A.filter( λ n, ¬ n ∈ B)).card ≤ A.card,
  { apply finset.card_filter_le, },
  linarith,
  exact h_local,
end

-- Inductive heart of Lemma 5.6
lemma pruning_lemma_two_ind :
  ∀ᶠ (N : ℕ) in at_top, ∀ M α ε: ℝ, ∀ A ⊆ finset.range(N+1),
  (0 < M) → (M < N) → (0 < ε) → (4*ε*log(log N) < α ) →
  (∀ n ∈ A, M ≤ (n: ℝ)) →
  (α  ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε*M ∧ ε < rec_sum_local A q) →
  (∀ i : ℕ, ∃ A_i ⊆ A, (α - 1/M ≤ rec_sum A_i) ∧ (∀ q ∈ ppowers_in_set A_i,
    ε < rec_sum_local A_i q) ∧ ( i ≤ (A.filter( λ n, ¬ n ∈ A_i)).card
    ∨ (rec_sum A_i : ℝ) < α) )
  :=
begin
  filter_upwards [pruning_lemma_one],
  intros N hN M α ε A hA hM hMN hε hεα hMA hrec hsmooth i,
  induction i,
  use A,
  split,
  refl,
  have hM2 : 1 / M > 0, { simp only [one_div, gt_iff_lt, inv_pos], exact hM, },
  split,
  linarith,
  split,
  intros q hq,
  specialize hsmooth q hq,
  exact hsmooth.2,
  simp only [nat.nat_zero_eq_zero, true_or, zero_le', finset.filter_congr_decidable],
  cases i_ih with A_i i_ih,
  cases i_ih with hA_i i_ih,
  obtain ⟨i_ih1, i_ih2, i_ih3⟩ := i_ih,
  by_cases hr : (rec_sum A_i : ℝ) < α,
  use A_i,
  split,
  exact hA_i,
  split,
  exact i_ih1,
  split,
  exact i_ih2,
  right,
  exact hr,
  have hA_ir : A_i ⊆ finset.range(N+1), { exact finset.subset.trans hA_i hA, },
  let ε' := 2*ε,
  have hε' : 0 < ε', { rw zero_lt_mul_left, exact hε, norm_num, },
  specialize hN A_i hA_ir ε' hε',
  cases hN with B hN,
  cases hN with hB hN,
  obtain ⟨hN1, hN2⟩ := hN,
  have ht0 : α ≤ rec_sum A_i, {  exact not_lt.mp hr, },
  have hBne : B ≠ ∅, {
    by_contra,
    rw ← rec_sum_eq_zero_iff at h,
    rw h at hN1,

    have ht : α ≤ ε' * 2 * log(log(N)),
    { norm_cast at hN1, linarith, },
    have ht1 : 4* ε * log(log N) < ε' * 2 * log(log N),
    { linarith, },
    have ht2 : ε * (4*log(log N)) < ε' * (2 * log(log N)),
    { linarith, },
    have ht21 : ε' * (2 * log(log N)) = ε * (4 * log(log N)),
    { rw mul_assoc 2 ε (2*log(log N)),
      rw ← mul_assoc 2 ε (2*log(log N)),
      rw mul_comm 2 ε,
      rw mul_assoc ε 2 (2*log(log N)),
      rw ← mul_assoc 2 2 (log(log N)),
      norm_num,
   },
    have ht22 : ε * (4*log(log N)) < ε * (4 * log(log N)),
    { rw ht21 at ht2, exact ht2, },
    have ht3 : 4*log(log N) < 4*log(log N),
    {  exact (mul_lt_mul_left hε).mp ht22,
      },
    linarith,
    apply finset.eq_empty_iff_forall_not_mem.mp,
    exact h,
   },
  have hBexists : ∃ (x : ℕ), x ∈ B, {
    by_contra,
    apply hBne,
    rw finset.eq_empty_iff_forall_not_mem,
    intros x hx,
    apply h,
    use x,
    exact hx,
    },
  cases hBexists with x hx,
  let A_i' := A_i.erase x,
  use A_i',
  have hxA1 : x ∈ A_i, {exact hB hx,},
  have hxA2 : x ∈ A, {exact hA_i hxA1,},
  have h3 : A_i' ⊆ A_i, { apply finset.erase_subset, },
  split,
  exact finset.subset.trans h3 hA_i,
  split,
  have hrs2 : (rec_sum A_i:ℝ) - 1/x = (rec_sum A_i':ℝ),
  { rw rec_sum,
    rw ← @finset.add_sum_erase _ _ _ _ A_i _ x _,
    rw rec_sum,
    push_cast,
    simp only [add_tsub_cancel_left, eq_self_iff_true, finset.sum_congr],
    exact hB hx, },
  rw ← hrs2,
  have htx : M ≤ (x : ℝ),
  { have htxx: x ∈ A_i, { exact hB hx, },
    specialize hMA x,
    apply hMA,
    exact hA_i htxx,
    },
  have ht2 : (1:ℝ)/x ≤ 1/M, { exact one_div_le_one_div_of_le hM htx, },
  linarith,
  split,
  intros q hq,
  by_cases hxq : q ∣ x ∧ coprime q (x/q),
  have hlocalpart : (local_part A_i' q) = (local_part A_i q).erase x,
  { ext,
    split,
    intro ha,
    rw finset.mem_erase,
    rw local_part at ha,
    rw finset.mem_filter at ha,
    split,
    intro ha2,
    apply finset.not_mem_erase x A_i,
    rw ha2 at ha,
    exact ha.1,
    rw local_part,
    rw finset.mem_filter,
    split,
    exact h3 ha.1,
    exact ha.2,
    intro ha,
    rw finset.mem_erase at ha,
    rw local_part,
    rw finset.mem_filter,
    rw local_part at ha,
    rw finset.mem_filter at ha,
    split,
    rw finset.mem_erase,
    refine ⟨ha.1, ha.2.1⟩,
    exact ha.2.2,
  },
  have hlocal : rec_sum_local A_i q = rec_sum_local A_i' q + q/x,
  { rw rec_sum_local,
    rw rec_sum_local,
    rw hlocalpart,
    rw @finset.sum_erase_add _ _ _ _ (local_part A_i q) _ x _,
    rw local_part,
    rw finset.mem_filter,
    refine ⟨hB hx, hxq⟩,
   },
  have hlocal2 : rec_sum_local A_i q - q/x = rec_sum_local A_i' q,
  { rw ← add_left_inj ((q:ℚ)/x), simp only [sub_add_cancel], exact hlocal, },
  rw ← hlocal2,
  push_cast,
  have hppB : q ∈ ppowers_in_set B,
  { rw ppowers_in_set, rw finset.mem_bUnion, use x, split, exact hx,
    rw finset.mem_filter, split, rw nat.mem_divisors, split, exact hxq.1,
    intro hxz, rw hxz at hx,
    have hx1 : 0 ∈ A_i, {exact hB hx,},
    have hx2 : 0 ∈ A, {exact hA_i hx1,},
    specialize hMA 0 hx2, norm_cast at hMA, linarith,
    split, rw ppowers_in_set at hq, rw finset.mem_bUnion at hq,
    cases hq with a hq,
    cases hq with ha hq,
    rw finset.mem_filter at hq, exact hq.2.1,
    exact hxq.2,
     },
  specialize hN2 q hppB,
  have hlocal3 : (rec_sum_local B q :ℝ)≤ rec_sum_local A_i q,
  { norm_cast, apply rec_sum_local_mono, exact hB, },
  have hll : ε+ε < rec_sum_local A_i q,
  { have hεaux : ε' = ε + ε, { exact two_mul ε, },
    rw hεaux at hN2, linarith, },
  have hll2 : (q:ℝ)/x ≤ ε,
  {
    specialize hMA x hxA2,
    refine (div_le_iff _).mpr _,
    linarith,
    have hppA : ppowers_in_set A_i' ⊆ ppowers_in_set A,
    { apply ppowers_in_set_subset, exact finset.subset.trans h3 hA_i,},
    have hppAq : q ∈ ppowers_in_set A, { exact hppA hq, },
    specialize hsmooth q hppAq,
    obtain hsmooth1 := hsmooth.1,
    have haux9 : ε * M ≤ ε * x, {
      apply mul_le_mul_of_nonneg_left, exact hMA, linarith,},
    linarith,
    },
  linarith,
  have hrecl : rec_sum_local A_i q = rec_sum_local A_i' q,
  { have hlocalaux : local_part A_i q = local_part A_i' q,
   { rw local_part, rw local_part, ext, rw finset.mem_filter, rw finset.mem_filter,
     split, intro ha, split, rw finset.mem_erase, split, intro hax,
     apply hxq, rw hax at ha, exact ha.2, exact ha.1,
     exact ha.2, intro ha, split, exact h3 ha.1, exact ha.2, },
   rw rec_sum_local, rw rec_sum_local,
   rw hlocalaux,
  },
  have hppA_i : ppowers_in_set A_i' ⊆ ppowers_in_set A_i,
    { apply ppowers_in_set_subset, exact h3,},
  have hppA_iq : q ∈ ppowers_in_set A_i, { exact hppA_i hq, },
  specialize i_ih2 q hppA_iq,
  rw ← hrecl, exact i_ih2,
  left,
  have hcard : (finset.filter (λ (n : ℕ), n ∉ A_i) A).card <
     (finset.filter (λ (n : ℕ), n ∉ A_i') A).card,
  {
    apply finset.card_lt_card,
    rw finset.ssubset_iff_of_subset,
    use x, split, rw finset.mem_filter, split, exact hxA2,
    apply finset.not_mem_erase, intro hxaux, rw finset.mem_filter at hxaux,
    apply hxaux.2, exact hxA1,
    refine finset.subset_iff.mpr _,
    intros y hy, rw finset.mem_filter, rw finset.mem_filter at hy,
    split, exact hy.1, intro hy2, apply hy.2, exact h3 hy2,
   },
  have hcard' : (finset.filter (λ (n : ℕ), n ∉ A_i) A).card + 1 ≤
     (finset.filter (λ (n : ℕ), n ∉ A_i') A).card,
  { exact nat.succ_le_iff.mpr hcard, },
  rw nat.succ_eq_add_one,
  cases i_ih3 with hf1 hf2,
  linarith,
  exfalso,
  linarith,
end

-- Lemma 5.6
lemma pruning_lemma_two :
  ∀ᶠ (N : ℕ) in at_top, ∀ M α ε: ℝ, ∀ A ⊆ finset.range(N+1),
  (0 < M) → (M < N) → (ε > 0) → (4*ε*log(log N) < α ) →
  (∀ n ∈ A, M ≤ (n: ℝ)) →
  (α + 2*ε*log(log N) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε*M) →
  ∃ B ⊆ A, ( (rec_sum B : ℝ) < α) ∧ ( α - 1/M ≤ rec_sum B) ∧
  (∀ q ∈ ppowers_in_set B, ε <
    rec_sum_local B q)
  :=
begin
 filter_upwards [pruning_lemma_one, pruning_lemma_two_ind],
 intros N h h2 M α ε A hA hMz hMN hε hεα hMA hrecA hsmooth,
 specialize h A hA ε hε,
 cases h with A' h,
 cases h with hA' h,
 obtain ⟨hA'1, hA'3⟩ := h,
 have hA'2 : A' ⊆ finset.range(N+1),
 { exact finset.subset.trans hA' hA, },
 have hMA' : ∀ n ∈ A', M ≤ (n: ℝ),
 { intros n hn, apply hMA, exact hA' hn, },
 have hrecA' : α ≤ rec_sum A',
 { linarith, },
 have hsmooth2 : ∀ (q : ℕ), q ∈ ppowers_in_set A' → ↑q ≤ ε * M ∧ ε < ↑(rec_sum_local A' q),
 { intros q hq,
   split,
  apply hsmooth,
  have hpp : ppowers_in_set A' ⊆ ppowers_in_set A,
  { apply ppowers_in_set_subset, exact hA', },
  exact hpp hq,
  apply hA'3,
  exact hq,
  },
 let i := A'.card + 1,
 specialize h2 M α ε A' hA'2 hMz hMN hε hεα hMA' hrecA' hsmooth2 i,
 cases h2 with B h2,
 cases h2 with hB h2,
 use B,
 split,
 exact finset.subset.trans hB hA',
 split,
 cases h2.2.2 with ha1 ha2,
 exfalso,
 have hi : (A'.filter( λ n, ¬ n ∈ B)).card ≤ A'.card,
 { apply finset.card_filter_le, },
 linarith,
 exact ha2,
 split,
 exact h2.1,
 exact h2.2.1,
end


lemma main_tech_lemma_ind :
  ∀ᶠ (N : ℕ) in at_top, ∀ M ε y w : ℝ, ∀ A ⊆ finset.range(N+1),
  (0 < M) → (M < N) → (0 < ε) → (2*M > w) → (1/M < ε*log(log N)) →
  (1 < y) → ( y + 1 ≤ w) →
  (3*ε*log(log N) ≤ 2/(w^2)) → (∀ n ∈ A, M ≤ (n: ℝ)) →
  (2/y + 2*ε*log(log N) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε*M) →
  (∀ n ∈ A, ∃ d : ℕ, (y ≤ d) ∧ ((d:ℝ) ≤ w) ∧ d ∣ n) →
  (∀ i : ℕ, ∃ A_i ⊆ A, ∃ d_i : ℕ, (y ≤ d_i) ∧ d_i ≤ (⌈y⌉₊+i) ∧ d_i ≤ ⌊w⌋₊ ∧
   rec_sum A_i < 2/d_i ∧ (2:ℝ)/d_i-1/M ≤ rec_sum A_i ∧
   (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
   (∀ n ∈ A_i, ∀ k : ℕ, k ∣ n → k < d_i → (k:ℝ) < y) ∧
   ((∃ n ∈ A_i, d_i ∣ n) ∨
   (∀ n ∈ A_i, ∀ k : ℕ, k ∣ n → k ≤ (⌈y⌉₊+i) → k ≤ ⌊w⌋₊ → (k:ℝ) < y)))
  :=
begin
     sorry,
    /-
 filter_upwards [pruning_lemma_two],
 intros N hN M ε y w A hA hM hMN hε hMw hMN2 hy hyw hNw hMA hrec hsmooth hdiv i,
 have h_largeN : 0 < log(log N), { sorry, },
 -- Preliminary estimates that will be convenient later
 have hy01 : 0 < y, {
   apply @lt_of_lt_of_le _ _ 0 1 y zero_lt_one (le_of_lt hy), },
 have hy12 : 2 ≤ y + 1, {refine add_le_add_right _ 1, apply le_of_lt hy, },
 have hobvaux : (⌈y⌉₊:ℝ) < y + 1, { apply nat.ceil_lt_add_one,
   apply le_of_lt hy01, },
 have hwzero : 0 ≤ w, { apply @le_trans _ _ 0 (y+1) w,
   apply @le_trans _ _ 0 2 (y+1) zero_le_two hy12, exact hyw, },
 have hyw2 : ⌈y⌉₊ ≤ ⌊w⌋₊, {
   rw nat.le_floor_iff, apply @le_trans _ _ (⌈y⌉₊:ℝ) (y+1) w,
   apply le_of_lt, apply nat.ceil_lt_add_one,
   apply @le_trans _ _ 0 1 y zero_le_one (le_of_lt hy), exact hyw, exact hwzero,
   },
 have hqaux : (⌊w⌋₊:ℝ) ≤ w, { apply nat.floor_le hwzero, },
 have hεNaux : 4*ε*log(log N) < 2*(3*ε*log(log N)), {
     rw ← mul_assoc, apply mul_lt_mul, rw ← mul_assoc,
     apply mul_lt_mul, norm_num, refl, exact hε,
     apply mul_nonneg zero_le_two, apply le_of_lt, exact zero_lt_three, refl,
     exact h_largeN, apply mul_nonneg zero_le_two,
     apply mul_nonneg (le_of_lt zero_lt_three) (le_of_lt hε),
   },
 have hεNaux2 : 2*(3*ε*log(log N)) ≤ 2*((2:ℝ)/w^2), {
     apply (mul_le_mul_left zero_lt_two).mpr hNw, },
 have hwaux : 2* w ≤ w^2,
   { rw pow_two, apply mul_le_mul, apply @le_trans _ _ 2 (y+1) w hy12 hyw,
     refl, exact hwzero, exact hwzero, },
 -- The actual proof begins, by induction
 induction i,
 -- The case i=0
 let α := (2:ℚ)/⌈y⌉₊,
 have hα : 4*ε*log(log N) < α, {
   have hα1 : 2*((2:ℝ)/w^2) ≤ 2/⌈y⌉₊, { rw ← mul_div_assoc,
   rw div_le_div_iff, rw mul_assoc, apply mul_le_mul, refl,
   have hyw2' : (⌈y⌉₊:ℝ) ≤ ⌊w⌋₊, { exact_mod_cast hyw2,},
   apply @le_trans _ _ ((2:ℝ)*⌈y⌉₊) (2*w) (w^2), apply mul_le_mul, refl,
   apply @le_trans _ _ (⌈y⌉₊:ℝ) (⌊w⌋₊:ℝ) w hyw2' hqaux, exact nat.cast_nonneg ⌈y⌉₊,
   exact zero_le_two, exact hwaux, apply mul_nonneg zero_le_two (nat.cast_nonneg ⌈y⌉₊),
   exact zero_le_two, rw sq_pos_iff, rw ne_iff_lt_or_gt, right,
   apply @lt_of_lt_of_le _ _ 0 (y+1) w,
   apply @lt_of_lt_of_le _ _ 0 2 (y+1) zero_lt_two hy12, exact hyw,
   norm_cast, rw nat.lt_ceil, norm_cast, exact hy01,
    },
  push_cast,
  apply @lt_of_lt_of_le _ _ (4*ε*log(log N)) (2*(3*ε*log(log N))) (2 /⌈y⌉₊) hεNaux,
  apply @le_trans _ _ (2*(3*ε*log(log N))) (2*((2:ℝ)/w^2)) (2/⌈y⌉₊) hεNaux2 hα1,
  },
 have hαaux : (α : ℝ) = 2/⌈y⌉₊, { push_cast,},
 have hrec2 : (α:ℝ) + 2*ε*log(log N) ≤ rec_sum A, {
   rw hαaux, apply @add_le_of_add_le_right _ (2/y) (2*ε*log(log N))
      (rec_sum A) ((2:ℝ)/⌈y⌉₊), exact hrec,
      refine div_le_div_of_le_left zero_le_two _ _, exact hy01, apply nat.le_ceil,
  },
 specialize hN M α ε A hA hM hMN hε hα hMA hrec2 hsmooth,
 rcases hN with ⟨B,hB,hN⟩,
 refine ⟨B, hB, ⌈y⌉₊, nat.le_ceil y, _⟩,
 split, refl, split,
 apply nat.le_floor, apply @le_trans _ _ (⌈y⌉₊:ℝ) (⌊w⌋₊:ℝ) w, norm_cast,
 exact hyw2, exact hqaux,
 split, exact_mod_cast hN.1, split, rw ← hαaux, exact hN.2.1,
 refine ⟨hN.2.2, λ n hn k hk1 hk2, _, _⟩,
 rw ← nat.lt_ceil, exact hk2,
 by_cases hp : (∃ (n : ℕ) (H : n ∈ B), ⌈y⌉₊ ∣ n),
 left, exact hp, right, intros n hn k hk1 hk2 hk3,
 simp only [add_zero, nat.nat_zero_eq_zero] at hk2,
 rw ← nat.lt_ceil,
 have hkaux : k ≠ ⌈y⌉₊, {
   intro hky,
   apply hp, use n, rw ← hky, refine ⟨hn,hk1⟩,
   },
 exact (ne.le_iff_lt hkaux).mp hk2,
 -- The inductive case
 rcases i_ih with ⟨A_i, hA_i, d_i, hstock⟩,
 obtain hstock1 := hstock.2.2.2.2.2.2.1,
 by_cases hdiv2 : (∃ n ∈ A_i, d_i ∣ n),
 use A_i, split, exact hA_i, use d_i, split, exact hstock.1,
 split, apply le_trans hstock.2.1 _, apply add_le_add_left (nat.le_succ i_n),
 refine ⟨hstock.2.2.1, hstock.2.2.2.1, hstock.2.2.2.2.1, hstock.2.2.2.2.2.1,
   hstock.2.2.2.2.2.2.1, _⟩,
 left, exact hdiv2,
 let d_i' := min (⌈y⌉₊+i_n+1) ⌊w⌋₊,
 have hd_i' : d_i + 1 ≤ d_i', {
   rw le_min_iff, split, apply add_le_add_right hstock.2.1, rw nat.succ_le_iff,
   rw ← ne.le_iff_lt, exact hstock.2.2.1, intro htaux,
   have hA_in : A_i.nonempty, {
     cases finset.eq_empty_or_nonempty A_i with hy1 hy2, exfalso,
     obtain hstock2 := hstock.2.2.2.2.1, rw hy1 at hstock2, rw rec_sum_empty at hstock2,
     norm_cast at hstock2, rw sub_nonpos at hstock2, rw div_le_div_iff at hstock2,
     have hA_in' : (d_i:ℝ) ≤ w, { rw htaux, exact hqaux, },
     rw one_mul at hstock2, apply @not_lt_of_le _ _ (2*M) w (hstock2.trans hA_in') hMw,
     apply lt_of_lt_of_le hy01 hstock.1, exact hM, exact hy2,
      },
   obtain ⟨x,hx⟩ := hA_in,
   have hx' : x ∈ A, { exact hA_i hx, },
   specialize hdiv x hx',
   cases hdiv with d hdiv,
   have hd_i'1 : d < d_i, {
     rw ← ne.le_iff_lt, rw htaux, rw nat.le_floor_iff, exact hdiv.2.1, exact hwzero,
     intro hdaux1, apply hdiv2, use x, split, exact hx, rw ← hdaux1, exact hdiv.2.2,
  },
   specialize hstock1 x hx d hdiv.2.2 hd_i'1,
   apply @not_le_of_lt _ _ (d:ℝ) y hstock1 hdiv.1,
    },
 let α' := (2:ℚ)/d_i',
 have hα'aux : (α' : ℝ) = 2/d_i', { push_cast, },
 have hqaux' : (d_i':ℝ) ≤ ⌊w⌋₊, {
      norm_cast, apply min_le_right, },
 have hqaux'' : (d_i':ℝ) ≤ w, { exact hqaux'.trans hqaux, },
  have hrec5'''aux : (0:ℝ) < d_i, { apply lt_of_lt_of_le hy01 hstock.1, },
  have hrec5''': 0 < d_i, { exact_mod_cast hrec5'''aux, },
  have hrec6''': 1 ≤ d_i, { rw nat.succ_le_iff, exact hrec5''', },
  have hqauxx : (1:ℝ) < d_i', { norm_cast,
  apply @lt_of_lt_of_le _ _ 1 (d_i+1) d_i', apply nat.succ_lt_succ hrec5''', exact hd_i',
   },
 have hα' : 4*ε*log(log N) < α', {
   have hα'1 : 2*((2:ℝ)/w^2) ≤ 2/d_i', { rw ← mul_div_assoc,
   rw div_le_div_iff, rw mul_assoc, apply mul_le_mul, refl,
   linarith, apply mul_nonneg, norm_num, linarith, norm_num,
   rw sq_pos_iff, linarith, linarith,
    },
   linarith,
  },

 have hrec2 : (α':ℝ) + 2*ε*log(log N) ≤ rec_sum A_i, {
  rw hα'aux,
  have hrec3p : (d_i:ℝ) ≤ (d_i':ℝ)-1, {
    have hrec3p' : (d_i:ℝ) + 1 ≤ d_i', {exact_mod_cast hd_i',},
    linarith, },
  have hrec3 : (2:ℝ)/(d_i'-1) - 1/M  ≤ rec_sum A_i, {
    have hrec3' : (2:ℝ)/(d_i'-1) ≤ 2/d_i, {
      refine div_le_div_of_le_left _ _ _, norm_num, exact hrec5'''aux,
      exact hrec3p,
     },
    linarith,
     },
  have hrec5 : (2:ℝ)/d_i'^2 ≤ 2/(d_i'-1) - 2/d_i', {
    rw div_sub_div,
    have hrec5'' : ((d_i':ℝ)-1)*d_i' = d_i'^2 - d_i', {
      rw sub_mul, rw ← pow_two, linarith,},
    have hrec5' : (2:ℝ)*d_i' - (d_i'-1)*2 = 2, {
      rw sub_mul, linarith, },
    rw hrec5',
    refine div_le_div_of_le_left _ _ _, norm_num,
    rw hrec5'', rw sub_pos, nth_rewrite 0 ← pow_one (d_i':ℝ),
    apply pow_lt_pow, norm_cast,
    linarith, norm_num, rw hrec5'', apply sub_le_self,
    linarith, intro hwaste, rw sub_eq_iff_eq_add at hwaste,
    simp only [zero_add] at hwaste, linarith, linarith,
    },

  have hrec6 :(2:ℝ)/w^2 ≤ 2/d_i'^2, {
    refine div_le_div_of_le_left _ _ _, norm_num,
    apply sq_pos_of_ne_zero, norm_cast, intro hrecaux,
    rw min_eq_iff at hrecaux,
    cases hrecaux with hpaux1 hpaux2,
    obtain hpaux1' := hpaux1.1, linarith,
    obtain hpaux2' := hpaux2.1, rw nat.floor_eq_zero at hpaux2',
    linarith, apply sq_le_sq',
    linarith, linarith, },
  linarith,
   },
 have hA_i' : A_i ⊆ finset.range(N+1),
 { exact finset.subset.trans hA_i hA, },
 have hMA' : (∀ (n : ℕ), n ∈ A_i → M ≤ n), {
   intros n hn, have haux9 : n ∈ A, { exact hA_i hn, },
   exact hMA n haux9,
    },
 have hsmooth' : (∀ q ∈ ppowers_in_set A_i, (q : ℝ) ≤ ε*M), {
   intros q hq,
   have hpp' : ppowers_in_set A_i ⊆ ppowers_in_set A,
   { exact ppowers_in_set_subset hA_i, },
   have hq' : q ∈ ppowers_in_set A, { exact hpp' hq, },
   exact hsmooth q hq',},
specialize hN M α' ε A_i hA_i' hM hMN hε hα' hMA' hrec2 hsmooth',
 rcases hN with ⟨B, hB, hN⟩,
 use B, split, exact finset.subset.trans hB hA_i,
 use d_i', split, rw ← nat.ceil_le, rw le_min_iff,
 split, linarith, exact hyw2,
 split, apply min_le_left, split, apply min_le_right,
 split, exact_mod_cast hN.1, split,
 have hα'aux : (α' : ℝ) = 2/d_i', { push_cast, },
 rw ← hα'aux, exact hN.2.1, split, exact hN.2.2,
 split,
 intros n hn k hk1 hk2,
 have hn2 : n ∈ A_i, { exact hB hn, },
 have hk2' : k ≤ d_i, {
   rw hd_i' at hk2, exact nat.lt_succ_iff.mp hk2,},
 have hk2'' : k < d_i, {
   rw ← ne.le_iff_lt, exact hk2',
   intro hkdiv, apply hdiv2, use n, use hn2, rw ← hkdiv,
   exact hk1, },
 exact hstock1 n hn2 k hk1 hk2'',
 by_cases hd_i'div : (∃ (n : ℕ) (H : n ∈ B), d_i' ∣ n),
 left, exact hd_i'div, right,
 intros n hn k hk1 hk2 hk3,
 have hn2 : n ∈ A_i, { exact hB hn, },
 have hk2' : k ≤ d_i', { rw le_min_iff, split,
   exact hk2, exact hk3, },
 have hk2'' : k < d_i', {
   rw ← ne.le_iff_lt, exact hk2', intro hkaux4,
   apply hd_i'div, use n, split, exact hn,
   rw ← hkaux4, exact hk1, },
 have hk2''' : k ≤ d_i, { rw hd_i' at hk2'',
     exact nat.lt_succ_iff.mp hk2'', },
 have hk2'''' : k < d_i, { rw ← ne.le_iff_lt, exact hk2''',
 intro haux5, apply hdiv2, use n, split, exact hn2,
  rw ← haux5, exact hk1, },
 exact hstock1 n hn2 k hk1 hk2'''',-/
end


lemma main_tech_lemma :
  ∀ᶠ (N : ℕ) in at_top, ∀ M ε y w : ℝ, ∀ A ⊆ finset.range(N+1),
  (0 < M) → (M < N) → (0 < ε) → (2*M > w) → (1/M < ε*log(log N)) →
  (1 < y) → ( y + 1 ≤ w) →
  (3*ε*log(log N) ≤ 2/(w^2)) → (∀ n ∈ A, M ≤ (n: ℝ)) →
  (2/y + 2*ε*log(log N) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε*M) →
  (∀ n ∈ A, ∃ d : ℕ, (y ≤ d) ∧ ((d:ℝ) ≤ w) ∧ d ∣ n) →
  (∃ A' ⊆ A, ∃ d : ℕ, A' ≠ ∅ ∧ (y ≤ d) ∧ ((d:ℝ) ≤ w) ∧ rec_sum A' < 2/d ∧
  (2:ℝ)/d-1/M ≤ rec_sum A' ∧ (∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q)
  ∧ (∃ n ∈ A', d ∣ n) ∧ (∀ n ∈ A', ∀ k : ℕ, k ∣ n → k < d → (k:ℝ) < y))
  :=
begin
  sorry,
  /-
 -- Also filter so that log log N > 0
 filter_upwards [main_tech_lemma_ind],
 intros N hN M ε y w A hA hM hMN hε hMw hMN2 hy hyw hNw hAM hrec hsmooth hdiv,
 have h_largeN : 0 < log(log N), { sorry, },
 have hy01 : 0 < y, {
   apply @lt_of_lt_of_le _ _ 0 1 y zero_lt_one (le_of_lt hy), },
 have hy12 : 2 ≤ y + 1, {refine add_le_add_right _ 1, apply le_of_lt hy, },
 have hwzero : 0 ≤ w, { apply @le_trans _ _ 0 (y+1) w,
   apply @le_trans _ _ 0 2 (y+1) zero_le_two hy12, exact hyw, },
 let i := ⌊w⌋₊ - ⌈y⌉₊,
 specialize hN M ε y w A hA hM hMN hε hMw hMN2 hy hyw hNw hAM hrec hsmooth hdiv i,
 rcases hN with ⟨A', hA', d, hN⟩,
 use A', split, exact hA', use d,
 have hdw : (d:ℝ) ≤ w, {
   have hauxw : (⌊w⌋₊:ℝ) ≤ w, { apply nat.floor_le hwzero, },
  have hauxw2 : (d:ℝ) ≤ (⌊w⌋₊:ℝ), {exact nat.cast_le.mpr hN.2.2.1, },
  exact hauxw2.trans hauxw,
  },
 have hA'ne : A' ≠ ∅, {
 intro hA'em,
 have hreczero : rec_sum A' = 0, {  rw hA'em, apply rec_sum_empty, },
 rw hreczero at hN,
 norm_cast at hN,
 have haux1 : (2:ℝ)/d ≤ 1/M, { apply sub_nonpos.mp hN.2.2.2.2.1, },
 have haux2 : (2:ℝ)/w ≤ 2/d,
 { refine div_le_div_of_le_left zero_le_two _ _,
   apply @lt_of_lt_of_le _ _ 0 y (d:ℝ), exact hy01, exact hN.1, exact hdw,
   },
 have haux3 : (2:ℝ)/w^2 ≤ 2/w,
 { refine div_le_div_of_le_left zero_le_two _ _,
   apply @lt_of_lt_of_le _ _ 0 (y+1) w,
   apply @lt_of_lt_of_le _ _ 0 y (y+1), exact hy01, exact le_add_of_nonneg_right zero_le_one,
   exact hyw, refine le_self_pow _ _, apply le_trans one_le_two _,
   apply le_trans hy12 hyw, exact one_le_two, },
 have haux4: 3*ε*log(log N) < ε*log(log N), {
   apply lt_of_le_of_lt hNw, apply lt_of_le_of_lt haux3, apply lt_of_le_of_lt haux2,
   apply lt_of_le_of_lt haux1 hMN2,
  },
 rw mul_lt_mul_right at haux4, rw mul_lt_iff_lt_one_left at haux4,
 norm_num at haux4, exact hε, exact h_largeN,},
 split, exact hA'ne, split, exact hN.1,
 split, exact hdw, split, exact hN.2.2.2.1, split, exact hN.2.2.2.2.1,
 split, exact hN.2.2.2.2.2.1, split,
 cases hN.2.2.2.2.2.2.2 with hv1 hv2, exact hv1,
 exfalso,
 have hAexists : ∃ (x : ℕ), x ∈ A', {
    by_contra, apply hA'ne, rw finset.eq_empty_iff_forall_not_mem,
    intros x hx, apply h, use x, exact hx,
    },
 cases hAexists with x hx,
 have hx2 : x ∈ A, {exact hA' hx,},
 specialize hdiv x hx2,
 cases hdiv with m hdiv,
 have htempw : m ≤ ⌊w⌋₊, {
   apply nat.le_floor, exact hdiv.2.1,
  },
 have htemp : m ≤ ⌈y⌉₊ + i, {
   have hobvious : ⌈y⌉₊ + i = ⌊w⌋₊, {
     rw ← add_tsub_assoc_of_le, simp only [add_tsub_cancel_left, eq_self_iff_true],
     apply nat.le_floor,
     have hobvaux : (⌈y⌉₊:ℝ) < y + 1, { apply nat.ceil_lt_add_one, apply le_of_lt hy01,  },
     apply le_of_lt, apply lt_of_lt_of_le hobvaux hyw,
     },
   rw hobvious, exact htempw,
  },
 specialize hv2 x hx m hdiv.2.2 htemp htempw, linarith,
 exact hN.2.2.2.2.2.2.1,
 -/
end
