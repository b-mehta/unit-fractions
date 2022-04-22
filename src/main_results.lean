/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import for_mathlib.basic_estimates
import defs

/-!
# Title

This file should contain a formal proof of https://arxiv.org/pdf/2112.03726.pdf, but for now it
contains associated results useful for that paper.
-/

open_locale big_operators -- this lets me use ∑ and ∏ notation
open filter finset real
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

-- The inductive heart of Lemma 5.5
lemma pruning_lemma_one_prec (A : finset ℕ) (ε : ℝ) (i : ℕ) :
  ∃ A_i ⊆ A, ∃ Q_i ⊆ ppowers_in_set A,
  (disjoint Q_i (ppowers_in_set A_i)) ∧
  ((rec_sum A : ℝ) - ε * rec_sum Q_i ≤ rec_sum A_i) ∧
  (i ≤ (A \ A_i).card ∨ ∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) :=
begin
  induction i with i ih,
  { exact ⟨A, finset.subset.rfl, ∅, by simp⟩ },
  obtain ⟨A', hA', Q', hQ', hQA', hr, ih⟩ := ih,
  by_cases hq : ∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q,
  { exact ⟨A', hA', Q', hQ', hQA', hr, or.inr hq⟩ },
  obtain ⟨q', hq', h4⟩ := not_ball.mp hq,
  have hq'zero : q' ≠ 0 := ne_of_mem_of_not_mem hq' zero_not_mem_ppowers_in_set,
  have hq'zero' : (q' : ℚ) ≠ 0 := by exact_mod_cast hq'zero,
  let A'' := A'.filter (λ n, ¬ (q' ∣ n ∧ coprime q' (n / q'))),
  refine ⟨A'', (A'.filter_subset _).trans hA', _⟩,
  let Q'' := insert q' Q',
  have hq'' : q' ∉ Q' := finset.disjoint_right.1 hQA' hq',
  refine ⟨Q'', _, _, _, _⟩,
  { exact finset.insert_subset.2 ⟨ppowers_in_set_subset hA' hq', hQ'⟩ },
  { refine finset.disjoint_insert_left.2 ⟨_, _⟩,
    { simp [A'', ppowers_in_set] {contextual := tt} },
    exact hQA'.mono_right (ppowers_in_set_subset (finset.filter_subset _ _)) },
  { have hrs : (rec_sum Q'' : ℝ) = rec_sum Q' + 1 / q',
    { rw [rec_sum, rec_sum, finset.sum_insert hq'', add_comm, rat.cast_add, rat.cast_div,
        rat.cast_coe_nat, rat.cast_one] },
    have hrs2a : rec_sum A'' + rec_sum_local A' q' / q' = rec_sum A' ,
    { simp only [rec_sum, rec_sum_local, div_eq_mul_one_div (q' : ℚ)],
      rw [←finset.mul_sum, mul_div_cancel_left _ hq'zero', add_comm, ←finset.sum_union, local_part,
        finset.filter_union_filter_neg_eq],
      exact finset.disjoint_filter_filter_neg _ _ },
    have hrs3 : (rec_sum A' : ℝ) ≤ rec_sum A'' + ε * (1 / q'),
    { rw [←hrs2a, rat.cast_add, add_le_add_iff_left, rat.cast_div, mul_one_div, rat.cast_coe_nat],
      exact (div_le_div_right (by rwa [nat.cast_pos, pos_iff_ne_zero])).2 (le_of_not_lt h4) },
    rw hrs,
    linarith only [hrs, hrs3, hr] },
  left,
  rw nat.succ_le_iff,
  refine (ih.resolve_right hq).trans_lt _,
  apply finset.card_lt_card,
  rw ssubset_iff_of_subset (sdiff_subset_sdiff subset.rfl (filter_subset _ _)),
  simp only [ppowers_in_set, mem_bUnion, mem_filter, exists_prop, nat.mem_divisors,
    and_assoc] at hq',
  obtain ⟨x, hx₁, hx₂, hx₃, -, hx₅⟩ := hq',
  refine ⟨x, _⟩,
  simp [hx₁, hx₂, hx₅, hA' hx₁],
end

lemma explicit_mertens :
  ∀ᶠ (N : ℕ) in at_top,
  ((∑ q in (finset.range (N + 1)).filter is_prime_pow, 1 / q) : ℝ) ≤ 2 * log (log N) :=
begin
  obtain ⟨b, hb⟩ := prime_power_reciprocal,
  -- take log log x ≥ b + 1 and log x ≥ 1, then done
  sorry
end

-- Lemma 5.5
lemma pruning_lemma_one :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range (N + 1), ∀ ε : ℝ, 0 < ε →
    ∃ B ⊆ A,
      ((rec_sum A : ℝ) - ε * 2 * log (log N) ≤ rec_sum B) ∧
      (∀ q ∈ ppowers_in_set B, ε < rec_sum_local B q) :=
begin
  filter_upwards [explicit_mertens] with N hN A hA ε hε,
  obtain ⟨B, hB, Q, hQ, haux, h_recsums, h_local⟩ := pruning_lemma_one_prec A ε (A.card + 1),
  refine ⟨B, hB, _, _⟩,
  { have hQu : Q ⊆ (finset.range (N + 1)).filter is_prime_pow,
    { intros q hq,
      rw [finset.mem_filter, finset.mem_range],
      have hqA : q ∈ ppowers_in_set A := hQ hq,
      simp only [ppowers_in_set, finset.mem_bUnion, finset.mem_filter, finset.mem_range, exists_prop,
        and_assoc] at hqA,
      obtain ⟨a, ha, hqa, hq', hq''⟩ := hqA,
      exact ⟨(nat.divisor_le hqa).trans_lt (finset.mem_range.1 (hA ha)), hq'⟩ },
    have hQt : (rec_sum Q : ℝ) ≤ ∑ q in (finset.range (N + 1)).filter is_prime_pow, 1 / q,
    { simp only [rec_sum, rat.cast_sum, one_div, rat.cast_inv, rat.cast_coe_nat],
      exact finset.sum_le_sum_of_subset_of_nonneg hQu (by simp) },
    nlinarith },
  refine h_local.resolve_left _,
  rw [not_le, nat.lt_succ_iff],
  exact card_le_of_subset (sdiff_subset _ _)
end

-- Inductive heart of Lemma 5.6
lemma pruning_lemma_two_ind :
  ∀ᶠ (N : ℕ) in at_top, ∀ M α ε : ℝ, ∀ A ⊆ finset.range (N + 1),
  0 < M → M < N → 0 < ε → 4 * ε * log (log N) < α → (∀ n ∈ A, M ≤ ↑n) → α ≤ rec_sum A →
  (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M ∧ ε < rec_sum_local A q) →
  (∀ i : ℕ, ∃ A_i ⊆ A,
      (α - 1 / M ≤ rec_sum A_i) ∧
      (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
      (i ≤ (A \ A_i).card ∨ (rec_sum A_i : ℝ) < α) )
  :=
begin
  filter_upwards [pruning_lemma_one] with N hN M α ε A hA hM hMN hε hεα hMA hrec hsmooth i,
  induction i with i ih,
  { refine ⟨A, subset.rfl, _, λ q hq, (hsmooth _ hq).2, or.inl zero_le'⟩,
    exact (sub_le_self _ (by simp only [hM.le, one_div, inv_nonneg])).trans hrec },
  obtain ⟨A_i, hA_i, ih1, ih2, ih3⟩ := ih,
  by_cases hr : (rec_sum A_i : ℝ) < α,
  { exact ⟨A_i, hA_i, ih1, ih2, or.inr hr⟩ },
  have hA_ir : A_i ⊆ finset.range (N + 1) := hA_i.trans hA,
  let ε' := 2 * ε,
  obtain ⟨B, hB, hN1, hN2⟩ := hN A_i hA_ir ε' (mul_pos zero_lt_two hε),
  have ht0 : α ≤ rec_sum A_i := not_lt.1 hr,
  have hBexists : B.nonempty,
  { rw finset.nonempty_iff_ne_empty,
    rintro rfl,
    simp only [rec_sum_empty, rat.cast_zero, sub_nonpos] at hN1,
    have ht1 : 4 * ε * log (log N) < ε' * 2 * log (log N),
    { exact hεα.trans_le (ht0.trans hN1), },
    rw [mul_right_comm 2 ε] at ht1,
    linarith only [ht1] },
  cases hBexists with x hx,
  have hxA1 : x ∈ A_i, {exact hB hx,},
  have hxA2 : x ∈ A, {exact hA_i hxA1,},
  let A_i' := A_i.erase x,
  have h3 : A_i' ⊆ A_i, { apply finset.erase_subset, },
  refine ⟨A_i', h3.trans hA_i, _, _, _⟩,
  { have hrs2 : (rec_sum A_i : ℝ) - 1 / x = rec_sum A_i',
    { simp only [rec_sum, sub_eq_iff_eq_add, rat.cast_sum, one_div, rat.cast_inv, rat.cast_coe_nat,
        finset.sum_erase_add _ _ hxA1] },
    linarith only [ht0, one_div_le_one_div_of_le hM (hMA x (hA_i (hB hx))), hrs2] },
  { intros q hq,
    by_cases hxq : q ∣ x ∧ coprime q (x / q),
    { have hlocalpart : local_part A_i' q = (local_part A_i q).erase x := filter_erase _ _ _,
      have hlocal : rec_sum_local A_i q = rec_sum_local A_i' q + q / x,
      { rw [rec_sum_local, rec_sum_local, hlocalpart, finset.sum_erase_add],
        rw [local_part, finset.mem_filter],
        exact ⟨hB hx, hxq⟩ },
      have hlocal2 : rec_sum_local A_i q - q / x = rec_sum_local A_i' q,
      { rwa [sub_eq_iff_eq_add] },
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
        exact hxq.2 },
      specialize hN2 q hppB,
      have hlocal3 : (rec_sum_local B q :ℝ)≤ rec_sum_local A_i q,
      { norm_cast, apply rec_sum_local_mono, exact hB, },
      have hll : ε+ε < rec_sum_local A_i q,
      { have hεaux : ε' = ε + ε, { exact two_mul ε, },
        linarith, },
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
      linarith },
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
    specialize ih2 q hppA_iq,
    rw ← hrecl, exact ih2 },
  left,
  have hcard : (A \ A_i).card < (A \ A_i').card,
  {
    apply finset.card_lt_card,
    rw finset.ssubset_iff_of_subset,
    use x, split, rw finset.mem_sdiff, split, exact hxA2,
    apply finset.not_mem_erase, intro hxaux, rw finset.mem_sdiff at hxaux,
    apply hxaux.2, exact hxA1,
    refine finset.subset_iff.mpr _,
    intros y hy, rw finset.mem_sdiff, rw finset.mem_sdiff at hy,
    split, exact hy.1, intro hy2, apply hy.2, exact h3 hy2,
   },
  have hcard' : (A \ A_i).card + 1 ≤ (A \ A_i').card,
  { exact nat.succ_le_iff.mpr hcard, },
  rw nat.succ_eq_add_one,
  cases ih3 with hf1 hf2,
  linarith,
  exfalso,
  linarith,
end
-- 668

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
 have hi : (A' \ B).card ≤ A'.card,
 { apply card_le_of_subset (sdiff_subset _ _) },
 linarith,
 exact ha2,
 split,
 exact h2.1,
 exact h2.2.1,
end

lemma main_tech_lemma_ind :
  ∀ᶠ (N : ℕ) in at_top, ∀ M ε y w : ℝ, ∀ A ⊆ finset.range(N+1),
  (0 < M) → (M < N) → (0 < ε) → (2*M > w) → (1/M < ε*log(log N)) →
  (1 ≤ y) → (2 ≤ w ) → (⌈y⌉₊ ≤ ⌊w⌋₊) →
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
  have : tendsto (λ N : ℕ, log (log N)) at_top at_top :=
    tendsto_log_at_top.comp (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top),
  filter_upwards [pruning_lemma_two, this (eventually_gt_at_top 0)],
  intros N hN h_largeN M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw2 hNw hMA hrec hsmooth hdiv i,
  -- Preliminary estimates that will be convenient later
  have hy01 : 0 < y := by apply lt_of_lt_of_le zero_lt_one hy,
  have hy12 : 2 ≤ y + 1 := add_le_add_right hy 1,
  have hobvaux : (⌈y⌉₊ : ℝ) < y + 1 := nat.ceil_lt_add_one hy01.le,
  have hwzero : 0 < w := by apply lt_of_lt_of_le zero_lt_two h2w,
  have hqaux : (⌊w⌋₊ : ℝ) ≤ w := nat.floor_le hwzero.le,
  have hεNaux : 4 * ε * log(log N) < 2 * (3 * ε * log (log N)),
  { have h₁ : (4 : ℝ) < 2 * 3 := by norm_num1,
    simpa only [mul_assoc] using (mul_lt_mul_right (mul_pos hε h_largeN)).2 h₁ },
  have hεNaux2 : 2 * (3 * ε * log (log N)) ≤ 2 * (2 / w ^ 2) := (mul_le_mul_left zero_lt_two).2 hNw,
  have hwaux : 2 * w ≤ w^2,
  { rw pow_two, exact mul_le_mul_of_nonneg_right h2w hwzero.le },
  -- The actual proof begins, by induction
  induction i,
  -- The case i=0
  { let α := (2 : ℚ) / ⌈y⌉₊,
    have hαaux : (α : ℝ) = 2 / ⌈y⌉₊,
    { rw [rat.cast_div, rat.cast_bit0, rat.cast_one, rat.cast_coe_nat] },
    have hα : 4 * ε * log (log N) < α,
    { have hα1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / ⌈y⌉₊,
      { rw [←mul_div_assoc, div_le_div_iff, mul_assoc, mul_le_mul_left],
        { refine le_trans (mul_le_mul_of_nonneg_left (le_trans _ hqaux) zero_le_two) hwaux,
          rwa nat.cast_le },
        { exact zero_lt_two },
        { exact pow_pos hwzero _ },
        { rwa [nat.cast_pos, nat.lt_ceil, nat.cast_zero] } },
      rw [rat.cast_div, rat.cast_bit0, rat.cast_one, rat.cast_coe_nat],
      exact hεNaux.trans_le (hεNaux2.trans hα1) },
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
    exact (ne.le_iff_lt hkaux).mp hk2 },
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
      rw ← ne.le_iff_lt, rw htaux, rw nat.le_floor_iff, exact hdiv.2.1, exact hwzero.le,
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
  have hα' : 4 * ε * log (log N) < α',
  {
    have hα'1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / d_i',
    { rw [←mul_div_assoc, div_le_div_iff, mul_assoc, mul_le_mul_left],
      { exact le_trans (mul_le_mul_of_nonneg_left (le_trans hqaux' hqaux) zero_le_two) hwaux },
      { exact zero_lt_two },
      { exact pow_pos hwzero _ },
      { exact zero_le_one.trans_lt hqauxx } },
    rw hα'aux,
    exact hεNaux.trans_le (hεNaux2.trans hα'1) },
  have hrec2 : (α' : ℝ) + 2 * ε * log (log N) ≤ rec_sum A_i,
  { rw hα'aux,
    have hrec3p : (d_i : ℝ) ≤ d_i' - 1,
    { rwa [le_sub_iff_add_le, ←nat.cast_add_one, nat.cast_le] },
    have hrec3 : (2 : ℝ) / (d_i' - 1) - 1 / M ≤ rec_sum A_i,
    { have hrec3' : (2 : ℝ) / (d_i' - 1) ≤ 2 / d_i,
      { exact div_le_div_of_le_left zero_le_two hrec5'''aux hrec3p },
      exact le_trans (sub_le_sub_right hrec3' _) hstock.2.2.2.2.1 },
    have hrec5 : (2:ℝ)/d_i'^2 ≤ 2/(d_i'-1) - 2/d_i',
    { rw div_sub_div,
      have hrec5'' : ((d_i' : ℝ) - 1) * d_i' = d_i' ^ 2 - d_i',
      { rw [sub_mul, sq, one_mul] },
      have hrec5' : (2 : ℝ) * d_i' - (d_i' - 1) * 2 = 2,
      { rw [sub_mul, mul_comm, sub_sub_cancel, one_mul] },
      rw hrec5',
      refine div_le_div_of_le_left zero_le_two _ _,
      rw hrec5'', rw sub_pos, nth_rewrite 0 ← pow_one (d_i':ℝ),
      { exact pow_lt_pow hqauxx one_lt_two },
      { rw hrec5'',
        apply sub_le_self,
        exact nat.cast_nonneg _ },
      { rw sub_ne_zero,
        exact hqauxx.ne' },
      { exact (zero_le_one.trans_lt hqauxx).ne' } },
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
    -- sorry
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
  rw ← hα'aux, exact hN.2.1, split, exact hN.2.2,
  split,
  intros n hn k hk1 hk2,
  have hn2 : n ∈ A_i, { exact hB hn, },
  cases hstock.2.2.2.2.2.2.2 with hnew1 hnew2,
  exfalso,
  apply hdiv2 hnew1,
  have hk2' : k ≤ ⌈y⌉₊ + i_n, { rw lt_min_iff at hk2,
  apply nat.le_of_lt_succ hk2.1, },
  have hk2'' : k ≤ ⌊w⌋₊, { rw lt_min_iff at hk2, apply le_of_lt hk2.2,},
  exact hnew2 n hn2 k hk1 hk2' hk2'',
  by_cases hd_i'div : (∃ (n : ℕ) (H : n ∈ B), d_i' ∣ n),
  left, exact hd_i'div, right,
  intros n hn k hk1 hk2 hk3,
  have hn2 : n ∈ A_i, { exact hB hn, },
  cases hstock.2.2.2.2.2.2.2 with hnew1 hnew2,
  exfalso, apply hdiv2 hnew1,
  have hk2' : k ≤ d_i', { rw le_min_iff, split,
   exact hk2, exact hk3, },
  have hk2'' : k < d_i', {
   rw ← ne.le_iff_lt, exact hk2', intro hkaux4,
   apply hd_i'div, use n, split, exact hn,
   rw ← hkaux4, exact hk1, },
  have hk2''' : k ≤ ⌈y⌉₊ + i_n, { rw lt_min_iff at hk2'',
    apply nat.le_of_lt_succ hk2''.1, },
  have hk2'''' : k ≤ ⌊w⌋₊, {
    rw lt_min_iff at hk2'', apply le_of_lt hk2''.2,},
  exact hnew2 n hn2 k hk1 hk2''' hk2'''',
end

lemma main_tech_lemma :
  ∀ᶠ (N : ℕ) in at_top, ∀ M ε y w : ℝ, ∀ A ⊆ finset.range(N+1),
  (0 < M) → (M < N) → (0 < ε) → (2*M > w) → (1/M < ε*log(log N)) →
  (1 ≤ y) → (2 ≤ w) → (⌈y⌉₊ ≤ ⌊w⌋₊) →
  (3*ε*log(log N) ≤ 2/(w^2)) → (∀ n ∈ A, M ≤ (n: ℝ)) →
  (2/y + 2*ε*log(log N) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε*M) →
  (∀ n ∈ A, ∃ d : ℕ, (y ≤ d) ∧ ((d:ℝ) ≤ w) ∧ d ∣ n) →
  (∃ A' ⊆ A, ∃ d : ℕ, A' ≠ ∅ ∧ (y ≤ d) ∧ ((d:ℝ) ≤ w) ∧ rec_sum A' < 2/d ∧
  (2:ℝ)/d-1/M ≤ rec_sum A' ∧ (∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q)
  ∧ (∃ n ∈ A', d ∣ n) ∧ (∀ n ∈ A', ∀ k : ℕ, k ∣ n → k < d → (k:ℝ) < y))
  :=
begin
  have : tendsto (λ N : ℕ, log (log N)) at_top at_top :=
    tendsto_log_at_top.comp (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top),
 filter_upwards [main_tech_lemma_ind, this (eventually_gt_at_top 0)],
 intros N hN h_largeN M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw hNw hAM hrec hsmooth hdiv,
 have hy01 : 0 < y, {
   apply @lt_of_lt_of_le _ _ 0 1 y zero_lt_one hy, },
 have hy12 : 2 ≤ y + 1, {refine add_le_add_right hy 1, },
 have hwzero : 0 < w := by apply lt_of_lt_of_le  zero_lt_two h2w,
 let i := ⌊w⌋₊ - ⌈y⌉₊,
 specialize hN M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw hNw hAM hrec hsmooth hdiv i,
 rcases hN with ⟨A', hA', d, hN⟩,
 use A', split, exact hA', use d,
 have hdw : (d:ℝ) ≤ w, {
   have hauxw : (⌊w⌋₊:ℝ) ≤ w, { apply nat.floor_le (le_of_lt hwzero), },
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
 { refine div_le_div_of_le_left zero_le_two hwzero _, refine le_self_pow _ one_le_two,
   apply le_trans one_le_two h2w, },
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
     exact hyw, },
   rw hobvious, exact htempw,
  },
 specialize hv2 x hx m hdiv.2.2 htemp htempw, linarith,
 exact hN.2.2.2.2.2.2.1,
end

-- Proposition 6.3
theorem force_good_properties :
  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  ((N:ℝ) ≤ M^(2:ℝ)) → arith_regular N A →
  ( (log N)^(-(1/101 : ℝ)) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A,
    ((log N)^(-(1/100 : ℝ)) ≤ rec_sum_local A q )) → (
  (∃ B ⊆ A, ((rec_sum A) ≤ 3*rec_sum B) ∧
  ((ppower_rec_sum B : ℝ) ≤ (2/3)* log(log N)))
  ∨ good_condition A (M*(N:ℝ)^(-(2:ℝ)/log(log N))) ((M:ℝ)/log N)
  (M / (2*(log N)^(1/100 : ℝ))) ) :=
sorry

-- Proposition 6.4
theorem force_good_properties2 :
  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  ((N:ℝ) ≤ M^(2:ℝ)) → arith_regular N A →
  (∀ q ∈ ppowers_in_set A,
    ((log N)^(-(1/100 : ℝ)) ≤ rec_sum_local A q )) →
  ((ppower_rec_sum A : ℝ) ≤ (2/3)* log(log N)) →
  good_condition A (M*(N:ℝ)^(-(2:ℝ)/log(log N))) ((M:ℝ)/log N)
  (M / (2*(log N)^(1/100 : ℝ)))
 :=
sorry


lemma one_lt_four : (1:ℝ) < 4 :=
begin
  norm_num,
end

lemma large_enough_N  :  ∀ᶠ (N : ℕ) in at_top,
 (N:ℝ)^(1-(6:ℝ)/(log(log N))) = (N:ℝ)^(-(5:ℝ)/(log(log N)))*((N:ℝ)^(1-(1:ℝ)/(log(log N)))) ∧
 1/((N:ℝ)^(1-(1:ℝ)/(log(log N)))) < (N:ℝ)^(-(5:ℝ)/(log(log N)))*log(log N) ∧
 0 < (N:ℝ)^(-(5:ℝ)/(log(log N))) ∧
 (N:ℝ) ≤ ((N:ℝ)^(1-(1:ℝ)/(log(log N))))^(2:ℝ) ∧
 ((N:ℝ)^(1-(1:ℝ)/(log(log N)))) < N ∧
 0 < ((N:ℝ)^(1-(1:ℝ)/(log(log N)))) ∧ (0:ℝ) < log N ∧
 8 ≤ (N:ℝ)^(1-(3:ℝ)/(log(log N))) ∧
 (N:ℝ)^(1-(3:ℝ)/(log(log N))) < ((N:ℝ)^(1-(1:ℝ)/(log(log N)))) ∧
 (log N)^((1/500 : ℝ)) < 2*(N:ℝ)^(1-(1:ℝ)/(log(log N))) ∧
  2*(N:ℝ)^(-(5:ℝ)/(log(log N)))*log(log N) ≤ (log N)^(-(1/200 : ℝ)) ∧
  3*(N:ℝ)^(-(5:ℝ)/(log(log N)))*log(log N) ≤ 2 / ((log N)^((1/500 : ℝ)))^2 :=
 sorry

-- Proposition 6.6
theorem technical_prop :
  ∀ᶠ (N : ℕ) in at_top, ∀ (A ⊆ finset.range (N+1)) (y z : ℝ),
  (1 ≤ y) → (4*y + 4 ≤ z) → (z ≤ (log N)^((1/500 : ℝ)))
  → (∀ n ∈ A, ( (N:ℝ)^(1-(1:ℝ)/(log(log N))) ≤ n ))
  → 2 / y + (log N)^(-(1/200 : ℝ)) ≤ rec_sum A
  → (∀ n ∈ A, ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧ (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z) )
  → (∀ n ∈ A, is_smooth ((N:ℝ)^(1-(6:ℝ)/(log(log N)))) n)
  → arith_regular N A
  → ∃ S ⊆ A, ∃ d : ℕ, (y ≤ d) ∧ ((d:ℝ) ≤ z) ∧
    rec_sum S = 1/d
  :=
  sorry

lemma prop_one_specialise :
  ∀ᶠ N : ℕ in at_top, ∀ A ⊆ finset.range (N + 1),
    (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n)
  → log N ^ (1 / 500 : ℝ) ≤ (rec_sum A : ℝ)
  → (∀ n ∈ A, ∃ d₂ : ℕ, d₂ ∣ n ∧ 4 ≤ d₂ ∧ (d₂ : ℝ) ≤ log N ^ (1 / 500 : ℝ))
  → (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (6 : ℝ) / log (log N))) n)
  → arith_regular N A
  → ∃ S ⊆ A, ∃ d : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ log N ^ (1 / 500 : ℝ) ∧ rec_sum S = 1 / d :=
begin
  have hf : tendsto (λ (x : ℕ), log x ^ (1 / 500 : ℝ)) at_top at_top :=
    tendsto_coe_log_pow_at_top _ (by norm_num1),
  have hf' : tendsto (λ (x : ℕ), log x ^ (1 / 200 : ℝ)) at_top at_top :=
    tendsto_coe_log_pow_at_top _ (by norm_num1),
  filter_upwards [technical_prop, hf (eventually_ge_at_top 8), hf' (eventually_ge_at_top 1),
    (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top) (eventually_ge_at_top 0)],
  intros N hN hN' hN'' hN''' A A_upper_bound A_lower_bound hA₁ hA₂ hA₃ hA₄,
  simp only [set.mem_set_of_eq, set.preimage_set_of_eq] at hN' hN'' hN''',
  exact_mod_cast hN A A_upper_bound 1 _ le_rfl _ le_rfl A_lower_bound _ _ hA₃ hA₄,
  { exact le_trans (by norm_num1) hN' },
  { apply (le_trans _ hN').trans hA₁,
    rw [←le_sub_iff_add_le', rpow_neg],
    { norm_num1, apply @le_trans _ _ _ (1:ℝ) 6,
      exact inv_le_one hN'', norm_num, },
    { exact hN''' } },
  intros n hn,
  obtain ⟨d₂, hd₂, hd₂', hd₂''⟩ := hA₂ n hn,
  exact ⟨1, d₂, one_dvd _, hd₂, by simp, by simpa, hd₂''⟩,
end

-- Corollary 1
theorem corollary_one :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range (N + 1),
  (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n)
  → 2 * log N ^ (1 / 500 : ℝ) ≤ rec_sum A
  → (∀ n ∈ A, ∃ p : ℕ, p ∣ n ∧ 4 ≤ p ∧ (p : ℝ) ≤ log N ^ (1/500 : ℝ))
  → (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (6 : ℝ) / log (log N))) n)
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
