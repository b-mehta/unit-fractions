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

/-- The following is Lemma 4.22, copied directly from fourier.lean - copied here with
 sorry as a temporary measure. I've changed the name to avoid conflicts when building,
 but this needs tidying up at some point. -/
theorem circle_method_prop2 :
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ (N : ℕ) in filter.at_top,
    ∀ {K L M T : ℝ} {k : ℕ} {A : finset ℕ},
    0 < T → 0 < L → 8 ≤ K → K < M → M ≤ N → k ≠ 0 → (k : ℝ) ≤ M / 128 → (∀ n ∈ A, M ≤ ↑n) →
    (∀ n ∈ A, n ≤ N) →
    rec_sum A < 2 / k → (2 : ℝ) / k - 1 / M ≤ rec_sum A →
    k ∣ (A.lcm id : ℕ) →
    (∀ q ∈ ppowers_in_set A, ↑q ≤ min (L * K^2 / (16 * N^2 * (log N)^2)) (min (c * M / k) (T * K^2 / (N^2 * log N)))) →
    good_condition A K T L →
    ∃ S ⊆ A, rec_sum S = 1 / k :=
sorry

lemma useful_rec_bound : ∃ C : ℝ, ∀ y N k: ℝ, ∀ D : finset ℕ, (C > 0) ∧
  (0 < y) → (y < N) → (1 ≤ k) → (∀ q : ℕ, q ∈ ppowers_in_set D → (y < q) ∧ ((q : ℝ) ≤ N) ) →
  ∑ d in D, k^(ω d) / d ≤ (C*(log N)/log y)^k :=
  sorry

-- Lemma 5.1
lemma rec_pp_sum_close :
  ∀ᶠ (N : ℕ) in at_top, ∀ x y : ℤ, (x ≠ y) → (|(x : ℝ)-y| ≤ N) →
  ∑ q in (finset.range(N+1)).filter(λ n, is_prime_pow n ∧ (n:ℤ) ∣ x ∧ (n:ℤ) ∣ y), (1 : ℝ)/q <
  ((1 : ℝ)/100)*log(log N) :=
  sorry


-- Lemma 5.4
lemma find_good_d : ∃ c C : ℝ, (0 < c) ∧ (0 < C) ∧ ∀ᶠ (N : ℕ) in at_top, ∀ M k : ℝ,
  ∀ A ⊆ finset.range(N+1), (0 ≤ M) →
  (M ≤ N) → ((N : ℝ) ≤ M^(2 : ℝ)) → ((1 : ℝ) ≤ k) → (k ≤ c* log(log N))
  → (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n) : ℝ) ≤ (log N)^(1/k)) →
    (∀ q ∈ ppowers_in_set A,
    (1/(log N) ≤ rec_sum_local A q) →
    (∃ d : ℕ,
    ( M*real.exp(-(log N)^(1 - 1/k)) < q*d ) ∧
    ( (ω d : ℝ) ≤ (5/log k) * log(log N) ) ∧
    ( C*(rec_sum_local A q) / (log N)^(2/k) ≤
      ∑ n in (local_part A q).filter(λ n, (q*d ∣ n) ∧
        (coprime (q*d) (n/q*d))), (q*d/n : ℝ)  ) ) )
  :=
begin
  sorry, /-
  -- Fix up these choices later
  let c := (1 : ℝ),
  let C := (2 : ℝ),
  have hC : 0 < C, { sorry, },
  use c, use C,
  -- Work out the right filter later
  filter_upwards [eventually_ge_at_top 0],
  intros N hN M k A hAN hzM hMN hNM h1k hkN hAreg q hq hsumq,

  have hlarge1 : 0 < log N, { sorry, },
  let y := real.exp(-(log N)^(1 - 2/k)),
  let u := real.exp(-(log N)^(1 - 1/k)),
  let D := (finset.range(N)).filter( λ d, (∀ r : ℕ, is_prime_pow r → r ∣ d → coprime r (d/r) →
     y < r ∧ r ≤ N) ∧ M*u < q*d ∧ q*d ≤ N),
  have hlocal : ∀ n ∈ local_part A q, ∃ d ∈ D, (q*d ∣ n) ∧ coprime (q*d) (n/q*d),
  { sorry, },
  let new_local := (λ d : ℕ, (local_part A q).filter(λ n, (q*d)∣n
     ∧ coprime (q*d) (n/q*d) )),
  have hlocal2 : local_part A q ⊆ D.bUnion (λ d, new_local d),
  { intros n hn, rw finset.mem_bUnion, specialize hlocal n hn,
    rcases hlocal with ⟨d,hd,hlocal⟩, refine ⟨d,hd,_⟩, rw finset.mem_filter,
    refine ⟨hn,hlocal⟩, },
  have hrecbound : rec_sum_local A q ≤ ∑ d in D, ∑ n in new_local d, (q:ℚ)/n,
  { sorry, },
  -- For the below, could use the aysmptotic for the sum, but that's overkill, is just
  -- the integral test upper bound in mathlib?
  have hharmonic : ∑ n in finset.range(N+1), (1 : ℝ)/n ≤ 2*log N,
  { sorry, },
  have hDnotzero : ∀ d ∈ D, d ≠ 0, {
   intros i hi hzi, rw finset.mem_filter at hi,
   obtain hi' := hi.2.2.1,rw hzi at hi', push_cast at hi', rw mul_zero at hi',
   apply (lt_iff_not_ge (M*u) 0).mp hi', apply mul_nonneg, exact hzM, apply le_of_lt,
   apply real.exp_pos,
  },
  have hrectrivial : ∀ d ∈ D, ((∑ n in new_local d, (q:ℚ)/n) : ℝ) ≤ 2*(log N)/d,
  { intros d hd,
    have hrectrivial' : ((∑ n in new_local d, (q:ℚ)/n) : ℝ) ≤
    ∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), (q/n), { sorry, },
    apply le_trans hrectrivial',
    have hrectrivial'' : ∑ n in (finset.range(N+1)).filter(λ x, (q*d)∣ x), ((q : ℝ)/n)
      = (1/d)*∑ m in (finset.range(N+1)).filter(λ x, q*d*x ≤ N), (1/m), {
        sorry,
       },
    rw hrectrivial'', rw le_div_iff, rw mul_comm, rw ← mul_assoc, rw mul_one_div_cancel,
    rw one_mul,
    have hrectrivial''' : ∑ m in (finset.range(N+1)).filter(λ x, q*d*x ≤ N), ((1 : ℝ)/m)
      ≤  ∑ n in finset.range(N+1), (1 : ℝ)/n, { sorry, },
    apply le_trans hrectrivial''' hharmonic, norm_cast, refine hDnotzero d hd, norm_cast,
    rw pos_iff_ne_zero, refine hDnotzero d hd,
      },
  let ω0 := (5/log k) * log(log N),
  let D1 := D.filter(λ d, ω0 < (ω d : ℝ)),
  have hbound1 : ∑ d in D1, ∑ n in new_local d, (q : ℝ)/n ≤ (rec_sum_local A q)/2, { sorry, },
  let D2 := D.filter(λ d, (ω d : ℝ) ≤ ω0),
  have hbound2 : (rec_sum_local A q)/2 ≤ ∑ d in D2, ∑ n in new_local d, q/n, { sorry, },
  have hbound3 : (rec_sum_local A q)/2 ≤ ∑ d in D2, (1/d)*(∑ n in new_local d, (q*d)/n),
  { sorry, },
  have hfound : ∃ d ∈ D2, ((rec_sum_local A q) : ℝ)/(2*∑ d in D2, (1/d)) ≤
     ∑ n in new_local d, (q*d)/n,
     { sorry, },
  have hbound4 : ∑ d in D2, ((1 : ℝ)/d) ≤ (log N)^(2/k) / (C*2), { sorry, },
  rcases hfound with ⟨d,hd,hfound⟩,
  use d, rw finset.mem_filter at hd, rw finset.mem_filter at hd,
  refine ⟨hd.1.2.2.1,hd.2,_⟩, apply le_trans _ hfound, rw div_le_div_iff,
  rw mul_comm C, rw mul_assoc, rw mul_le_mul_left, rw ← mul_assoc, rw mul_comm,
  rw ← le_div_iff, exact hbound4, apply mul_pos hC zero_lt_two,
  apply lt_of_lt_of_le _ hsumq, apply div_pos, exact zero_lt_one, exact hlarge1,
  apply rpow_pos_of_pos hlarge1, refine mul_pos zero_lt_two _,
  apply sum_pos, intros i hi, apply div_pos, exact zero_lt_one, norm_cast,
  rw pos_iff_ne_zero, apply hDnotzero,
  have : D2 ⊆ D, { refine finset.filter_subset _ _, },
  exact this hi,  rw finset.nonempty_iff_ne_empty, intro hempty,
 have hempty2 : ∑ d in D2, ((1:ℚ)/d)*(∑ n in new_local d, (q*d)/n) = 0, {
   rw hempty, apply finset.sum_empty,  },
 rw hempty2 at hbound3, apply (lt_iff_not_ge 0 ((rec_sum_local A q)/2)).mp,
 apply div_pos,
 have : (0 : ℝ) < rec_sum_local A q, {
   refine lt_of_lt_of_le _ hsumq, apply div_pos, exact zero_lt_one, exact hlarge1,
 }, exact_mod_cast this, exact zero_lt_two, exact hbound3,
 -/
end

-- Lemma 6.1
lemma find_good_x :  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  (0 ≤ M) → (M ≤ N) → ((N : ℝ) ≤ M^(2 : ℝ)) →
  (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
  (∀ (t : ℝ) (I : finset ℤ) (q ∈ ppowers_in_set A),
  I = finset.Icc ⌈t - (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) / 2⌉ ⌊t + (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) / 2⌋ →
  (((1 : ℝ)/(2*(log N)^((1 : ℝ)/100))) < rec_sum_local (A.filter (λ n, ∀ x ∈ I, ¬ (n:ℤ) ∣ x)) q)
  → (∃ xq ∈ I, ((q:ℤ) ∣ xq) ∧ (((35 : ℝ)/100)*log(log N)) ≤
     ∑ r in (ppowers_in_set A).filter(λ n, (n:ℤ) ∣ xq), 1/r ))
  --(∃ xq ∈ I, q ∣ xq ∧ (((35 : ℝ)/100)*log(log N)) ≤ 1))
  :=
begin
  obtain hgoodd := find_good_d,
  rcases hgoodd with ⟨c,C,hc,hC,hgoodd⟩,
  -- Work out the right filter later
  filter_upwards [hgoodd],
  clear hgoodd,
  intros N hgooddN M A hA h0M hMN hNM hMA hreg t I q hq hI hqlocal,
  let A_I := A.filter (λ n : ℕ, ∀ x ∈ I, ¬ (n:ℤ) ∣ x),
  let k := (log (log N))/((log 2) + log(log(log N))),
  have h1k : 1 ≤ k, { sorry, },
  have hkc : k ≤ c* log(log N), { sorry, },
  have hA_I : A_I ⊆ finset.range(N+1), { apply subset_trans _ hA, apply finset.filter_subset,},
  have hA_I' : (∀ n ∈ A_I, M ≤ (n : ℝ) ∧ ((ω n) : ℝ) ≤ (log N)^(1/k)), { sorry, },
  have hqA_I : q ∈ ppowers_in_set A_I, { sorry, },
  have hqlocal2 :  (1/(log N) ≤ rec_sum_local A_I q), { sorry, },
  specialize hgooddN M k A_I hA_I h0M hMN hNM h1k hkc hA_I' q hqA_I hqlocal2,
  rcases hgooddN with ⟨d,hgood1,hgood2,hgood3⟩,
sorry,
end


lemma two_in_Icc (a b x y: ℤ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : |(x : ℝ)-y| ≤ b-a :=
sorry

-- Proposition 6.3
theorem force_good_properties :
  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  ((N : ℝ) ≤ M^(2 : ℝ)) → arith_regular N A →
  ( (log N)^(-(1/101 : ℝ)) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A,
    ((log N)^(-(1/100 : ℝ)) ≤ rec_sum_local A q )) → (
  (∃ B ⊆ A, ((rec_sum A) ≤ 3*rec_sum B) ∧
  ((ppower_rec_sum B : ℝ) ≤ (2/3)* log(log N)))
  ∨ good_condition A (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) ((M : ℝ)/log N)
  (M / (2*(log N)^(1/100 : ℝ))) ) :=
sorry

-- Proposition 6.4
theorem force_good_properties2 :
  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  ((N : ℝ) ≤ M^(2 : ℝ)) → arith_regular N A →
  (∀ q ∈ ppowers_in_set A,
    ((log N)^(-(1/100 : ℝ)) ≤ rec_sum_local A q )) →
  ((ppower_rec_sum A : ℝ) ≤ (2/3)* log(log N)) →
  good_condition A (M*(N : ℝ)^(-(2 : ℝ)/log(log N))) ((M : ℝ)/log N)
  (M / (2*(log N)^(1/100 : ℝ)))
 :=
begin
  let c := (35 : ℝ)/100,
  -- Work out the right filter later
  filter_upwards [rec_pp_sum_close],
  intros N hrecN M A hA hNM hreg hreclocal hpprecA,
  -- Some routine N bounds
  have hlarge1 : 1 ≤ M*(N)^(-(2 : ℝ)/log(log N)), { sorry, },
  have hlarge2 : M * N ^ ((-2) / log (log N)) ≤ N, { sorry, },
  rw good_condition,
  intros t I hI,
  refine or_iff_not_imp_left.2 (λ hP, _),
  let A_I := A.filter((λ (n : ℕ), ∀ (x : ℤ), x ∈ I → ¬(n:ℤ) ∣ x)),
  let D := interval_rare_ppowers I A (M / (2 * log N ^ ((1 : ℝ) / 100))),
  by_cases hDne : D.nonempty,
  rcases hDne with ⟨x1,hx1⟩,
  -- The following is involved, uses a couple of other lemmas
  have hlocal : ∀ q ∈ D, ∃ x ∈ I, ((q:ℤ) ∣x) ∧
   c*log(log N) ≤ ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣x)), 1/r, {
     intros q hq, sorry,
    },
  choose! f hf using hlocal,
  use f x1,
  have hfcopy := hf,
  specialize hf x1 hx1, refine ⟨hf.1,_⟩, intros q hq,
  specialize hfcopy q hq,
  by_cases htwoxs : f q = f x1,
  obtain hf' := hfcopy.2.1, rw htwoxs at hf', exact hf',
  exfalso,
  have hsum1 :  2*c*log(log N) ≤ ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f x1)), 1/r
    +  ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f q)), 1/r, {
      rw [two_mul, add_mul], apply add_le_add hf.2.2 hfcopy.2.2,
     },
  -- The following uses an inclusion/exclusion principle
  have hsum2 :
       ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f x1)), (1 : ℝ)/r
    +  ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f q)), (1 : ℝ)/r
    -  ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f q ∧ (n:ℤ)∣f x1)), (1 : ℝ)/r
    ≤ ppower_rec_sum A, { sorry },
  have hsum3 :
    ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f x1)), (1 : ℝ)/r
    + ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f q)), (1 : ℝ)/r  - ppower_rec_sum A ≤
    ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f q ∧ (n:ℤ)∣f x1)), (1 : ℝ)/r,
    { apply  sub_left_le_of_le_add, nth_rewrite 1 add_comm,
      apply le_add_of_sub_left_le hsum2, },
  -- The following is a trivial rearranging of inequalities we already have
  have hsum4 :
    ((1 : ℝ)/100)*log(log N) ≤
      ∑ r in ((ppowers_in_set A).filter(λ n, (n:ℤ)∣f q ∧ (n:ℤ)∣f x1)), (1 : ℝ)/r,
    { sorry, },
  have hqx1close : |(f q : ℝ)-(f x1)| ≤ N, {
    apply @le_trans _ _ _ ((⌊t + M * N ^ ((-2) / log (log N)) / 2⌋ : ℝ)-⌈t - M * N ^ ((-2) / log (log N)) / 2⌉) N,
    apply two_in_Icc, rw ← hI, exact hfcopy.1, rw ← hI, exact hf.1,
    rw sub_le,
    apply @le_trans _ _ _ (t - M * N ^ ((-2) / log (log N)) / 2) _,
    apply sub_left_le_of_le_add, apply @le_trans _ _ _ (t + M * N ^ ((-2) / log (log N)) / 2) _,
    apply int.floor_le, rw add_sub, rw add_comm (N : ℝ) t, rw ← add_sub, apply add_le_add_left,
    apply le_sub_left_of_add_le, rw add_halves', exact hlarge2, apply int.le_ceil,
   },
  specialize hrecN (f q) (f x1) htwoxs hqx1close, rw lt_iff_not_ge at hrecN,
  apply hrecN, apply le_trans hsum4, apply finset.sum_le_sum_of_subset_of_nonneg,
  intros r hr, rw finset.mem_filter, rw finset.mem_filter at hr,
  rw [ppowers_in_set,finset.mem_bUnion] at hr, rcases hr.1 with ⟨m,hm1,hm2⟩,
  rw finset.mem_filter at hm2,  refine ⟨_,hm2.2.1,hr.2⟩, rw finset.mem_range,
  apply @lt_of_le_of_lt _ _ r m _, apply nat.divisor_le hm2.1, rw ← finset.mem_range,
  exact hA hm1, intros i hi1 hi2, apply div_nonneg, exact zero_le_one, apply nat.cast_nonneg,
  clear hrecN,
  have hIne : I.nonempty, {
    rw [hI, finset.nonempty_Icc], rw int.ceil_le,
    apply @le_trans _ _ _ (t + M * N ^ ((-2) / log (log N)) / 2 - 1) _,
    rw [le_sub,← sub_add, ← sub_add_eq_add_sub], simp only [zero_add, add_halves', sub_self],
    exact hlarge1, apply le_of_lt, apply int.sub_one_lt_floor,
   },
  rcases hIne with ⟨x,hx⟩, refine ⟨x,hx,_⟩,
  intros q hq, exfalso, apply hDne, use q, exact hq,
end


lemma one_lt_four : (1 : ℝ) < 4 :=
begin
  norm_num,
end



theorem unit_fractions_upper_density (A : set ℕ) (hA : upper_density A > 0):
   ∃ (S : finset ℕ), (S : set ℕ) ⊆ A ∧ ∑ n in S, (1 / n : ℝ) = 1 :=
sorry

theorem unit_fractions_upper_log_density :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range (N+1),
    25 * log (log (log N)) * log N / log (log N) ≤ ∑ n in A, (1 / n : ℝ) →
      ∃ S ⊆ A, ∑ n in S, (1 / n : ℝ) = 1 :=
sorry


-- This shows up often enough here that it's worth having separately
lemma tendsto_coe_log_pow_at_top (c : ℝ) (hc : 0 < c) :
  tendsto (λ (x : ℕ), (log x)^c) at_top at_top :=
(tendsto_rpow_at_top hc).comp (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top)



-- define the X in Lemma 1 as a separate definition?
def X (y z : ℝ) : set ℕ := sorry

-- Sieve of Eratosthenes-Legendre, again belongs in basic_estimates
-- Bhavik, this is clumsily expressed, condensed form?
lemma sieve_eratosthenes (x y u v : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 1 ≤ u) (huv : u ≤ v) :
  |((((Ioc ⌊x⌋₊ ⌊x+y⌋₊).filter (λ n : ℕ, ∀ p : ℕ, p.prime → p ∣ n → p ∉ Icc ⌈u⌉₊ ⌊v⌋₊))).card : ℝ) -
   y * ∏ p in (finset.Icc ⌈u⌉₊ ⌊v⌋₊).filter prime, (1 - p⁻¹)| ≤ 2 ^ (v + 1) :=
sorry

-- (Proof: write the filtered cardinality as a sum, using the Mobius function
-- to detect the divisibility constraint, then rearrange. Uses the trivial bound
-- of v for number of primes in [u,v])

-- Lemma 1
lemma sieve_lemma_one  : ∃ C : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ y z : ℝ, (3 ≤ y) → (y < z) → (z ≤ log N) →
   let X : set ℕ := { n : ℕ | ∀ p:ℕ, (prime p) → (p ∣ n) →
   ( ((p : ℝ) < y) ∨ (z < p)) } in
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
   ∧ ((p₂ : ℝ) ≤ z) } in
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
  → (∀ n ∈ A, ((1 - ε)*log(log N) ≤ ω n ) ∧ ( (ω n : ℝ) ≤ 2*(log (log N))))
  → (1 - 2*ε)*log(log N) *real.exp(-1) ≤ ∑ q in ppowers_in_set A, (1/q : ℝ)
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
    rw [mul_comm M, mul_div_assoc, mul_assoc, div_mul_div_comm, mul_comm M, div_self, mul_one],
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
  ∀ᶠ N : ℕ in at_top,
    ((∑ q in (finset.range (N + 1)).filter is_prime_pow, 1 / q) : ℝ) ≤ 2 * log (log N) :=
begin
  obtain ⟨b, hb⟩ := prime_power_reciprocal,
  obtain ⟨c, hc₀, hc⟩ := hb.exists_pos,
  filter_upwards [(tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
    (eventually_ge_at_top (c : ℝ)), (tendsto_log_at_top.comp (tendsto_log_at_top.comp
    tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top (b + 1)),
    tendsto_coe_nat_at_top_at_top.eventually hc.bound]
    with N hN₁ hN₂ hN₃,
  dsimp at hN₁ hN₂,
  have hN₄ : 0 < log N := hc₀.trans_le hN₁,
  simp_rw [norm_inv, ←div_eq_mul_inv, ←one_div, norm_eq_abs, abs_of_nonneg hN₄.le,
    nat.floor_coe] at hN₃,
  have : c / log N ≤ 1 := div_le_one_of_le hN₁ hN₄.le,
  have := sub_le_iff_le_add.1 (sub_le_of_abs_sub_le_right (hN₃.trans this)),
  convert this.trans (show log (log N) + b + 1 ≤ 2 * log (log N), by linarith) using 2,
  rw [range_eq_Ico, nat.Ico_succ_right],
  ext n,
  simpa only [mem_filter, and.congr_left_iff, mem_Icc, zero_le', iff_and_self, true_and] using
    λ h _, (is_prime_pow.one_lt h).le,
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
  have hxA1 : x ∈ A_i := hB hx,
  have hxA2 : x ∈ A := hA_i hxA1,
  let A_i' := A_i.erase x,
  have h3 : A_i' ⊆ A_i := erase_subset _ _,
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
      { rw [ppowers_in_set, finset.mem_bUnion],
        refine ⟨x, hx, mem_filter.2 ⟨nat.mem_divisors.2 ⟨hxq.1, _⟩, (mem_ppowers_in_set.1 hq).1,
          hxq.2⟩⟩,
        rintro rfl,
        exact hM.not_le (by simpa only [nat.cast_zero] using hMA _ hxA2) },
      have hlocal3 : (rec_sum_local B q : ℝ) ≤ rec_sum_local A_i q :=
        rat.cast_le.2 (rec_sum_local_mono hB),
      have hll : ε + ε < rec_sum_local A_i q,
      { rw ←two_mul ε,
        exact (hN2 q hppB).trans_le hlocal3 },
      have hll2 : (q : ℝ) / x ≤ ε,
      { rw (div_le_iff (hM.trans_le (hMA x hxA2))),
        have hppA : ppowers_in_set A_i' ⊆ ppowers_in_set A := ppowers_in_set_subset (h3.trans hA_i),
        exact (hsmooth q (hppA hq)).1.trans (mul_le_mul_of_nonneg_left (hMA x hxA2) hε.le) },
      rw lt_sub,
      apply hll2.trans_lt,
      rwa lt_sub_iff_add_lt },
    have hrecl : rec_sum_local A_i q = rec_sum_local A_i' q,
    { have hlocalaux : local_part A_i q = local_part A_i' q,
      { rw [local_part, local_part, filter_erase, erase_eq_of_not_mem],
        rw [mem_filter, not_and_distrib],
        exact or.inr hxq },
    rw [rec_sum_local, rec_sum_local, hlocalaux] },
    rw ←hrecl,
    exact ih2 q (ppowers_in_set_subset h3 hq) },
  left,
  have hcard : (A \ A_i).card < (A \ A_i').card,
  { rw [card_sdiff hA_i, card_sdiff (h3.trans hA_i),
      tsub_lt_tsub_iff_left_of_le (card_le_of_subset hA_i)],
    exact card_erase_lt_of_mem hxA1 },
  have hcard' : (A \ A_i).card + 1 ≤ (A \ A_i').card := nat.succ_le_iff.2 hcard,
  rw nat.succ_eq_add_one,
  cases ih3 with hf1 hf2,
  { linarith },
  { exfalso, linarith },
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
  rcases h A hA ε hε with ⟨A', hA', hA'1, hA'3⟩,
  have hA'2 : A' ⊆ finset.range (N + 1) := hA'.trans hA,
  have hMA' : ∀ n ∈ A', M ≤ (n : ℝ) := λ n hn, hMA n (hA' hn),
  have hrecA' : α ≤ rec_sum A',
  { refine (le_sub_right_of_add_le _).trans hA'1, rwa mul_comm ε 2, },
  have hsmooth2 : ∀ q ∈ ppowers_in_set A', ↑q ≤ ε * M ∧ ε < rec_sum_local A' q :=
    λ q hq, ⟨hsmooth q ((ppowers_in_set_subset hA') hq), hA'3 q hq⟩,
  let i := A'.card + 1,
  rcases h2 M α ε A' hA'2 hMz hMN hε hεα hMA' hrecA' hsmooth2 i with ⟨B, hB, h2, h3, ha⟩,
  refine ⟨B, hB.trans hA', ha.resolve_left (λ ha1, _), h2, h3⟩,
  exact not_le.2 (nat.lt_succ_self A'.card) (ha1.trans (card_le_of_subset (sdiff_subset _ _))),
end

lemma main_tech_lemma_ind :
  ∀ᶠ (N : ℕ) in at_top, ∀ M ε y w : ℝ, ∀ A ⊆ finset.range (N + 1),
    0 < M → M < N → 0 < ε → w < 2 * M → 1 / M < ε * log (log N) →
    1 ≤ y → 2 ≤ w → ⌈y⌉₊ ≤ ⌊w⌋₊ →
    (3 * ε * log (log N) ≤ 2 / w ^ 2) → (∀ n ∈ A, M ≤ (n : ℝ)) →
    (2 / y + 2 * ε * log (log N) ≤ rec_sum A) →
    (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
    (∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ (d : ℝ) ≤ w ∧ d ∣ n) →
    (∀ i : ℕ, ∃ A_i ⊆ A, ∃ d_i : ℕ,
      y ≤ d_i ∧ d_i ≤ ⌈y⌉₊ + i ∧ d_i ≤ ⌊w⌋₊ ∧
      rec_sum A_i < 2 / d_i ∧ (2 : ℝ) / d_i - 1 / M ≤ rec_sum A_i ∧
      (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
      (∀ n ∈ A_i, ∀ k, k ∣ n → k < d_i → (k : ℝ) < y) ∧
      ((∃ n ∈ A_i, d_i ∣ n) ∨ (∀ n ∈ A_i, ∀ k, k ∣ n → k ≤ ⌈y⌉₊ + i → k ≤ ⌊w⌋₊ → (k : ℝ) < y))) :=
begin
  have : tendsto (λ N : ℕ, log (log N)) at_top at_top :=
    tendsto_log_at_top.comp (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top),
  filter_upwards [pruning_lemma_two, this.eventually (eventually_gt_at_top 0)],
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
      { rw [←mul_div_assoc, div_le_div_iff (pow_pos hwzero _), mul_assoc, mul_le_mul_left],
        { refine le_trans (mul_le_mul_of_nonneg_left (le_trans _ hqaux) zero_le_two) hwaux,
          rwa nat.cast_le },
        { exact zero_lt_two },
        { rwa [nat.cast_pos, nat.lt_ceil, nat.cast_zero] } },
      rw [rat.cast_div, rat.cast_bit0, rat.cast_one, rat.cast_coe_nat],
      exact hεNaux.trans_le (hεNaux2.trans hα1) },
    have hrec2 : (α : ℝ) + 2 * ε * log (log N) ≤ rec_sum A,
    { rw hαaux,
      exact add_le_of_add_le_right hrec (div_le_div_of_le_left zero_le_two hy01 (nat.le_ceil _)) },
    rcases hN M α ε A hA hM hMN hε hα hMA hrec2 hsmooth with ⟨B, hB, hB', hB'', hN⟩,
    refine ⟨B, hB, _, nat.le_ceil y, le_rfl, hyw2, rat.cast_lt.1 hB', by rwa ←hαaux, hN,
      λ n hn k hk1 hk2, by rwa ←nat.lt_ceil, _⟩,
    rw or_iff_not_imp_left,
    intros hp n hn k hk1 hk2 hk3,
    rw ← nat.lt_ceil,
    refine lt_of_le_of_ne hk2 _,
    rintro rfl,
    exact hp ⟨n, hn, hk1⟩ },
  -- The inductive case
  rcases i_ih with ⟨A_i, hA_i, d_i, hstock⟩,
  obtain hstock1 := hstock.2.2.2.2.2.2.1,
  by_cases hdiv2 : ∃ n ∈ A_i, d_i ∣ n,
  { exact ⟨A_i, hA_i, d_i, hstock.1, hstock.2.1.trans (add_le_add_left i_n.le_succ _),
      hstock.2.2.1, hstock.2.2.2.1, hstock.2.2.2.2.1, hstock.2.2.2.2.2.1, hstock.2.2.2.2.2.2.1,
      or.inl hdiv2⟩ },
  let d_i' := min (⌈y⌉₊ + i_n + 1) ⌊w⌋₊,
  have hd_i' : d_i + 1 ≤ d_i',
  { rw le_min_iff,
    refine ⟨add_le_add_right hstock.2.1 _, lt_of_le_of_ne hstock.2.2.1 _⟩,
    rintro rfl,
    have hA_in : A_i.nonempty,
    { rw nonempty_iff_ne_empty,
      rintro rfl,
      obtain hstock2 := hstock.2.2.2.2.1,
      rw [rec_sum_empty, rat.cast_zero, sub_nonpos, div_le_div_iff (hy01.trans_le hstock.1) hM,
        one_mul] at hstock2,
      exact (hstock2.trans hqaux).not_lt hMw },
    obtain ⟨x, hx⟩ := hA_in,
    cases hdiv x (hA_i hx) with d hdiv,
    refine (hstock1 x hx d hdiv.2.2 (lt_of_le_of_ne (nat.le_floor hdiv.2.1) _)).not_le hdiv.1,
    rintro rfl,
    exact hdiv2 ⟨x, hx, hdiv.2.2⟩ },
  let α' := (2 : ℚ) / d_i',
  have hα'aux : (α' : ℝ) = 2 / d_i', by push_cast,
  have hqaux' : (d_i' : ℝ) ≤ ⌊w⌋₊ := nat.cast_le.2 (min_le_right _ _),
  have hqaux'' : (d_i' : ℝ) ≤ w := hqaux'.trans hqaux,
  have hrec5'''aux : (0 : ℝ) < d_i := hy01.trans_le hstock.1,
  have hrec5''' : 0 < d_i := nat.cast_pos.1 hrec5'''aux,
  have hqauxx : (1 : ℝ) < d_i' := nat.one_lt_cast.2 ((nat.succ_lt_succ hrec5''').trans_le hd_i'),
  have hα' : 4 * ε * log (log N) < α',
  { have hα'1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / d_i',
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
    have hrec5 : (2 : ℝ)/d_i'^2 ≤ 2/(d_i'-1) - 2/d_i',
    { rw div_sub_div,
      have hrec5'' : ((d_i' : ℝ) - 1) * d_i' = d_i' ^ 2 - d_i',
      { rw [sub_mul, sq, one_mul] },
      have hrec5' : (2 : ℝ) * d_i' - (d_i' - 1) * 2 = 2,
      { rw [sub_mul, mul_comm, sub_sub_cancel, one_mul] },
      rw hrec5',
      refine div_le_div_of_le_left zero_le_two _ _,
      rw hrec5'', rw sub_pos, nth_rewrite 0 ← pow_one (d_i' : ℝ),
      { exact pow_lt_pow hqauxx one_lt_two },
      { rw hrec5'',
        apply sub_le_self,
        exact nat.cast_nonneg _ },
      { rw sub_ne_zero,
        exact hqauxx.ne' },
      { exact (zero_le_one.trans_lt hqauxx).ne' } },
    have hrec6 :(2 : ℝ)/w^2 ≤ 2/d_i'^2, {
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
  (∀ n ∈ A, ∃ d : ℕ, (y ≤ d) ∧ ((d : ℝ) ≤ w) ∧ d ∣ n) →
  (∃ A' ⊆ A, ∃ d : ℕ, A' ≠ ∅ ∧ (y ≤ d) ∧ ((d : ℝ) ≤ w) ∧ rec_sum A' < 2/d ∧
  (2 : ℝ)/d-1/M ≤ rec_sum A' ∧ (∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q)
  ∧ (∃ n ∈ A', d ∣ n) ∧ (∀ n ∈ A', ∀ k : ℕ, k ∣ n → k < d → (k : ℝ) < y))
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
 have hdw : (d : ℝ) ≤ w, {
   have hauxw : (⌊w⌋₊ : ℝ) ≤ w, { apply nat.floor_le (le_of_lt hwzero), },
  have hauxw2 : (d : ℝ) ≤ (⌊w⌋₊ : ℝ), {exact nat.cast_le.mpr hN.2.2.1, },
  exact hauxw2.trans hauxw,
  },
 have hA'ne : A' ≠ ∅, {
 intro hA'em,
 have hreczero : rec_sum A' = 0, {  rw hA'em, apply rec_sum_empty, },
 rw hreczero at hN,
 norm_cast at hN,
 have haux1 : (2 : ℝ)/d ≤ 1/M, { apply sub_nonpos.mp hN.2.2.2.2.1, },
 have haux2 : (2 : ℝ)/w ≤ 2/d,
 { refine div_le_div_of_le_left zero_le_two _ _,
   apply @lt_of_lt_of_le _ _ 0 y (d : ℝ), exact hy01, exact hN.1, exact hdw,
   },
 have haux3 : (2 : ℝ)/w^2 ≤ 2/w,
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

-- lemma large_enough_Naux1 : (∀ᶠ (N : ℕ) in at_top,
--   (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
--    ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ ((1 : ℝ) / 100))) *
--      (((N : ℝ) ^ (1 - (3 : ℝ)/ log (log N)))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) :=
-- begin
--   have haux4: asymptotics.is_O_with ((1 : ℝ) / (2 * log (2 * 16))) log id at_top,
--   { refine is_o_log_id_at_top.def' _,
--     rw one_div_pos,
--     exact mul_pos zero_lt_two (log_pos (by norm_num1)) },
--   have haux5: asymptotics.is_O_with ((1 : ℝ) / ((2 * (2 + 1 / 100)) ^ ((1 : ℝ) / 2))) log
--      (λ x, x^((1 : ℝ) / 2)) at_top,
--   { refine (is_o_log_rpow_at_top (half_pos zero_lt_one)).def' _,
--     rw one_div_pos,
--     refine rpow_pos_of_pos _ _,
--     norm_num1, },
--   filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_ge_at_top 6),
--     tendsto_log_coe_at_top.eventually (eventually_ge_at_top (128^(500 : ℝ))),
--     eventually_ge_at_top 64,
--     tendsto_log_coe_at_top.eventually haux4.bound,
--     tendsto_log_coe_at_top.eventually haux5.bound]
--     with N hN1 hN2 hN3 hN3new4 hN3new5,
--   clear haux4 haux5,
--   have hN4 : 1 < log (log N), { exact hN1.trans_lt' (by norm_num1) },
--   have hN5 : (1 : ℝ) < N, { rw nat.one_lt_cast, refine le_trans _ hN3, norm_num1, },
--   have hN6 : (0 : ℝ) < N := zero_le_one.trans_lt hN5,
--   have hN7 : 0 < log (log N) := zero_le_one.trans_lt hN4,
--   have hN8 : 0 < log N, { exact hN2.trans_lt' (by norm_num1) },
--   have hN12 : 2 * log (2 * 16) * log (log N) ≤ log N,
--   { rwa [norm_of_nonneg hN7.le, id.def, norm_of_nonneg hN8.le, mul_comm,
--       ←div_eq_mul_one_div, le_div_iff'] at hN3new4,
--     refine mul_pos zero_lt_two (log_pos _),
--     norm_num1 },
--   have hN13 : (2 * (2 + 1 / 100)) ^ ((1 : ℝ) / 2) * log (log N) ≤ log N ^ ((1 : ℝ) / 2),
--   { simp_rw [norm_eq_abs] at hN3new5,
--     rw [abs_of_nonneg hN7.le, abs_of_nonneg (rpow_nonneg_of_nonneg hN8.le _), mul_comm, mul_div,
--       mul_one] at hN3new5,
--     rw [mul_comm, ← le_div_iff (rpow_pos_of_pos _ _)],
--     exact hN3new5,
--     norm_num1 },
--   rw le_div_iff,
--   convert_to 16 * ((N : ℝ)^(1 - (8 : ℝ)/(log(log N))) * (N ^ 2)) * (log N) ^ 2 ≤
--     ((↑N ^ (1 - 3 / log (log ↑N))) ^ 2 * (N : ℝ)^(1 - (1 : ℝ)/(log(log N)))) /
--     (2 * (log N)^((1/100 : ℝ)))
--     using 0,
--     { sorry -- ring_nf,
--     },
--   rw [le_div_iff, ← rpow_two, ← rpow_two, ← rpow_two, ← rpow_add, ← rpow_mul, ← rpow_add],
--   convert_to (2 * 16) * (log N ^ (2 : ℝ) * log N ^ (1 / 100 : ℝ)) * (N : ℝ) ^ (1 - 8 / log (log N) + 2)
--     ≤ (N : ℝ) ^ ((1 - 3 / log (log N)) * 2 + (1 - 1 / log (log N))) using 0,
--     { ring_nf,},
--   rw [← le_div_iff, ← rpow_sub, ← rpow_add],
--   have : (1 - 3 / log (log N)) * 2 + (1 - 1 / log (log N)) - (1 - 8 / log (log N) + 2)
--    = 1 / log (log N),
--    { sorry
--     --  ring,
--    },
--   rw [this, ← log_le_log, log_rpow, log_mul, log_rpow],
--   nth_rewrite 2 mul_comm,
--   rw [← div_eq_mul_one_div, le_div_iff, add_mul, mul_assoc, ← sq],
--   apply @le_trans _ _ _ ((1/2)*(log N)+(1/2)*(log N)) _,
--   apply add_le_add,
--   rwa [← mul_le_mul_left (zero_lt_two : (0 : ℝ) < 2), ← mul_assoc, ← mul_assoc, mul_one_div_cancel,
--     one_mul],
--   exact two_ne_zero,
--   rw [← mul_le_mul_left (@zero_lt_two ℝ _ _), ← mul_assoc, ← mul_assoc, mul_one_div_cancel,
--    one_mul, ← rpow_two, ← real.sqrt_le_sqrt_iff, real.sqrt_eq_rpow, real.sqrt_eq_rpow,
--    real.mul_rpow, ← rpow_mul, mul_one_div_cancel, rpow_one],
--   exact hN13,
--   refine ne_of_gt zero_lt_two,
--   exact le_of_lt hN7,
--   apply mul_nonneg zero_le_two,
--   norm_num1,
--   exact rpow_nonneg_of_nonneg hN7.le _,
--   exact le_of_lt hN8,
--   refine ne_of_gt zero_lt_two,
--   rw [mul_comm, mul_div, mul_one, add_halves],
--   exact hN7,
--   exact hN8,
--   norm_num1,
--   apply ne_of_gt,
--   apply rpow_pos_of_pos hN8,
--   exact hN6,
--   apply mul_pos,
--   norm_num1,
--   apply rpow_pos_of_pos hN8,
--   apply rpow_pos_of_pos hN6,
--   exact hN8,
--   exact hN6,
--   apply rpow_pos_of_pos hN6,
--   exact hN6,
--   exact le_of_lt hN6,
--   exact hN6,
--   refine mul_pos zero_lt_two _,
--   apply rpow_pos_of_pos hN8,
--   exact mul_pos (mul_pos (by norm_num1) (sq_pos_of_pos hN6)) (sq_pos_of_pos hN8),
-- end

-- lemma large_enough_Naux2 : ∀ (c: ℝ), (c > 0) → ∀ᶠ (N : ℕ) in at_top,
--   (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ c*(N : ℝ)^(1 - (1 : ℝ)/(log(log N)))/(log N)^((1/500 : ℝ)) ∧
--   (log N)^(-(1/101 : ℝ)) ≤ (2 : ℝ)/((log N)^(1/500 : ℝ)/4) - 1/ (N : ℝ)^(1 - (1 : ℝ)/(log(log N)))
--   :=
-- begin
--   intros c hc,
--   have haux: asymptotics.is_O_with ((1 : ℝ)) (λ (x : ℝ), (log x))
--      (λ (x : ℝ), x^((1 : ℝ)/2)) at_top, {
--     refine asymptotics.is_o.def' _ _, refine is_o_log_rpow_at_top _,
--     norm_num1, exact zero_lt_one,
--     },
--   have haux2: asymptotics.is_O_with ((1 : ℝ)) (λ (x : ℝ), (log x))
--      (λ (x : ℝ), x^((1 : ℝ))) at_top, {
--     refine asymptotics.is_o.def' _ _, refine is_o_log_rpow_at_top _,
--      norm_num1, norm_num1, },
--   filter_upwards [(tendsto_log_at_top.comp (tendsto_log_at_top.comp
--     tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top 6),
--     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
--     (eventually_ge_at_top (1 : ℝ)), eventually_ge_at_top 64,
--     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually haux.bound,
--     tendsto_coe_nat_at_top_at_top.eventually haux2.bound,
--     (tendsto_log_at_top.comp (tendsto_log_at_top.comp
--     tendsto_coe_nat_at_top_at_top)).eventually
--        (eventually_ge_at_top (-log c / (7 - 1 / 500)))
--     ] with N hN1 hN2 hN3 hNnew hNnew2 hNnew3,
--   dsimp at hN1 hN2 hNnew3,
--   have hN5 : (1 : ℝ) < N, { norm_cast, refine le_trans _ hN3, norm_num1, },
--   have hN6 : (0 : ℝ) < N, { refine lt_trans zero_lt_one hN5, },
--   have hN7 : 0 < (log(log N)), {refine lt_of_lt_of_le _ hN1, norm_num1, },
--   have hN8 : 0 < log N, { apply lt_of_lt_of_le _ hN2, norm_num1,},
--   have hN9 : log(log N) ≤ (log N)^((1 : ℝ)/2), {
--       simp_rw [norm_eq_abs] at hNnew, rw abs_of_nonneg at hNnew,
--       rw abs_of_nonneg at hNnew, dsimp at hNnew,
--       rw one_mul at hNnew, exact hNnew,
--       apply rpow_nonneg_of_nonneg, dsimp, exact le_of_lt hN8, dsimp,
--       exact le_of_lt hN7,
--    },
--   have hN10 : log N ≤ N, {
--       simp_rw [norm_eq_abs] at hNnew2, rw abs_of_nonneg at hNnew2,
--       rw abs_of_nonneg at hNnew2,
--       rw [one_mul, rpow_one] at hNnew2, exact hNnew2,
--       apply rpow_nonneg_of_nonneg, exact le_of_lt hN6,
--       exact le_of_lt hN8,
--    },
--   split,
--   rw [le_div_iff, mul_comm, ← le_div_iff, ← mul_div, ← rpow_sub],
--   have : 1 - 1 / log (log N) - (1 - 8 / log (log N)) = 7/log(log N) := by ring,
--   rw [this, ← log_le_log, log_rpow, log_mul, log_rpow],
--   nth_rewrite 1 mul_comm, rw mul_div,
--   have hcN : -(7-1/500)*log(log N) ≤ log c, {
--     rw [neg_mul, ← neg_le, ← div_le_iff'], exact hNnew3, norm_num1,},
--   apply @le_trans _ _ _ (-(7-1/500)*log(log N)+(log N)*7/log(log N)) _,
--   rw [neg_mul, neg_add_eq_sub, le_sub_iff_add_le, ← add_mul, add_sub, add_comm,
--     ← add_sub, sub_self, add_zero], nth_rewrite 1 mul_comm,
--   rw [← mul_div, mul_le_mul_left, le_div_iff, ← real.sqrt_le_sqrt_iff, sqrt_mul_self,
--        sqrt_eq_rpow],
--   exact hN9, exact le_of_lt hN7, exact le_of_lt hN8, exact hN7, norm_num1,
--   apply add_le_add_right hcN, exact hN6, apply ne_of_gt hc,
--   apply ne_of_gt, apply rpow_pos_of_pos hN6, exact hN8,
--   apply rpow_pos_of_pos hN8, apply mul_pos hc, apply rpow_pos_of_pos hN6, exact hN6,
--   apply rpow_pos_of_pos hN6, apply rpow_pos_of_pos hN8,
--   apply @le_trans _ _ _ ((7 : ℝ)/((log N)^(1/500 : ℝ))) _,
--   rw [le_div_iff, ← rpow_add], apply @le_trans _ _ _ (1 : ℝ) _,
--   apply rpow_le_one_of_one_le_of_nonpos hN2, norm_num1, norm_num1,
--   exact hN8, apply rpow_pos_of_pos hN8,
--   rw [le_sub, div_div_eq_mul_div, div_sub_div_same], norm_num1,
--   rw one_div_le_one_div,
--   apply @le_trans _ _ _ ((N : ℝ)^(((1 : ℝ)/500))) _,
--   rw rpow_le_rpow_iff, exact hN10, exact le_of_lt hN8, exact le_of_lt hN6,
--   norm_num1, apply rpow_le_rpow_of_exponent_le, exact le_of_lt hN5,
--   rw le_sub, rw one_div_le, apply le_trans _ hN1, norm_num1, exact hN7,
--   norm_num1, apply rpow_pos_of_pos hN6, apply rpow_pos_of_pos hN8,
-- end



-- lemma large_enough_Naux  :  ∀ (c: ℝ), (c > 0) → ∀ᶠ (N : ℕ) in at_top,
-- let M := (N : ℝ)^(1 - (1 : ℝ)/(log(log N))), L := M / (2 * log N ^ ((1 : ℝ)/100)),
--     T := M / log N, ε := (N : ℝ)^(-(5 : ℝ)/(log(log N))),
--     ε' := (log N)^(-(1/100 : ℝ)), K := (N : ℝ)^(1 - (3 : ℝ)/(log(log N)))  in
--   (ε ≤ ε') →
--   (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤  ε'*M ∧
--   (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) ∧
--   (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ (T * K ^ 2 / (N ^ 2 * log N)) ∧
--   (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ c*M/(log N)^((1/500 : ℝ)) ∧
--   (log N)^(-(1/101 : ℝ)) ≤ (2 : ℝ)/((log N)^(1/500 : ℝ)/4) - 1/M
--   :=
-- begin
--   intros c hc,
--   obtain hlargeaux1 := large_enough_Naux1,
--   obtain hlargeaux2 := large_enough_Naux2,
--   specialize hlargeaux2 c hc,
--   filter_upwards [(tendsto_log_at_top.comp (tendsto_log_at_top.comp
--     tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top 6),
--     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
--     (eventually_ge_at_top (128^(500 : ℝ))), eventually_ge_at_top 64,
--     hlargeaux2, hlargeaux1
--     ] with N hN1 hN2 hN3 hotheraux hnec,
--   dsimp at hN1 hN2,
--   clear hlargeaux2 hlargeaux1,
--   have hN4 : 1 < (log(log N)), { refine lt_of_lt_of_le _ hN1, norm_num1, },
--   have hN5 : (1 : ℝ) < N, { norm_cast, refine le_trans _ hN3, norm_num1, },
--   have hN6 : (0 : ℝ) < N, { refine lt_trans zero_lt_one hN5, },
--   have hN7 : 0 < (log(log N)), { refine lt_trans zero_lt_one hN4, },
--   have hN8 : 0 < log N, { apply lt_of_lt_of_le _ hN2, norm_num1,},
--   intro hT3, split,
--   rw [← div_le_iff, ← rpow_sub], apply le_trans _ hT3,
--   apply rpow_le_rpow_of_exponent_le, exact le_of_lt hN5,
--   convert_to (-7)/log(log N) ≤ (-5)/log(log N) using 0, { ring_nf, },
--   rw div_le_div_right, apply neg_le_neg, norm_num1, exact hN7, exact hN6,
--   apply rpow_pos_of_pos hN6, split,
--   exact hnec, split, apply le_trans hnec,
--   rw [div_le_div_iff, div_eq_mul_inv _ (2 * log ↑N ^ ((1 : ℝ)/100)),div_eq_mul_inv _ (log N)],
--   convert_to (((N : ℝ)^(1 - (1 : ℝ)/log(log N)))*((N : ℝ)^(1 - (3 : ℝ)/log(log N)))^2*(N : ℝ)^2)*((2*(log N)^((1 : ℝ)/100))⁻¹*(log N))
--        ≤  (((N : ℝ)^(1 - (1 : ℝ)/log(log N)))*((N : ℝ)^(1 - (3 : ℝ)/log(log N)))^2*(N : ℝ)^2)*((log N)⁻¹*16*(log N)^2) using 0,
--        { ring_nf, },
--   rw [mul_le_mul_left, ← rpow_neg_one, ← rpow_neg_one,
--       mul_comm ((log N)^(-(1 : ℝ))) 16, mul_assoc, ← rpow_two, ← rpow_add], norm_num1,
--   rw [rpow_one, mul_le_mul_right, rpow_neg_one, inv_le],
--   apply @le_trans _ _ _ (2 : ℝ) _, norm_num1,
--   rw [← mul_one (2 : ℝ), mul_assoc, mul_le_mul_left, one_mul], apply one_le_rpow,
--   apply le_trans _ hN2, norm_num1, norm_num1, exact zero_lt_two, apply mul_pos zero_lt_two,
--   apply rpow_pos_of_pos hN8, exact real.nontrivial, norm_num1, exact hN8, exact hN8,
--   apply mul_pos, apply mul_pos, apply rpow_pos_of_pos hN6,
--   apply sq_pos_of_pos, apply rpow_pos_of_pos hN6, apply sq_pos_of_pos hN6,
--   apply mul_pos, apply mul_pos, norm_num1, apply sq_pos_of_pos hN6,
--   apply sq_pos_of_pos hN8, apply mul_pos, apply sq_pos_of_pos hN6, exact hN8,
--   exact hotheraux,
-- end

lemma large_enough_N  :  ∀ (c: ℝ), (c > 0) → ∀ᶠ (N : ℕ) in at_top,
let M := (N : ℝ)^(1 - (1 : ℝ)/(log(log N))), L := M / (2 * log N ^ ((1 : ℝ)/100)),
    T := M / log N, ε := (N : ℝ)^(-(5 : ℝ)/(log(log N))),
    ε' := (log N)^(-(1/100 : ℝ)), K := (N : ℝ)^(1 - (3 : ℝ)/(log(log N)))  in
 1/M < ε*log(log N) ∧ 0 < ε ∧ (N : ℝ) ≤ M^(2 : ℝ) ∧ M < N ∧ 0 < M ∧ (0 : ℝ) < log N ∧
 8 ≤ K ∧ K < M ∧ (log N)^((1/500 : ℝ)) < 2*M ∧
  2*ε*log(log N) ≤ (log N)^(-(1/200 : ℝ)) ∧
  3*ε*log(log N) ≤ 2 / ((log N)^((1/500 : ℝ)))^2 ∧
  3 * (2 * ε' * log (log ↑N)) + 1 / M ≤ (1/(2*(log N)^((1/500 : ℝ)))) ∧
  (log N)^((1/500 : ℝ)) ≤ M/128  ∧ 1/M < ε'*log(log N) ∧
  3*ε'*log(log N) ≤ 2/((log N)^((1/500 : ℝ)))^2 ∧
   2*ε'*log(log N) ≤ (log N)^(-(1/200 : ℝ)) ∧
  (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤  ε'*M ∧
  (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) ∧
  (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ (T * K ^ 2 / (N ^ 2 * log N)) ∧
  (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ c*M/(log N)^((1/500 : ℝ)) ∧
  (log N)^(-(1/101 : ℝ)) ≤ (2 : ℝ)/((log N)^(1/500 : ℝ)/4) - 1/M
  :=
sorry
-- begin
--   intros c hc,
--   obtain hlargeaux := large_enough_Naux,
--   specialize hlargeaux c hc,
--   have haux: asymptotics.is_O_with ((1 : ℝ)/24) (λ (x : ℝ), (log x))
--      (λ (x : ℝ), x^((1 : ℝ)/125)) at_top,
--   { refine asymptotics.is_o.def' _ _, refine is_o_log_rpow_at_top _,
--      norm_num1, norm_num1, },
--  have haux2: asymptotics.is_O_with ((2 : ℝ)/3) (λ (x : ℝ), (log x))
--      (λ (x : ℝ), x^((3 : ℝ)/500)) at_top,
--   { refine asymptotics.is_o.def' _ _, refine is_o_log_rpow_at_top _,
--      norm_num1, norm_num1, },
--       have haux3: asymptotics.is_O_with ((1 : ℝ)/2) (λ (x : ℝ), (log x))
--      (λ (x : ℝ), x^((1 : ℝ)/200)) at_top,
--   { refine asymptotics.is_o.def' _ _, refine is_o_log_rpow_at_top _,
--      norm_num1, norm_num1, },
--   filter_upwards [(tendsto_log_at_top.comp (tendsto_log_at_top.comp
--     tendsto_coe_nat_at_top_at_top)).eventually (eventually_ge_at_top 6),
--     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually
--     (eventually_ge_at_top (128^(500 : ℝ))), eventually_ge_at_top 64,
--     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually haux.bound,
--     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually haux2.bound,
--     (tendsto_log_at_top.comp tendsto_coe_nat_at_top_at_top).eventually haux3.bound,
--     hlargeaux
--     ]
--     with N hN1 hN2 hN3 hN3new hN3new2 hN3new3 hotheraux,
--   dsimp at hN1 hN2,
--   clear haux haux2 haux3 hlargeaux,
--   have hN4 : 1 < (log(log N)), { refine lt_of_lt_of_le _ hN1, norm_num1, },
--   have hN5 : (1 : ℝ) < N, { norm_cast, refine le_trans _ hN3, norm_num1, },
--   have hN6 : (0 : ℝ) < N, { refine lt_trans zero_lt_one hN5, },
--   have hN7 : 0 < (log(log N)), { refine lt_trans zero_lt_one hN4, },
--   have hN8 : 0 < log N, { apply lt_of_lt_of_le _ hN2, norm_num1,},
--   have hN9 : 24*log(log N) ≤ (log N)^((1/125 : ℝ)), {
--       simp_rw [norm_eq_abs] at hN3new, rw abs_of_nonneg at hN3new,
--       rw abs_of_nonneg at hN3new, dsimp at hN3new, rw [mul_comm, ← le_div_iff],
--       rw [mul_comm, mul_div, mul_one] at hN3new, exact hN3new, norm_num1,
--       apply rpow_nonneg_of_nonneg, dsimp, exact le_of_lt hN8, dsimp,
--       exact le_of_lt hN7,
--    },
--      have hN10 : log(log N) ≤ (2/3)*(log N)^((3/500 : ℝ)), {
--       simp_rw [norm_eq_abs] at hN3new2, rw abs_of_nonneg at hN3new2,
--       rw abs_of_nonneg at hN3new2, dsimp at hN3new2, exact hN3new2,
--       apply rpow_nonneg_of_nonneg, dsimp, exact le_of_lt hN8, dsimp,
--       exact le_of_lt hN7,
--    },
--         have hN11 : 2*log(log N) ≤ (log N)^((1/200 : ℝ)), {
--       simp_rw [norm_eq_abs] at hN3new3, rw abs_of_nonneg at hN3new3,
--       rw abs_of_nonneg at hN3new3, dsimp at hN3new3, rw [mul_comm, ← le_div_iff],
--       rw [mul_comm, mul_div, mul_one] at hN3new3, exact hN3new3, norm_num1,
--       apply rpow_nonneg_of_nonneg, dsimp, exact le_of_lt hN8, dsimp,
--       exact le_of_lt hN7,
--    },
--   clear hN3new hN3new2 hN3new3,
--   have h500 : (0 : ℝ) < 500 := by norm_num1,
--   have h5002 : (0 : ℝ) < 500/2 := by norm_num1,
--     have hTp : 128*(log N)^((1/500 : ℝ)) < (N : ℝ)^(1 - (1 : ℝ)/(log(log N))),
--   { have : 128*(log N)^((1/500 : ℝ)) ≤ (log N)^((1/500 : ℝ))*(log N)^((1/500 : ℝ)),
--     { apply mul_le_mul, rw ← (real.rpow_le_rpow_iff _ _ h500), rw ← rpow_mul,
--     apply le_trans hN2, norm_num1, rw rpow_one, exact le_of_lt hN8, norm_num1,
--     apply rpow_nonneg_of_nonneg (le_of_lt hN8), refl,
--     apply rpow_nonneg_of_nonneg (le_of_lt hN8), apply rpow_nonneg_of_nonneg (le_of_lt hN8),},
--    apply lt_of_le_of_lt this, rw ← rpow_add, rw ← (real.rpow_lt_rpow_iff _ _ h5002),
--    rw ← rpow_mul, norm_num1, rw rpow_one,
--    apply lt_of_le_of_lt (real.log_le_sub_one_of_pos hN6),
--    apply lt_of_lt_of_le (sub_one_lt (N : ℝ)), rw ← rpow_mul, nth_rewrite 0 ← (real.rpow_one N),
--    apply rpow_le_rpow_of_exponent_le (le_of_lt hN5),
--    rw [sub_mul, le_sub, mul_comm, mul_one_div, div_le_iff, mul_comm,← div_le_iff],
--    apply le_trans _ hN1, norm_num1, norm_num1, exact hN7, exact le_of_lt hN6,
--    exact le_of_lt hN8, apply real.rpow_nonneg_of_nonneg (le_of_lt hN8),
--    apply real.rpow_nonneg_of_nonneg (le_of_lt hN6), exact hN8,
--    },
--   have hT : 4*(log N)^((1/500 : ℝ)) < (N : ℝ)^(1 - (1 : ℝ)/(log(log N))),
--   { apply lt_of_le_of_lt _ hTp, refine (mul_le_mul_right _).mpr _,
--     apply real.rpow_pos_of_pos hN8, norm_num1,},
--   have hT' : (log N)^((1/500 : ℝ)) < (N : ℝ)^(1 - (1 : ℝ)/(log(log N))),
--   { apply lt_of_le_of_lt _ hT, refine (le_mul_iff_one_le_left _).mpr _,
--     apply real.rpow_pos_of_pos hN8, norm_num1,},
--   split, rw [one_div, inv_pos_lt_iff_one_lt_mul, mul_comm, ← mul_assoc],
--   apply one_lt_mul, rw ← real.rpow_add, apply real.one_le_rpow (le_of_lt hN5),
--   rw [sub_add, ← sub_div, sub_nonneg, div_le_one], norm_num1,
--   exact hN1, refine lt_trans zero_lt_one hN4, exact hN6,
--   exact hN4, apply real.rpow_pos_of_pos hN6, split,
--   apply real.rpow_pos_of_pos hN6, split,
--   rw ← rpow_mul, nth_rewrite 0 ← (real.rpow_one N),
--   apply real.rpow_le_rpow_of_exponent_le (le_of_lt hN5),
--   rw [sub_mul, le_sub, mul_comm, mul_one_div], norm_num1, rw div_le_one,
--   refine le_trans _ hN1, norm_num1, exact hN7, apply le_of_lt hN6, split,
--   nth_rewrite 2 ← (real.rpow_one N), apply real.rpow_lt_rpow_of_exponent_lt hN5,
--   apply sub_lt_self, refine div_pos zero_lt_one hN7, split,
--   apply real.rpow_pos_of_pos hN6, split,
--   refine lt_of_lt_of_le _ hN2, norm_num1, split,
--   apply @le_trans _ _ 8 ((N : ℝ)^((1 : ℝ)/2)) _,
--   rw ← (real.rpow_le_rpow_iff _ _ zero_lt_two), rw ← rpow_mul, norm_num1,
--   rw rpow_one, norm_cast, exact hN3, apply le_of_lt hN6, norm_num1,
--   apply real.rpow_nonneg_of_nonneg (le_of_lt hN6), apply rpow_le_rpow_of_exponent_le,
--   apply le_of_lt hN5, rw le_sub, norm_num1, rw div_le_div_iff, norm_num1, rw one_mul,
--   exact hN1, exact hN7, exact zero_lt_two, split,
--   apply real.rpow_lt_rpow_of_exponent_lt hN5, apply sub_lt_sub_left,
--   apply div_lt_div_of_lt hN7, norm_num1, split,
--   apply lt_of_lt_of_le hT', refine (le_mul_iff_one_le_left _).mpr one_le_two,
--   apply real.rpow_pos_of_pos hN6,
--   let ε := (N : ℝ)^(-(5 : ℝ)/(log(log N))),
--   let ε' := (log N)^(-(1/100 : ℝ)),
--  have hT1 :   3*ε'*log(log N) ≤ 2/((log N)^((1/500 : ℝ)))^2, {
--   rw [le_div_iff, ← real.rpow_two, ← rpow_mul, mul_comm, ← mul_assoc,
--     ← mul_assoc, mul_comm ((log N)^((1/500 : ℝ)*2)),
--     mul_assoc 3 ((log N)^((1/500 : ℝ)*2)), ← rpow_add], norm_num1,
--     rw [mul_comm, ← mul_assoc, ← le_div_iff, mul_comm, div_eq_mul_one_div, one_div,
--       ← real.rpow_neg, neg_neg, ← le_div_iff', div_eq_mul_one_div, mul_comm, ← mul_assoc],
--     norm_num1, exact hN10, exact zero_lt_three, exact le_of_lt hN8,
--     apply rpow_pos_of_pos hN8, exact hN8, exact le_of_lt hN8, apply sq_pos_of_pos,
--     apply rpow_pos_of_pos hN8,
--   },
--  have hT2 :  2*ε'*log(log N) ≤ (log N)^(-(1/200 : ℝ)), {
--    rw [real.rpow_neg, ← one_div, le_div_iff, mul_comm, ← mul_assoc,
--    ← mul_assoc, mul_comm ((log N)^((1/200 : ℝ))),
--    mul_assoc 2 ((log N)^((1/200 : ℝ))), ← rpow_add], norm_num1,
--    rw [mul_comm, ← mul_assoc, ← le_div_iff, one_div,
--       ← real.rpow_neg, neg_neg, mul_comm], exact hN11, exact le_of_lt hN8,
--     apply rpow_pos_of_pos hN8, exact hN8, apply rpow_pos_of_pos hN8, exact le_of_lt hN8,
--   },
--  have hT3 : ε ≤ ε', {
--    rw [← one_div_le_one_div, one_div, one_div, ← rpow_neg, neg_neg, ← rpow_neg,
--      ← neg_div, neg_neg, ← log_le_log, log_rpow, log_rpow],
--      nth_rewrite 1 mul_comm, rw [mul_div, mul_comm, ← div_eq_mul_one_div,
--     div_le_div_iff],
--     apply @le_trans _ _ _ ((2/3)*(log N)^((3/500 : ℝ))*(2/3)*(log N)^((3/500 : ℝ))) _,
--     rw mul_assoc, apply mul_le_mul, exact hN10, exact hN10, exact le_of_lt hN7,
--     apply mul_nonneg, norm_num1, apply rpow_nonneg_of_nonneg (le_of_lt hN8),
--     convert_to (((log N)^((3/500 : ℝ)))*((log N)^((3/500 : ℝ))))*((2/3)*(2/3)) ≤
--      (log N)*(5*100) using 0,
--      { ring_nf, },
--     apply mul_le_mul, rw ← rpow_add, nth_rewrite 1 ← real.rpow_one (log N),
--     apply real.rpow_le_rpow_of_exponent_le, apply le_trans _ hN2,
--     norm_num1, norm_num1, exact hN8, norm_num1, norm_num1, exact le_of_lt hN8,
--     norm_num1, exact hN7, exact hN6, exact hN8, apply rpow_pos_of_pos hN8,
--     apply rpow_pos_of_pos hN6, exact le_of_lt hN6, exact le_of_lt hN8,
--     apply rpow_pos_of_pos hN8, apply rpow_pos_of_pos hN6,
--   },
--  split, refine le_trans _ hT2, rw mul_le_mul_right hN7,
--  refine (mul_le_mul_left zero_lt_two).mpr hT3, split,
--  refine le_trans _ hT1, rw mul_le_mul_right hN7,
--  refine (mul_le_mul_left zero_lt_three).mpr hT3, split,
--  apply @le_trans _ _ _ ((1/(4*(log N)^((1/500 : ℝ)))+(1/(4*(log N)^((1/500 : ℝ)))))) _,
--  apply add_le_add, rw [le_div_iff],
--  convert_to (3 * 2 * 4) * (ε' * (log N)^((1/500 : ℝ))) *  log (log N) ≤ 1 using 0,
--    { ring_nf, }, norm_num1, rw ← rpow_add, norm_num1, rw [mul_comm, ← mul_assoc],
--    rw ←  le_div_iff, nth_rewrite 0 one_div,
--    rw [← real.rpow_neg, neg_neg, mul_comm],
--    exact hN9, exact le_of_lt hN8, apply rpow_pos_of_pos hN8, exact hN8,
--    refine mul_pos zero_lt_four _, apply rpow_pos_of_pos hN8,
--    rw [div_le_div_iff, one_mul, one_mul],
--    exact le_of_lt hT,  apply rpow_pos_of_pos hN6,
--    refine mul_pos zero_lt_four _, apply rpow_pos_of_pos hN8,
--    rw [← two_mul, mul_div, div_le_div_iff, mul_one, one_mul, ← mul_assoc],
--    norm_num1, refl, refine mul_pos zero_lt_four _, apply rpow_pos_of_pos hN8,
--   refine mul_pos zero_lt_two _, apply rpow_pos_of_pos hN8,
--   split,
--   apply le_of_lt, rw lt_div_iff, rw mul_comm, exact hTp, norm_num1,
--   split,
--   rw div_lt_iff,
--   have hTq : (log N)^((1/100 : ℝ)) < (N : ℝ)^(1 - (1 : ℝ)/(log(log N))),
--   { have : (0 : ℝ) < 100 := by norm_num1,
--    rw ← (real.rpow_lt_rpow_iff _ _ this),
--    rw ← rpow_mul, norm_num1, rw rpow_one,
--    apply lt_of_le_of_lt (real.log_le_sub_one_of_pos hN6),
--    apply lt_of_lt_of_le (sub_one_lt (N : ℝ)), rw ← rpow_mul, nth_rewrite 0 ← (real.rpow_one N),
--    apply rpow_le_rpow_of_exponent_le (le_of_lt hN5),
--    rw [sub_mul, le_sub, mul_comm, mul_one_div, div_le_iff, mul_comm,← div_le_iff],
--    apply le_trans _ hN1, norm_num1, norm_num1, exact hN7, exact le_of_lt hN6,
--    exact le_of_lt hN8, apply real.rpow_nonneg_of_nonneg (le_of_lt hN8),
--    apply real.rpow_nonneg_of_nonneg (le_of_lt hN6), },
--    rw [mul_assoc, ← div_lt_iff'], nth_rewrite 0 one_div,
--    rw [← real.rpow_neg_one, ← rpow_mul], norm_num1, apply lt_trans hTq,
--    nth_rewrite 0 ← one_mul ((N : ℝ)^(1 - (1 : ℝ)/(log(log N)))),
--    refine (mul_lt_mul_right _).mpr _, apply rpow_pos_of_pos hN6, exact hN4,
--    exact le_of_lt hN8, apply rpow_pos_of_pos hN8, apply rpow_pos_of_pos hN6,
--    refine ⟨hT1, hT2, hotheraux hT3⟩,
-- end

-- Proposition 6.6
theorem technical_prop :
  ∀ᶠ (N : ℕ) in at_top, ∀ (A ⊆ finset.range (N+1)) (y z : ℝ),
  (1 ≤ y) → (4*y + 4 ≤ z) → (z ≤ (log N)^((1/500 : ℝ)))
  → (∀ n ∈ A, ( (N : ℝ)^(1 - (1 : ℝ)/(log(log N))) ≤ n ))
  → 2 / y + (log N)^(-(1/200 : ℝ)) ≤ rec_sum A
  → (∀ n ∈ A, ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧ (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z) )
  → (∀ n ∈ A, is_smooth ((N : ℝ)^(1 - (8 : ℝ)/(log(log N)))) n)
  → arith_regular N A
  → ∃ S ⊆ A, ∃ d : ℕ, (y ≤ d) ∧ ((d : ℝ) ≤ z) ∧
    rec_sum S = 1/d
  :=
begin
  obtain ⟨c,hc,circle_method⟩ := circle_method_prop2,
  obtain hlargeN := large_enough_N,
  specialize hlargeN c hc,
  filter_upwards [main_tech_lemma, force_good_properties,
     force_good_properties2, circle_method,hlargeN],
  clear circle_method,
  intros N htechlemma hforce1 hforce2 hcircle hlargeN,
  let M := (N : ℝ)^(1 - (1 : ℝ)/(log(log N))),
  let ε := (N : ℝ)^(-(5 : ℝ)/(log(log N))),
  let K := (N : ℝ)^(1 - (3 : ℝ)/(log(log N))),
  let η := (1 : ℝ)/(2*(log N)^((1 : ℝ)/100)),
  let L := M / (2 * log N ^ ((1 : ℝ)/100)),
  let T := M / log N,
  rcases hlargeN with ⟨hMε, hε, hM3, hM2, hM1, hlogN3, heK, hKM, hlogN4,
     hlogN5, hlogN6, hlargeNnew, hlargenew2, hε'M, hlarge3, hlarge4, hεε'M,
     hUhelper, hUhelper2, hUhelper3, hlarge7⟩,
have hM2aux : M ≤ N, { apply le_of_lt hM2, },
  intros A hA y z h1y hyz hzN hA2 hrec hdiv hsmooth hreg,
  have htemp6 : (N : ℝ)^(1 - (1 : ℝ)/(log(log N)))*(N : ℝ)^(-(2 : ℝ)/(log(log N))) = K, {
    rw ← rpow_add,
    have : 1 - (1 : ℝ)/(log(log N))+(-(2 : ℝ)/(log(log N))) = 1 - (3 : ℝ)/(log(log N)),
     { rw [sub_add_eq_add_sub, ← add_sub, div_sub_div_same, sub_eq_add_neg,
           sub_eq_add_neg, ← neg_div], norm_num1, refl,
     },
     rw this, apply lt_of_lt_of_le hM1 hM2aux, },
  have hzT : 0 < T, { apply div_pos hM1 hlogN3, },
  have hzL : 0 < L, {
    apply div_pos hM1, apply mul_pos, exact zero_lt_two,
    apply rpow_pos_of_pos hlogN3, },
  have hyzaux : y ≤ z, { apply @le_trans _ _ y (4*y) z, apply le_mul_of_one_le_left,
    apply le_trans zero_le_one h1y, apply le_of_lt one_lt_four,
    apply le_trans _ hyz, apply le_add_of_nonneg_right,
    apply le_trans zero_le_one, apply le_of_lt one_lt_four,},
  have hz_pos : 0 < z, {
    apply @lt_of_lt_of_le _ _ 0 1 z, exact zero_lt_one, apply le_trans h1y hyzaux, },
  have hwM : (z/4) < 2*M, {
    apply @lt_of_lt_of_le _ _ (z/4) z (2*M), rw div_lt_iff,
    apply lt_mul_of_one_lt_right hz_pos one_lt_four,
    exact zero_lt_four, apply le_trans hzN, apply le_of_lt hlogN4,
  },
  have h8z : 8 ≤ z, { apply le_trans _ hyz, apply add_le_add_right,
    apply le_mul_of_one_le_right (le_of_lt zero_lt_four) h1y, },
  have h2z : 2 ≤ z/4, { rw le_div_iff, norm_num1,
     exact h8z, exact zero_lt_four,  },
  have hyz' : ⌈y⌉₊ ≤ ⌊z/4⌋₊, {
    rw nat.ceil_le, apply @le_trans _ _ y (z/4 - 1) _,
    apply le_sub_right_of_add_le,
    rw [le_div_iff, add_mul, one_mul, mul_comm],
    exact hyz, exact zero_lt_four, rw sub_le_iff_le_add,
    apply @le_trans _ _ (z/4) (⌊z/4⌋₊.succ) _,
    apply le_of_lt, apply nat.lt_succ_floor, rw nat.succ_eq_add_one,
    push_cast,
   },
  let ε' := (log N)^(-(1/100 : ℝ)),
  have h0ε' : 0 < ε' := by apply rpow_pos_of_pos hlogN3,
  have hε'w2 : 3*ε'*log(log N) ≤ 2/(z^2), { apply le_trans hlarge3, rw div_le_div_left,
    apply sq_le_sq',  apply @le_trans _ _ _ 0 z, rw neg_nonpos, apply rpow_nonneg_of_nonneg,
    apply le_of_lt hlogN3, apply le_of_lt hz_pos, exact hzN, exact zero_lt_two,
    apply sq_pos_of_pos, apply rpow_pos_of_pos hlogN3, apply sq_pos_of_pos hz_pos, },
  have hε'z : 3*ε'*log(log N) ≤ 2/((z/4)^2), {
    have hεzaux : (z/4)^2 ≤ z^2, {
      apply sq_le_sq', apply @le_trans _ _ _ 0 (z/4),
      rw left.neg_nonpos_iff, apply le_of_lt hz_pos,
      apply le_of_lt (div_pos hz_pos zero_lt_four),
      rw div_le_iff, rw le_mul_iff_one_le_right,
      apply le_of_lt one_lt_four, exact hz_pos, exact zero_lt_four,
    },
    have hεzaux2 : 0 < (log N)^((1/500 : ℝ)), {
      apply rpow_pos_of_pos hlogN3, },
    apply le_trans hε'w2, rw div_le_div_iff, rw mul_le_mul_left,
    apply le_trans hεzaux, apply sq_le_sq',
    apply @le_trans _ _ _ 0 z, rw left.neg_nonpos_iff,
    apply le_of_lt hz_pos, apply le_of_lt hz_pos, refl, exact zero_lt_two,
    apply sq_pos_of_pos hz_pos, apply sq_pos_of_pos,
    apply div_pos hz_pos zero_lt_four,
   },
  have hrec' : 2/y + 2*ε'*log(log N) ≤ rec_sum A, {
    apply le_trans _ hrec, apply add_le_add, refl, exact hlarge4, },
  have hsmooth' : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε'*M, {
    intros q hq, rw [ppowers_in_set,finset.mem_bUnion] at hq,
    rcases hq with ⟨a,ha,hq⟩, rw finset.mem_filter at hq, simp_rw is_smooth at hsmooth,
    specialize hsmooth a ha q hq.2.1, apply le_trans _ hεε'M,
    apply hsmooth (nat.dvd_of_mem_divisors hq.1),
      },
  have hdiv' : (∀ n ∈ A, ∃ d : ℕ, (y ≤ d) ∧ ((d : ℝ) ≤ (z/4)) ∧ d ∣ n),
   { intros n hn, specialize hdiv n hn, rcases hdiv with ⟨d_1,d_2,hdiv⟩,
     refine ⟨d_1,hdiv.2.2.1,_,hdiv.1⟩, rw le_div_iff',
     apply le_trans _ hdiv.2.2.2.2, exact_mod_cast hdiv.2.2.2.1, exact zero_lt_four, },
  have htech2 := htechlemma,
  specialize htechlemma M ε' y (z/4) A hA hM1 hM2 h0ε' hwM hε'M h1y h2z hyz' hε'z
      hA2 hrec' hsmooth' hdiv',
  rcases htechlemma with ⟨A',hA',d,htech⟩,
  have hzd : d ≠ 0, {
    apply ne_of_gt, apply lt_of_lt_of_le zero_lt_one,
    exact_mod_cast le_trans h1y htech.2.1, exact nat.nontrivial,
   },
  by_cases hgoodsubset : (∃ B ⊆ A', ((rec_sum A') ≤ 3*rec_sum B) ∧
    ((ppower_rec_sum B : ℝ) ≤ (2/3)* log(log N))),
  -- The first case
  clear hforce1,
  rcases hgoodsubset with ⟨B, hB, hrecB, hppB⟩,
  have hB2 : B ⊆ finset.range(N+1), { apply subset_trans (subset_trans hB hA') hA, },
  have hzM : z < 2*M, {
     apply lt_of_le_of_lt hzN hlogN4, },
  have h14d : 1 ≤ ((4 : ℝ)*d), {
    norm_cast, rw nat.one_le_iff_ne_zero, apply mul_ne_zero,
    refine ne_of_gt zero_lt_four, exact hzd, },
  have h2z' : 2 ≤ z, { apply le_trans _ h8z, norm_num1, },
  have hdz : ⌈(4 : ℝ)*d⌉₊ ≤ ⌊z⌋₊, {
    rw nat.ceil_le, norm_cast, rw nat.le_floor_iff',
    have : (4 : ℝ)*d ≤ z, {
      rw ← le_div_iff', exact htech.2.2.1, exact zero_lt_four,},
    exact_mod_cast this, refine ne_of_gt _,
    have : (0 : ℝ) < 4*d , { apply lt_of_lt_of_le zero_lt_one h14d, },
    exact_mod_cast this,
   },
  have hB3 : ∀ (n:ℕ), n ∈ B → M ≤ n, { intros n hn,
  specialize hA2 n, apply hA2 (hA' (hB hn)), },
  have hrecB : 2/((4 : ℝ)*d) + 2*ε'*log(log N) ≤ rec_sum B, {
    have : (3 : ℝ)*(2/(4*d)) = (3/2)/d, {
        rw [div_mul_eq_div_mul_one_div, ← mul_assoc],
        rw div_eq_mul_one_div ((3 : ℝ)/2) d, norm_num1, refl,
     },
    refine (mul_le_mul_left zero_lt_three).mp _,
    apply @le_trans _ _ _ (rec_sum A' : ℝ) (3*rec_sum B),
    apply le_trans _ htech.2.2.2.2.1, apply le_sub_right_of_add_le,
    rw mul_add, rw add_assoc, apply add_le_of_le_sub_left,
    rw this, rw div_sub_div_same,
    apply @le_trans _ _ _ ((1 : ℝ)/(2*z)) ((2-3/2)/d),
    apply @le_trans _ _ _ (1/(2*(log N)^((1/500 : ℝ)))) ((1 : ℝ)/(2*z)),
    exact hlargeNnew, rw one_div_le_one_div, apply mul_le_mul_of_nonneg_left hzN,
    exact zero_le_two, refine mul_pos zero_lt_two _,
    refine lt_of_lt_of_le hz_pos hzN, refine mul_pos zero_lt_two hz_pos,
    rw [div_le_div_iff,one_mul], apply le_trans htech.2.2.1,
    rw div_eq_inv_mul, rw ← mul_assoc, rw mul_le_mul_right, norm_num1, exact hz_pos,
    refine mul_pos zero_lt_two hz_pos, refine lt_of_lt_of_le zero_lt_one _,
    refine le_trans h1y htech.2.1, exact_mod_cast hrecB,
   },
  have hsmoothB : ∀ q ∈ ppowers_in_set B, (q : ℝ) ≤ ε'*M, {
    intros q hq, specialize hsmooth' q,
    apply hsmooth' ((ppowers_in_set_subset (subset_trans hB hA')) hq),
  },
  have hdivB : (∀ (n : ℕ), n ∈ B → (∃ (d_1 : ℕ), (4 : ℝ)*d ≤ d_1 ∧ (d_1 : ℝ) ≤ z ∧ d_1 ∣ n)),
    {intros n hn, specialize hdiv n (hA' (hB hn)),
     rcases hdiv with ⟨d_1,d_2,hdiv⟩,
     have : d ≤ d_1, {
       obtain htech' := htech.2.2.2.2.2.2.2,
       specialize htech' n (hB hn) d_1 hdiv.1,
       apply le_of_not_gt, intro hfoo, specialize htech' hfoo,
       apply (not_le.mpr htech') hdiv.2.2.1,
      },
     refine ⟨d_2,_,hdiv.2.2.2.2,hdiv.2.1⟩,
     norm_cast, apply le_trans _ hdiv.2.2.2.1,
     exact (mul_le_mul_left zero_lt_four).mpr this,
     },
  specialize htech2 M ε' ((4 : ℝ)*d) z B hB2 hM1 hM2 h0ε' hzM hε'M
      h14d h2z' hdz hε'w2 hB3 hrecB hsmoothB hdivB,
  rcases htech2 with ⟨B',hB',d',htech2⟩,
  have hB'2 : B' ⊆ finset.range(N+1), { exact subset_trans hB' hB2, },
  have hB'reg : arith_regular N B' := hreg.subset (subset_trans hB' (subset_trans hB hA')),
  have hB'3 : (∀ q ∈ ppowers_in_set B',
    ((log N)^(-(1/100 : ℝ)) ≤ rec_sum_local B' q )), {
      obtain htech2' := htech2.2.2.2.2.2.1,
      intros q hq, apply le_of_lt, specialize htech2' q hq,
      exact htech2',
     },
  have hB'4 : (ppower_rec_sum B' : ℝ) ≤ (2/3)* log(log N), {
    apply le_trans _ hppB, norm_cast, apply ppower_rec_sum_mono hB',
   },

  specialize hforce2 M B' hB'2 hM3 hB'reg hB'3 hB'4,
  have hzd' : d' ≠ 0, {
    apply ne_of_gt, refine lt_of_lt_of_le zero_lt_one _,
    exact_mod_cast le_trans h14d htech2.2.1,
   },
  have hd'M : (d' : ℝ) ≤ M / 128, {
    apply le_trans htech2.2.2.1, apply le_trans hzN hlargenew2, },
  have hB'5 : (∀ (n : ℕ), n ∈ B' → M ≤ n), { intros n hn,
     specialize hA2 n, apply hA2 (hA' (hB (hB' hn))), },
  have hB'6 : (∀ (n : ℕ), n ∈ B' → n ≤ N), {
    intros n hn, rw [← nat.lt_add_one_iff, ← finset.mem_range],
    exact hB'2 hn,
   },
  have hdB' : d' ∣ B'.lcm id, {
    rcases htech2.2.2.2.2.2.2.1 with ⟨n,hn,hnew⟩,
    apply dvd_trans hnew, apply dvd_lcm hn,
   },
  let U' := min (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) (min (c * M / d') (T * K ^ 2 / (N ^ 2 * log N))),
  have hU'M : (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ U', {
    rw le_min_iff, split, exact hUhelper, rw le_min_iff, split,
    apply @le_trans _ _ _ (c*M/z) _,
    apply @le_trans _ _ _ (c*M/(log N)^((1/500 : ℝ))) _,
    exact hUhelper3, rw div_le_div_left, exact hzN, apply mul_pos hc hM1,
    apply rpow_pos_of_pos hlogN3, exact hz_pos, rw div_le_div_left,
    exact htech2.2.2.1, apply mul_pos hc hM1, exact hz_pos, norm_num,
    rw pos_iff_ne_zero, exact hzd', exact hUhelper2,
     },
  have hppB' : (∀ (q : ℕ), q ∈ ppowers_in_set B' → (q : ℝ) ≤ U'), {
    intros q hq, rw [ppowers_in_set,finset.mem_bUnion] at hq,
    rcases hq with ⟨a,ha,hq⟩, rw finset.mem_filter at hq, simp_rw is_smooth at hsmooth,
    specialize hsmooth a (hA' (hB (hB' ha))) q hq.2.1, apply le_trans _ hU'M,
    apply hsmooth (nat.dvd_of_mem_divisors hq.1),
   },
  have hgoodB' : good_condition B' K T L, { rw htemp6 at hforce2, exact hforce2,  },
  specialize @hcircle K L M T d' B' hzT hzL heK hKM hM2aux hzd'
    hd'M hB'5 hB'6 htech2.2.2.2.1 htech2.2.2.2.2.1 hdB' hppB' hgoodB',
  rcases hcircle with ⟨S,hS,hcirc⟩,
  use S, split,
  exact subset_trans hS (subset_trans hB' (subset_trans hB hA')),
  refine ⟨d',_,htech2.2.2.1,hcirc⟩, apply le_trans htech.2.1 _,
  apply le_trans _ htech2.2.1, apply le_mul_of_one_le_left,
  apply nat.cast_nonneg, norm_num,
  -- The second case
  clear hforce2 htech2,
  have hrangeA' : A' ⊆ finset.range(N+1), { apply subset_trans hA' hA, },
  have hregA' : arith_regular N A' := hreg.subset hA',
  have hNA' : (log N)^(-(1/101 : ℝ)) ≤ rec_sum A', {
    apply le_trans _ htech.2.2.2.2.1,
    apply @le_trans _ _ _ ((2 : ℝ)/((log N)^(1/500 : ℝ)/4) - 1/M) _,
    exact hlarge7, apply sub_le_sub_right, rw div_le_div_left,
    apply le_trans htech.2.2.1, rw div_le_div_right, exact hzN,
    exact zero_lt_four, exact zero_lt_two,
    apply div_pos, apply rpow_pos_of_pos hlogN3, exact zero_lt_four,
    norm_cast, rw pos_iff_ne_zero, exact hzd,
   },
  have hppA' : (∀ q ∈ ppowers_in_set A',
    ((log N)^(-(1/100 : ℝ)) ≤ rec_sum_local A' q )), {
      obtain htech' := htech.2.2.2.2.2.1,
      intros q hq, apply le_of_lt, specialize htech' q hq,
      exact htech',
     },
  specialize hforce1 M A' hrangeA' hM3 hregA' hNA' hppA',
  cases hforce1 with htemp1 htemp2,
  exfalso, apply hgoodsubset htemp1,
  have hgoodA' : good_condition A' K T L, { rw htemp6 at htemp2, exact htemp2, },
  have hdM : (d : ℝ) ≤ M / 128, {
    apply le_trans htech.2.2.1, apply le_trans _ (le_trans hzN hlargenew2),
    apply div_le_self, apply le_of_lt hz_pos, apply le_of_lt one_lt_four,
   },
  have hA'5 : (∀ (n : ℕ), n ∈ A' → M ≤ n), { intros n hn,
   specialize hA2 n, apply hA2 (hA' hn), },
  have hA'6 : (∀ (n : ℕ), n ∈ A' → n ≤ N), { intros n hn,
    rw [← nat.lt_add_one_iff, ← finset.mem_range], exact hrangeA' hn, },
  have hdA' : d ∣ A'.lcm id, {
    rcases htech.2.2.2.2.2.2.1 with ⟨n,hn,hnew⟩,
    apply dvd_trans hnew, apply dvd_lcm hn,
   },
  let U := min (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) (min (c * M / d) (T * K ^ 2 / (N ^ 2 * log N))),
  have hUM : (N : ℝ)^(1 - (8 : ℝ)/(log(log N))) ≤ U, {
    rw le_min_iff, split, exact hUhelper, rw le_min_iff, split,
    apply @le_trans _ _ _ (c*M/z) _,
    apply @le_trans _ _ _ (c*M/(log N)^((1/500 : ℝ))) _,
    exact hUhelper3, rw div_le_div_left, exact hzN, apply mul_pos hc hM1,
    apply rpow_pos_of_pos hlogN3, exact hz_pos, rw div_le_div_left,
    apply @le_trans _ _ _ (z/4) z, exact htech.2.2.1, rw div_le_iff,
    rw le_mul_iff_one_le_right, apply le_of_lt one_lt_four, exact hz_pos,
    exact zero_lt_four,
    apply mul_pos hc hM1, exact hz_pos, norm_num,
    rw pos_iff_ne_zero, exact hzd, exact hUhelper2,
   },
  have hppA' : (∀ (q : ℕ), q ∈ ppowers_in_set A' → (q : ℝ) ≤ U), {
    intros q hq, rw [ppowers_in_set,finset.mem_bUnion] at hq,
    rcases hq with ⟨a,ha,hq⟩, rw finset.mem_filter at hq, simp_rw is_smooth at hsmooth,
    specialize hsmooth a (hA' ha) q hq.2.1, apply le_trans _ hUM,
    apply hsmooth (nat.dvd_of_mem_divisors hq.1),
   },
  specialize @hcircle K L M T d A' hzT hzL heK hKM hM2aux hzd
    hdM hA'5 hA'6 htech.2.2.2.1 htech.2.2.2.2.1 hdA' hppA' hgoodA',
  rcases hcircle with ⟨S,hS,hcirc⟩,
  use S, split, exact subset_trans hS hA',
  refine ⟨d,htech.2.1,_,hcirc⟩,
  apply le_trans htech.2.2.1, apply div_le_self,
  apply @le_trans _ _ 0 1 z zero_le_one, apply le_trans h1y hyzaux,
  norm_num,
end

lemma prop_one_specialise :
  ∀ᶠ N : ℕ in at_top, ∀ A ⊆ finset.range (N + 1),
    (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n)
  → log N ^ (1 / 500 : ℝ) ≤ (rec_sum A : ℝ)
  → (∀ n ∈ A, ∃ d₂ : ℕ, d₂ ∣ n ∧ 4 ≤ d₂ ∧ (d₂ : ℝ) ≤ log N ^ (1 / 500 : ℝ))
  → (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n)
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
    { norm_num1, apply @le_trans _ _ _ (1 : ℝ) 6,
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
  → (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n)
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
