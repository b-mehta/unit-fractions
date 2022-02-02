import analysis.convex.specific_functions
import algebra.is_prime_pow

section jordan

open_locale real
open real

lemma lt_sin_mul {x : ℝ} (hx : 0 < x) (hx' : x < 1) : x < sin ((π / 2) * x) :=
by simpa [mul_comm x] using strict_concave_on_sin_Icc.2 ⟨le_rfl, pi_pos.le⟩
  ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ pi_div_two_pos.ne (sub_pos.2 hx') hx

lemma le_sin_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : x ≤ sin ((π / 2) * x) :=
by simpa [mul_comm x] using strict_concave_on_sin_Icc.concave_on.2 ⟨le_rfl, pi_pos.le⟩
  ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ (sub_nonneg.2 hx') hx

lemma mul_lt_sin {x : ℝ} (hx : 0 < x) (hx' : x < π / 2) : (2 / π) * x < sin x :=
begin
  rw [←inv_div],
  simpa [pi_div_two_pos.ne', mul_nonneg, inv_nonneg] using @lt_sin_mul ((π / 2)⁻¹ * x) _ _,
  { exact mul_pos (inv_pos.2 pi_div_two_pos) hx },
  { rwa [←div_eq_inv_mul, div_lt_one pi_div_two_pos] },
end

/-- In the range `[0, π / 2]`, we have a linear lower bound on `sin`. This inequality forms one half
of Jordan's inequality, the other half is `real.sin_lt` -/
lemma mul_le_sin {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) : (2 / π) * x ≤ sin x :=
begin
  rw [←inv_div],
  simpa [pi_div_two_pos.ne', mul_nonneg, inv_nonneg] using @le_sin_mul ((π / 2)⁻¹ * x) _ _,
  { exact mul_nonneg (inv_nonneg.2 pi_div_two_pos.le) hx },
  { rwa [←div_eq_inv_mul, div_le_one pi_div_two_pos] },
end

end jordan

-- begin
--   obtain ⟨p, k, hp, hk, rfl⟩ := hn,
--   rw ←nat.prime_iff at hp,
--   rw [hp.pow_min_fac hk.ne', hp.factorization_pow, finsupp.single_eq_same],
-- end


-- lemma prime_dvd_is_prime_pow {p q : ℕ} (hp : p.prime) (hq : is_prime_pow q) (hpq : p ∣ q) :
--   p ^ q.factorization p = q :=
-- begin
--   rw is_prime_pow_nat_iff at hq,
--   obtain ⟨p', k, hp', hk, rfl⟩ := hq,
--   rw [hp'.factorization_pow, (nat.prime_dvd_prime_iff_eq hp hp').1 (hp.dvd_of_dvd_pow hpq),
--     finsupp.single_eq_same],
-- end

-- lemma prime_dvd_is_prime_pow' {p q : ℕ} (hp : p.prime) (hq : is_prime_pow q) :
--   p ∣ q ↔ ∃ k, 0 < k ∧ q = p ^ k :=
-- begin
--   split,
--   { intro h,
--     refine ⟨q.factorization p, _⟩,
--     rw [pos_iff_ne_zero, ←finsupp.mem_support_iff, nat.factor_iff_mem_factorization,
--       nat.mem_factors_iff_dvd, prime_dvd_is_prime_pow],

--   },
-- end

-- lemma is_prime_pow.not_coprime_iff {q₁ q₂ : ℕ} (h₁ : is_prime_pow q₁) (h₂ : is_prime_pow q₂) :
--   ¬q₁.coprime q₂ ↔ ∃ (p k₁ k₂ : ℕ), p.prime ∧ q₁ = p ^ k₁ ∧ q₂ = p ^ k₂ :=
-- begin
--   simp only [nat.prime.not_coprime_iff_dvd, exists_and_distrib_left],
--   refine exists_congr (λ p, and_congr_right (λ hp, _)),

-- end


open_locale big_operators

@[simp, norm_cast] lemma rat.cast_sum {α β : Type*} [division_ring β] [char_zero β] (s : finset α)
  (f : α → ℚ) :
  ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : β)) :=
(rat.cast_hom β).map_sum f s

lemma complex.re_sum {α : Type*} (s : finset α) (f : α → ℂ) :
  (∑ i in s, f i).re = ∑ i in s, (f i).re :=
complex.re_add_group_hom.map_sum f s
