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

lemma int.Ico_succ_right {a b : ℤ} : finset.Ico a (b+1) = finset.Icc a b :=
by { ext x, simp only [finset.mem_Icc, finset.mem_Ico, int.lt_add_one_iff] }

lemma int.Ioc_succ_right {a b : ℤ} (h : a ≤ b) :
  finset.Ioc a (b+1) = insert (b+1) (finset.Ioc a b) :=
begin
  ext x,
  simp only [finset.mem_Ioc, finset.mem_insert],
  rw [le_iff_lt_or_eq, int.lt_add_one_iff, or_comm, and_or_distrib_left, or_congr_left],
  rw and_iff_right_of_imp,
  rintro rfl,
  exact int.lt_add_one_iff.2 h
end

lemma int.insert_Ioc_succ_left {a b : ℤ} (h : a < b) :
  insert (a+1) (finset.Ioc (a+1) b) = finset.Ioc a b :=
begin
  ext x,
  simp only [finset.mem_Ioc, finset.mem_insert],
  rw [or_and_distrib_left, eq_comm, ←le_iff_eq_or_lt, int.add_one_le_iff, and_congr_right'],
  rw or_iff_right_of_imp,
  rintro rfl,
  rwa int.add_one_le_iff,
end

lemma int.Ioc_succ_left {a b : ℤ} (h : a < b) :
  finset.Ioc (a+1) b = (finset.Ioc a b).erase (a+1) :=
begin
  rw [←@int.insert_Ioc_succ_left a b h, finset.erase_insert],
  simp only [finset.left_not_mem_Ioc, not_false_iff],
end

lemma int.Ioc_succ_succ {a b : ℤ} (h : a ≤ b) :
  finset.Ioc (a+1) (b+1) = (insert (b+1) (finset.Ioc a b)).erase (a+1) :=
begin
  rw [int.Ioc_succ_left, int.Ioc_succ_right h],
  rwa int.lt_add_one_iff,
end

open_locale big_operators

@[simp, norm_cast] lemma rat.cast_sum {α β : Type*} [division_ring β] [char_zero β] (s : finset α)
  (f : α → ℚ) :
  ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : β)) :=
(rat.cast_hom β).map_sum f s

lemma complex.re_sum {α : Type*} (s : finset α) (f : α → ℂ) :
  (∑ i in s, f i).re = ∑ i in s, (f i).re :=
complex.re_add_group_hom.map_sum f s

lemma finset.sum_erase_eq_sub {α β : Type*} [decidable_eq α] [add_comm_group β]
  {f : α → β} {s : finset α} {a : α} (ha : a ∈ s) :
  ∑ x in s.erase a, f x = (∑ x in s, f x) - f a :=
by rw [←finset.sum_erase_add _ _ ha, add_sub_cancel]

lemma finset.filter_comm {α : Type*} (p q : α → Prop) [decidable_eq α]
  [decidable_pred p] [decidable_pred q] (s : finset α) :
  (s.filter p).filter q = (s.filter q).filter p :=
by simp only [finset.filter_filter, and_comm]
