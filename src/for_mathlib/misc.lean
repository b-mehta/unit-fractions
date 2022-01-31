import analysis.convex.specific_functions

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

open_locale big_operators

@[simp, norm_cast] lemma rat.cast_sum {α β : Type*} [division_ring β] [char_zero β] (s : finset α)
  (f : α → ℚ) :
  ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : β)) :=
(rat.cast_hom β).map_sum f s
