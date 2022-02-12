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

lemma finset.Icc_subset_range_add_one {x y : ℕ} : finset.Icc x y ⊆ finset.range (y+1) :=
begin
  rw [finset.range_eq_Ico, nat.Ico_succ_right],
  exact finset.Icc_subset_Icc_left (nat.zero_le _),
end

lemma Ico_union_Icc_eq_Icc {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
  finset.Ico x y ∪ finset.Icc y z = finset.Icc x z :=
by rw [←finset.coe_inj, finset.coe_union, finset.coe_Ico, finset.coe_Icc, finset.coe_Icc,
    set.Ico_union_Icc_eq_Icc h₁ h₂]

@[simp] lemma Ico_inter_Icc_consecutive {α : Type*} [linear_order α]
  [locally_finite_order α] (a b c : α) : finset.Ico a b ∩ finset.Icc b c = ∅ :=
begin
  refine finset.eq_empty_of_forall_not_mem (λ x hx, _),
  rw [finset.mem_inter, finset.mem_Ico, finset.mem_Icc] at hx,
  exact hx.1.2.not_le hx.2.1,
end

lemma Ico_disjoint_Icc_consecutive {α : Type*} [linear_order α]
  [locally_finite_order α] (a b c : α): disjoint (finset.Ico a b) (finset.Icc b c) :=
le_of_eq $ Ico_inter_Icc_consecutive a b c

lemma finset.Icc_sdiff_Icc_right {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
  finset.Icc x z \ finset.Icc y z = finset.Ico x y :=
begin
  rw ←Ico_union_Icc_eq_Icc h₁ h₂,
  rw finset.union_sdiff_self,
  rw finset.sdiff_eq_self_of_disjoint,
  apply Ico_disjoint_Icc_consecutive,
end

lemma range_sdiff_Icc {x y : ℕ} (h : x ≤ y) :
  finset.range (y+1) \ finset.Icc x y = finset.Ico 0 x :=
begin
  rw [finset.range_eq_Ico, nat.Ico_succ_right, finset.Icc_sdiff_Icc_right (nat.zero_le _) h],
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
