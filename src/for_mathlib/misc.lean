import analysis.convex.specific_functions
import analysis.special_functions.trigonometric.complex
import algebra.is_prime_pow

lemma int.Ico_succ_right {a b : ℤ} : finset.Ico a (b+1) = finset.Icc a b :=
by { ext x, simp only [finset.mem_Icc, finset.mem_Ico, int.lt_add_one_iff] }

lemma int.Ioc_succ_right {a b : ℤ} (h : a ≤ b) :
  finset.Ioc a (b+1) = insert (b+1) (finset.Ioc a b) :=
begin
  ext x,
  simp only [finset.mem_Ioc, finset.mem_insert],
  rw [le_iff_lt_or_eq, int.lt_add_one_iff, or_comm, and_or_distrib_left, or_congr_left'],
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

lemma finset.Ico_union_Icc_eq_Icc {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
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
  rw ←finset.Ico_union_Icc_eq_Icc h₁ h₂,
  rw finset.union_sdiff_self,
  rw finset.sdiff_eq_self_of_disjoint,
  apply Ico_disjoint_Icc_consecutive,
end

lemma range_sdiff_Icc {x y : ℕ} (h : x ≤ y) :
  finset.range (y+1) \ finset.Icc x y = finset.Ico 0 x :=
begin
  rw [finset.range_eq_Ico, nat.Ico_succ_right, finset.Icc_sdiff_Icc_right (nat.zero_le _) h],
end

lemma Ici_diff_Icc {a b : ℝ} (hab : a ≤ b) : set.Ici a \ set.Icc a b = set.Ioi b :=
begin
  rw [←set.Icc_union_Ioi_eq_Ici hab, set.union_diff_left, set.diff_eq_self],
  rintro x ⟨⟨_, hx⟩, hx'⟩,
  exact not_le_of_lt hx' hx,
end

lemma Ioi_diff_Icc {a b : ℝ} (hab : a ≤ b) : set.Ioi a \ set.Ioc a b = set.Ioi b :=
begin
  rw [←set.Ioc_union_Ioi_eq_Ioi hab, set.union_diff_left, set.diff_eq_self, set.subset_def],
  simp,
end

open_locale big_operators

@[simp, norm_cast] lemma rat.cast_sum {α β : Type*} [division_ring β] [char_zero β] (s : finset α)
  (f : α → ℚ) :
  ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : β)) :=
(rat.cast_hom β).map_sum f s

lemma complex.re_sum {α : Type*} (s : finset α) (f : α → ℂ) :
  (∑ i in s, f i).re = ∑ i in s, (f i).re :=
complex.re_add_group_hom.map_sum f s

lemma finset.prod_rpow {ι : Type*} {s : finset ι} {f : ι → ℝ}
  (c : ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) :
  (∏ i in s, f i) ^ c = ∏ i in s, f i ^ c :=
begin
  induction s using finset.cons_induction_on with a s has ih generalizing hf,
  { simp },
  simp only [finset.mem_cons, forall_eq_or_imp] at hf,
  rw [finset.prod_cons has, real.mul_rpow hf.1 (finset.prod_nonneg hf.2),
    finset.prod_cons has, ih hf.2],
end

lemma one_le_prod {ι R : Type*} [ordered_comm_semiring R] {f : ι → R} {s : finset ι}
  (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i in s, f i :=
(finset.prod_le_prod (λ _ _, zero_le_one) h1).trans' (by simp)

lemma finset.filter_comm {α : Type*} (p q : α → Prop) [decidable_eq α]
  [decidable_pred p] [decidable_pred q] (s : finset α) :
  (s.filter p).filter q = (s.filter q).filter p :=
by simp only [finset.filter_filter, and_comm]

lemma real.le_rpow_self_of_one_le {x r : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) :
  x ≤ x ^ r :=
by simpa using real.rpow_le_rpow_of_exponent_le hx hr

lemma real.le_rpow_self_of {x : ℝ} {r : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (h_one_le : r ≤ 1) :
  x ≤ x ^ r :=
begin
  rcases eq_or_ne r 0 with rfl | hr,
  { simp [hx₁] },
  rcases eq_or_lt_of_le hx₀ with rfl | hx₀,
  { rw real.zero_rpow hr },
  simpa using real.rpow_le_rpow_of_exponent_ge hx₀ hx₁ h_one_le
end

@[to_additive]
lemma prod_powerset_compl {α β : Type*} [decidable_eq α] [comm_monoid β]
  (s : finset α) (f : finset α → β) :
  ∏ x in s.powerset, f (s \ x) = ∏ x in s.powerset, f x :=
begin
  refine finset.prod_bij' (λ x _, s \ x) (by simp) (λ _ _, rfl) (λ x _, s \ x) (by simp) _ _;
  simp [finset.inter_eq_right_iff_subset],
end
