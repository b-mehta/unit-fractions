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

open_locale big_operators

@[simp, norm_cast] lemma rat.cast_sum {α β : Type*} [division_ring β] [char_zero β] (s : finset α)
  (f : α → ℚ) :
  ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : β)) :=
(rat.cast_hom β).map_sum f s

lemma complex.re_sum {α : Type*} (s : finset α) (f : α → ℂ) :
  (∑ i in s, f i).re = ∑ i in s, (f i).re :=
complex.re_add_group_hom.map_sum f s

lemma prod_of_re {α : Type*} (s : finset α) (f : α → ℝ) :
  ∏ i in s, (f i : ℂ) = (∏ i in s, f i : ℝ) :=
begin
  simp only [complex.of_real_prod],
end

lemma prod_rpow {ι : Type*} [decidable_eq ι] {s : finset ι} {f : ι → ℝ}
  (c : ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) :
  (∏ i in s, f i) ^ c = ∏ i in s, f i ^ c :=
begin
  revert hf,
  apply finset.induction_on s,
  { simp },
  intros a s has ih hf,
  simp only [finset.mem_insert, forall_eq_or_imp] at hf,
  rw [finset.prod_insert has, real.mul_rpow hf.1 (finset.prod_nonneg hf.2),
    finset.prod_insert has, ih hf.2],
end

lemma finset.sum_erase_eq_sub {α β : Type*} [decidable_eq α] [add_comm_group β]
  {f : α → β} {s : finset α} {a : α} (ha : a ∈ s) :
  ∑ x in s.erase a, f x = (∑ x in s, f x) - f a :=
by rw [←finset.sum_erase_add _ _ ha, add_sub_cancel]

lemma finset.filter_comm {α : Type*} (p q : α → Prop) [decidable_eq α]
  [decidable_pred p] [decidable_pred q] (s : finset α) :
  (s.filter p).filter q = (s.filter q).filter p :=
by simp only [finset.filter_filter, and_comm]

@[simp] theorem int.cast_dvd {α : Type*} [field α] {m n : ℤ}
  (n_dvd : n ∣ m) (n_nonzero : (n:α) ≠ 0) :
  ((m / n : ℤ) : α) = m / n :=
begin
  rcases n_dvd with ⟨k, rfl⟩,
  have : n ≠ 0, {rintro rfl, simpa using n_nonzero},
  rw [int.mul_div_cancel_left _ this, int.cast_mul, mul_div_cancel_left _ n_nonzero],
end

@[simp, norm_cast]
theorem int.cast_dvd_char_zero {k : Type*} [field k] [char_zero k] {m n : ℤ}
  (n_dvd : n ∣ m) : ((m / n : ℤ) : k) = m / n :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  rw int.cast_dvd n_dvd,
  exact int.cast_ne_zero.2 hn,
end

section asymp

open filter asymptotics

-- lemma is_O_sum (k : ℕ) (f : ℝ → ℕ) (g₁ g₂ : ℝ → ℝ)
--   (hf : tendsto f at_top at_top) (hg : is_O g₁ g₂ at_top) :
--   is_O (λ x, ∑ i in finset.Icc k (f x), g₁ i) (λ x, ∑ i in finset.Icc k (f x), g₂ i) at_top :=
-- begin
--   obtain ⟨c, hc⟩ := asymptotics.is_O.bound hg,
--   obtain ⟨K, hkK, hK : ∀ (x : ℝ), _ ≤ _ → _ ≤ _⟩ := (at_top_basis' (k : ℝ)).mem_iff.1 hc,
--   suffices :
--     is_O
--       (λ x, ∑ i in finset.Ico k ⌊K⌋₊, g₁ i + ∑ i in finset.Icc ⌊K⌋₊ (f x), g₁ i)
--       (λ x, ∑ i in finset.Ico k ⌊K⌋₊, g₂ i + ∑ i in finset.Icc ⌊K⌋₊ (f x), g₂ i) at_top,
--   { refine this.congr' _ _,
--     all_goals {
--       rw [eventually_eq],
--       filter_upwards [hf (eventually_ge_at_top ⌊K⌋₊)],
--       rintro y (hy : _ ≤ _),
--       rw [←finset.sum_union (Ico_disjoint_Icc_consecutive _ _ _),
--         finset.Ico_union_Icc_eq_Icc (nat.le_floor hkK) hy] } },
--   apply is_O.trans _ (is_o.right_is_O_add _),

--   -- have := finset.Ico_union_Icc_eq_Icc,
--   -- have : ∀ x, ∑ i in finset.Icc k (f x), g₁ i = ∑ i in finset.Ico k K, g₁ i +

--   -- apply asymptotics.is_O.of_bound sorry,
--   -- filter_upwards [hf (eventually_ge_at_top ⌈c⌉₊)],
--   -- rintro x (hx : _ ≤ _),
--   -- rw nat.ceil_le at hx,
--   -- filter_upwards [hf],
-- end

end asymp
