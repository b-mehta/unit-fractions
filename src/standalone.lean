/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import data.real.basic
import analysis.special_functions.log.basic
import number_theory.arithmetic_function
import algebra.is_prime_pow

open_locale classical big_operators arithmetic_function

open filter finset real
open nat (coprime)

noncomputable theory

theorem card_bUnion_lt_card_mul_real_standalone {s : finset ℤ} {f : ℤ → finset ℕ} (m : ℝ) (hs : s.nonempty)
  (h : ∀ (a : ℤ), a ∈ s → ((f a).card : ℝ) < m) :
((s.bUnion f).card : ℝ) < s.card * m := sorry

lemma sum_bUnion_le_standalone {f : ℕ → ℚ} {s : finset ℕ} {t : ℕ → finset ℕ}
(hf : ∀ (i : ℕ), 0 ≤ f i) :
(s.bUnion t).sum (λ (x : ℕ), f x) ≤ s.sum (λ (x : ℕ), (t x).sum (λ (i : ℕ), f i)) :=
begin
  induction s using finset.induction_on with k s hks ih,
  { simp },
  rw [sum_insert hks, bUnion_insert],
  apply le_of_add_le_of_nonneg_left,
  { rw [sum_union_inter],
    exact add_le_add le_rfl ih },
  { exact sum_nonneg' hf }
end

lemma nat_cast_diff_issue_standalone {x y : ℤ} : (|x-y|:ℝ) = int.nat_abs (x-y) :=
by rw [←int.cast_sub, int.cast_nat_abs]

lemma two_in_Icc'_standalone {a b x y: ℤ} (I : finset ℤ) (hI : I = Icc a b) (hx : x ∈ I) (hy : y ∈ I) :
  (|x-y|:ℝ) ≤ b-a :=
begin
  suffices : ∀ {c d}, c ∈ I → d ∈ I → c ≤ d → (|d - c| : ℝ) ≤ b-a,
  { rcases le_total x y with h | h,
    { convert this hx hy h using 1,
      rw [←abs_neg],
      simp },
    { exact this hy hx h } },
  subst hI,
  clear_except,
  intros c d hc hd hcd,
  rw abs_of_nonneg,
  swap, { norm_cast, rwa sub_nonneg },
  rw mem_Icc at hc hd,
  cases hc,
  cases hd,
  norm_cast,
  linarith,
end

lemma two_in_Icc_standalone {a b x y: ℤ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : (|x-y|:ℝ) ≤ b-a :=
two_in_Icc'_standalone _ rfl hx hy

lemma omega_div_standalone {a b : ℕ} (h: b ∣ a) : (ω a:ℝ) - ω b ≤ ω (a/b) :=
begin
  rcases a.eq_zero_or_pos with rfl | ha,
  { simp },
  rcases b.eq_zero_or_pos with rfl | hb,
  { simp [zero_dvd_iff.mp h] },
  rw sub_le_iff_le_add,
  norm_cast,
  simp only [nat.arithmetic_function.card_distinct_factors_apply],
  rw [add_comm, ←list.length_append],
  apply list.subperm.length_le,
  obtain ⟨k, rfl⟩ := h,
  have hk : 0 < k := pos_of_mul_pos_left ha hb.le,
  rw [k.mul_div_cancel_left hb],
  refine (list.nodup_dedup _).subperm _,
  intros x hx,
  rw [list.mem_dedup, nat.mem_factors_mul hb.ne' hk.ne'] at hx,
  rwa [list.mem_append, list.mem_dedup, list.mem_dedup]
end

lemma omega_div_le_standalone {a b : ℕ} (h : b ∣ a) : ω (a/b) ≤ ω a :=
begin
  obtain ⟨k, rfl⟩ := h,
  rcases eq_or_ne k 0 with rfl|hk,
  { simp },
  rcases b.eq_zero_or_pos with rfl|hb,
  { simp },
  simp only [nat.arithmetic_function.card_distinct_factors_apply, k.mul_div_cancel_left hb],
  refine (k.factors.nodup_dedup.subperm $ λ t ht, _).length_le,
  rw [list.mem_dedup, nat.mem_factors_mul hb.ne' hk],
  exact or.inr (list.mem_dedup.mp ht),
end

section list

open list

lemma list.mem_join_repeat {α} {n : ℕ} {a : list α} {t} (hn : n ≠ 0) :
  t ∈ (list.repeat a n).join ↔ t ∈ a :=
begin
  simp_rw [list.mem_join, list.mem_repeat],
  exact ⟨by { rintro ⟨a, ⟨hn, rfl⟩, h⟩, exact h }, λ h, ⟨_, ⟨hn, rfl⟩, h⟩⟩
end

lemma nat.factors_pow_perm (a : ℕ) {n : ℕ} (hn : n ≠ 0) :
  (a ^ n).factors ~ (list.repeat a.factors n).join :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simpa using or.inl hn.bot_lt },
  refine (nat.factors_unique _ $ λ p hp, _).symm,
  { simp [nat.prod_factors ha] },
  rw [list.mem_join_repeat hn, nat.mem_factors ha] at hp,
  exact hp.1
end

lemma nat.factors_pow (a : ℕ) {n : ℕ} (hn : n ≠ 0) :
  (a ^ n).factors = (list.repeat a.factors n).join.merge_sort (≤) :=
eq_of_perm_of_sorted ((a.factors_pow_perm hn).trans (perm_merge_sort _ _).symm)
                     ((a ^ n).factors_sorted) $ sorted_merge_sort _ _

lemma list.repeat_cons_dedup {α} [decidable_eq α] {t : α} {n} (hn : n ≠ 0) :
  ∀ {l}, (list.repeat t n ++ l).dedup = (t :: l).dedup :=
begin
  refine nat.le_induction _ (λ x hx ih l, _) _ (show 1 ≤ n, from hn.bot_lt),
  { simp },
  clear' n hn,
  rw [repeat_add, append_assoc, ih],
  simp
end

end list

lemma omega_pow {a n : ℕ} (hn : n ≠ 0) : ω a = ω (a ^ n) :=
begin
  simp only [nat.arithmetic_function.card_distinct_factors_apply],
  apply list.perm.length_eq,
  rw [list.perm_ext (list.nodup_dedup _) (list.nodup_dedup _)],
  intro x,
  rw [list.mem_dedup, list.mem_dedup, (a.factors_pow_perm hn).mem_iff, list.mem_join_repeat hn]
end

lemma has_dvd.dvd.omega_mul {a b n : ℕ} (h : a ∣ b) : ω (a ^ n * b) = ω b :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  rcases eq_or_ne b 0 with rfl | hb,
  { simp },
  have ha := ne_zero_of_dvd_ne_zero hb h,
  simp only [nat.arithmetic_function.card_distinct_factors_apply],
  apply list.perm.length_eq,
  simp only [list.perm_ext (list.nodup_dedup _) (list.nodup_dedup _), list.mem_dedup,
             nat.mem_factors_mul (pow_ne_zero n ha) hb, or_iff_right_iff_imp,
             (a.factors_pow_perm hn).mem_iff, list.mem_join_repeat hn],
  exact nat.factors_subset_of_dvd h hb,
end

lemma nat.prime.factors {p : ℕ} (hp : p.prime) : p.factors = [p] :=
by rw [←pow_one p, hp.factors_pow, pow_one, list.repeat_succ, list.repeat]

lemma nat.prime.omega_mul_pow_of_not_dvd {n p k : ℕ} (hp : p.prime) (h : ¬ p ∣ n) (hk : k ≠ 0) :
  ω (n * p ^ k) = ω n + 1 :=
begin
  have hn : n ≠ 0 := λ hn, (hn ▸ h) (dvd_zero p),
  simp only [nat.arithmetic_function.card_distinct_factors_apply],
  have key := nat.perm_factors_mul (pow_ne_zero k hp.ne_zero) hn,
  rw [hp.factors_pow, mul_comm] at key,
  replace key := key.dedup,
  rw [list.repeat_cons_dedup hk, list.dedup_cons_of_not_mem] at key,
  { exact key.length_eq },
  { rwa nat.mem_factors_iff_dvd hn hp }
end

lemma omega_mul_ppower_standalone {a q : ℕ} (hq : is_prime_pow q) : ω (q*a) ≤ 1 + ω a :=
begin
  obtain ⟨p, n, hp, hn, rfl⟩ := (is_prime_pow_nat_iff _).mp hq,
  by_cases p ∣ a,
  { rw [h.omega_mul],
    apply le_add_self },
  { rw [mul_comm, hp.omega_mul_pow_of_not_dvd h hn.ne', add_comm] }
end

lemma sum_add_sum_standalone {A B : finset ℕ} {f : ℕ → ℝ} :
A.sum (λ (i : ℕ), f i) + B.sum (λ (i : ℕ), f i) = (A∪B).sum (λ (i : ℕ), f i) +
(A∩B).sum (λ (i : ℕ), f i) :=
by rw sum_union_inter

lemma sum_add_sum_add_sum_standalone {A B C : finset ℕ} {f : ℕ → ℝ} :
A.sum (λ (i : ℕ), f i) + B.sum (λ (i : ℕ), f i) + C.sum (λ (i : ℕ), f i) =
(A∪B∪C).sum (λ (i : ℕ), f i) + (A∩B).sum (λ (i : ℕ), f i) + (A∩C).sum (λ (i : ℕ), f i)
+ (B∩C).sum (λ (i : ℕ), f i) - (A∩B∩C).sum (λ (i : ℕ), f i)
 := sorry

lemma sum_le_sum_of_inj_standalone {A B : finset ℕ} {f1 f2 : ℕ → ℝ} (g : ℕ → ℕ) (hf2 : ∀ b ∈ B, 0 ≤ f2 b )
(hgB : ∀ a ∈ A, g a ∈ B) (hginj : ∀ a1 a2 ∈ A, (g a1 = g a2) → a1 = a2) (hgf : ∀ a ∈ A, f2 (g a) = f1 a) :
A.sum (λ (i : ℕ), f1 i) ≤ B.sum (λ (i : ℕ), f2 i) :=
sorry

lemma eq_iff_ppowers_dvd_standalone (a b  : ℕ) : a = b ↔ (∀ q ∣ a, is_prime_pow q → coprime q (a/q)
 → q ∣ b) ∧ (∀ q ∣ b, is_prime_pow q → coprime q (b/q) → q ∣ a) := sorry

theorem is_prime_pow_dvd_prod_standalone {n : ℕ} {D : finset ℕ}
 (hD : ∀ a b ∈ D, a ≠ b → coprime a b) (hn : is_prime_pow n) :
n ∣ ∏ d in D, d ↔ ∃ d ∈ D, n ∣ d := sorry

lemma prime_pow_not_coprime_iff_standalone {a b : ℕ} (ha : is_prime_pow a) (hb : is_prime_pow b) :
 ¬ coprime a b ↔ ∃ (p : ℕ) (ka kb : ℕ), p.prime ∧ ka ≠ 0 ∧ kb ≠ 0 ∧
 p ^ ka = a ∧ p ^ kb = b := sorry

lemma prime_pow_not_coprime_prod_iff_standalone {a : ℕ} {D : finset ℕ} (ha : is_prime_pow a)
(hD : ∀ d ∈ D, is_prime_pow d) :
 ¬ coprime a (∏ d in D, d) ↔ ∃ (p : ℕ) (ka kd : ℕ) (d ∈ D), p.prime ∧ ka ≠ 0 ∧ kd ≠ 0 ∧
 p ^ ka = a ∧ p ^ kd = d := sorry

 lemma prime_pow_dvd_prod_prime_pow_standalone {a : ℕ} {D : finset ℕ} (ha : is_prime_pow a)
(hD : ∀ d ∈ D, is_prime_pow d) :
a ∣ (∏ d in D, d) → coprime a ((∏ d in D, d)/a) → a ∈ D := sorry

lemma prime_pow_prods_coprime_standalone {A B : finset ℕ} (hA : ∀ a ∈ A, is_prime_pow a)
 (hB : ∀ b ∈ B, is_prime_pow b) : coprime (∏ a in A, a) (∏ b in B, b) ↔
 ∀ a ∈ A, ∀ b ∈ B, coprime a b := sorry

lemma prod_le_max_size_standalone {ι N : Type*} [ordered_comm_semiring N]
  {s : finset ι} {f : ι → N} (hs : ∀ i ∈ s, 0 ≤ f i) (M : N) (hf : ∀ i ∈ s, f i ≤ M) :
  ∏ i in s, f i ≤ M^s.card :=
sorry

lemma omega_count_eq_ppowers_standalone {n : ℕ} :
  (filter (λ (r : ℕ), is_prime_pow r ∧ r.coprime (n / r)) n.divisors).card = ω n := sorry

lemma prod_of_subset_le_prod_of_ge_one_standalone {ι N : Type*} [ordered_comm_semiring N]
  {s t : finset ι} {f : ι → N} (h : t ⊆ s) (hs : ∀ i ∈ t, 0 ≤ f i) (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
  ∏ i in t, f i ≤ ∏ i in s, f i :=
sorry

theorem sum_bUnion_le_sum_of_nonneg_standalone
{f : ℕ → ℚ} {s : finset ℕ} {t : ℕ → finset ℕ}
 (hf : ∀ x ∈ s.bUnion t, 0 ≤ f x) :
(s.bUnion t).sum (λ (x : ℕ), f x) ≤ s.sum (λ (x : ℕ), (t x).sum (λ (i : ℕ), f i)) :=
sorry

theorem weighted_ph_standalone {α M: Type*} {s : finset α}
{f : α → M} {w : α → M} {b : M} [ordered_comm_semiring M] (h0b : 0 < b)
(hw : ∀ (a : α), a ∈ s → 0 ≤ w a) (hf : ∀ (a : α), a ∈ s → 0 ≤ f a)
(hb : b ≤ s.sum (λ (x : α), ((w x) * (f x)))) :
∃ (y : α) (H : y ∈ s), b ≤ (s.sum (λ (x : α), w x))*f y
:= sorry
