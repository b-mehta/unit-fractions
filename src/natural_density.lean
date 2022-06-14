/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import data.real.basic
import analysis.special_functions.log.basic
import analysis.special_functions.pow
import order.filter.at_top_bot
import number_theory.arithmetic_function
import algebra.is_prime_pow

open_locale big_operators
open filter real finset
open nat (coprime)

open_locale arithmetic_function classical
noncomputable theory

section

variables (A : set ℕ)

def partial_density (N : ℕ) : ℝ := ((range N).filter (λ n, n ∈ A)).card / N
def partial_density' (s : finset ℕ) : ℝ := (s.filter (λ n, n ∈ A)).card / s.card

def upper_density : ℝ := limsup at_top (partial_density A)
def upper_density' : ℝ := limsup at_top (partial_density' A)

variables {A}

lemma partial_density'_eq {N : ℕ} : partial_density' A (range N) = partial_density A N :=
by simp only [partial_density', partial_density, card_range]

lemma finset_at_top_iff {α β : Type*} [preorder β] {f : β → finset α} :
  (∀ (x : α), ∀ᶠ (n : β) in at_top, x ∈ f n) ↔ tendsto f at_top at_top :=
by simp [at_top_finset_eq_infi]

lemma tendsto_at_top_finset_of_monotone {α β : Type*} [preorder β] {f : β → finset α}
  (h : monotone f) (h' : ∀ x : α, ∃ n, x ∈ f n) :
  tendsto f at_top at_top :=
finset_at_top_iff.1 $ λ a, let ⟨b, hb⟩ := h' a in eventually.mono (mem_at_top b) (λ i hi, h hi hb)

lemma filter_le_of {α : Type*} {f g : filter α} (h : ∀ t ∈ g, ∃ s ∈ f, s ⊆ t) :
  f ≤ g :=
begin
  intros t ht,
  obtain ⟨s, hs₁, hs₂⟩ := h t ht,
  exact filter.mem_of_superset hs₁ hs₂,
end

example : ∃ x ∉ (at_top : filter (finset ℕ)), x ∈ map range at_top :=
begin
  refine ⟨set.range range, _, _⟩,
  { simp only [mem_at_top_sets, set.mem_range, ge_iff_le, le_iff_subset, not_exists, not_forall,
      ←ne.def],
    intros s,
    refine ⟨insert (s.sup id + 2) s, subset_insert _ _, λ x, _⟩,
    intro h,
    have : s.sup id + 2 ∈ range x,
    { rw h,
      apply mem_insert_self },
    rw [mem_range] at this,
    have : s.sup id + 1 ∈ insert (s.sup id + 2) s,
    { rw [←h, mem_range],
      apply this.trans_le',
      simp },
    simp only [mem_insert, add_right_inj, nat.one_ne_bit0, false_or] at this,
    apply (nat.lt_succ_self (s.sup id)).not_le,
    have : _ ≤ s.sup id := finset.le_sup this,
    exact this },
  { simp only [filter.mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage, set.mem_range],
    refine ⟨0, λ x hx, ⟨x, rfl⟩⟩ },
end

lemma map_range_at_top_lt : map finset.range at_top < at_top :=
begin

end

lemma map_range_at_top : filter.map finset.range at_top = at_top :=
begin
  apply le_antisymm,
  { exact tendsto_finset_range },
  -- apply filter_le_of,
  intro s,
  simp only [filter.mem_map, mem_at_top_sets, ge_iff_le, forall_exists_index, set.mem_preimage,
    le_eq_subset, exists_prop],
  intros x hx,

  -- refine ⟨range '' set.Ici x, ⟨range x, _⟩, _⟩,
  -- intros x hx,

  -- rw le_map_iff,
  -- simp only [at_top_finset_eq_infi, mem_at_top_sets],

  -- rw at_top_finset_eq_infi,
  -- intro s,
  -- simp only [filter.mem_map],
  -- simp only [mem_at_top_sets],
  -- -- simp only [ge_iff_le, set.mem_preimage, le_eq_subset, forall_exists_index],
  -- -- intros x hx,

  -- simp only [forall_exists_index],
  -- simp only [set.mem_preimage],
  -- simp only [ge_iff_le],
  -- intros x hx,
  -- rw mem_infi_of_directed,
  -- simp only [mem_principal, set.subset_def, set.mem_Ici, le_eq_subset, singleton_subset_iff],
  -- apply mem_infi_of_mem,
  -- rw mem_principal,
  -- intros p hp,
  -- simp only [set.mem_Ici, le_eq_subset, singleton_subset_iff] at hp,
  -- rw filter.mem_infi,
  -- simp only [mem_principal, set_coe.forall, subtype.coe_mk, set.Inter_coe_set],
  -- ext s,

end

#exit

-- lemma upper_density_eq : upper_density' A = upper_density A :=
-- begin
--   have := filter.at_top_finset
-- end

lemma partial_density_sdiff_finset (N : ℕ) (S : finset ℕ) :
  partial_density A N ≤ partial_density (A \ S) N + S.card / N :=
begin
  rw [partial_density, partial_density, ←add_div],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  rw [←nat.cast_add, nat.cast_le],
  refine (card_le_of_subset _).trans (card_union_le _ _),
  intros x hx,
  simp only [mem_filter] at hx,
  simp only [mem_union, mem_filter, set.mem_diff, hx.1, hx.2, mem_coe, true_and],
  apply em'
end

lemma is_bounded_under_ge_partial_density : is_bounded_under (≥) at_top (partial_density A) :=
is_bounded_under_of ⟨0, λ x, div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)⟩

lemma is_cobounded_under_le_partial_density : is_cobounded_under (≤) at_top (partial_density A) :=
is_bounded_under_ge_partial_density.is_cobounded_le

lemma is_bounded_under_le_partial_density : is_bounded_under (≤) at_top (partial_density A) :=
is_bounded_under_of
  ⟨1, λ x, div_le_one_of_le
    (nat.cast_le.2 ((card_le_of_subset (filter_subset _ _)).trans (by simp))) (nat.cast_nonneg _)⟩

lemma upper_density_preserved {S : finset ℕ} :
  upper_density A = upper_density (A \ (S : set ℕ)) :=
begin
  apply ge_antisymm,
  { refine limsup_le_limsup _ is_cobounded_under_le_partial_density
      is_bounded_under_le_partial_density,
    refine eventually_of_forall (λ N, div_le_div_of_le (nat.cast_nonneg _) _),
    refine nat.mono_cast (card_le_of_subset _),
    letI := classical.prop_decidable,
    refine monotone_filter_right _ (λ n, _),
    simp only [set.mem_diff, le_Prop_eq, and_imp, implies_true_iff] {contextual := tt} },
  rw le_iff_forall_pos_le_add,
  intros ε hε,
  rw ←sub_le_iff_le_add,
  apply le_Limsup_of_le is_bounded_under_le_partial_density,
  rintro a (ha : ∀ᶠ n : ℕ in at_top, _ ≤ _),
  rw sub_le_iff_le_add,
  apply Limsup_le_of_le is_cobounded_under_le_partial_density,
  change ∀ᶠ n : ℕ in at_top, _ ≤ _,
  have := tendsto_coe_nat_at_top_at_top.eventually_ge_at_top (↑S.card / ε),
  filter_upwards [ha, this, eventually_gt_at_top 0] with N hN hN' hN'',
  have : 0 < (N : ℝ) := nat.cast_pos.2 hN'',
  rw [div_le_iff hε, ←div_le_iff' this] at hN',
  exact (partial_density_sdiff_finset _ S).trans (add_le_add hN hN'),
end

lemma frequently_nat_of {ε : ℝ} (hA : ε < upper_density A) :
  ∃ᶠ (N : ℕ) in at_top, ε < ((range N).filter (λ n, n ∈ A)).card / N :=
frequently_lt_of_lt_limsup is_cobounded_under_le_partial_density hA

lemma exists_nat_of {ε : ℝ} (hA : ε < upper_density A) :
  ∃ (N : ℕ), 0 < N ∧ ε < ((range N).filter (λ n, n ∈ A)).card / N :=
by simpa using frequently_at_top'.1 (frequently_nat_of hA) 0

lemma exists_density_of {ε : ℝ} (hA : ε < upper_density A) :
  ∃ (N : ℕ), 0 < N ∧ ε * N < ((range N).filter (λ n, n ∈ A)).card :=
begin
  obtain ⟨N, hN, hN'⟩ := exists_nat_of hA,
  refine ⟨N, hN, _⟩,
  rwa lt_div_iff at hN',
  rwa nat.cast_pos
end

lemma upper_density_nonneg : 0 ≤ upper_density A :=
begin
  refine le_limsup_of_frequently_le _ is_bounded_under_le_partial_density,
  exact frequently_of_forall (λ x, div_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
end

end
