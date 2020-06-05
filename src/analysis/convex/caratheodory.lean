/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import analysis.convex.basic
import linear_algebra.finite_dimensional

/-!
# Carathéodory's convexity theorem

This file is devoted to proving Carathéodory's convexity theorem:
The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.

## Main results:

* `convex_hull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/

universes u

open set finset finite_dimensional
open_locale big_operators

variables {E : Type u} [add_comm_group E] [vector_space ℝ E] [finite_dimensional ℝ E]

namespace caratheodory

/--
If `x` is in the convex hull of some finset `t` with strictly more than `findim + 1` elements,
then it is in the union of the convex hulls of the finsets `t.erase y` for `y ∈ t`.
-/
lemma mem_convex_hull_erase [decidable_eq E] {t : finset E} (h : findim ℝ E + 1 < t.card)
  {x : E} (m : x ∈ convex_hull (↑t : set E)) :
  ∃ (y : (↑t : set E)), x ∈ convex_hull (↑(t.erase y) : set E) :=
begin
  rw finset.convex_hull_eq at m,
  obtain ⟨f, fpos, fsum, rfl⟩ := m,
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card h,
  clear h,
  let s := t.filter (λ z : E, 0 < g z),
  have : s.nonempty,
  { obtain ⟨x, hx, hgx⟩ : ∃ x ∈ t, 0 < g x := gpos,
    refine ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩, },
  obtain ⟨i₀, mem, w⟩ := s.exists_min_image (λ z, f z / g z) this,
  have hg : 0 < g i₀ := by { rw mem_filter at mem, exact mem.2 },
  have hi₀ : i₀ ∈ t := filter_subset _ mem,
  let k : E → ℝ := λ z, f z - (f i₀ / g i₀) * g z,
  have hk : k i₀ = 0 := by field_simp [k, ne_of_gt hg],
  have ksum : ∑ e in t.erase i₀, k e = 1,
  { calc ∑ e in t.erase i₀, k e = ∑ e in t, k e :
      by conv_rhs { rw [← insert_erase hi₀, sum_insert (not_mem_erase i₀ t), hk, zero_add], }
    ... = ∑ e in t, (f e - f i₀ / g i₀ * g e) : rfl
    ... = 1 : by rw [sum_sub_distrib, fsum, ← mul_sum, gsum, mul_zero, sub_zero] },
  refine ⟨⟨i₀, hi₀⟩, _⟩,
  { rw finset.convex_hull_eq,
    refine ⟨k, _, ksum, _⟩,
    { simp only [and_imp, sub_nonneg, mem_erase, ne.def, subtype.coe_mk],
      intros e hei₀ het,
      by_cases hes : e ∈ s,
      { have hge : 0 < g e := by { rw mem_filter at hes, exact hes.2 },
        rw ← le_div_iff hge,
        exact w _ hes, },
      { calc _ ≤ 0   : mul_nonpos_of_nonneg_of_nonpos _ _ -- prove two goals below
           ... ≤ f e : fpos e het,
        { apply div_nonneg_of_nonneg_of_pos (fpos i₀ (mem_of_subset (filter_subset t) mem)) hg },
        { simpa [mem_filter, het] using hes }, } },
    { simp only [subtype.coe_mk, center_mass_eq_of_sum_1 _ id ksum, id],
      calc ∑ e in t.erase i₀, k e • e = ∑ e in t, k e • e :
        by conv_rhs { rw [← insert_erase hi₀, sum_insert (not_mem_erase i₀ t), hk, zero_smul, zero_add], }
      ... = ∑ e in t, (f e - f i₀ / g i₀ * g e) • e : rfl
      ... = _ : _,
      simp only [sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, gcombo, smul_zero, sub_zero,
        center_mass, fsum, inv_one', id.def, one_smul], }, },
end

/--
The convex hull of a finset `t` with `findim ℝ E + 1 < t.card` is equal to
the union of the convex hulls of the finsets `t.erase x` for `x ∈ t`.
-/
lemma step [decidable_eq E] (t : finset E) (h : findim ℝ E + 1 < t.card) :
  convex_hull (↑t : set E) = ⋃ (x : (↑t : set E)), convex_hull ↑(t.erase x) :=
begin
  apply set.subset.antisymm,
  { intros x m',
    obtain ⟨y, m⟩ := mem_convex_hull_erase h m',
    exact mem_Union.2 ⟨y, m⟩, },
  { convert Union_subset _,
    intro x,
    apply convex_hull_mono, simp, }
end

/--
The convex hull of a finset `t` with `findim ℝ E + 1 < t.card` is contained in
the union of the convex hulls of the finsets `t' ⊆ t` with `t'.card ≤ findim ℝ E + 1`.
-/
lemma shrink' (t : finset E) (k : ℕ) (h : t.card = findim ℝ E + 1 + k) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  induction k with k ih generalizing t,
  { apply subset_subset_Union t,
    apply subset_subset_Union (set.subset.refl _),
    exact subset_subset_Union (le_of_eq h) (subset.refl _), },
  { classical,
    rw step _ (by { rw h, simp, } : findim ℝ E + 1 < t.card),
    apply Union_subset,
    intro i,
    transitivity,
    { apply ih,
      rw [card_erase_of_mem, h, nat.pred_succ],
      exact i.2, },
    { apply Union_subset_Union,
      intro t',
      apply Union_subset_Union_const,
      exact λ h, set.subset.trans h (erase_subset _ _), } }
end

/--
The convex hull of any finset `t` is contained in
the union of the convex hulls of the finsets `t' ⊆ t` with `t'.card ≤ findim ℝ E + 1`.
-/
lemma shrink (t : finset E) :
  convex_hull (↑t : set E) ⊆
    ⋃ (t' : finset E) (w : t' ⊆ t) (b : t'.card ≤ findim ℝ E + 1), convex_hull ↑t' :=
begin
  by_cases h : t.card ≤ findim ℝ E + 1,
  { apply subset_subset_Union t,
    apply subset_subset_Union (set.subset.refl _),
    exact subset_subset_Union h (set.subset.refl _), },
  simp at h,
  obtain ⟨k, w⟩ := le_iff_exists_add.mp (le_of_lt h), clear h,
  exact shrink' _ _ w,
end


end caratheodory

/--
One inclusion of Carathéodory's convexity theorem.

The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.
-/
lemma convex_hull_subset_union (s : set E) :
  convex_hull s ⊆ ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  -- First we replace `convex_hull s` with the union of the convex hulls of finite subsets,
  rw convex_hull_eq_union_convex_hull_finite_subsets,
  -- and prove the inclusion for each of those.
  apply Union_subset,
  intro r,
  apply Union_subset,
  intro h,
  -- Second, for each convex hull of a finite subset, we shrink it.
  transitivity,
  { apply caratheodory.shrink, },
  { -- After that it's just shuffling unions around.
    iterate 3 { apply Union_subset, intro, },
    apply set.subset_subset_Union,
    apply set.subset_subset_Union,
    exact subset.trans ‹i ⊆ r› ‹↑r ⊆ s›,
    apply subset_Union _ ‹i.card ≤ findim ℝ E + 1›, },
end

/--
Carathéodory's convexity theorem.

The convex hull of a set `s` in ℝᵈ is the union of the convex hulls of the (d+1)-tuples in `s`.
-/
theorem convex_hull_eq_union (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t :=
begin
  apply set.subset.antisymm,
  { apply convex_hull_subset_union, },
  iterate 3 { convert Union_subset _, intro, },
  exact convex_hull_mono ‹_›,
end

/--
A more explicit formulation of Carathéodory's convexity theorem,
writing an element of a convex hull as the center of mass
of an explicit `finset` with cardinality at most `dim + 1`.
-/
theorem eq_center_mass_card_dim_succ_of_mem_convex_hull (s : set E) (x : E) (h : x ∈ convex_hull s) :
  ∃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1)
    (f : E → ℝ), (∀ y ∈ t, 0 ≤ f y) ∧ t.sum f = 1 ∧ t.center_mass f id = x :=
begin
  rw convex_hull_eq_union at h,
  simp only [exists_prop, mem_Union] at h,
  obtain ⟨t, w, b, m⟩ := h,
  refine ⟨t, w, b, _⟩,
  rw finset.convex_hull_eq at m,
  simpa using m,
end
