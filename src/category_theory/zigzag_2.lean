-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category
import category_theory.eq_to_hom
import category_theory.equivalence
import data.fin data.finset data.fintype
import category_theory.opposites
import tactic

@[simp] lemma fin.last_val (n : ℕ) : (fin.last n).val = n := rfl

lemma squeeze {a b : ℕ} (h : a ≤ b) (h' : b < a + 1) : a = b :=
begin
  cases h, refl, linarith,
end


namespace tactic
meta def force {α : Type} (t : tactic α) : tactic α :=
do gs ← get_goals,
   r ← t,
   gs' ← get_goals,
   guard (gs ≠ gs') <|> fail "tactic succeeded, but did not change the goal",
   return r

namespace interactive
meta def force (t : itactic) := tactic.force t
end interactive
end tactic

open opposite

namespace category_theory

universes v₁ u₁ -- declare the `v`'s first; see `category_theory.category` for an explanation

def Δ := ℕ
instance : category Δ :=
{ hom := λ n m, { f : fin n → fin m | monotone f},
  id := λ n, ⟨id, by obviously⟩,
  comp := λ l m n f g, ⟨g.val ∘ f.val, by obviously⟩ }

namespace Δ
instance  {n m : Δ} : has_coe_to_fun (n ⟶ m) :=
{ F := λ f, fin n → fin m,
  coe := λ f, f.val }

@[simp] lemma id_coe {n : Δ} (x : fin n) : ((𝟙 n) : fin n → fin n) x = x := rfl
@[simp] lemma comp_coe {l m n : Δ} (f : l ⟶ m) (g : m ⟶ n) (x : fin l) : (f ≫ g : fin l → fin n) x = g (f x) := rfl
@[simp] lemma mk_coe {n m : Δ} (f : fin n → fin m) (h) (x) : (⟨f, h⟩ : n ⟶ m) x = f x := rfl

@[extensionality] lemma hom_ext {n m : Δ} {f g : n ⟶ m} (h : (f : fin n → fin m) = g) : f = g :=
begin
  cases f,
  cases g,
  congr,
  assumption,
end

end Δ


section T
def T_map {n m : Δ} (f : n ⟶ m) : fin (n + 1) →  fin (m + 1) :=
λ i, if h : i.val < n then (f (i.cast_lt h)).cast_succ else fin.last _

lemma T_map_mono {n m : Δ} {f : n ⟶ m} : monotone (T_map f) :=
λ a b h,
begin
  cases f,
  dsimp [T_map] at *,
  split_ifs,
  {tidy},
  {apply fin.le_last},
  {rw [fin.le_iff_val_le_val] at h,
  dsimp [(Δ)] at n, -- without this line linarith doesn't know that n : ℕ and fails
  linarith},
  {apply fin.le_last}
end

lemma T_map_id {n : Δ} : T_map (𝟙 _) = @id (fin (n + 1)) :=
funext (λ a,
begin
  dsimp [T_map],
  split_ifs,
  {tidy},
  {exact fin.eq_of_veq (eq.trans rfl (eq.symm (nat.eq_of_lt_succ_of_not_lt a.is_lt h)))}
end)

-- These two lemmas should go in fin.lean. Something similiar might already be in mathlib.
lemma cast_succ_val_lt {n : ℕ} {i : fin n} : (fin.cast_succ i).val < n :=
begin
 rw [fin.cast_succ_val],
 exact i.is_lt,
end

lemma cast_lt_cast_succ {n : ℕ} (i : fin n) :
  fin.cast_lt (fin.cast_succ i) (cast_succ_val_lt) = i :=
fin.eq_of_veq (by simp only [fin.cast_lt_val, fin.cast_succ_val])

lemma T_map_comp {l m n : Δ} {f : l ⟶ m} {g : m ⟶ n} : T_map (f ≫ g) = (T_map g) ∘ (T_map f) :=
funext (λ a,
begin
  dsimp [T_map],
  split_ifs,
  { -- a.val < l
    by_cases h2 : ((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h)))
      (λ h, fin.last m)).val < m), -- see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60split_ifs.60.2C.20and.20nested.20.60dite.60/near/167593063
    { -- (dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m
      rw dif_pos h2,
      split_ifs,
      simp [cast_lt_cast_succ] at *,
    },
    { -- ¬((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m)
      rw dif_neg h2,
      split_ifs at h2,
      rw [fin.cast_succ_val] at h2,
      exact absurd ((f (fin.cast_lt a h)).is_lt) h2,
    },
  },
  { -- ¬(a.val < l)
    by_cases h2 : ((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h)))
            (λ h, fin.last m)).val < m),
    { -- (dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m
      rw dif_pos h2,
      split_ifs at h2 with h3, -- with h3 isn't working. split_ifs introduces a new variable called h2
      simp [fin.last] at h2,
      dsimp [(Δ)] at m,
      exact (absurd h2_1 (irrefl m)),
    },
    { -- ¬((dite (a.val < l) (λ h, fin.cast_succ (f (fin.cast_lt a h))) (λ h, fin.last m)).val < m)
      rw dif_neg h2,
    },
  }
end)

def T : Δ ⥤ Δ :=
{ obj := λ n, (n + 1 : ℕ),
  map := λ n m f, ⟨T_map f, T_map_mono⟩,
  map_id' := λ n, Δ.hom_ext T_map_id,
  map_comp' := λ l n m f g, Δ.hom_ext T_map_comp}

end T

section above

-- Changed above to be of type finset (fin n) rather than set (fin n)
def above {n m : Δ} (f : n ⟶ m) (j : fin m) := finset.univ.filter { i : fin n | f i ≥ j }

@[simp] lemma mem_above_iff {n m : Δ} {f : n ⟶ m} {j : fin m} {i : fin n} :
  (i ∈ (above f j)) ↔ f i ≥ j :=
⟨λ h, (finset.mem_filter.1 h).2, λ h, finset.mem_filter.2 ⟨finset.mem_univ i, h⟩⟩

lemma n_mem_above_of_T {n m : Δ} {f : n ⟶ m} {j : fin (m + 1)} :
  fin.mk n (lt_add_one _) ∈ (above (T.map f) j) :=
mem_above_iff.2
begin
  {show T_map f ⟨n,_⟩ ≥ j,
  dsimp [T_map],
  dsimp [(Δ)] at n,
  have h : ¬(n < n) := irrefl n,
  split_ifs,
  apply fin.le_last,}
end

lemma above_of_T_non_empty {n m : Δ} {f : n ⟶ m} {j : fin (m + 1)} :
  above (T.map f) j ≠ ∅ := finset.ne_empty_of_mem n_mem_above_of_T

def prime_map_fn {n m : Δ} (f : n ⟶ m) (j : fin (m + 1)) : fin (n + 1) :=
(above (T.map f) j).min' above_of_T_non_empty

lemma f_prime_map_fn_mem_above  {n m : Δ} {f : n ⟶ m} {j : fin (m + 1)} :
  prime_map_fn f j ∈ above (T.map f) j :=
finset.min'_mem _ above_of_T_non_empty

lemma f_prime_map_fn_le_j {n m : Δ} (f : n ⟶ m) (j : fin (m + 1)) :
  (T.map f) (prime_map_fn f j) ≥ j :=
mem_above_iff.1 f_prime_map_fn_mem_above

lemma zero_lt_T_obj {n : Δ} : (0 : ℕ) < T.obj n := by {dsimp [T], apply nat.succ_pos}

lemma zero_mem_above_T_zero {n m : Δ} {f : n ⟶ m} :
  fin.mk 0 zero_lt_T_obj ∈ (above (T.map f) ⟨0, zero_lt_T_obj⟩) :=
mem_above_iff.2 (fin.zero_le _)

lemma prime_map_fn_zero_eq_zero {n m : Δ} {f : n ⟶ m} :
  prime_map_fn f ⟨0, zero_lt_T_obj⟩ = ⟨0, zero_lt_T_obj⟩ :=
le_antisymm (finset.min'_le _ _ _ zero_mem_above_T_zero) (fin.zero_le _)

lemma above_subset_above {n m : Δ} {f : n ⟶ m} {j k : fin m} (h : j ≥ k) :
  above f j ⊆ above f k :=
λ i w, mem_above_iff.2 $ ge_trans (mem_above_iff.1 w) h

lemma prime_map_mono {n m : Δ} {f : n ⟶ m} {j k : fin (m + 1)} (h : j ≤ k) :
  prime_map_fn f j ≤ prime_map_fn f k :=
finset.min'_le _ above_of_T_non_empty _ $ (above_subset_above h) (finset.min'_mem _ _)

lemma n_le_mem_above_T_m {n m : Δ} {f : n ⟶ m} {i : fin (n+1)} (h : (T.map f) i ≥ fin.last m) :
  fin.last n ≤ i :=
begin
  cases f,
  dsimp at *,
  dsimp [T, T_map] at *,
  split_ifs at h with w,
  {-- i.val < n
  dsimp [(≥), (≤), fin.le] at h,
  have w' : (f_val (fin.cast_lt i w)).val < m := (f_val (fin.cast_lt i w)).is_lt,
  exact absurd h (nat.lt_le_antisymm w')
  },
  {-- ¬ i.val < n
  exact not_lt.mp w}
end

lemma prime_map_fn_top_eq_top {n m : Δ} {f : n ⟶ m} :
  prime_map_fn f (fin.last m) = fin.last n :=
le_antisymm (fin.le_last _) (finset.le_min' _ _ _ $ λ i h, n_le_mem_above_T_m (mem_above_iff.1 h))

lemma prime_map_fn_id {n : Δ} {i : fin (n + 1)} :
  prime_map_fn (𝟙 _) i = i :=
le_antisymm
(finset.min'_le _ _ _
(mem_above_iff.2 (by {rw [T.map_id'], exact le_refl _})))
(finset.le_min' _ _ _ (λ j h, by {rw [T.map_id'] at h, exact (mem_above_iff.1 h)}))

lemma min_of_min_mem_above_comp {l m n : Δ} {f : l ⟶ m} {g : m ⟶ n} {i} :
  (above (T.map f) (prime_map_fn g i)).min'
      above_of_T_non_empty ∈ above (T.map (f ≫ g)) i :=
mem_above_iff.2
begin
  rw [T.map_comp', Δ.comp_coe] at *,
  cases (T.map g) with _ T_g_mono,
  rw Δ.mk_coe at *,
  apply le_trans,
  {exact f_prime_map_fn_le_j g _},
  {exact T_g_mono
    (mem_above_iff.1 (finset.min'_mem (above (T.map f) (prime_map_fn g i)) above_of_T_non_empty))},
end

#check finset.min'_mem

lemma min_above_comp {l m n : Δ} {f : l ⟶ m} {g : m ⟶ n} {i} :
  finset.min' (above (T.map (f ≫ g)) i) above_of_T_non_empty =
      finset.min' (above (T.map f) (finset.min' (above (T.map g) i) above_of_T_non_empty)) above_of_T_non_empty :=
begin
  apply le_antisymm,
  { apply finset.min'_le,
    rw [T.map_comp'],
    dsimp [above],
    tidy?,}
end

#print T

example {l m n : Δ} {f : l ⟶ m} {g : m ⟶ n} : T.map (f ≫ g) = T.map f ≫ T.map g := by library_search

end above

section Δ_
def Δ_ := ℕ
instance : has_coe Δ_ Δ :=
{ coe := λ n, (n + 1 : ℕ) }

instance category_Δ_ : category Δ_ :=
{ hom := λ n m, { f : fin (n+1) → fin (m+1) | monotone f ∧ f 0 = 0 ∧ f (fin.last _) = fin.last _ },
  id := λ n, ⟨id, by obviously⟩,
  comp := λ l m n f g, ⟨g.val ∘ f.val,
  by obviously,
  by {cases g with _ hg,
      cases f with _ hf,
      dsimp at *,
      rw [hf.2.1, hg.2.1]},
  by {cases g with _ hg,
      cases f with _ hf,
      dsimp at *,
      rw [hf.2.2, hg.2.2]}⟩ }.

end Δ_

namespace Δ_

instance  {n m : Δ_} : has_coe_to_fun (n ⟶ m) :=
{ F := λ f, fin (n + 1) → fin (m + 1),
  coe := λ f, f.val }

@[simp] lemma id_coe {n : Δ_} (x : fin n) : ((𝟙 n) : fin (n + 1) → fin _) x = x := rfl
@[simp] lemma comp_coe {l m n : Δ_} (f : l ⟶ m) (g : m ⟶ n) (x : fin (l+1)) :
  (f ≫ g : fin _ → fin _) x = g (f x)
:= rfl
@[simp] lemma mk_coe {n m : Δ_} (f : fin _ → fin _) (h) (x) : (⟨f, h⟩ : n ⟶ m) x = f x := rfl

@[extensionality] lemma hom_ext {n m : Δ_} {f g : n ⟶ m} (h : (f : fin _ → fin _) = g) : f = g :=
begin
  cases f,
  cases g,
  congr,
  assumption,
end

instance : has_coe Δ_ᵒᵖ ℕ := {coe := λ n, unop n}

@[simp] lemma op_id_coe {n : Δ_ᵒᵖ} (x) : ((𝟙 n) : fin (n + 1) → fin _) x = x := rfl
@[simp] lemma op_comp_coe {l m n : Δ_ᵒᵖ} (f : l ⟶ m) (g : m ⟶ n) (x : fin _) :
  (f ≫ g : fin _ → fin _) x = f (g x)
:= rfl

@[extensionality] lemma op_hom_ext {n m : Δ_ᵒᵖ} {f g : n ⟶ m} (h : (f : fin _ → fin _) = g) :
  f = g :=
has_hom.hom.unop_inj $ hom_ext h

end Δ_

section prime

def prime_obj (n : Δ) : Δ_ᵒᵖ := op (n : ℕ)
def prime_map_fn {n m : Δ} (f : n ⟶ m) (j : fin (m + 1)) : fin (n + 1) :=
(above (T.map f) j).min' above_of_T_non_empty


def prime_map {n m : Δ} (f : n ⟶ m) : (prime_obj n) ⟶ (prime_obj m) :=
has_hom.hom.op
  ⟨prime_map_fn f,
  -- f' mono
  λ j k h, prime_map_mono h,
  -- f' 0 = 0
  prime_map_fn_zero_eq_zero
  ,
  -- f' m = n
  prime_map_fn_top_eq_top⟩

#check @Δ_.op_id_coe

lemma prime_map_id (n : Δ) : prime_map (𝟙 n) = 𝟙 _ :=
Δ_.op_hom_ext
begin
  ext1,
  rw [Δ_.op_id_coe],
  dsimp [prime_map, has_hom.hom.op],
  unfold_coes,
  dsimp at *,prime_map_fn
end

lemma prime_map_comp (l m n : Δ) (f : l ⟶ m) (g : m ⟶ n) :
  prime_map (f ≫ g) = prime_map f ≫ prime_map g :=
Δ_.op_hom_ext
begin
  ext1,
  rw [Δ_.op_comp_coe],
  dsimp [prime_map, has_hom.hom.op],
  unfold_coes,
  dsimp at *,
  dsimp [prime_map_fn],

end


def prime : Δ ⥤ Δ_ᵒᵖ :=
{ obj := prime_obj,
  map := λ n m f, prime_map f,
  map_id' := prime_map_fn_id,
  map_comp' := sorry }

end prime

namespace prime
instance : ess_surj prime := sorry
instance : full prime := sorry
instance : faithful prime := sorry

def is_equivalence : is_equivalence prime :=
  is_equivalence.of_fully_faithfully_ess_surj prime
end prime

variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

structure zigzag :=
(n : Δ)
(singular : fin n → C)
(regular : fin (n+1) → C)
(forwards : Π (i : fin n), regular (i.cast_succ) ⟶ singular i)
(backwards : Π (i : fin n), regular (i.succ) ⟶ singular i)

namespace zigzag

structure hom (X Y : zigzag.{v₁} C):=
(f : fin X.n → fin Y.n)


end zigzag

end category_theory