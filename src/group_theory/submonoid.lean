/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import algebra.big_operators
import algebra.free_monoid
import algebra.group.prod
import data.equiv.mul_add

/-!
# Submonoids

This file defines bundled multiplicative and additive submonoids.

We prove submonoids of a monoid form a complete lattice, and results about images and preimages of
submonoids under monoid homomorphisms.

There are also theorems about the submonoids generated by an element or a subset of a monoid,
defined as the infimum of the set of submonoids containing a given element/subset.

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

## Tags
submonoid, submonoids
-/

variables {M : Type*} [monoid M] {s : set M}
variables {A : Type*} [add_monoid A] {t : set A}

/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure submonoid (M : Type*) [monoid M] :=
(carrier : set M)
(one_mem' : (1 : M) ∈ carrier)
(mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)

/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
structure add_submonoid (M : Type*) [add_monoid M] :=
(carrier : set M)
(zero_mem' : (0 : M) ∈ carrier)
(add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)

attribute [to_additive add_submonoid] submonoid

/-- Map from submonoids of monoid `M` to `add_submonoid`s of `additive M`. -/
def submonoid.to_add_submonoid {M : Type*} [monoid M] (S : submonoid M) :
  add_submonoid (additive M) :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- Map from `add_submonoid`s of `additive M` to submonoids of `M`. -/
def submonoid.of_add_submonoid {M : Type*} [monoid M] (S : add_submonoid (additive M)) :
  submonoid M :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from `add_submonoid`s of `add_monoid M` to submonoids of `multiplicative M`. -/
def add_submonoid.to_submonoid {M : Type*} [add_monoid M] (S : add_submonoid M) :
  submonoid (multiplicative M) :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from submonoids of `multiplicative M` to `add_submonoid`s of `add_monoid M`. -/
def add_submonoid.of_submonoid {M : Type*} [add_monoid M] (S : submonoid (multiplicative M)) :
  add_submonoid M :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
def submonoid.add_submonoid_equiv (M : Type*) [monoid M] :
submonoid M ≃ add_submonoid (additive M) :=
{ to_fun := submonoid.to_add_submonoid,
  inv_fun := submonoid.of_add_submonoid,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl }

namespace submonoid

@[to_additive]
instance : has_coe (submonoid M) (set M) := ⟨submonoid.carrier⟩

@[to_additive]
instance : has_coe_to_sort (submonoid M) := ⟨Type*, λ S, S.carrier⟩

@[to_additive]
instance : has_mem M (submonoid M) := ⟨λ m S, m ∈ (S:set M)⟩

@[simp, to_additive]
lemma mem_carrier {s : submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[simp, norm_cast, to_additive]
lemma mem_coe {S : submonoid M} {m : M} : m ∈ (S : set M) ↔ m ∈ S := iff.rfl

@[simp, norm_cast, to_additive]
lemma coe_coe (s : submonoid M) : ↥(s : set M) = s := rfl

attribute [norm_cast] add_submonoid.mem_coe add_submonoid.coe_coe

end submonoid

@[to_additive]
protected lemma submonoid.exists {s : submonoid M} {p : s → Prop} :
  (∃ x : s, p x) ↔ ∃ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.exists

@[to_additive]
protected lemma submonoid.forall {s : submonoid M} {p : s → Prop} :
  (∀ x : s, p x) ↔ ∀ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.forall

namespace submonoid

variables (S : submonoid M)

/-- Two submonoids are equal if the underlying subsets are equal. -/
@[to_additive "Two `add_submonoid`s are equal if the underlying subsets are equal."]
theorem ext' ⦃S T : submonoid M⦄ (h : (S : set M) = T) : S = T :=
by cases S; cases T; congr'

/-- Two submonoids are equal if and only if the underlying subsets are equal. -/
@[to_additive "Two `add_submonoid`s are equal if and only if the underlying subsets are equal."]
protected theorem ext'_iff {S T : submonoid M}  : S = T ↔ (S : set M) = T :=
⟨λ h, h ▸ rfl, λ h, ext' h⟩

/-- Two submonoids are equal if they have the same elements. -/
@[ext, to_additive "Two `add_submonoid`s are equal if they have the same elements."]
theorem ext {S T : submonoid M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

attribute [ext] add_submonoid.ext

/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive submonoid replacing `carrier` with a set that is equal to it."]
def copy (S : submonoid M) (s : set M) (hs : s = S) : submonoid M :=
{ carrier := s,
  one_mem' := hs.symm ▸ S.one_mem',
  mul_mem' := hs.symm ▸ S.mul_mem' }

@[simp, to_additive] lemma coe_copy {S : submonoid M} {s : set M} (hs : s = S) :
  (S.copy s hs : set M) = s := rfl

@[to_additive] lemma copy_eq {S : submonoid M} {s : set M} (hs : s = S) : S.copy s hs = S := ext' hs

/-- A submonoid contains the monoid's 1. -/
@[to_additive "An `add_submonoid` contains the monoid's 0."]
theorem one_mem : (1 : M) ∈ S := S.one_mem'

/-- A submonoid is closed under multiplication. -/
@[to_additive "An `add_submonoid` is closed under addition."]
theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S := submonoid.mul_mem' S

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
lemma list_prod_mem : ∀ {l : list M}, (∀x ∈ l, x ∈ S) → l.prod ∈ S
| []     h := S.one_mem
| (a::l) h :=
  suffices a * l.prod ∈ S, by rwa [list.prod_cons],
  have a ∈ S ∧ (∀ x ∈ l, x ∈ S), from list.forall_mem_cons.1 h,
  S.mul_mem this.1 (list_prod_mem this.2)

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is
in the `add_submonoid`."]
lemma multiset_prod_mem {M} [comm_monoid M] (S : submonoid M) (m : multiset M) :
  (∀a ∈ m, a ∈ S) → m.prod ∈ S :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact S.list_prod_mem hl
end

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`
is in the `add_submonoid`."]
lemma prod_mem {M : Type*} [comm_monoid M] (S : submonoid M)
  {ι : Type*} {t : finset ι} {f : ι → M} (h : ∀c ∈ t, f c ∈ S) :
  t.prod f ∈ S :=
S.multiset_prod_mem (t.1.map f) $ λ x hx, let ⟨i, hi, hix⟩ := multiset.mem_map.1 hx in hix ▸ h i hi

lemma pow_mem {x : M} (hx : x ∈ S) : ∀ n:ℕ, x^n ∈ S
| 0 := S.one_mem
| (n+1) := S.mul_mem hx (pow_mem n)

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an addition."]
instance has_mul : has_mul S := ⟨λ a b, ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance has_one : has_one S := ⟨⟨_, S.one_mem⟩⟩

@[simp, to_additive] lemma coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y := rfl
@[simp, to_additive] lemma coe_one : ((1 : S) : M) = 1 := rfl
@[simp, to_additive] lemma coe_eq_coe (x y : S) : (x : M) = y ↔ x = y := set_coe.ext_iff
attribute [norm_cast] coe_eq_coe coe_mul coe_one
attribute [norm_cast] add_submonoid.coe_eq_coe add_submonoid.coe_add add_submonoid.coe_zero

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive to_add_monoid "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`
structure."]
instance to_monoid {M : Type*} [monoid M] (S : submonoid M) : monoid S :=
by refine { mul := (*), one := 1, .. }; simp [mul_assoc, ← submonoid.coe_eq_coe]

/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
@[to_additive to_add_comm_monoid "An `add_submonoid` of an `add_comm_monoid` is
an `add_comm_monoid`."]
instance to_comm_monoid {M} [comm_monoid M] (S : submonoid M) : comm_monoid S :=
{ mul_comm := λ _ _, subtype.eq $ mul_comm _ _, ..S.to_monoid}

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def subtype : S →* M := ⟨coe, rfl, λ _ _, rfl⟩

@[simp, to_additive] theorem coe_subtype : ⇑S.subtype = coe := rfl

@[to_additive]
instance : has_le (submonoid M) := ⟨λ S T, ∀ ⦃x⦄, x ∈ S → x ∈ T⟩

@[to_additive]
lemma le_def {S T : submonoid M} : S ≤ T ↔ ∀ ⦃x : M⦄, x ∈ S → x ∈ T := iff.rfl

@[simp, norm_cast, to_additive]
lemma coe_subset_coe {S T : submonoid M} : (S : set M) ⊆ T ↔ S ≤ T := iff.rfl

@[to_additive]
instance : partial_order (submonoid M) :=
{ le := λ S T, ∀ ⦃x⦄, x ∈ S → x ∈ T,
  .. partial_order.lift (coe : submonoid M → set M) ext' infer_instance }

@[simp, norm_cast, to_additive]
lemma coe_ssubset_coe {S T : submonoid M} : (S : set M) ⊂ T ↔ S < T := iff.rfl

attribute [norm_cast]  add_submonoid.coe_subset_coe add_submonoid.coe_ssubset_coe

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive "The `add_submonoid M` of the `add_monoid M`."]
instance : has_top (submonoid M) :=
⟨{ carrier := set.univ,
   one_mem' := set.mem_univ 1,
   mul_mem' := λ _ _ _ _, set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of an monoid `M`. -/
@[to_additive "The trivial `add_submonoid` `{0}` of an `add_monoid` `M`."]
instance : has_bot (submonoid M) :=
⟨{ carrier := {1},
   one_mem' := set.mem_singleton 1,
   mul_mem' := λ a b ha hb, by { simp only [set.mem_singleton_iff] at *, rw [ha, hb, mul_one] }}⟩

@[to_additive]
instance : inhabited (submonoid M) := ⟨⊥⟩

@[simp, to_additive] lemma mem_bot {x : M} : x ∈ (⊥ : submonoid M) ↔ x = 1 := set.mem_singleton_iff

@[simp, to_additive] lemma mem_top (x : M) : x ∈ (⊤ : submonoid M) := set.mem_univ x

@[simp, to_additive] lemma coe_top : ((⊤ : submonoid M) : set M) = set.univ := rfl

@[simp, to_additive] lemma coe_bot : ((⊥ : submonoid M) : set M) = {1} := rfl

/-- The inf of two submonoids is their intersection. -/
@[to_additive "The inf of two `add_submonoid`s is their intersection."]
instance : has_inf (submonoid M) :=
⟨λ S₁ S₂,
  { carrier := S₁ ∩ S₂,
    one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩,
    mul_mem' := λ _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩,
      ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

@[simp, to_additive]
lemma coe_inf (p p' : submonoid M) : ((p ⊓ p' : submonoid M) : set M) = p ∩ p' := rfl

@[simp, to_additive]
lemma mem_inf {p p' : submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

@[to_additive]
instance : has_Inf (submonoid M) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, ↑t,
  one_mem' := set.mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, set.mem_bInter $ λ i h,
    i.mul_mem (by apply set.mem_bInter_iff.1 hx i h) (by apply set.mem_bInter_iff.1 hy i h) }⟩

@[simp, to_additive]
lemma coe_Inf (S : set (submonoid M)) : ((Inf S : submonoid M) : set M) = ⋂ s ∈ S, ↑s := rfl

@[to_additive]
lemma mem_Inf {S : set (submonoid M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

@[to_additive]
lemma mem_infi {ι : Sort*} {S : ι → submonoid M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp, to_additive]
lemma coe_infi {ι : Sort*} {S : ι → submonoid M} : (↑(⨅ i, S i) : set M) = ⋂ i, S i :=
by simp only [infi, coe_Inf, set.bInter_range]

attribute [norm_cast] coe_Inf coe_infi

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive "The `add_submonoid`s of an `add_monoid` form a complete lattice."]
instance : complete_lattice (submonoid M) :=
{ le           := (≤),
  lt           := (<),
  bot          := (⊥),
  bot_le       := λ S x hx, (mem_bot.1 hx).symm ▸ S.one_mem,
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (submonoid M) $ λ s,
    is_glb.of_image (λ S T, show (S : set M) ≤ T ↔ S ≤ T, from coe_subset_coe) is_glb_binfi }

/-- The `submonoid` generated by a set. -/
@[to_additive "The `add_submonoid` generated by a set"]
def closure (s : set M) : submonoid M := Inf {S | s ⊆ S}

@[to_additive]
lemma mem_closure {x : M} : x ∈ closure s ↔ ∀ S : submonoid M, s ⊆ S → x ∈ S :=
mem_Inf

/-- The submonoid generated by a set includes the set. -/
@[simp, to_additive "The `add_submonoid` generated by a set includes the set."]
lemma subset_closure : s ⊆ closure s := λ x hx, mem_closure.2 $ λ S hS, hS hx

variable {S}
open set

/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[simp, to_additive "An additive submonoid `S` includes `closure s` if and only if it includes `s`"]
lemma closure_le : closure s ≤ S ↔ s ⊆ S :=
⟨subset.trans subset_closure, λ h, Inf_le h⟩

/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive "Additive submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`"]
lemma closure_mono ⦃s t : set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
closure_le.2 $ subset.trans h subset_closure

@[to_additive]
lemma closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
le_antisymm (closure_le.2 h₁) h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive "An induction principle for additive closure membership. If `p` holds for `0` and all
elements of `s`, and is preserved under addition, then `p` holds for all elements
of the additive closure of `s`."]
lemma closure_induction {p : M → Prop} {x} (h : x ∈ closure s)
  (Hs : ∀ x ∈ s, p x) (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
(@closure_le _ _ _ ⟨p, H1, Hmul⟩).2 Hs h

attribute [elab_as_eliminator] submonoid.closure_induction add_submonoid.closure_induction

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : galois_insertion (@closure M _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {M}

/-- Closure of a submonoid `S` equals `S`. -/
@[simp, to_additive "Additive closure of an additive submonoid `S` equals `S`"]
lemma closure_eq : closure (S : set M) = S := (submonoid.gi M).l_u_eq S

@[simp, to_additive] lemma closure_empty : closure (∅ : set M) = ⊥ :=
(submonoid.gi M).gc.l_bot

@[simp, to_additive] lemma closure_univ : closure (univ : set M) = ⊤ :=
@coe_top M _ ▸ closure_eq ⊤

@[to_additive]
lemma closure_union (s t : set M) : closure (s ∪ t) = closure s ⊔ closure t :=
(submonoid.gi M).gc.l_sup

@[to_additive]
lemma closure_Union {ι} (s : ι → set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(submonoid.gi M).gc.l_supr

@[to_additive]
lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → submonoid M} (hS : directed (≤) S)
  {x : M} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (le_def.1 $ le_supr S i) hi⟩,
  suffices : x ∈ closure (⋃ i, (S i : set M)) → ∃ i, x ∈ S i,
    by simpa only [closure_Union, closure_eq (S _)] using this,
  refine (λ hx, closure_induction hx (λ _, mem_Union.1) _ _),
  { exact hι.elim (λ i, ⟨i, (S i).one_mem⟩) },
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    rcases hS i j with ⟨k, hki, hkj⟩,
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩ }
end

@[to_additive]
lemma coe_supr_of_directed {ι} [nonempty ι] {S : ι → submonoid M} (hS : directed (≤) S) :
  ((⨆ i, S i : submonoid M) : set M) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

@[to_additive]
lemma mem_Sup_of_directed_on {S : set (submonoid M)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : M} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  rw [Sup_eq_supr, supr_subtype', mem_supr_of_directed, subtype.exists],
  exact (directed_on_iff_directed _).1 hS
end

@[to_additive]
lemma coe_Sup_of_directed_on {S : set (submonoid M)} (Sne : S.nonempty) (hS : directed_on (≤) S) :
  (↑(Sup S) : set M) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

variables {N : Type*} [monoid N] {P : Type*} [monoid P]

/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The preimage of an `add_submonoid` along an `add_monoid` homomorphism is an
`add_submonoid`."]
def comap (f : M →* N) (S : submonoid N) : submonoid M :=
{ carrier := (f ⁻¹' S),
  one_mem' := show f 1 ∈ S, by rw f.map_one; exact S.one_mem,
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw f.map_mul; exact S.mul_mem ha hb }

@[simp, to_additive]
lemma coe_comap (S : submonoid N) (f : M →* N) : (S.comap f : set M) = f ⁻¹' S := rfl

@[simp, to_additive]
lemma mem_comap {S : submonoid N} {f : M →* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := iff.rfl

@[to_additive]
lemma comap_comap (S : submonoid P) (g : N →* P) (f : M →* N) :
  (S.comap g).comap f = S.comap (g.comp f) :=
rfl

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The image of an `add_submonoid` along an `add_monoid` homomorphism is
an `add_submonoid`."]
def map (f : M →* N) (S : submonoid M) : submonoid N :=
{ carrier := (f '' S),
  one_mem' := ⟨1, S.one_mem, f.map_one⟩,
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, S.mul_mem hx hy,
    by rw f.map_mul; refl⟩ end }

@[simp, to_additive]
lemma coe_map (f : M →* N) (S : submonoid M) :
  (S.map f : set N) = f '' S := rfl

@[simp, to_additive]
lemma mem_map {f : M →* N} {S : submonoid M} {y : N} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

@[to_additive]
lemma map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
ext' $ image_image _ _ _

@[to_additive]
lemma map_le_iff_le_comap {f : M →* N} {S : submonoid M} {T : submonoid N} :
  S.map f ≤ T ↔ S ≤ T.comap f :=
image_subset_iff

@[to_additive]
lemma gc_map_comap (f : M →* N) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

@[to_additive]
lemma map_sup (S T : submonoid M) (f : M →* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(gc_map_comap f).l_sup

@[to_additive]
lemma map_supr {ι : Sort*} (f : M →* N) (s : ι → submonoid M) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

@[to_additive]
lemma comap_inf (S T : submonoid N) (f : M →* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
(gc_map_comap f).u_inf

@[to_additive]
lemma comap_infi {ι : Sort*} (f : M →* N) (s : ι → submonoid N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp, to_additive] lemma map_bot (f : M →* N) : (⊥ : submonoid M).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp, to_additive] lemma comap_top (f : M →* N) : (⊤ : submonoid N).comap f = ⊤ :=
(gc_map_comap f).u_top

/-- Given `submonoid`s `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
@[to_additive prod "Given `add_submonoid`s `s`, `t` of `add_monoid`s `A`, `B` respectively, `s × t`
as an `add_submonoid` of `A × B`."]
def prod (s : submonoid M) (t : submonoid N) : submonoid (M × N) :=
{ carrier := (s : set M).prod t,
  one_mem' := ⟨s.one_mem, t.one_mem⟩,
  mul_mem' := λ p q hp hq, ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩ }

@[to_additive coe_prod]
lemma coe_prod (s : submonoid M) (t : submonoid N) :
 (s.prod t : set (M × N)) = (s : set M).prod (t : set N) :=
rfl

@[to_additive mem_prod]
lemma mem_prod {s : submonoid M} {t : submonoid N} {p : M × N} :
  p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[to_additive prod_mono]
lemma prod_mono : ((≤) ⇒ (≤) ⇒ (≤)) (@prod M _ N _) (@prod M _ N _) :=
λ s s' hs t t' ht, set.prod_mono hs ht

@[to_additive prod_mono_right]
lemma prod_mono_right (s : submonoid M) : monotone (λ t : submonoid N, s.prod t) :=
prod_mono (le_refl s)

@[to_additive prod_mono_left]
lemma prod_mono_left (t : submonoid N) : monotone (λ s : submonoid M, s.prod t) :=
λ s₁ s₂ hs, prod_mono hs (le_refl t)

@[to_additive prod_top]
lemma prod_top (s : submonoid M) :
  s.prod (⊤ : submonoid N) = s.comap (monoid_hom.fst M N) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

@[to_additive top_prod]
lemma top_prod (s : submonoid N) :
  (⊤ : submonoid M).prod s = s.comap (monoid_hom.snd M N) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp, to_additive top_prod_top]
lemma top_prod_top : (⊤ : submonoid M).prod (⊤ : submonoid N) = ⊤ :=
(top_prod _).trans $ comap_top _

@[to_additive] lemma bot_prod_bot : (⊥ : submonoid M).prod (⊥ : submonoid N) = ⊥ :=
ext' $ by simp [coe_prod, prod.one_eq_mk]

/-- Product of submonoids is isomorphic to their product as monoids. -/
@[to_additive prod_equiv "Product of additive submonoids is isomorphic to their product
as additive monoids"]
def prod_equiv (s : submonoid M) (t : submonoid N) : s.prod t ≃* s × t :=
{ map_mul' := λ x y, rfl, .. equiv.set.prod ↑s ↑t }

end submonoid

namespace monoid_hom

variables {N : Type*} {P : Type*} [monoid N] [monoid P] (S : submonoid M)

open submonoid

/-- The range of a monoid homomorphism is a submonoid. -/
@[to_additive "The range of an `add_monoid_hom` is an `add_submonoid`."]
def mrange (f : M →* N) : submonoid N := (⊤ : submonoid M).map f

@[simp, to_additive] lemma coe_mrange (f : M →* N) :
  (f.mrange : set N) = set.range f :=
set.image_univ

@[simp, to_additive] lemma mem_mrange {f : M →* N} {y : N} :
  y ∈ f.mrange ↔ ∃ x, f x = y :=
by simp [mrange]

@[to_additive]
lemma map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = (g.comp f).mrange :=
(⊤ : submonoid M).map_map g f

/-- Restriction of a monoid hom to a submonoid of the domain. -/
@[to_additive "Restriction of an add_monoid hom to an `add_submonoid` of the domain."]
def mrestrict {N : Type*} [monoid N] (f : M →* N) (S : submonoid M) : S →* N := f.comp S.subtype

@[simp, to_additive]
lemma mrestrict_apply {N : Type*} [monoid N] (f : M →* N) (x : S) : f.mrestrict S x = f x := rfl

/-- Restriction of a monoid hom to a submonoid of the codomain. -/
@[to_additive "Restriction of an `add_monoid` hom to an `add_submonoid` of the codomain."]
def cod_mrestrict (f : M →* N) (S : submonoid N) (h : ∀ x, f x ∈ S) : M →* S :=
{ to_fun := λ n, ⟨f n, h n⟩,
  map_one' := subtype.eq f.map_one,
  map_mul' := λ x y, subtype.eq (f.map_mul x y) }

/-- Restriction of a monoid hom to its range iterpreted as a submonoid. -/
@[to_additive "Restriction of an `add_monoid` hom to its range interpreted as a submonoid."]
def mrange_restrict {N} [monoid N] (f : M →* N) : M →* f.mrange :=
f.cod_mrestrict f.mrange $ λ x, ⟨x, submonoid.mem_top x, rfl⟩

@[simp, to_additive]
lemma coe_mrange_restrict {N} [monoid N] (f : M →* N) (x : M) :
  (f.mrange_restrict x : N) = f x :=
rfl

@[to_additive]
lemma mrange_top_iff_surjective {N} [monoid N] {f : M →* N} :
  f.mrange = (⊤ : submonoid N) ↔ function.surjective f :=
submonoid.ext'_iff.trans $ iff.trans (by rw [coe_mrange, coe_top]) set.range_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_monoid` hom is the whole of the codomain."]
lemma mrange_top_of_surjective {N} [monoid N] (f : M →* N) (hf : function.surjective f) :
  f.mrange = (⊤ : submonoid N) :=
mrange_top_iff_surjective.2 hf

/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive submonoid of elements `x : M` such that `f x = g x`"]
def eq_mlocus (f g : M →* N) : submonoid M :=
{ carrier := {x | f x = g x},
  one_mem' := by rw [set.mem_set_of_eq, f.map_one, g.map_one],
  mul_mem' := λ x y (hx : _ = _) (hy : _ = _), by simp [*] }

/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
@[to_additive]
lemma eq_on_mclosure {f g : M →* N} {s : set M} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_mlocus g, from closure_le.2 h

@[to_additive]
lemma eq_of_eq_on_mtop {f g : M →* N} (h : set.eq_on f g (⊤ : submonoid M)) :
  f = g :=
ext $ λ x, h trivial

@[to_additive]
lemma eq_of_eq_on_mdense {s : set M} (hs : closure s = ⊤) {f g : M →* N} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_mtop $ hs ▸ eq_on_mclosure h

@[to_additive]
lemma mclosure_preimage_le (f : M →* N) (s : set N) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
closure_le.2 $ λ x hx, mem_coe.2 $ mem_comap.2 $ subset_closure hx

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
@[to_additive "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals
the `add_submonoid` generated by the image of the set."]
lemma map_mclosure (f : M →* N) (s : set M) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image _ _)
    (mclosure_preimage_le _ _))
  (closure_le.2 $ set.image_subset _ subset_closure)

end monoid_hom

namespace free_monoid

variables {α : Type*}

open submonoid

@[to_additive]
theorem closure_range_of : closure (set.range $ @of α) = ⊤ :=
eq_top_iff.2 $ λ x hx, free_monoid.rec_on x (one_mem _) $ λ x xs hxs,
  mul_mem _ (subset_closure $ set.mem_range_self _) hxs

end free_monoid

namespace submonoid

variables {N : Type*} [monoid N]

open monoid_hom

/-- The monoid hom associated to an inclusion of submonoids. -/
@[to_additive "The `add_monoid` hom associated to an inclusion of submonoids."]
def inclusion {S T : submonoid M} (h : S ≤ T) : S →* T :=
S.subtype.cod_mrestrict _ (λ x, h x.2)

@[simp, to_additive]
lemma range_subtype (s : submonoid M) : s.subtype.mrange = s :=
ext' $ (coe_mrange _).trans $ set.range_coe_subtype s

lemma closure_singleton_eq (x : M) : closure ({x} : set M) = (powers_hom M x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨multiplicative.of_add 1, trivial, pow_one x⟩) $
  λ x ⟨n, _, hn⟩, hn ▸ pow_mem _ (subset_closure $ set.mem_singleton _) _

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
lemma mem_closure_singleton {x y : M} : y ∈ closure ({x} : set M) ↔ ∃ n:ℕ, x^n=y :=
by rw [closure_singleton_eq, mem_mrange]; refl

@[to_additive]
lemma closure_eq_mrange (s : set M) : closure s = (free_monoid.lift (coe : s → M)).mrange :=
by rw [mrange, ← free_monoid.closure_range_of, map_mclosure,
  ← set.range_comp, free_monoid.lift_comp_of, set.range_coe_subtype]

@[to_additive]
lemma exists_list_of_mem_closure {s : set M} {x : M} (hx : x ∈ closure s) :
  ∃ (l : list M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
begin
  rw [closure_eq_mrange, mem_mrange] at hx,
  rcases hx with ⟨l, hx⟩,
  exact ⟨list.map coe l, λ y hy, let ⟨z, hz, hy⟩ := list.mem_map.1 hy in hy ▸ z.2, hx⟩
end

@[to_additive]
lemma map_inl (s : submonoid M) : s.map (inl M N) = s.prod ⊥ :=
ext $ λ p, ⟨λ ⟨x, hx, hp⟩, hp ▸ ⟨hx, set.mem_singleton 1⟩,
  λ ⟨hps, hp1⟩, ⟨p.1, hps, prod.ext rfl $ (set.eq_of_mem_singleton hp1).symm⟩⟩

@[to_additive]
lemma map_inr (s : submonoid N) : s.map (inr M N) = prod ⊥ s :=
ext $ λ p, ⟨λ ⟨x, hx, hp⟩, hp ▸ ⟨set.mem_singleton 1, hx⟩,
  λ ⟨hp1, hps⟩, ⟨p.2, hps, prod.ext (set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[to_additive]
lemma range_inl : (inl M N).mrange = prod ⊤ ⊥ := map_inl ⊤

@[to_additive]
lemma range_inr : (inr M N).mrange = prod ⊥ ⊤ := map_inr ⊤

@[to_additive]
lemma range_inl' : (inl M N).mrange = comap (snd M N) ⊥ := range_inl.trans (top_prod _)

@[to_additive]
lemma range_inr' : (inr M N).mrange = comap (fst M N) ⊥ := range_inr.trans (prod_top _)

@[simp, to_additive]
lemma range_fst : (fst M N).mrange = ⊤ :=
(fst M N).mrange_top_of_surjective $ @prod.fst_surjective _ _ ⟨1⟩

@[simp, to_additive]
lemma range_snd : (snd M N).mrange = ⊤ :=
(snd M N).mrange_top_of_surjective $ @prod.snd_surjective _ _ ⟨1⟩

@[simp, to_additive prod_bot_sup_bot_prod]
lemma prod_bot_sup_bot_prod (s : submonoid M) (t : submonoid N) :
  (s.prod ⊥) ⊔ (prod ⊥ t) = s.prod t :=
le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) $
assume p hp, prod.fst_mul_snd p ▸ mul_mem _
  ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, set.mem_singleton 1⟩)
  ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨set.mem_singleton 1, hp.2⟩)

@[simp, to_additive]
lemma range_inl_sup_range_inr : (inl M N).mrange ⊔ (inr M N).mrange = ⊤ :=
by simp only [range_inl, range_inr, prod_bot_sup_bot_prod, top_prod_top]

end submonoid

namespace submonoid

variables {N : Type*} [comm_monoid N]

open monoid_hom

@[to_additive]
lemma sup_eq_range (s t : submonoid N) : s ⊔ t = (s.subtype.coprod t.subtype).mrange :=
by rw [mrange, ← range_inl_sup_range_inr, map_sup, map_mrange, coprod_comp_inl,
  map_mrange, coprod_comp_inr, range_subtype, range_subtype]

@[to_additive]
lemma mem_sup {s t : submonoid N} {x : N} :
  x ∈ s ⊔ t ↔ ∃ (y ∈ s) (z ∈ t), y * z = x :=
by simp only [sup_eq_range, mem_mrange, coprod_apply, prod.exists, submonoid.exists,
  coe_subtype, subtype.coe_mk]

end submonoid

namespace add_submonoid

open set

lemma smul_mem (S : add_submonoid A) {x : A} (hx : x ∈ S) :
  ∀ n : ℕ, n •ℕ x ∈ S
| 0     := S.zero_mem
| (n+1) := S.add_mem hx (smul_mem n)

lemma closure_singleton_eq (x : A) : closure ({x} : set A) = (multiples_hom x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨1, trivial, one_nsmul x⟩) $
  λ x ⟨n, _, hn⟩, hn ▸ smul_mem _ (subset_closure $ set.mem_singleton _) _

/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
lemma mem_closure_singleton {x y : A} :
  y ∈ closure ({x} : set A) ↔ ∃ n:ℕ, n •ℕ x = y :=
by rw [closure_singleton_eq, add_monoid_hom.mem_mrange]; refl

end add_submonoid


namespace mul_equiv

variables {S T : submonoid M}

/-- Makes the identity isomorphism from a proof two submonoids of a multiplicative
    monoid are equal. -/
@[to_additive add_submonoid_congr "Makes the identity additive isomorphism from a proof two
submonoids of an additive monoid are equal."]
def submonoid_congr (h : S = T) : S ≃* T :=
{ map_mul' :=  λ _ _, rfl, ..equiv.set_congr $ submonoid.ext'_iff.1 h }

end mul_equiv
