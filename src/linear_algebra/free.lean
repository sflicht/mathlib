import linear_algebra.basic 
       linear_algebra.direct_sum_module 
       linear_algebra.tensor_product
       linear_algebra.basis 
       linear_algebra.finsupp_vector_space
       algebra.category.Module.basic
       ring_theory.noetherian
       data.finsupp
       tactic

noncomputable theory
open_locale classical
universes u v w
variables (R : Type u) [comm_ring R]
variables (ι : Type*) 

namespace module

def free := ι →₀ R
instance : has_coe_to_fun (free R ι) := finsupp.has_coe_to_fun

-- FIXME: this belongs elsewhere (where?)
variables (M N : Type v)
variables [add_comm_group M] [module R M] [add_comm_group N] [module R N]
abbreviation Hom  := M →ₗ[R] N

end module 

-- by defining M^⊕ι as M ⊗[R] R^⊕ι, all the compatibilities between
-- ι →₀ M and direct_sum ι (λ _:ι, M) should in principle follow from 
-- the case of free modules
notation R ` ^⊕ `:40 ι:66  := module.free R ι 
 

namespace free

instance : add_comm_group (R^⊕ι)  := finsupp.add_comm_group
example (x y : R^⊕ι ) : R^⊕ι := x + y
example (x y : ι →₀ R) : ι →₀ R := x + y
instance : module R (R^⊕ι) := {..@finsupp.module ι R R _ _ _}
example (x : R^⊕ι) (r : R) : R^⊕ι := r • x
example (x : ι →₀ R) (r : R) : ι →₀ R := r • x

end free

namespace module

def is_free (M : Type*) [add_comm_group M] [module R M] := ∃ (ι : Type*), nonempty ((R^⊕ι) ≃ₗ[R] M)

end module

namespace free

lemma equiv_of_bijection {μ : Type*} (h : ι ≃ μ) : R^⊕ι ≃ₗ[R] R^⊕μ :=
{ to_fun := finsupp.map_domain h.to_fun,
  add := λ x y, finsupp.map_domain_add,
  smul := finsupp.map_domain_smul,
  inv_fun := λ x, finsupp.comap_domain h.to_fun x (by tidy),
  left_inv := λ x, begin ext, simp only [finsupp.comap_domain_apply], 
                apply finsupp.map_domain_apply, from equiv.injective h end,
  right_inv := λ x, finsupp.map_domain_comap_domain h.to_fun x (by tidy) 
              (by {have := equiv.surjective h, tauto})}

open module 
-- two special cases of free modules are important for the 
-- monoidal and abelian structures on the category Module R

abbreviation one := R ^⊕ unit -- unit for the closed monoidal structure
abbreviation zero := R ^⊕ empty -- empty biproduct, the terminal/initial object

/- variables (M : Type*)
variables [add_comm_group M] [module R M]
 -/

variables {R}
-- outside of this namespace, can write "free.of_rank 42" etc
abbreviation of_rank (n : ℕ):= R^⊕(fin n)
variables {n : ℕ}
example (x y : @of_rank R _ n) : of_rank n := x + y
example (x : @of_rank R _ n) (r : R) : @of_rank R _ n := r • x

/- 
notation R ` ^⊔ `:40 n:66 := of_rank n 
variables {R n}
instance of_rank.add_comm_group : add_comm_group (R ^⊔ n) := 

example (x y : R ^⊔ (1:ℕ)) : R ^⊔ 1 := x + y
 -/

@[simp] lemma equiv_of_rank_card [fintype ι]: R^⊕ι ≃ₗ[R] (@of_rank R _ (fintype.card ι)) :=
free.equiv_of_bijection _ _ $ trunc.out $ fintype.equiv_fin ι 
@[simp] lemma one_equiv_of_rank_one   : one R  ≃ₗ[R] (@of_rank R _ 1) := @equiv_of_rank_card R _ unit _
@[simp] lemma zero_equiv_of_rank_zero : zero R ≃ₗ[R] (@of_rank R _ 0) := @equiv_of_rank_card R _ empty _

variables (R)
-- FIXME what's a less verbose form of this?
@[simp] lemma zero.equiv : zero R ≃ₗ[R] punit := { to_fun := λ _, punit.star,
  add := by tidy,
  smul := by tidy,
  inv_fun := begin intro, fconstructor, use ∅, tidy, end,
  left_inv := by tidy,
  right_inv := by tidy}

def one.unit : one R := finsupp.single unit.star (1:R)

@[simp] def one_equiv.to_fun  : one R → R := λ f, f unit.star
@[simp] def one_equiv.inv_fun : R → one R := λ r, r • one.unit R
@[simp] lemma one.equiv : one R ≃ₗ[R] R := { to_fun := one_equiv.to_fun R,
  add := by tidy,
  smul := by tidy,
  inv_fun := one_equiv.inv_fun R,
  left_inv := begin intro f, ext, simp only [finsupp.smul_apply, algebra.id.smul_eq_mul, one_equiv.inv_fun, one_equiv.to_fun], rw one.unit, tidy end,
  right_inv := begin intro r, simp only [finsupp.smul_apply, algebra.id.smul_eq_mul, one_equiv.inv_fun, one_equiv.to_fun], rw one.unit, tidy end}

def corepr_id.to_fun (M : Type*) [add_comm_group M] [module R M] (m : M) :
    module.Hom R (one R) M := { to_fun := λ f, (f unit.star) • m,
  add := begin intros, simp only [finsupp.add_apply], apply add_smul end,
  smul := begin intros, simp only [finsupp.smul_apply], apply mul_smul end }
def corepr_id.inv_fun 
    (M : Type*) [add_comm_group M] [module R M] 
    (T : module.Hom R (one R) M) : M := T (one.unit R)

-- natural transformation from the identity functor on Module R
-- to the functor (internally) co-represented by one R
-- This is part of the monoidal structure on Module R
def corepr_id (M : Type*) [add_comm_group M] [module R M] : M ≃ₗ[R] module.Hom R (one R) M := { to_fun := corepr_id.to_fun R M,
  add := begin intros x y, repeat {rw corepr_id.to_fun}, suffices : ∀ (f : R^⊕unit), 
    f () • (x + y) = f() • x + f() • y, finish, intro f, rw smul_add end,
  smul := begin intros r x, repeat {rw corepr_id.to_fun}, suffices : ∀ (f : R^⊕unit), 
    f () • (r • x) = r • f() • x, finish, intro f, rw [smul_smul, mul_comm, smul_smul]  end,
  inv_fun := corepr_id.inv_fun R M,
  left_inv := begin intro x, rw [corepr_id.inv_fun, corepr_id.to_fun],
        suffices : (one.unit R) () • x = x, tauto, rw one.unit, simp end,
  right_inv := begin intro T, rw [corepr_id.to_fun, corepr_id.inv_fun], ext f,
        suffices : f () • T.to_fun (one.unit R) = T.to_fun f, finish,
        rw ← T.smul (f ()) (one.unit R), congr, rw one.unit, ext,
        simp only [mul_one, algebra.id.smul_eq_mul, finsupp.smul_single], 
        rw finsupp.single_apply, split_ifs with h, rw h, finish end}

variables {R ι}

-------------------------------------------------------------------------
---       Canonical maps  R →ₗ[R] R^⊕ι →ₗ[R] R
---
-- the projection to the i'th factor is component i
abbreviation lapply    : Π (i:ι), R^⊕ι →ₗ[R] R := finsupp.lapply
abbreviation component : Π (i:ι), R^⊕ι →ₗ[R] R := finsupp.lapply
-- FIXME should "component" be called "lproj"

-- the inclusion supported on the i'th summand is lof i
abbreviation lsingle    : ι → R →ₗ[R]  R^⊕ι := finsupp.lsingle
abbreviation lof        : ι → R →ₗ[R]  R^⊕ι := finsupp.lsingle 
-- FIXME should "lof" bee called "linclude"

-- we keep the component and lof synonyms because they are used in the
-- general case of dependent direct sums

--  compatibilities
@[simp] lemma component.lof_self (i : ι) (r : R) : component i (lof i r) = r 
    := by {simp}

lemma component.lof (i j : ι) (r : R) :
    component i (lof j r : R^⊕ι) = finsupp.single j r i := by {simp}

-- the analogue of finsupp.sum_single
lemma sum_comp (x : R^⊕ι) : x.support.sum(λ i:ι, lof i (component i x)) = x :=
begin simp only [finsupp.lapply_apply, finsupp.lsingle_apply],
rw ← finsupp.sum, simp end

--------------------------------------------------------------------------
--         Universal property of free modules
--
-- lift a family of elements of an aribtrary R-module M
-- to a map from the corresponding free module to M
def lift₀ {M : Type*} [add_comm_group M] [module R M] :
    (ι → M) → R^⊕ι →ₗ[R] M := λ m : ι → M, { 
    to_fun := λ f, f.sum (λ i r, r • m i),
    add := λ x y, @finsupp.sum_add_index ι R M _ _ x y (λ i r, r • m i) (by simp) 
                    (by {intros, simp, rw add_smul}),
    smul := begin intros r x, rw finsupp.smul_sum, 
        have := @finsupp.sum_smul_index ι R M _ _ x r (λ i r, r • m i) (by simp),
        simp only [] at this, 
        rw [this, finsupp.sum, finsupp.sum, finset.sum_congr rfl],
        intros i _, rw mul_smul end }

-- this is indeed a lift (relative to the inclusions lsingle i : R →ₗ[R] R^⊕ι)
-- in the sense that (lift₀ m) ∘ (lsingle i) : R → M is r ↦ r • m i
@[simp] lemma lift₀_lsingle {M : Type*} [add_comm_group M] [module R M]
    {m : ι → M} {i : ι} {r : R} : (lift₀ m) (lsingle i r) = r • m i :=
begin
rw lift₀, simp only [linear_map.coe_mk, finsupp.lsingle_apply], 
apply finsupp.sum_single_index, simp
end

-- can also (via canonical identifications) treat this as lifting
-- a family of maps ι → R →ₗ[R] M
def lift {M : Type*} [add_comm_group M] [module R M] :
    (ι → one R →ₗ[R] M) → R^⊕ι →ₗ[R] M := λ T : ι → one R →ₗ[R] M, 
    lift₀ (λ i, (corepr_id R M).symm.1 (T i))

-- this is indeed a lift (relative to the inclusions lsingle i : R →ₗ[R] R^⊕ι)
-- in the sense that (lift T).comp (lsingle i) = T i in module.Hom R M
@[simp] lemma lift_lsingle {M : Type*} [add_comm_group M] [module R M] 
  {T : ι → one R →ₗ[R] M} {i : ι} {r : R} : 
  (lift T).comp (lsingle i) r = (T i) (one_equiv.inv_fun R r) :=
begin
rw lift, simp only [finsupp.lsingle_apply, linear_map.comp_apply],
have : finsupp.single i r = lsingle i r := rfl, 
rw [this, lift₀_lsingle],
replace this : T i (one_equiv.inv_fun R r) = r • T i (one_equiv.inv_fun R 1), 
    {replace this : 
        T i (one_equiv.inv_fun R r)= T i (r • (one_equiv.inv_fun R 1)), {simp},
     {rw this, from linear_map.smul (T i) r (one_equiv.inv_fun R 1)}},
rw this, congr, rw corepr_id, 
suffices : corepr_id.inv_fun R M (T i)= T i (one_equiv.inv_fun R 1), {tauto},
rw corepr_id.inv_fun, congr, rw one_equiv.inv_fun, simp end

-----------------------------------------------------------------------
--        Isomorphism between R^⊕ι [defined in terms of finsupp]
--        and direct_sum ι (λ _:ι, R)  [defined in terms of dfinsupp]
--
-- FIXME:
-- It seems nice to have an API for the isomorphism  R^⊕ι ≃ₗ[R] direct_sum ι (λ _:ι, R)
-- However, I think it's really painful to actually use this isomorphism in practice
-- So maybe the API should only assert that one exists?


-- this is ugly... but seems much MUCH easier than trying to invoke the
-- universal mapping properties on both the finsupp and dfinsupp sides!
private def to_dfinsupp :  R^⊕ι → direct_sum ι (λ _:ι, R) :=
    λ x, @dfinsupp.mk ι (λ _:ι, R) _ _ x.support (λ i, x i)
private def of_dfinsupp : direct_sum ι (λ _:ι, R) → R^⊕ι :=
    λ x, { support := x.support,
  to_fun := λ i, x i,
  mem_support_to_fun := dfinsupp.mem_support_iff x }

-- FIXME: For this isomorphism to be sufficient for all downstream needs
-- (meaning users of free modules never need to worry about dfinsupp at all!),
-- we may need to show (from the definitions of to_dfinsupp and of_dfinsupp)
-- that it is functorial in R, i.e. it's an isomorphism of functors on CommRing
-- between direct_sum ι (λ _:ι, • ) and ( • )^⊕ι
@[simp] lemma direct_sum_equiv :  direct_sum ι (λ _:ι, R) ≃ₗ[R] R^⊕ι  := { 
    to_fun := of_dfinsupp,
    add := begin intros x y, ext, rw of_dfinsupp, 
          simp only [dfinsupp.add_apply, finsupp.add_apply], tauto end,
    smul := begin intros r x, ext, rw of_dfinsupp, 
          simp only [finsupp.smul_apply, algebra.id.smul_eq_mul, dfinsupp.smul_apply],
          tauto end,
    inv_fun := to_dfinsupp,
    left_inv := begin intro x, ext i, by_cases h : i ∈ x.support, 
         {rw [to_dfinsupp, of_dfinsupp], 
         simp only [dfinsupp.mk_apply, subtype.coe_mk], split_ifs with h', tauto,
         exfalso, tauto},
        {rw to_dfinsupp, simp only [dfinsupp.mk_apply, subtype.coe_mk],
          have : i ∉ (of_dfinsupp x).support, 
            {simp only [finsupp.mem_support_iff, dfinsupp.mem_support_to_fun, classical.not_not] at *, 
             rw of_dfinsupp, suffices : x i = 0, tauto, from h},
          split_ifs, simp only [finsupp.mem_support_iff, dfinsupp.mem_support_to_fun, classical.not_not] at *, 
          from h.symm} end,
    right_inv := begin intro x, ext i, rw of_dfinsupp, simp only [], 
          suffices : (to_dfinsupp x) i = x i, tauto,
          rw to_dfinsupp, simp only [dfinsupp.mk_apply, subtype.coe_mk], 
          split_ifs, refl,
          simp only [finsupp.mem_support_iff, classical.not_not] at h, 
          from h.symm end }
--
-------------------------------------------------------------------

-------------------------------------------------------------------
--          extensionality
@[ext] lemma ext {f g : R^⊕ι}
  (h : ∀ i, component i f = component i g) : f = g := by {ext i, from h i}

lemma ext_iff {f g : R^⊕ι} : f = g ↔
  ∀ i, component i f = component i g := ⟨by {tauto}, ext⟩ 
-------------------------------------------------------------------

-------------------------------------------------------------------
---        The standard basis for R^⊕ι
---
def std_basis (i:ι) := lof i (1:R)

-- FIXME : experts advise me that users should always use lof = lsingle
-- instead of std_basis, so these should be unnecessary
-- kronecker delta on ι with values in R
@[simp] def δ (i j : ι) : R := ite (j = i) (1:R) 0
@[simp] lemma component.std_basis (i j : ι) :
 (component i) (std_basis j : R^⊕ι) = δ i j := sorry


 -- instead we translate finsupp.{l}single_apply into std_basis language
@[simp] lemma std_basis_apply (i j : ι) (r : R) :
 r * (std_basis j) i = ite (j = i) r 0 :=
 begin
 rw [std_basis, finsupp.lsingle_apply, finsupp.single_apply], finish, 
 end

-- presumably instead of proving this directly, we could remove the [field K]
-- hypothesis from finsupp.is_basis_single and apply that 
-- FIXME: that's probably worth doing anyway...
lemma is_basis_std_basis : @is_basis ι R (R^⊕ι) std_basis _ _ _ :=
begin
rw is_basis, split, 
-- linear independence
{
  rw linear_independent_iff, intros l h, rw ext_iff at h, ext i, 
  replace h := h i,  simp only [finsupp.lapply_apply, finsupp.zero_apply] at *,
  rw finsupp.total_apply R l at h,
  simp only [finsupp.smul_apply, algebra.id.smul_eq_mul, finsupp.sum_apply] at h, 
  rw finsupp.sum at h,  
  rw @finset.sum_congr ι R l.support _ 
    (λ a, l a * (std_basis a) i) 
    (λ a, finsupp.single a (l a) i) _ rfl
    begin intros j _, simp only [], rw [std_basis_apply, finsupp.single_apply] end
  at h,
  have : finsupp.sum l (λ j r, finsupp.single j r i) = l.support.sum (λ a :ι, finsupp.single a (l a) i) := rfl, 
  rw [← this, ← finsupp.sum_apply, finsupp.sum_single] at h, exact h
}, 
-- span
{
  rw submodule.span, simp only [Inf_eq_top, set.mem_set_of_eq] at *, intros,
  ext1, split, tauto, intros hx, cases hx, 
  replace H : ∀ (i:ι), std_basis i ∈ a := by 
        {intro, apply H, fconstructor, from i, refl},
  apply finsupp.induction x,
    {finish},
    {intros i r y hy hr ha, have Hi := H i, 
    suffices : finsupp.single i r ∈ a, {exact submodule.add_mem a this ha},
    suffices : finsupp.single i r = r • std_basis i, {rw this, apply submodule.smul_mem, from Hi},
    rw std_basis, ext j, simp}
} 
end
--
-------------------------------------------

---------------------------------------------------------
-- Given a finitely generated module M, produce an augmentation
--      R^⊕(fin n) →ₗ[R] M → 0
lemma surj_of_fg {M : Type v}[add_comm_group M][module R M]
    (hfg : (⊤ : submodule R M).fg) :
    ∃(ι : Type v) [fintype ι], ∃ (π : R^⊕ι →ₗ[R] M), function.surjective π  :=
begin
  cases hfg with s hs,
  let ι := {m : M // m ∈ s},
  let π₀ : ι → M := λ i, i,
  let π  : R^⊕ι →ₗ[R] M := lift₀ π₀,
  refine ⟨ι, infer_instance, π, _⟩,
  intro m,
  have hm : m ∈ submodule.span R (subtype.val '' (set.univ : set ι)),
  { simp [hs] },
  rw finsupp.mem_span_iff_total at hm,
  rcases hm with ⟨l, hl, hlm⟩,
  refine ⟨l, _⟩,
  rw ← hlm, 
  rw finsupp.total_apply,
  apply finset.sum_congr rfl,
  intros i hi, refl
end
-- FIXME: If R is noetherian, produce a finite presentation 
-- R^⊕(fin m) →ₗ[R] R^⊕(fin n) →ₗ[R] M → 0
-- for a f.g. module M
-- (so f.g. modules are coherent and thus Moduleᶠ R is an abelian category)

end free
namespace tensor_product

open module
#check is_free 
open_locale tensor_product
variables {M N: Type w}
variables [add_comm_group M] [module R M] [add_comm_group N] [module R N] 
variables {R}
lemma is_free_of_free_factors (hm :is_free R M) (hn : is_free R N) :
 is_free R (M ⊗[R] N) :=
begin
cases hm with μ hμ,
cases hn with ν hν,
cases hμ, cases hν,
rw is_free, -- use μ × ν, (fails for universe reasons?!)
sorry 
end

/- 
variables (M : Type v)
variables [add_comm_group M] [module R M] 
variables {R}
-- doesn't work for some reason:
notation M ` ^⊕ `:40 ι:66   := M ⊗[R] R^⊕ι 
 -/

-- FIXME : we need to add notation ⨁ (i:ι), M i for the (dependent) direct_sum ι M
-- FIXME: tensor_prod.direct_sum establishes 
-- ⨁ ι₁ M₁ ⊗[R] ⨁ ι₂ M₂ ≃ₗ[R] 
--    ⨁ (ι₁ × ι₂) (λ i, M₁ i.1 ⊗[R] M₂ i.2)
-- (this is related to the external tensor product on (Module R)^Set = { category of indexed families of module R instancers } = collections consisting of the data
-- variables (ι : Type v) [decidable_eq ι] (M : ι → Type w)
-- variables [Π i, add_comm_group (M i)] [Π i, module R (M i)])

-- see https://ncatlab.org/nlab/show/indexed+monoidal+category

-- we need some corresponding canonical isos for arbitrary ⊗s of free/non-dependent ⨁s 
-- and dependent ⨁s (in any order)

end tensor_product


