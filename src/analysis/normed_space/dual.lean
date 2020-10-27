/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import analysis.normed_space.hahn_banach
import analysis.normed_space.banach
import analysis.normed_space.inner_product
import analysis.normed_space.operator_norm

/-!
# The topological dual of a normed space

In this file we define the topological dual of a normed space, and the bounded linear map from
a normed space into its double dual.

We also prove that, for base field such as the real or the complex numbers, this map is an isometry.
More generically, this is proved for any field in the class `has_exists_extension_norm_eq`, i.e.,
satisfying the Hahn-Banach theorem.

In the case of inner product spaces, we define `to_dual` which maps an element x of the space
to `λ y, ⟪x, y⟫`. We also give the Fréchet-Riesz representation, which states that every element
of the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`, and define
`to_primal` which gives the corresponding primal vector of an element of the dual. We also prove
that the dual of a Hilbert space is itself a Hilbert space.

## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

noncomputable theory
universes u v

namespace normed_space

section general
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (E : Type*) [normed_group E] [normed_space 𝕜 E]

/-- The topological dual of a normed space `E`. -/
@[derive [has_coe_to_fun, normed_group, normed_space 𝕜]] def dual := E →L[𝕜] 𝕜

instance : inhabited (dual 𝕜 E) := ⟨0⟩

/-- The inclusion of a normed space in its double (topological) dual. -/
def inclusion_in_double_dual' (x : E) : (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ f, f x,
    map_add'    := by simp,
    map_smul'   := by simp }
  ∥x∥
  (λ f, by { rw mul_comm, exact f.le_op_norm x } )

@[simp] lemma dual_def (x : E) (f : dual 𝕜 E) :
  ((inclusion_in_double_dual' 𝕜 E) x) f = f x := rfl

lemma double_dual_bound (x : E) : ∥(inclusion_in_double_dual' 𝕜 E) x∥ ≤ ∥x∥ :=
begin
  apply continuous_linear_map.op_norm_le_bound,
  { simp },
  { intros f, rw mul_comm, exact f.le_op_norm x, }
end

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual : E →L[𝕜] (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ (x : E), (inclusion_in_double_dual' 𝕜 E) x,
    map_add'    := λ x y, by { ext, simp },
    map_smul'   := λ (c : 𝕜) x, by { ext, simp } }
  1
  (λ x, by { convert double_dual_bound _ _ _, simp } )

end general

section bidual_isometry

variables {𝕜 : Type v} [nondiscrete_normed_field 𝕜] [normed_algebra ℝ 𝕜]
[has_exists_extension_norm_eq.{u} 𝕜]
{E : Type u} [normed_group E] [normed_space 𝕜 E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
lemma norm_le_dual_bound (x : E) {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ (f : dual 𝕜 E), ∥f x∥ ≤ M * ∥f∥) :
  ∥x∥ ≤ M :=
begin
  classical,
  by_cases h : x = 0,
  { simp only [h, hMp, norm_zero] },
  { obtain ⟨f, hf⟩ : ∃ g : E →L[𝕜] 𝕜, _ := exists_dual_vector x h,
    calc ∥x∥ = ∥norm' 𝕜 x∥ : (norm_norm' _ _ _).symm
    ... = ∥f x∥ : by rw hf.2
    ... ≤ M * ∥f∥ : hM f
    ... = M : by rw [hf.1, mul_one] }
end

/-- The inclusion of a real normed space in its double dual is an isometry onto its image.-/
lemma inclusion_in_double_dual_isometry (x : E) : ∥inclusion_in_double_dual 𝕜 E x∥ = ∥x∥ :=
begin
  apply le_antisymm,
  { exact double_dual_bound 𝕜 E x },
  { rw continuous_linear_map.norm_def,
    apply real.lb_le_Inf _ continuous_linear_map.bounds_nonempty,
    rintros c ⟨hc1, hc2⟩,
    exact norm_le_dual_bound x hc1 hc2 },
end

end bidual_isometry

end normed_space

namespace inner_product_space
open is_R_or_C continuous_linear_map

variables (𝕜 : Type*)
variables {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
variables {F : Type*} [inner_product_space ℝ F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local postfix `†`:90 := @is_R_or_C.conj 𝕜 _

/--
Given some x in an inner product space, we can define its dual as the continuous linear map
λ y, ⟪x, y⟫.
-/
def to_dual' (x : E) : normed_space.dual 𝕜 E :=
linear_map.mk_continuous
  { to_fun := λ y, ⟪x, y⟫,
    map_add' := λ _ _, inner_add_right,
    map_smul' := λ _ _, inner_smul_right }
  ∥x∥
  (λ y, by { rw [is_R_or_C.norm_eq_abs], exact abs_inner_le_norm _ _ })

@[simp] lemma to_dual'_def {x y : E} : to_dual' 𝕜 x y = ⟪x, y⟫ := rfl

variables {𝕜}

/-- The inner product can be written as an application of the dual of the first argument. -/
lemma inner_eq_to_dual'_apply {x y : E} : ⟪x, y⟫ = (to_dual' 𝕜 x) y :=
by simp only [to_dual'_def]

def to_dual'' : F →L[ℝ] (normed_space.dual ℝ F) :=
linear_map.mk_continuous
  { to_fun := λ x, to_dual' ℝ x,
    map_add' := λ x y, by { ext, simp [inner_add_left] },
    map_smul' := λ c x, by { ext, simp [inner_smul_left] } }
  1
  begin
    intros x,
    apply op_norm_le_bound,
    { simp [norm_nonneg] },
    { intros y,
      simp only [one_mul, linear_map.coe_mk, to_dual'_def, norm_eq_abs, abs_inner_le_norm] }
  end

variables [complete_space F]

/--
Fréchet-Riesz representation: any ℓ in the dual of a real Hilbert space F is of the form
λ u, ⟪y, u⟫ for some y in F.
-/
-- TODO extend to `is_R_or_C` (requires a definition of conjugate linear maps)
lemma exists_elem_of_mem_dual : (@to_dual'' F _).range = ⊤ :=
begin
  apply (@linear_map.range_eq_top ℝ F _ _ _ _ _ _ (@to_dual'' F _).to_linear_map).mpr,
  intros ℓ,
  set Y := ker ℓ with hY,
  by_cases htriv : Y = ⊤,
  { have hℓ : ℓ = 0,
    { have h' := linear_map.ker_eq_top.mp htriv,
      rw [←coe_zero] at h',
      apply coe_injective,
      exact h' },
    exact ⟨0, by simp [hℓ]⟩ },
  { have Ycomplete := is_complete_ker ℓ,
    rw [submodule.eq_top_iff_orthogonal_eq_bot Ycomplete, ←hY] at htriv,
    change Y.orthogonal ≠ ⊥ at htriv,
    rw [submodule.ne_bot_iff] at htriv,
    obtain ⟨z : F, hz : z ∈ Y.orthogonal, z_ne_0 : z ≠ 0⟩ := htriv,
    refine ⟨((ℓ z) / ⟪z, z⟫_ℝ) • z, _⟩,
    ext x,
    have h₁ : (ℓ z) • x - (ℓ x) • z ∈ Y,
    { rw [mem_ker, map_sub, map_smul, map_smul, algebra.id.smul_eq_mul, algebra.id.smul_eq_mul,
          mul_comm],
      exact sub_self (ℓ x * ℓ z) },
    have h₂ : (ℓ z) * ⟪z, x⟫_ℝ = (ℓ x) * ⟪z, z⟫_ℝ,
    { have h₃ := calc
        0    = ⟪z, (ℓ z) • x - (ℓ x) • z⟫_ℝ       :
                  by { rw [(Y.mem_orthogonal' z).mp hz], exact h₁ }
         ... = ⟪z, (ℓ z) • x⟫_ℝ - ⟪z, (ℓ x) • z⟫_ℝ  : by rw [inner_sub_right]
         ... = (ℓ z) * ⟪z, x⟫_ℝ - (ℓ x) * ⟪z, z⟫_ℝ  : by simp [inner_smul_right],
      exact sub_eq_zero.mp (eq.symm h₃) },
    have h₄ := calc
      ⟪((ℓ z) / ⟪z, z⟫_ℝ) • z, x⟫_ℝ = (ℓ z) / ⟪z, z⟫_ℝ * ⟪z, x⟫_ℝ
            : by simp [inner_smul_left, conj_div, conj_conj]
                            ... = (ℓ z) * ⟪z, x⟫_ℝ / ⟪z, z⟫_ℝ
            : by rw [←div_mul_eq_mul_div]
                            ... = (ℓ x) * ⟪z, z⟫_ℝ / ⟪z, z⟫_ℝ
            : by rw [h₂]
                            ... = ℓ x
            : begin
                have : ⟪z, z⟫_ℝ ≠ 0,
                { change z = 0 → false at z_ne_0,
                  rwa ←inner_self_eq_zero at z_ne_0 },
                field_simp [this]
              end,
    exact h₄ }
end

lemma to_dual''_isometry (x : F) :
  ∥to_dual'' x∥ = ∥x∥ :=
begin
  refine le_antisymm _ _,
  { change ∥to_dual'' x∥ ≤ ∥x∥,
    simp only [to_dual''],
    exact linear_map.mk_continuous_norm_le _ (norm_nonneg _) _ },
  { cases eq_or_lt_of_le (norm_nonneg x),
    { have : x = 0 := norm_eq_zero.mp (eq.symm h),
      simp [this] },
    { refine (mul_le_mul_right h).mp _,
      calc ∥x∥ * ∥x∥ = ∥x∥ ^2 : by ring
      ... = ⟪x, x⟫_ℝ : norm_sq_eq_inner _
      ... ≤ ∥to_dual'' x x∥ : le_abs_self _
      ... ≤ ∥to_dual'' x∥ * ∥x∥ : le_op_norm (to_dual'' x) x } }
end

lemma to_dual''_injective : (@to_dual'' F _).ker = ⊥ :=
begin
  rw eq_bot_iff,
  intros x hx,
  have : ∥x∥ = 0,
  { rw ← to_dual''_isometry,
    simpa using hx },
  simpa using this
end

/-- If `F` is a Hilbert space, the function that takes a vector in the conjugate
vector space of `F` to its dual is a continuous linear equivalence.  -/
def to_dual : F ≃L[ℝ] (normed_space.dual ℝ F) :=
continuous_linear_equiv.of_homothety
  ℝ
  (linear_equiv.of_bijective
    (@to_dual'' F _).to_linear_map
    (@to_dual''_injective F _ _)
    (@exists_elem_of_mem_dual F _ _))
  1
  (by norm_num)
  (λ x, by { convert to_dual''_isometry x, simp })

@[simp] lemma to_dual_apply {x y : F} : to_dual x y = ⟪x, y⟫_ℝ := rfl

@[simp] lemma to_dual_eq_iff_eq {x y : F} : to_dual x = to_dual y ↔ x = y :=
(@to_dual F _ _).injective.eq_iff

/-- In a Hilbert space, the norm of the dual of a vector x is `∥x∥` -/
@[simp] lemma to_dual_norm_eq_primal_norm (x : F) : ∥to_dual x∥ = ∥x∥ :=
to_dual''_isometry x

/-- In a Hilbert space, the norm of a vector in the dual space is the norm of its corresponding
primal vector. -/
lemma dual_norm_eq_primal_norm (ℓ : normed_space.dual ℝ F) :
  ∥ℓ∥ = ∥to_dual.symm ℓ∥ :=
by { convert to_dual_norm_eq_primal_norm (to_dual.symm ℓ), simp }

end inner_product_space
