/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import ring_theory.ideal.over
import ring_theory.jacobson_ideal
import ring_theory.localization

/-!
# Jacobson Rings

The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its jacobson radical

Any ring satisfying any of these equivalent conditions is said to be Jacobson.

Some particular examples of Jacobson rings are also proven.
`is_jacobson_quotient` says that the quotient of a Jacobson ring is Jacobson.
`is_jacobson_localization` says the localization of a Jacobson ring to a single element is Jacobson.

## Main definitions

Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions

* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements

* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.

* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.

* `is_jacobson_of_surjective` says that if `R` is a Jacobson ring and `f : R →+* S` is surjective,
  then `S` is also a Jacobson ring

## Tags

Jacobson, Jacobson Ring

-/

universes u v

namespace ideal
variables {R : Type u} [comm_ring R] {I : ideal R}
variables {S : Type v} [comm_ring S]

section is_jacobson

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `is_jacobson_iff_prime_eq` and `is_jacobson_iff_Inf_maximal` for equivalent definitions. -/
@[class] def is_jacobson (R : Type u) [comm_ring R] :=
    ∀ (I : ideal R), I.radical = I → I.jacobson = I

/--  A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
lemma is_jacobson_iff_prime_eq : is_jacobson R ↔ ∀ P : ideal R, is_prime P → P.jacobson = P :=
begin
  split,
  { exact λ h I hI, h I (is_prime.radical hI) },
  { refine λ h I hI, le_antisymm (λ x hx, _) (λ x hx, mem_Inf.mpr (λ _ hJ, hJ.left hx)),
    erw mem_Inf at hx,
    rw [← hI, radical_eq_Inf I, mem_Inf],
    intros P hP,
    rw set.mem_set_of_eq at hP,
    erw [← h P hP.right, mem_Inf],
    exact λ J hJ, hx ⟨le_trans hP.left hJ.left, hJ.right⟩ }
end

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals.
 Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
lemma is_jacobson_iff_Inf_maximal : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M : set (ideal R), (∀ J ∈ M, is_maximal J ∨ J = ⊤) ∧ I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal.1 (H _ (is_prime.radical h)),
  λ H , is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal.2 (H hP))⟩

lemma is_jacobson_iff_Inf_maximal' : is_jacobson R ↔
  ∀ {I : ideal R}, I.is_prime → ∃ M : set (ideal R), (∀ (J ∈ M) (K : ideal R), J < K → K = ⊤) ∧ I = Inf M :=
⟨λ H I h, eq_jacobson_iff_Inf_maximal'.1 (H _ (is_prime.radical h)),
  λ H , is_jacobson_iff_prime_eq.2 (λ P hP, eq_jacobson_iff_Inf_maximal'.2 (H hP))⟩

lemma radical_eq_jacobson (H : is_jacobson R) (I : ideal R) : I.radical = I.jacobson :=
le_antisymm (le_Inf (λ J ⟨hJ, hJ_max⟩, (is_prime.radical_le_iff hJ_max.is_prime).mpr hJ))
            ((H I.radical (radical_idem I)) ▸ (jacobson_mono le_radical))

/-- Fields have only two ideals, and the condition holds for both of them -/
@[priority 100]
instance is_jacobson_field {K : Type u} [field K] : is_jacobson K :=
λ I hI, or.rec_on (eq_bot_or_top I)
(λ h, le_antisymm
  (Inf_le ⟨le_of_eq rfl, (eq.symm h) ▸ bot_is_maximal⟩)
  ((eq.symm h) ▸ bot_le))
(λ h, by rw [h, jacobson_eq_top_iff])

theorem is_jacobson_of_surjective [H : is_jacobson R] :
  (∃ (f : R →+* S), function.surjective f) → is_jacobson S :=
begin
  rintros ⟨f, hf⟩,
  rw is_jacobson_iff_Inf_maximal,
  intros p hp,
  use map f '' {J : ideal R | comap f p ≤ J ∧ J.is_maximal },
  use λ j ⟨J, hJ, hmap⟩, hmap ▸ or.symm (map_eq_top_or_is_maximal_of_surjective f hf hJ.right),
  have : p = map f ((comap f p).jacobson),
  from (H (comap f p) (by rw [← comap_radical, is_prime.radical hp])).symm
    ▸ (map_comap_of_surjective f hf p).symm,
  exact eq.trans this (map_Inf hf (λ J ⟨hJ, _⟩, le_trans (ideal.ker_le_comap f) hJ)),
end

@[priority 100]
instance is_jacobson_quotient [is_jacobson R] : is_jacobson (quotient I) :=
is_jacobson_of_surjective ⟨quotient.mk I, (by rintro ⟨x⟩; use x; refl)⟩

lemma is_jacobson_iso (e : R ≃+* S) : is_jacobson R ↔ is_jacobson S :=
⟨λ h, @is_jacobson_of_surjective _ _ _ _ h ⟨(e : R →+* S), e.surjective⟩,
  λ h, @is_jacobson_of_surjective _ _ _ _ h ⟨(e.symm : S →+* R), e.symm.surjective⟩⟩

lemma is_jacobson_of_is_integral [algebra R S] (hRS : algebra.is_integral R S)
  (hR : is_jacobson R) : is_jacobson S :=
begin
  rw is_jacobson_iff_prime_eq,
  introsI P hP,
  by_cases hP_top : comap (algebra_map R S) P = ⊤,
  { simp [comap_eq_top_iff.1 hP_top] },
  { haveI : nontrivial (comap (algebra_map R S) P).quotient := quotient.nontrivial hP_top,
    rw jacobson_eq_iff_jacobson_quotient_eq_bot,
    refine eq_bot_of_comap_eq_bot (is_integral_quotient_of_is_integral hRS) _,
    rw [eq_bot_iff, ← jacobson_eq_iff_jacobson_quotient_eq_bot.1 ((is_jacobson_iff_prime_eq.1 hR)
      (comap (algebra_map R S) P) (comap_is_prime _ _)), comap_jacobson],
    refine Inf_le_Inf (λ J hJ, _),
    simp only [true_and, set.mem_image, bot_le, set.mem_set_of_eq],
    haveI : J.is_maximal := by simpa using hJ,
    exact exists_ideal_over_maximal_of_is_integral (is_integral_quotient_of_is_integral hRS) J
      (comap_bot_le_of_injective _ algebra_map_quotient_injective) }
end

lemma is_jacobson_of_is_integral' (f : R →+* S) (hf : f.is_integral)
  (hR : is_jacobson R) : is_jacobson S :=
@is_jacobson_of_is_integral _ _ _ _ f.to_algebra hf hR

end is_jacobson


section localization
open localization_map
variables {y : R} (f : away_map y S)

lemma disjoint_powers_iff_not_mem {I : ideal R} (hI : I.radical = I) :
  disjoint ((submonoid.powers y) : set R) ↑I ↔ y ∉ I.1 :=
begin
  refine ⟨λ h, set.disjoint_left.1 h (submonoid.mem_powers _), λ h, _⟩,
  rw [disjoint_iff, eq_bot_iff],
  rintros x ⟨hx, hx'⟩,
  obtain ⟨n, hn⟩ := hx,
  rw [← hn, ← hI] at hx',
  exact absurd (hI ▸ mem_radical_of_pow_mem hx' : y ∈ I.carrier) h
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_rel_iso_of_maximal` for the more general relation isomorphism -/
lemma is_maximal_iff_is_maximal_disjoint [H : is_jacobson R] (J : ideal S) :
  J.is_maximal ↔ (comap f.to_map J).is_maximal ∧ y ∉ ideal.comap f.to_map J :=
begin
  split,
  { refine λ h, ⟨_, λ hy, h.1 (ideal.eq_top_of_is_unit_mem _ hy
      (map_units f ⟨y, submonoid.mem_powers _⟩))⟩,
    have hJ : J.is_prime := is_maximal.is_prime h,
    rw is_prime_iff_is_prime_disjoint f at hJ,
    have : y ∉ (comap f.to_map J).1 :=
      set.disjoint_left.1 hJ.right (submonoid.mem_powers _),
    erw [← H (comap f.to_map J) (is_prime.radical hJ.left), mem_Inf] at this,
    push_neg at this,
    rcases this with ⟨I, hI, hI'⟩,
    convert hI.right,
    by_cases hJ : J = map f.to_map I,
    { rw [hJ, comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI.right)],
      rwa disjoint_powers_iff_not_mem (is_maximal.is_prime hI.right).radical},
    { have hI_p : (map f.to_map I).is_prime,
      { refine is_prime_of_is_prime_disjoint f I hI.right.is_prime _,
        rwa disjoint_powers_iff_not_mem (is_maximal.is_prime hI.right).radical },
      have : J ≤ map f.to_map I := (map_comap f J) ▸ (map_mono hI.left),
      exact absurd (h.right _ (lt_of_le_of_ne this hJ)) hI_p.left } },
  { refine λ h, ⟨λ hJ, h.left.left (eq_top_iff.2 _), λ I hI, _⟩,
    { rwa [eq_top_iff, (order_embedding f).map_rel_iff] at hJ },
    { have := congr_arg (map f.to_map) (h.left.right _ ⟨comap_mono (le_of_lt hI), _⟩),
      rwa [map_comap f I, map_top f.to_map] at this,
      refine λ hI', hI.right _,
      rw [← map_comap f I, ← map_comap f J],
      exact map_mono hI' } }
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_rel_iso_of_maximal` for the more general statement, and the reverse of this implication -/
lemma is_maximal_of_is_maximal_disjoint [is_jacobson R] (I : ideal R) (hI : I.is_maximal)
  (hy : y ∉ I) : (map f.to_map I).is_maximal :=
begin
  rw [is_maximal_iff_is_maximal_disjoint f,
    comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI)
    ((disjoint_powers_iff_not_mem (is_maximal.is_prime hI).radical).2 hy)],
  exact ⟨hI, hy⟩
end

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def order_iso_of_maximal [is_jacobson R] :
  {p : ideal S // p.is_maximal} ≃o {p : ideal R // p.is_maximal ∧ y ∉ p} :=
{ to_fun := λ p, ⟨ideal.comap f.to_map p.1, (is_maximal_iff_is_maximal_disjoint f p.1).1 p.2⟩,
  inv_fun := λ p, ⟨ideal.map f.to_map p.1, is_maximal_of_is_maximal_disjoint f p.1 p.2.1 p.2.2⟩,
  left_inv := λ J, subtype.eq (map_comap f J),
  right_inv := λ I, subtype.eq (comap_map_of_is_prime_disjoint f I.1 (is_maximal.is_prime I.2.1)
    ((disjoint_powers_iff_not_mem I.2.1.is_prime.radical).2 I.2.2)),
  map_rel_iff' := λ I I', ⟨λ h x hx, h hx, λ h, (show I.val ≤ I'.val,
    from (map_comap f I.val) ▸ (map_comap f I'.val) ▸ (ideal.map_mono h))⟩ }

/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then `S` is Jacobson. -/
lemma is_jacobson_localization [H : is_jacobson R]
  (f : away_map y S) : is_jacobson S :=
begin
  rw is_jacobson_iff_prime_eq,
  refine λ P' hP', le_antisymm _ le_jacobson,
  obtain ⟨hP', hPM⟩ := (localization_map.is_prime_iff_is_prime_disjoint f P').mp hP',
  have hP := H (comap f.to_map P') (is_prime.radical hP'),
  refine le_trans (le_trans (le_of_eq (localization_map.map_comap f P'.jacobson).symm) (map_mono _))
    (le_of_eq (localization_map.map_comap f P')),
  have : Inf { I : ideal R | comap f.to_map P' ≤ I ∧ I.is_maximal ∧ y ∉ I } ≤ comap f.to_map P',
  { intros x hx,
    have hxy : x * y ∈ (comap f.to_map P').jacobson,
    { rw [ideal.jacobson, mem_Inf],
      intros J hJ,
      by_cases y ∈ J,
      { exact J.smul_mem x h },
      { exact (mul_comm y x) ▸ J.smul_mem y ((mem_Inf.1 hx) ⟨hJ.left, ⟨hJ.right, h⟩⟩) } },
    rw hP at hxy,
    cases hP'.right hxy with hxy hxy,
    { exact hxy },
    { exfalso,
      refine hPM ⟨submonoid.mem_powers _, hxy⟩ } },
  refine le_trans _ this,
  rw [ideal.jacobson, comap_Inf', Inf_eq_infi],
  refine infi_le_infi_of_subset (λ I hI, ⟨map f.to_map I, ⟨_, _⟩⟩),
  { exact ⟨le_trans (le_of_eq ((localization_map.map_comap f P').symm)) (map_mono hI.1),
    is_maximal_of_is_maximal_disjoint f _ hI.2.1 hI.2.2⟩ },
  { exact localization_map.comap_map_of_is_prime_disjoint f I (is_maximal.is_prime hI.2.1)
    ((disjoint_powers_iff_not_mem hI.2.1.is_prime.radical).2 hI.2.2) }
end

theorem is_jacobson_of_eisenbud
  (H : ∀ (P : ideal R) [P.is_prime] (b : R) (hb : b ≠ 0) (ϕ : away_map b (localization (submonoid.powers b))),
    (P.map ϕ.to_map).is_maximal → P.is_maximal)
  : is_jacobson R :=
begin
  rw is_jacobson_iff_prime_eq,
  refine λ Q hQ, le_antisymm (λ x hx, classical.by_contradiction (λ hx', _)) le_jacobson,
  obtain ⟨P, ⟨hP_prime, hP, hPx⟩, hQP, h⟩ := zorn.zorn_partial_order₀
    {P : ideal R | P.is_prime ∧ Q ≤ P ∧ x ∉ P} _ Q ⟨hQ, le_refl Q, hx'⟩,
  { haveI : P.is_prime := hP_prime,
    refine absurd (H P x (λ hx'', hx' (hx''.symm ▸ Q.zero_mem))
      (localization.of (submonoid.powers x)) _ : P.is_maximal)
      (λ hP_max, hPx ((mem_Inf.1 hx) ⟨hP, hP_max⟩)),
    { refine ⟨(is_prime_of_is_prime_disjoint _ _ hP_prime
        (by rwa disjoint_powers_iff_not_mem (is_prime.radical hP_prime))).1, _⟩,
      refine maximal_of_no_maximal (λ J hJ hJ_max, _),
      haveI hJ_prime : J.is_prime := is_maximal.is_prime hJ_max,
      have hJp := is_maximal.is_prime hJ_max,
      rw is_prime_iff_is_prime_disjoint (localization.of (submonoid.powers x)) at hJp,
      have := hJp.right,
      rw disjoint_powers_iff_not_mem (is_prime.radical (comap_is_prime _ J)) at this,
      specialize h (comap (localization.of (submonoid.powers x)).to_map J) ⟨comap_is_prime _ J,
        (le_trans hQP (le_trans le_comap_map (comap_mono (le_of_lt hJ)))), this⟩
        (le_trans le_comap_map (comap_mono (le_of_lt hJ))),
      refine hJ.2 (le_of_eq (by rw [← h, map_comap (localization.of (submonoid.powers x))])) } },
  { intros S SC cC I IS,
    have hxS : x ∉ Sup S := λ hxS, let ⟨J, hJ, hJxy⟩ :=
      (submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).1 hxS in (SC hJ).2.2 hJxy,
    refine ⟨Sup S, ⟨_, le_trans (SC IS).2.1 (le_Sup IS), hxS⟩, λ z, le_Sup⟩,
    refine ⟨ne_of_lt ⟨le_top, λ hS, absurd (hS (by simp)) hxS⟩, λ x y hxy, _⟩,
    obtain ⟨J, hJ, hJxy⟩ := (submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).1 hxy,
    refine or.rec_on ((SC hJ).1.2 hJxy)
      (λ h, or.inl ((submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).2 ⟨J, hJ, h⟩))
      (λ h, or.inr ((submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).2 ⟨J, hJ, h⟩)) },
end

theorem is_jacobson_of_eisenbud'
  (H : ∀ (b : R) (hb : b ≠ 0) (ϕ : away_map b (localization (submonoid.powers b)))
    (P : ideal (localization (submonoid.powers b))) [(P.comap ϕ.to_map).is_prime],
    P.is_maximal → (P.comap ϕ.to_map).is_maximal)
  : is_jacobson R :=
begin
  rw is_jacobson_iff_prime_eq,
  refine λ Q hQ, le_antisymm (λ x hx, classical.by_contradiction (λ hx', _)) le_jacobson,
  obtain ⟨P, ⟨hP_prime, hP, hPx⟩, hQP, h⟩ := zorn.zorn_partial_order₀
    {P : ideal R | P.is_prime ∧ Q ≤ P ∧ x ∉ P} _ Q ⟨hQ, le_refl Q, hx'⟩,
  { let ϕ := localization.of (submonoid.powers x),
    haveI : ((P.map ϕ.to_map).comap ϕ.to_map).is_prime := by rwa ϕ.comap_map_of_is_prime_disjoint
      P hP_prime ((disjoint_powers_iff_not_mem hP_prime.radical).2 hPx),
    refine absurd (H x (λ hx'', hx' (hx''.symm ▸ Q.zero_mem)) ϕ (P.map ϕ.to_map) _) _,
    { refine ⟨(is_prime_of_is_prime_disjoint _ _ hP_prime
        (by rwa disjoint_powers_iff_not_mem (is_prime.radical hP_prime))).1, _⟩,
      refine maximal_of_no_maximal (λ J hJ hJ_max, _),
      haveI hJ_prime : J.is_prime := is_maximal.is_prime hJ_max,
      have hJp := is_maximal.is_prime hJ_max,
      rw is_prime_iff_is_prime_disjoint (localization.of (submonoid.powers x)) at hJp,
      have := hJp.right,
      rw disjoint_powers_iff_not_mem (is_prime.radical (comap_is_prime _ J)) at this,
      specialize h (comap (localization.of (submonoid.powers x)).to_map J) ⟨comap_is_prime _ J,
        (le_trans hQP (le_trans le_comap_map (comap_mono (le_of_lt hJ)))), this⟩
        (le_trans le_comap_map (comap_mono (le_of_lt hJ))),
      refine hJ.2 (le_of_eq (by rw [← h, map_comap (localization.of (submonoid.powers x))])) },
    { rw ϕ.comap_map_of_is_prime_disjoint P hP_prime
        ((disjoint_powers_iff_not_mem hP_prime.radical).2 hPx),
      exact (λ hP_max, hPx ((mem_Inf.1 hx) ⟨hP, hP_max⟩)) } },
  { intros S SC cC I IS,
    have hxS : x ∉ Sup S := λ hxS, let ⟨J, hJ, hJxy⟩ :=
      (submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).1 hxS in (SC hJ).2.2 hJxy,
    refine ⟨Sup S, ⟨_, le_trans (SC IS).2.1 (le_Sup IS), hxS⟩, λ z, le_Sup⟩,
    refine ⟨ne_of_lt ⟨le_top, λ hS, absurd (hS (by simp)) hxS⟩, λ x y hxy, _⟩,
    obtain ⟨J, hJ, hJxy⟩ := (submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).1 hxy,
    refine or.rec_on ((SC hJ).1.2 hJxy)
      (λ h, or.inl ((submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).2 ⟨J, hJ, h⟩))
      (λ h, or.inr ((submodule.mem_Sup_of_directed ⟨I, IS⟩ cC.directed_on).2 ⟨J, hJ, h⟩)) },
end

end localization


section polynomial
open polynomial

lemma radical_bot_of_integral_domain {R : Type u} [integral_domain R] : radical (⊥ : ideal R) = ⊥ :=
eq_bot_iff.2 (λ x hx, hx.rec_on (λ n hn, pow_eq_zero hn))

lemma jacobson_bot_polynomial_le_Inf_map_maximal :
  jacobson (⊥ : ideal (polynomial R)) ≤ Inf (map C '' {J : ideal R | J.is_maximal}) :=
begin
  refine le_Inf (λ J, exists_imp_distrib.2 (λ j hj, _)),
  haveI : j.is_maximal := hj.1,
  refine trans (jacobson_mono bot_le) (le_of_eq _ : J.jacobson ≤ J),
  suffices : (⊥ : ideal (polynomial j.quotient)).jacobson = ⊥,
  { rw [← hj.2, jacobson_eq_iff_jacobson_quotient_eq_bot],
    replace this := congr_arg (map (polynomial_quotient_equiv_quotient_polynomial j).to_ring_hom) this,
    rwa [map_jacobson_of_bijective _, map_bot] at this,
    exact (ring_equiv.bijective (polynomial_quotient_equiv_quotient_polynomial j)) },
  refine eq_bot_iff.2 (λ f hf, _),
  simpa [(λ hX, by simpa using congr_arg (λ f, coeff f 1) hX : (X : polynomial j.quotient) ≠ 0)]
    using eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit ((mem_jacobson_bot.1 hf) X)),
end

lemma jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : ideal R) = ⊥) :
  jacobson (⊥ : ideal (polynomial R)) = ⊥ :=
begin
  refine eq_bot_iff.2 (le_trans jacobson_bot_polynomial_le_Inf_map_maximal _),
  refine (λ f hf, ((submodule.mem_bot _).2 (polynomial.ext (λ n, trans _ (coeff_zero n).symm)))),
  suffices : f.coeff n ∈ ideal.jacobson ⊥, by rwa [h, submodule.mem_bot] at this,
  exact mem_Inf.2 (λ j hj, (mem_map_C_iff.1 ((mem_Inf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n),
end

lemma is_maximal_iff_quotient_is_maximal (I : ideal R) :
  I.is_maximal ↔ (⊥ : ideal I.quotient).is_maximal :=
⟨λ hI, @bot_is_maximal _ (@quotient.field _ _ I hI), λ hI, (@mk_ker _ _ I) ▸
  @comap_is_maximal_of_surjective _ _ _ _ (quotient.mk I) ⊥ quotient.mk_surjective hI⟩

lemma quotient_map_injective {R S : Type*} [comm_ring R] [comm_ring S] {I : ideal S} {f : R →+* S} :
  function.injective (quotient_map I f le_rfl) :=
begin
  rw ring_hom.injective_iff,
  refine λ a ha, _,
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a,
  rw quotient.eq_zero_iff_mem,
  unfold quotient_map at ha,
  rwa [quotient.lift_mk, ring_hom.comp_apply, quotient.eq_zero_iff_mem] at ha
end

@[simp]
lemma quotient_map_mk {R S : Type*} [comm_ring R] [comm_ring S]
  {J : ideal R} {I : ideal S}
  {f : R →+* S} {H : J ≤ I.comap f}
  {x : R} : (quotient_map I f H) (quotient.mk J x) = (quotient.mk I) (f x) :=
quotient.lift_mk _ _ _

lemma surjective_localization_field {R S : Type*} [comm_ring R] [comm_ring S] {M : submonoid R}
  {f : localization_map M S} {I : ideal S} [I.is_prime] {J : ideal R} {H : J ≤ I.comap f.to_map}
  (hI : (I.comap f.to_map).is_maximal) :
  function.surjective (quotient_map I f.to_map H) :=
begin
  intros s,
  obtain ⟨s, rfl⟩ := quotient.mk_surjective s,
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := f.mk'_surjective s,
  by_cases hM : (quotient.mk (I.comap f.to_map)) m = 0,
  { refine ⟨0, _⟩,
    rw [quotient.eq_zero_iff_mem, mem_comap] at hM,
    have := I.smul_mem (f.mk' 1 ⟨m, hm⟩) hM,
    rw [smul_eq_mul, mul_comm, ← localization_map.mk'_eq_mul_mk'_one, f.mk'_self,
      ← eq_top_iff_one] at this,
    rw [ring_hom.map_zero, eq_comm, quotient.eq_zero_iff_mem, this],
    exact submodule.mem_top },
  { rw quotient.maximal_ideal_iff_is_field_quotient at hI,
    obtain ⟨n, hn⟩ := hI.3 hM,
    obtain ⟨rn, rfl⟩ := quotient.mk_surjective n,
    refine ⟨(quotient.mk J) (r * rn), _⟩,
    rw [← ring_hom.map_mul] at hn,
    replace hn := congr_arg (quotient_map I f.to_map le_rfl) hn,
    simp only [ring_hom.map_one, quotient_map_mk, ring_hom.map_mul] at hn,
    rw [quotient_map_mk, ← sub_eq_zero_iff_eq, ← ring_hom.map_sub, quotient.eq_zero_iff_mem,
      ← quotient.eq_zero_iff_mem, ring_hom.map_sub, sub_eq_zero_iff_eq,
      localization_map.mk'_eq_mul_mk'_one],
    simp only [mul_eq_mul_left_iff, ring_hom.map_mul],
    refine or.inl (mul_left_cancel'
      (λ hn, hM (quotient.eq_zero_iff_mem.2 (mem_comap.2 (quotient.eq_zero_iff_mem.1 hn))))
      (trans hn (by rw [← ring_hom.map_mul, ← f.mk'_eq_mul_mk'_one, f.mk'_self, ring_hom.map_one]))) }
end

lemma technical_lemma {R S : Type*} [integral_domain R] [integral_domain S]
  {Rₘ Sₘ : Type*} [comm_ring Rₘ] [comm_ring Sₘ]
  [is_jacobson R]
  (φ : R →+* S) (hφ : function.injective φ)
  (x : R) (hx : x ≠ 0)
  (ϕ : localization_map (submonoid.powers x) Rₘ)
  (ϕ' : localization_map ((submonoid.powers x).map φ : submonoid S) Sₘ)
  (hφ' : (ϕ.map (mem_map_submonoid_of_mem φ) ϕ').is_integral) :
  (⊥ : ideal S).jacobson = ⊥ :=
begin
  have hM : ((submonoid.powers x).map φ : submonoid S) ≤ non_zero_divisors S :=
    map_le_non_zero_divisors_of_injective hφ
      (le_non_zero_divisors_of_domain (λ h0, hx (let ⟨n, hn⟩ := h0 in pow_eq_zero hn))),
  letI : integral_domain Sₘ := localization_map.integral_domain_of_le_non_zero_divisors ϕ' hM,
  let φ' : Rₘ →+* Sₘ := ϕ.map (mem_map_submonoid_of_mem φ) ϕ',
  have hϕ' : function.injective ϕ'.to_map := ϕ'.injective hM,
  rw [ring_hom.injective_iff_ker_eq_bot, ring_hom.ker_eq_comap_bot] at hϕ',
  have hSₘ : is_jacobson Sₘ := is_jacobson_of_is_integral' φ' hφ' (is_jacobson_localization ϕ),
  specialize hSₘ ⊥ radical_bot_of_integral_domain,
  have hcomm: φ'.comp ϕ.to_map = ϕ'.to_map.comp φ := ϕ.map_comp _,

  -- This sub-proof is mostly just messing around with a commutative square of quotients
  have : ∀ I : ideal Sₘ, I.is_maximal → (I.comap ϕ'.to_map).is_maximal,
  { introsI I hI,
    have : (I.comap φ').is_maximal := is_maximal_comap_of_is_integral_of_is_maximal' φ' hφ' I hI,
    rw [is_maximal_iff_is_maximal_disjoint ϕ, comap_comap, hcomm, ← comap_comap] at this,
    have := this.left,
    rw is_maximal_iff_quotient_is_maximal at this ⊢,

    haveI : (I.comap ϕ'.to_map).is_prime := comap_is_prime ϕ'.to_map I,
    haveI : (I.comap φ').is_prime := comap_is_prime φ' I,
    haveI : (⊥ : ideal (I.comap ϕ'.to_map).quotient).is_prime := bot_prime,

    let A := ((I.comap ϕ'.to_map).comap φ).quotient,
    let B := (I.comap ϕ'.to_map).quotient,
    let A' := (I.comap φ').quotient,
    let B' := I.quotient,

    let f := quotient_map (I.comap ϕ'.to_map) φ le_rfl,
    let f' := quotient_map I φ' le_rfl,
    let g := quotient_map I ϕ'.to_map le_rfl,
    let g' : A →+* A' := quotient_map (I.comap φ') ϕ.to_map
      (le_of_eq (trans (comap_comap φ ϕ'.to_map) (hcomm ▸ (comap_comap ϕ.to_map φ').symm))),
    have hfg : g.comp f = f'.comp g',
    { refine ring_hom.ext (λ a, _),
      obtain ⟨r, rfl⟩ := quotient.mk_surjective a,
      simp [ring_hom.comp_apply],
      congr,
      rw [← ring_hom.comp_apply, ← hcomm, ring_hom.comp_apply] },

    refine is_maximal_of_is_integral_of_is_maximal_comap' f _ ⊥
      ((eq_bot_iff.2 (comap_bot_le_of_injective f quotient_map_injective)).symm ▸ this),
    refine is_integral_tower_bot_of_is_integral' f g quotient_map_injective (hfg.symm ▸
      (ring_hom.is_integral_trans (is_integral_of_surjective' (surjective_localization_field _))
        (is_integral_quotient_of_is_integral' hφ'))),
    rwa [comap_comap, hcomm, is_maximal_iff_quotient_is_maximal],
  },
  refine eq_bot_iff.2 (le_trans _ (le_of_eq hϕ')),
  rw [← hSₘ, comap_jacobson],
  refine Inf_le_Inf (λ j hj, ⟨bot_le, _⟩),
  cases hj with J hJ,
  rw ← hJ.2,
  exact this J hJ.1.2
end

lemma eval₂_C_X {R : Type*} [comm_ring R] (p : polynomial R) :
  eval₂ C X p = p :=
polynomial.induction_on' p (λ p q hp hq, by simp [hp, hq])
  (λ n x, by rw [eval₂_monomial, monomial_eq_smul_X, C_mul'])

private lemma is_jacobson_polynomial_of_domain' (R : Type*) [integral_domain R] [hR : is_jacobson R]
  (P : ideal (polynomial R)) [P.is_prime] (hP : ∀ (x : R), C x ∈ P → x = 0) : P.jacobson = P :=
begin
  by_cases hP' : (P = ⊥),
  { rw hP',
    refine jacobson_bot_polynomial_of_jacobson_bot _,
    refine hR ⊥ radical_bot_of_integral_domain },
  { rw jacobson_eq_iff_jacobson_quotient_eq_bot,
    let P' : ideal R := P.comap C,
    have : P' = ⊥ := by rwa eq_bot_iff,
    have hP'_inj : function.injective (quotient.mk P'),
    { rw ring_hom.injective_iff,
      refine λ x hx, _,
      rwa [quotient.eq_zero_iff_mem, this] at hx },
    haveI : P'.is_prime := comap_is_prime C P,
    have : ∃ (p : polynomial R) (hp : p ∈ P), p ≠ 0,
    { contrapose! hP',
      rw eq_bot_iff,
      exact λ x hx, (hP' x hx).symm ▸ (ideal.zero_mem ⊥) },
    obtain ⟨p, hp, hp0⟩ := this,
    have hp0 : (p.map (quotient.mk P')) ≠ 0,
    { refine λ hp0', hp0 _,
      rw ← leading_coeff_eq_zero at ⊢ hp0',
      rw leading_coeff_map' hP'_inj at hp0',
      exact hP'_inj (trans hp0' (ring_hom.map_zero _).symm) },
    let x : P'.quotient := (p.map (quotient.mk P')).leading_coeff,
    have hx : x ≠ 0,
    { intro hx,
      rw leading_coeff_eq_zero at hx,
      refine hp0 hx },
    let φ : P'.quotient →+* P.quotient := quotient.lift P' ((quotient.mk P).comp C)
       (λ a ha, by rwa [ring_hom.comp_apply, quotient.eq_zero_iff_mem]),
    have hφ' : φ.comp (quotient.mk P') = (quotient.mk P).comp C := rfl,
    have hφ : function.injective φ,
    { refine λ x y hxy, _,
      obtain ⟨x, rfl⟩ := quotient.mk_surjective x,
      obtain ⟨y, rfl⟩ := quotient.mk_surjective y,
      rw [← sub_eq_zero_iff_eq, ← ring_hom.map_sub, ← ring_hom.map_sub] at hxy,
      rw [quotient.lift_mk, ring_hom.comp_apply, quotient.eq_zero_iff_mem] at hxy,
      rw [← sub_eq_zero_iff_eq, ← ring_hom.map_sub, quotient.eq_zero_iff_mem],
      exact hxy },
    let M : submonoid P'.quotient := submonoid.powers (p.map (quotient.mk P')).leading_coeff,
    let M' : submonoid P.quotient := M.map φ,
    let ϕ : localization_map M (localization M) := localization.of M,
    let ϕ' : localization_map M' (localization M') := localization.of M',
    refine technical_lemma φ hφ x hx ϕ ϕ' _,
    { suffices : (ϕ.map (mem_map_submonoid_of_mem φ) ϕ').is_integral_elem (ϕ'.to_map ((quotient.mk P) X)),
      { intro p,
        obtain ⟨p, q, rfl⟩ := ϕ'.mk'_surjective p,
        suffices : (ϕ.map (mem_map_submonoid_of_mem φ) ϕ').is_integral_elem (ϕ'.to_map p),
        { rw ϕ'.mk'_eq_mul_mk'_one,
          refine @is_integral_mul _ _ _ _
            (ϕ.map (mem_map_submonoid_of_mem φ) ϕ').to_algebra _ _ this _,
          obtain ⟨q', hq⟩ := q.2,
          refine ⟨X - C (ϕ.mk' 1 ⟨q', hq.1⟩), monic_X_sub_C _, _⟩,
          simp only [eval₂_sub, eval₂_C, eval₂_X],
          rw sub_eq_zero_iff_eq,
          erw localization_map.map_mk',
          simp only [ring_hom.map_one, subtype.coe_mk],
          congr,
          exact subtype.eq hq.2.symm },
        obtain ⟨p, rfl⟩ := quotient.mk_surjective p,
        refine polynomial.induction_on p _ _ _,
        { refine λ r, ⟨X - C (ϕ.to_map ((quotient.mk P') r)), monic_X_sub_C _, _⟩,
          simp only [eval₂_sub, eval₂_C, eval₂_X],
          rw [sub_eq_zero_iff_eq, ← (ϕ.map (mem_map_submonoid_of_mem φ) ϕ').comp_apply,
            localization_map.map_comp, ring_hom.comp_apply],
          refl },
        { refine λ p q hp hq, _,
          rw [ring_hom.map_add, ring_hom.map_add],
          exact @is_integral_add _ _ _ _
            (ϕ.map (mem_map_submonoid_of_mem φ) ϕ').to_algebra _ _ hp hq },
        { refine λ n r h, _,
          rw [pow_succ X n, mul_comm X, ← mul_assoc, ring_hom.map_mul, ϕ'.to_map.map_mul],
          exact @is_integral_mul _ _ _ _
            (ϕ.map (mem_map_submonoid_of_mem φ) ϕ').to_algebra _ _ h this } },
      refine is_integral_localization_at_leading_coeff' ((quotient.mk P) X)
        (p.map (quotient.mk P')) φ _ M ⟨1, pow_one _⟩ _ _,
      rwa [eval₂_map, hφ', ← hom_eval₂, quotient.eq_zero_iff_mem, eval₂_C_X] } }
end

lemma polynomial_map_surjective {R S : Type*} [comm_ring R] [comm_ring S]
  (φ : R →+* S) (hφ : function.surjective φ) :
  (function.surjective (polynomial.map φ : polynomial R → polynomial S)) :=
λ f, polynomial.induction_on' f
  (λ p q hp hq, let ⟨p', hp'⟩ := hp in let ⟨q', hq'⟩ := hq in ⟨p' + q', by rw [map_add φ, hp', hq']⟩)
  (λ n s, let ⟨r, hr⟩ := hφ s in ⟨monomial n r, by rw [map_monomial φ, hr]⟩)

lemma mem_ideal_of_coeff_mem {R : Type*} [comm_ring R]
  (I : ideal (polynomial R)) (p : polynomial R)
  (hp : ∀ (n : ℕ), C (p.coeff n) ∈ I) : p ∈ I :=
sum_C_mul_X_eq p ▸ submodule.sum_mem I (λ n hn, I.mul_mem_right (hp n))

lemma zero_lemma (I : ideal (polynomial R)) [hI : I.is_prime]
  (hi' : (polynomial.map_ring_hom ((quotient.mk I).comp C).range_restrict).ker ≤ I)
  (x : ((quotient.mk I).comp C).range)
  (hx : C x ∈ (I.map (polynomial.map_ring_hom ((quotient.mk I).comp C).range_restrict))) :
  x = 0 :=
begin
  let R' := ((quotient.mk I).comp C).range,
  let i : R →+* R' := ((quotient.mk I).comp C).range_restrict,
  have hi : function.surjective (i : R → R') := ((quotient.mk I).comp C).surjective_onto_range,
  induction x with x hx',
  refine subtype.eq _,
  simp only [subring.coe_zero, subtype.val_eq_coe],
  obtain ⟨y, hy⟩ := (ring_hom.mem_range).1 hx',
  rw ring_hom.comp_apply at hy,
  rw [← hy, quotient.eq_zero_iff_mem],
  suffices : (polynomial.map i) (C y) ∈ (I.map (polynomial.map_ring_hom i)),
  { obtain ⟨f, hf⟩ := mem_image_of_mem_map_of_surjective (polynomial.map_ring_hom i)
      (polynomial_map_surjective _ hi) this,
    have hn : (C y - f) ∈ I := hi' _,
    have := I.add_mem hn hf.1,
    rwa sub_add_cancel (C y) f at this,
    rw [ring_hom.mem_ker, ring_hom.map_sub, hf.2, sub_eq_zero_iff_eq, coe_map_ring_hom] },
  convert hx,
  simp only [map_C, C_inj, coe_map_ring_hom],
  refine subtype.eq hy
end


-- Bootstrap the full theorem from the integral domain case
theorem is_jacobson_polynomial_iff_is_jacobson : is_jacobson R ↔ is_jacobson (polynomial R) :=
begin
  split; introI H,
  { rw is_jacobson_iff_prime_eq,
    introsI I hI,
    let R' := ((quotient.mk I).comp C).range,
    let i : R →+* R' := ((quotient.mk I).comp C).range_restrict,
    let i' : polynomial R →+* polynomial R' := polynomial.map_ring_hom i,
    have hi : function.surjective (i : R → R') := ((quotient.mk I).comp C).surjective_onto_range,
    have hi' : (polynomial.map_ring_hom i : polynomial R →+* polynomial R').ker ≤ I,
    { refine λ f hf, mem_ideal_of_coeff_mem I f (λ n, _),
      rw [← quotient.eq_zero_iff_mem, ← ring_hom.comp_apply],
      rw [ring_hom.mem_ker, coe_map_ring_hom] at hf,
      replace hf := congr_arg (λ (f : polynomial R'), f.coeff n) hf,
      simp only [coeff_map, coeff_zero] at hf,
      rwa [subtype.ext_iff, ring_hom.coe_range_restrict] at hf },
    haveI hR' : is_jacobson R' := is_jacobson_of_surjective ⟨i, hi⟩,
    let I' : ideal (polynomial R') := I.map (polynomial.map_ring_hom i),
    haveI : I'.is_prime := map_is_prime_of_surjective (polynomial_map_surjective i hi) hi',
    suffices : (I.map (polynomial.map_ring_hom i)).jacobson = (I.map (polynomial.map_ring_hom i)),
    { replace this := congr_arg (comap (polynomial.map_ring_hom i)) this,
      rw [← map_jacobson_of_surjective _ hi',
        comap_map_of_surjective _ _, comap_map_of_surjective _ _] at this,
      refine le_antisymm (le_trans (le_sup_left_of_le le_rfl)
        (le_trans (le_of_eq this) (sup_le le_rfl hi'))) le_jacobson,
      all_goals {exact polynomial_map_surjective i hi} },
    refine is_jacobson_polynomial_of_domain' R' I' (zero_lemma I hi'),
    },
  { exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x, ⟨C x, by simp⟩⟩ }
end

/-- Classical Nullstellensatz is half given by this theorem -/
lemma is_jacobson_mv_polynomial (H : is_jacobson R) (n : ℕ) :
  is_jacobson (mv_polynomial (fin n) R) :=
nat.rec_on n
  ((is_jacobson_iso
    ((mv_polynomial.ring_equiv_of_equiv R (equiv.equiv_pempty $ fin.elim0)).trans
    (mv_polynomial.pempty_ring_equiv R))).mpr H)
  (λ n hn, (is_jacobson_iso (mv_polynomial.fin_succ_equiv R n)).2
    (is_jacobson_polynomial_iff_is_jacobson.1 hn))

end polynomial

end ideal
