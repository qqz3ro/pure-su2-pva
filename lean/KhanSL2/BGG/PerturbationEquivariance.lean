module

public import TauCeti.Algebra.Homology.Contraction.Perturbation

@[expose] public section

/-! Additive equivariance of perturbation, including symmetries that are not
linear over the noncommutative coefficient algebra. -/

namespace KhanSL2.BGG
namespace Perturbation

variable {R M N : Type*} [Semiring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {dM : Module.End R M} {dN : Module.End R N}
  (c : TauCeti.LinearSpecialContraction dM dN) (δ : Module.End R M)
  (f : M →+ M) (g : N →+ N)

/-- Any additive symmetry commuting with the perturbation and homotopy also
commutes with the finite perturbation operator. -/
theorem series_commute
    (hh : ∀ x, f (c.homotopy x) = c.homotopy (f x))
    (hδ : ∀ x, f (δ x) = δ (f x)) (hU : IsUnit (1 + δ * c.homotopy)) (x : M) :
    f (c.perturbationSeries δ x) = c.perturbationSeries δ (f x) := by
  apply ((Module.End.isUnit_iff _).mp hU).1
  have hT (y : M) : (1 + δ * c.homotopy) (f y) = f ((1 + δ * c.homotopy) y) := by
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply,
      map_add, hδ, hh]
  rw [hT]
  have hX (y : M) : (1 + δ * c.homotopy) (c.perturbationSeries δ y) = δ y :=
    LinearMap.congr_fun (c.one_add_mul_perturbationSeries δ hU) y
  rw [hX, hX, hδ]

/-- Equivariance of the transferred differential requires only additive symmetries. -/
theorem differential_commute
    (hi : ∀ x, f (c.incl x) = c.incl (g x))
    (hp : ∀ x, g (c.proj x) = c.proj (f x))
    (hh : ∀ x, f (c.homotopy x) = c.homotopy (f x))
    (hd : ∀ x, g (dN x) = dN (g x))
    (hδ : ∀ x, f (δ x) = δ (f x)) (hU : IsUnit (1 + δ * c.homotopy)) (x : N) :
    g (c.perturbedDifferential δ x) = c.perturbedDifferential δ (g x) := by
  simp only [TauCeti.LinearSpecialContraction.perturbedDifferential_def,
    LinearMap.add_apply, LinearMap.comp_apply, map_add, hd, hp,
    series_commute c δ f hh hδ hU, hi]

/-- Equivariance of the perturbed inclusion. -/
theorem inclusion_commute
    (hi : ∀ x, f (c.incl x) = c.incl (g x))
    (hh : ∀ x, f (c.homotopy x) = c.homotopy (f x))
    (hδ : ∀ x, f (δ x) = δ (f x))
    (hsq : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM)
    (hU : IsUnit (1 + δ * c.homotopy)) (x : N) :
    f ((c.perturb δ hsq hU).incl x) = (c.perturb δ hsq hU).incl (g x) := by
  simp only [TauCeti.LinearSpecialContraction.perturb_incl, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub, hi, hh, series_commute c δ f hh hδ hU]

/-- Equivariance of the perturbed projection. -/
theorem projection_commute
    (hp : ∀ x, g (c.proj x) = c.proj (f x))
    (hh : ∀ x, f (c.homotopy x) = c.homotopy (f x))
    (hδ : ∀ x, f (δ x) = δ (f x))
    (hsq : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM)
    (hU : IsUnit (1 + δ * c.homotopy)) (x : M) :
    g ((c.perturb δ hsq hU).proj x) = (c.perturb δ hsq hU).proj (f x) := by
  simp only [TauCeti.LinearSpecialContraction.perturb_proj, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub, hp, hh, series_commute c δ f hh hδ hU]

/-- Equivariance of the perturbed homotopy. -/
theorem homotopy_commute
    (hh : ∀ x, f (c.homotopy x) = c.homotopy (f x))
    (hδ : ∀ x, f (δ x) = δ (f x))
    (hsq : (dM + δ) ∘ₗ (dM + δ) = dM ∘ₗ dM)
    (hU : IsUnit (1 + δ * c.homotopy)) (x : M) :
    f ((c.perturb δ hsq hU).homotopy x) = (c.perturb δ hsq hU).homotopy (f x) := by
  simp only [TauCeti.LinearSpecialContraction.perturb_homotopy, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub, hh, series_commute c δ f hh hδ hU]

end Perturbation
end KhanSL2.BGG