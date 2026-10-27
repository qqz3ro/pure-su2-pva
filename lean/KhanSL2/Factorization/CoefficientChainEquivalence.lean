module

public import KhanSL2.Factorization.CoefficientChainMaps

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R:Type) [CommRing R] [Algebra ℂ R]
variable {M N : Type} [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [AddCommGroup N] [Module ℂ N] [Module R N] [IsScalarTower ℂ R N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent R N]

/-- A specified coefficient-linear current equivalence gives the corresponding
isomorphism of the original coefficient-linear CE complexes. -/
def coefficientRelativeComplexIso (e:M≃ₗ⁅ℂ,Current⁆N)
    (he : ∀ (r : R) (m : M), e (r • m) = r • e m) :
    coefficientRelativeComplex R M ≅ coefficientRelativeComplex R N where
  hom := coefficientRelativeComplexMap R e.toLieModuleHom he
  inv := coefficientRelativeComplexMap R e.symm.toLieModuleHom (fun r n=>by
    apply e.injective
    change e (e.symm (r • n)) = e (r • e.symm n)
    rw [e.apply_symm_apply,he,e.apply_symm_apply])
  hom_inv_id := by
    ext j : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply coefficientDegreeMap_leftInverse e.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.toLinearMap
      (constantEquivariant_of_lieHom e.toLieModuleHom)
      (constantEquivariant_of_lieHom e.symm.toLieModuleHom)
    ext m
    exact e.symm_apply_apply m
  inv_hom_id := by
    ext j : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply coefficientDegreeMap_leftInverse e.symm.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap
      (constantEquivariant_of_lieHom e.symm.toLieModuleHom)
      (constantEquivariant_of_lieHom e.toLieModuleHom)
    ext n
    exact e.apply_symm_apply n

end KhanSL2.Factorization



