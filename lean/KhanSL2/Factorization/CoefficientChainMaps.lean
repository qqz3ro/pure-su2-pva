module

public import KhanSL2.Factorization.CoefficientChainScalars

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Coefficient-linear maps on the original relative CE complexes, retaining
both their original current action and their coefficient scalars. -/
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable {M N : Type}
  [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [AddCommGroup N] [Module ℂ N] [Module R N]
  [IsScalarTower ℂ R N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent R N]

attribute [local instance] coefficientChainModule coefficientDegreeModule
  coefficientChainSMulCommClass coefficientChainIsScalarTower
  coefficientDegreeSMulCommClass coefficientDegreeIsScalarTower

/-- The induced original chain map respects every original coefficient scalar. -/
theorem coefficientMap_coefficient_smul (f : M →ₗ⁅ℂ,Current⁆ N)
    (hf : ∀ (r : R) (m : M), f (r • m) = r • f m) (r : R)
    (z : RelativeChains M) :
    coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f) (r • z) =
      r • coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f) z := by
  obtain ⟨z,rfl⟩ := (relC M).mkQ_surjective z
  change Submodule.Quotient.mk
    (rawMap f.toLinearMap (rawMap (coefficientScalarLieHom R M r).toLinearMap z)) =
      Submodule.Quotient.mk (rawMap (coefficientScalarLieHom R N r).toLinearMap
        (rawMap f.toLinearMap z))
  congr 1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simp only [map_add,hz,ht]
  | tmul ω m =>
    change ω ⊗ₜ[ℂ] f (r • m) = ω ⊗ₜ[ℂ] (r • f m)
    rw [hf]

/-- Bundle the same specified current-module chain map over the coefficient ring. -/
def coefficientMapLinear (f : M →ₗ⁅ℂ,Current⁆ N)
    (hf : ∀ (r : R) (m : M), f (r • m) = r • f m) :
    RelativeChains M →ₗ[R] RelativeChains N where
  __ := (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f)).toAddMonoidHom
  map_smul' := coefficientMap_coefficient_smul R f hf

/-- Restrict the original coefficient-linear chain map to its actual exterior degree. -/
def coefficientDegreeMapLinear (f : M →ₗ⁅ℂ,Current⁆ N)
    (hf : ∀ (r : R) (m : M), f (r • m) = r • f m) (j : ℕ) :
    degree M j →ₗ[R] degree N j where
  __ := (coefficientDegreeMap f.toLinearMap (constantEquivariant_of_lieHom f) j).toAddMonoidHom
  map_smul' r z := Subtype.ext (coefficientMap_coefficient_smul R f hf r z.val)

/-- The original specified coefficient map is a morphism of complexes over its ring. -/
def coefficientRelativeComplexMap (f : M →ₗ⁅ℂ,Current⁆ N)
    (hf : ∀ (r : R) (m : M), f (r • m) = r • f m) :
    coefficientRelativeComplex R M ⟶ coefficientRelativeComplex R N :=
  ChainComplex.ofHom (fun j => ModuleCat.ofHom (coefficientDegreeMapLinear R f hf j)) (fun j => by
    rw [coefficientRelativeComplex_d,coefficientRelativeComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (coefficientMap_differential f
      (show RelativeChains M from (show degree M (j+1) from z).val)).symm)

end KhanSL2.Factorization
