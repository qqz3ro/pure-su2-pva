module

public import KhanSL2.SymmetricFamily.SymmetricChartComplex
public import KhanSL2.Factorization.ShuffleSymmetricTotal
public import KhanSL2.Factorization.ShuffleRelativeNaturality

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

/-! The chart unit on actual relative CE chains is literally the original
symmetric coproduct followed by the two coefficient insertions and balancing. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open BGG BGGBridge Macdonald Factorization
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass

section Naturality
variable {A : Type} [CommRing A] [Algebra ℂ A]
variable {M N P Q : Type}
  [AddCommGroup M] [Module ℂ M] [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
  [AddCommGroup P] [Module ℂ P] [Module A P] [IsScalarTower ℂ A P]
  [LieRingModule BGG.Current P] [LieModule ℂ BGG.Current P] [CoefficientLinearCurrent A P]
  [AddCommGroup Q] [Module ℂ Q] [Module A Q] [IsScalarTower ℂ A Q]
  [LieRingModule BGG.Current Q] [LieModule ℂ BGG.Current Q] [CoefficientLinearCurrent A Q]

theorem balancedRelativeShuffle_tensorCoeffMap (f : M →ₗ⁅ℂ,BGG.Current⁆ P)
    (g : N →ₗ⁅ℂ,BGG.Current⁆ Q) (z : RelativeChains (M ⊗[ℂ] N)) :
    balancedRelativeShuffle A P Q
      (Factorization.coefficientMap (tensorOverLieHom (A:=A) f g).toLinearMap
        (constantEquivariant_of_lieHom (tensorOverLieHom (A:=A) f g)) z) =
      relativeTensorBalance A P Q
        (TensorProduct.map
          (Factorization.coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
          (Factorization.coefficientMap g.toLinearMap (constantEquivariant_of_lieHom g))
            (relativeShuffle M N z)) := by
  have he := coefficientMap_comp (TensorProduct.map f.toLinearMap g.toLinearMap)
    (balancedCoefficientLieHom A P Q).toLinearMap
    ((constantEquivariant_of_lieHom f).tensorMap (constantEquivariant_of_lieHom g))
    (constantEquivariant_of_lieHom (balancedCoefficientLieHom A P Q))
  change balancedRelativeShuffle A P Q
    (Factorization.coefficientMap
      ((balancedCoefficientLieHom A P Q).toLinearMap.comp
        (TensorProduct.map f.toLinearMap g.toLinearMap))
        (constantEquivariant_of_lieHom (tensorOverLieHom (A:=A) f g)) z) = _
  rw [he,LinearMap.comp_apply,balancedRelativeShuffle_balance,relativeShuffle_coeffMap]

end Naturality

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The literal insertion of the two original relative chain factors. -/
def factorSymmetricChainTensorUnit (r s : ℕ) (f g : Polynomial A) :
    RelativeChains (symmetricPower r) ⊗[ℂ] RelativeChains (symmetricPower s) →ₗ[ℂ]
      RelativeChains (FactorSymmetric r f) ⊗[A] RelativeChains (FactorSymmetric s g) :=
  (relativeTensorBalance A (FactorSymmetric r f) (FactorSymmetric s g)).comp
    (TensorProduct.map
      (Factorization.coefficientMap (factorSymmetricUnitLieHom r f).toLinearMap
        (constantEquivariant_of_lieHom (factorSymmetricUnitLieHom r f)))
      (Factorization.coefficientMap (factorSymmetricUnitLieHom s g).toLinearMap
        (constantEquivariant_of_lieHom (factorSymmetricUnitLieHom s g))))

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
theorem specializedSymmetricTotalMap_original (c : Collision.ChartData (r+s) r s A)
    (z : RelativeChains (symmetricPower (r+s))) :
    specializedSymmetricTotalMap c z =
      factorSymmetricChainTensorUnit r s c.f₁ c.f₂ (symmetricPowerChainCoproduct r s z) := by
  have he := coefficientMap_comp (symmetricCoproductComponent r s).toLinearMap
    (tensorOverLieHom (A:=A) (factorSymmetricUnitLieHom r c.f₁)
      (factorSymmetricUnitLieHom s c.f₂)).toLinearMap
    (constantEquivariant_of_lieHom (symmetricCoproductComponent r s))
    (constantEquivariant_of_lieHom (tensorOverLieHom (A:=A)
      (factorSymmetricUnitLieHom r c.f₁) (factorSymmetricUnitLieHom s c.f₂)))
  change balancedRelativeShuffle A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)
    (Factorization.coefficientMap
      ((tensorOverLieHom (A:=A) (factorSymmetricUnitLieHom r c.f₁)
        (factorSymmetricUnitLieHom s c.f₂)).toLinearMap.comp
          (symmetricCoproductComponent r s).toLinearMap)
            (constantEquivariant_of_lieHom (specializedSymmetricCoproduct c)) z) = _
  rw [he,LinearMap.comp_apply,balancedRelativeShuffle_tensorCoeffMap]
  rfl

/-- Exact original normalized coproduct formula for every coefficient-unit chain. -/
theorem symmetricChartTotalMap_unit_original (c : Collision.ChartData (r+s) r s A)
    (z : RelativeChains (symmetricPower (r+s))) :
    symmetricChartTotalMap c (relativeChainsScalarMap (Depth.RB (r+s))
      (symmetricPower (r+s)) A ((1:A) ⊗ₜ[Depth.RB (r+s)] z)) =
        (Nat.choose (r+s) r : ℂ)⁻¹ •
          factorSymmetricChainTensorUnit r s c.f₁ c.f₂ (symmetricPowerChainCoproduct r s z) := by
  rw [symmetricChartTotalMap_unit,specializedSymmetricTotalMap_original]

end KhanSL2.SymmetricFamily
