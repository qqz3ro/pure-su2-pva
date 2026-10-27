module

public import KhanSL2.SymmetricFamily.ChartHomologyKunneth
public import KhanSL2.SymmetricFamily.NormalizedCoproductCycles
public import KhanSL2.Factorization.BalancedTotalQuasiIso

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-! The independently specified actual chart chain map induces the proved
normalized homology root-chart isomorphism. Both flat base-change and Künneth
are compared on their original cycle representatives. -/
noncomputable section
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open BGG Macdonald Factorization
open scoped FactorHomologyScalars
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientTotalHomologyModule coefficientTotalHomologyIsScalarTower coefficientTotalHomologySMulCommClass

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]
variable (c : Collision.ChartData (r+s) r s A)
variable [Algebra.Etale (Depth.RB (r+s)) A]

/-- The induced map on actual homology of the original normalized chart chain map. -/
def symmetricChartTotalHomologyMap :
    TotalHomology (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A) →ₗ[A]
      BalancedTensorTotalHomology A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) :=
  balancedTotalComparisonMap A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)
    (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A)
    (symmetricChartTotalMap c) (symmetricChartTotalMap_differential c)

/-- Express this independently constructed map in the original factor homology coordinates. -/
def symmetricChartHomologyCoordinateMap :
    A ⊗[Depth.RB (r+s)] TotalHomology (symmetricPower (r+s)) →ₗ[A]
      FactorSymmetricHomology r c.f₁ ⊗[A] FactorSymmetricHomology s c.f₂ :=
  (symmetricChartBalancedKunnethEquiv c).symm.toLinearMap.comp
    ((symmetricChartTotalHomologyMap c).comp
      (coefficientFlatHomologyEquiv (Depth.RB (r+s)) (symmetricPower (r+s)) A).toLinearMap)

/-- Exact unit-cycle identification with the previously specified normalized coproduct. -/
theorem symmetricChartHomologyCoordinateMap_unit
    (h : TotalHomology (symmetricPower (r+s))) :
    symmetricChartHomologyCoordinateMap c (1 ⊗ₜ[Depth.RB (r+s)] h) =
      specializedNormalizedHomologyCoproduct r s c.f₁ c.f₂ h := by
  apply (symmetricChartBalancedKunnethEquiv c).injective
  change symmetricChartBalancedKunnethEquiv c
    ((symmetricChartBalancedKunnethEquiv c).symm
      (symmetricChartTotalHomologyMap c
        (coefficientFlatHomologyEquiv (Depth.RB (r+s)) (symmetricPower (r+s)) A
          (1 ⊗ₜ[Depth.RB (r+s)] h)))) = _
  rw [LinearEquiv.apply_symm_apply,coefficientFlatHomologyEquiv_unit]
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential (symmetricPower (r+s)))
      (differential (symmetricPower (r+s)))) h
  simp only [Submodule.mkQ_apply]
  rw [coefficientTotalHomologyMap_mk]
  change balancedTotalComparisonMap A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)
    (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A)
    (symmetricChartTotalMap c) (symmetricChartTotalMap_differential c)
    (Submodule.Quotient.mk _) = _
  rw [balancedTotalComparisonMap_mk]
  change Submodule.Quotient.mk _ = symmetricChartBalancedKunnethEquiv c
    (tensorOverMap (factorSymmetricHomologyUnit r c.f₁) (factorSymmetricHomologyUnit s c.f₂)
      (normalizedSymmetricPowerHomologyCoproduct r s (Submodule.Quotient.mk z)))
  rw [normalizedSymmetricPowerHomologyCoproduct_mk,
    symmetricChartBalancedKunnethEquiv_unit_inverse_mk]
  congr 1
  apply Subtype.ext
  rw [symmetricChartTensorCycle_val]
  change symmetricChartTotalMap c
    (Factorization.coefficientMap
      (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A).toLinearMap
      (constantEquivariant_of_lieHom
        (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A)) z.val) =
    factorSymmetricChainTensorUnit r s c.f₁ c.f₂
      ((Nat.choose (r+s) r : ℂ)⁻¹ • symmetricPowerChainCoproduct r s z.val)
  have he := symmetricChartTotalMap_unit_original c z.val
  change symmetricChartTotalMap c ((1:A) • Factorization.coefficientMap
    (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A).toLinearMap
    (constantEquivariant_of_lieHom
      (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A)) z.val) = _ at he
  rw [one_smul] at he
  exact he.trans ((factorSymmetricChainTensorUnit r s c.f₁ c.f₂).map_smul
    ((Nat.choose (r+s) r : ℂ)⁻¹) (symmetricPowerChainCoproduct r s z.val)).symm

/-- Bijectivity is proved for the actual homology map, through the exact unit formula. -/
theorem symmetricChartTotalHomologyMap_bijective :
    Function.Bijective (symmetricChartTotalHomologyMap c) := by
  have hF := normalizedHomologyChart_bijective_of_unit c (symmetricChartHomologyCoordinateMap c)
    (symmetricChartHomologyCoordinateMap_unit c)
  have he : symmetricChartTotalHomologyMap c =
      (symmetricChartBalancedKunnethEquiv c).toLinearMap.comp
        ((symmetricChartHomologyCoordinateMap c).comp
          (coefficientFlatHomologyEquiv (Depth.RB (r+s)) (symmetricPower (r+s)) A).symm.toLinearMap) := by
    apply LinearMap.ext
    intro z
    change symmetricChartTotalHomologyMap c z = symmetricChartBalancedKunnethEquiv c
      ((symmetricChartBalancedKunnethEquiv c).symm (symmetricChartTotalHomologyMap c
        (coefficientFlatHomologyEquiv (Depth.RB (r+s)) (symmetricPower (r+s)) A
          ((coefficientFlatHomologyEquiv (Depth.RB (r+s)) (symmetricPower (r+s)) A).symm z))))
    rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  rw [he]
  exact (symmetricChartBalancedKunnethEquiv c).bijective.comp
    (hF.comp (coefficientFlatHomologyEquiv (Depth.RB (r+s)) (symmetricPower (r+s)) A).symm.bijective)

/-- The actual normalized symmetric coefficient comparison is a quasi-isomorphism
on every etale coprime chart. All required flatness and map identifications are proved. -/
theorem symmetricChartComplex_quasiIso : QuasiIso (symmetricChartComplex c) :=
  quasiIso_of_balancedTotalHomology_bijective A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)
    (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A)
    (symmetricChartTotalMap c) (symmetricChartComplex c) (symmetricChartComplex_forget c)
    (symmetricChartTotalMap_differential c) (symmetricChartTotalHomologyMap_bijective c)

end KhanSL2.SymmetricFamily
