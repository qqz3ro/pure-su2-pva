module
public import KhanSL2.Factorization.ShuffleSymmetricKunneth
public import KhanSL2.Factorization.KunnethTotalInverse
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open Macdonald

/-- The original coefficient projections determine exactly the fixed component. -/
theorem symmetricPowerHomologyCoproduct_eq_projection (k₁ k₂ : ℕ)
    (z : TotalHomology (symmetricPower (k₁+k₂))) :
    symmetricPowerHomologyCoproduct k₁ k₂ z =
      TensorProduct.map (symmetricHomologyProjection k₁) (symmetricHomologyProjection k₂)
        (symmetricHomologyCoproduct (symmetricHomologyInclusion (k₁+k₂) z)) := by
  apply (totalKunnethEquiv (symmetricPower k₁) (symmetricPower k₂)).injective
  simp only [symmetricPowerHomologyCoproduct,symmetricHomologyCoproduct,
    totalKunnethInverse,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  have hn := totalKunnethEquiv_natural (symmetricPowerProjection k₁)
    (symmetricPowerProjection k₂)
    ((totalKunnethEquiv SymmetricCoefficients SymmetricCoefficients).symm
      (symmetricCoproductTotalHomology (symmetricHomologyInclusion (k₁+k₂) z)))
  simp only [coefficientTotalHomologyMap_symmetricPowerProjection,
    LinearEquiv.apply_symm_apply] at hn
  have hp := LinearMap.congr_fun (symmetricPowerCoproductTotalHomology_eq_projection k₁ k₂) z
  simp only [LinearMap.comp_apply] at hp
  set_option backward.isDefEq.respectTransparency true in
    with_reducible exact hp.trans hn

end KhanSL2.Factorization
