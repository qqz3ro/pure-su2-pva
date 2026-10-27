module

public import KhanSL2.Factorization.ShuffleSymmetricTotal
public import KhanSL2.Factorization.RelativeChainsSymmetricHomology
public import KhanSL2.Factorization.KunnethCoefficientMaps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The fixed symmetric-bidegree coproduct is exactly the corresponding actual
coefficient projection of the full primitive CE coproduct, also on homology. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open Macdonald

theorem symmetricPowerChainCoproduct_eq_projection (k₁ k₂ : ℕ)
    (z : RelativeChains (symmetricPower (k₁+k₂))) :
    symmetricPowerChainCoproduct k₁ k₂ z =
      TensorProduct.map (symmetricChainProjection k₁) (symmetricChainProjection k₂)
        (symmetricChainCoproduct (symmetricChainInclusion (k₁+k₂) z)) := by
  have hcomp : coefficientMap (symmetricCoproductComponent k₁ k₂).toLinearMap
      (constantEquivariant_of_lieHom (symmetricCoproductComponent k₁ k₂)) =
      (coefficientMap (TensorProduct.map (symmetricPowerProjection k₁).toLinearMap
        (symmetricPowerProjection k₂).toLinearMap)
          ((constantEquivariant_of_lieHom (symmetricPowerProjection k₁)).tensorMap
            (constantEquivariant_of_lieHom (symmetricPowerProjection k₂)))).comp
        ((coefficientMap symmetricCoproduct.toLinearMap
          (constantEquivariant_of_lieHom symmetricCoproduct)).comp
            (symmetricChainInclusion (k₁+k₂))) := by
    apply Submodule.linearMap_qext
    apply TensorProduct.ext'
    intro ω p
    rfl
  change relativeShuffle (symmetricPower k₁) (symmetricPower k₂)
    (coefficientMap (symmetricCoproductComponent k₁ k₂).toLinearMap
      (constantEquivariant_of_lieHom (symmetricCoproductComponent k₁ k₂)) z) = _
  rw [hcomp,LinearMap.comp_apply,LinearMap.comp_apply,relativeShuffle_coeffMap]
  rfl

/-- The full primitive coefficient coproduct on the actual total CE homology. -/
def symmetricCoproductTotalHomology : TotalHomology SymmetricCoefficients →ₗ[ℂ]
    TensorTotalHomology SymmetricCoefficients SymmetricCoefficients :=
  (totalPairMap symmetricChainCoproduct
    (LinearMap.ext symmetricChainCoproduct_differential)).homologyMap
      (differential_comp_self SymmetricCoefficients)
      (relativeTensorDifferential_comp_self SymmetricCoefficients SymmetricCoefficients)

/-- Exact naturality of the specified fixed-bidegree homology coproduct. -/
theorem symmetricPowerCoproductTotalHomology_eq_projection (k₁ k₂ : ℕ) :
    symmetricPowerCoproductTotalHomology k₁ k₂ =
      (tensorCoefficientTotalHomologyMap (symmetricPowerProjection k₁)
        (symmetricPowerProjection k₂)).comp
          (symmetricCoproductTotalHomology.comp (symmetricHomologyInclusion (k₁+k₂))) := by
  apply LinearMap.ext
  intro z
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential (symmetricPower (k₁+k₂)))
      (differential (symmetricPower (k₁+k₂)))) z
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  exact symmetricPowerChainCoproduct_eq_projection k₁ k₂ u.val

end KhanSL2.Factorization
