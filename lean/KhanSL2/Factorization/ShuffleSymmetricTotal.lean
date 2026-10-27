module

public import KhanSL2.Factorization.ShuffleTotalQuasiIso
public import KhanSL2.Factorization.ShuffleSymmetric

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The fixed symmetric-degree CE coproduct, with its actual total-homology map
and its exact categorical counterpart. -/

noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open Macdonald

/-- Actual symmetric coefficient coproduct followed by the canonical CE shuffle,
restricted to the specified coefficient degrees. -/
def symmetricPowerChainCoproduct (k₁ k₂ : ℕ) :
    RelativeChains (symmetricPower (k₁+k₂)) →ₗ[ℂ]
      RelativeChains (symmetricPower k₁) ⊗[ℂ] RelativeChains (symmetricPower k₂) :=
  (relativeShuffle (symmetricPower k₁) (symmetricPower k₂)).comp
    (coefficientMap (symmetricCoproductComponent k₁ k₂).toLinearMap
      (constantEquivariant_of_lieHom (symmetricCoproductComponent k₁ k₂)))

theorem symmetricPowerChainCoproduct_differential (k₁ k₂ : ℕ)
    (z : RelativeChains (symmetricPower (k₁+k₂))) :
    symmetricPowerChainCoproduct k₁ k₂ (differential (symmetricPower (k₁+k₂)) z) =
      relativeTensorDifferential (symmetricPower k₁) (symmetricPower k₂)
        (symmetricPowerChainCoproduct k₁ k₂ z) := by
  simp only [symmetricPowerChainCoproduct,LinearMap.comp_apply,
    coefficientMap_differential,relativeShuffle_differential]

theorem symmetricPowerCoproductComplex_component (k₁ k₂ j : ℕ)
    (z : degree (symmetricPower (k₁+k₂)) j) :
    tensorDegreeForget (symmetricPower k₁) (symmetricPower k₂) j
      ((symmetricPowerCoproductComplex k₁ k₂).f j z) = symmetricPowerChainCoproduct k₁ k₂ z.val := by
  change tensorDegreeForget (symmetricPower k₁) (symmetricPower k₂) j
    (degreeShuffle (symmetricPower k₁) (symmetricPower k₂) j
      (coefficientDegreeMap (symmetricCoproductComponent k₁ k₂).toLinearMap
        (constantEquivariant_of_lieHom (symmetricCoproductComponent k₁ k₂)) j z)) = _
  rw [tensorDegreeForget_degreeShuffle]
  rfl

/-- The original symmetric-power coproduct acts on the original total CE homology. -/
def symmetricPowerCoproductTotalHomology (k₁ k₂ : ℕ) :
    TotalHomology (symmetricPower (k₁+k₂)) →ₗ[ℂ]
      PerfectDuality.PairHomology
        (relativeTensorDifferential (symmetricPower k₁) (symmetricPower k₂))
        (relativeTensorDifferential (symmetricPower k₁) (symmetricPower k₂))
        (relativeTensorDifferential_comp_self (symmetricPower k₁) (symmetricPower k₂)) :=
  (totalPairMap (symmetricPowerChainCoproduct k₁ k₂)
    (LinearMap.ext (symmetricPowerChainCoproduct_differential k₁ k₂))).homologyMap
      (differential_comp_self (symmetricPower (k₁+k₂)))
      (relativeTensorDifferential_comp_self (symmetricPower k₁) (symmetricPower k₂))

/-- A proof about this specified total-homology map yields the categorical
quasi-isomorphism of the same specified coproduct in every exterior degree. -/
theorem symmetricPowerCoproduct_quasiIso_of_total (k₁ k₂ : ℕ)
    (h : Function.Bijective (symmetricPowerCoproductTotalHomology k₁ k₂)) :
    QuasiIso (symmetricPowerCoproductComplex k₁ k₂) :=
  quasiIso_of_totalTensorHomology_bijective (symmetricPower (k₁+k₂))
    (symmetricPower k₁) (symmetricPower k₂)
    (symmetricPowerChainCoproduct k₁ k₂) (symmetricPowerCoproductComplex k₁ k₂)
    (symmetricPowerCoproductComplex_component k₁ k₂)
    (LinearMap.ext (symmetricPowerChainCoproduct_differential k₁ k₂)) h

end KhanSL2.Factorization
