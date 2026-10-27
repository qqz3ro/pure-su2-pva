module

public import KhanSL2.Factorization.KunnethTotalInverse
public import KhanSL2.Factorization.ShuffleSymmetricProjection

@[expose] public section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

/-! The actual primitive/shuffle homology coproduct, expressed in the tensor
of the original homology groups using the canonical Künneth map. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open Macdonald

/-- Full actual symmetric CE coproduct on homology, after canonical Künneth. -/
def symmetricHomologyCoproduct : TotalHomology SymmetricCoefficients →ₗ[ℂ]
    TotalHomology SymmetricCoefficients ⊗[ℂ] TotalHomology SymmetricCoefficients :=
  (totalKunnethEquiv SymmetricCoefficients SymmetricCoefficients).symm.toLinearMap.comp
    symmetricCoproductTotalHomology

/-- The specified fixed-bidegree homology coproduct. -/
def symmetricPowerHomologyCoproduct (k₁ k₂ : ℕ) :
    TotalHomology (symmetricPower (k₁+k₂)) →ₗ[ℂ]
      TotalHomology (symmetricPower k₁) ⊗[ℂ] TotalHomology (symmetricPower k₂) :=
  (totalKunnethInverse (symmetricPower k₁) (symmetricPower k₂)).comp
    (symmetricPowerCoproductTotalHomology k₁ k₂)

@[simp] theorem coefficientTotalHomologyMap_symmetricPowerProjection (s : ℕ) :
    coefficientTotalHomologyMap (symmetricPowerProjection s) = symmetricHomologyProjection s := by
  apply LinearMap.ext
  intro z
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential SymmetricCoefficients)
      (differential SymmetricCoefficients)) z
  rfl

end KhanSL2.Factorization
