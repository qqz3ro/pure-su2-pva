module

public import KhanSL2.Macdonald.StrongBridgeHomologyCoproductEvaluation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual homology coproduct pairs with the product of the specified
harmonic representatives, with exactly the original Gmap normalization. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization

@[simp] theorem strongFreeRelativeEvaluation_mixedProjection (u : strongFree) (w : W) :
    strongFreeRelativeEvaluation u (mixedRelativeProjection w) =
      pairing (strongModel (StrongMacdonald.Gmap u.val)) w := by
  obtain ⟨z,rfl⟩ := chainModel.surjective w
  rw [mixedRelativeProjection_chainModel,strongFreeRelativeEvaluation_mk]

/-- The invariant tensor functional is exactly the ambient finite tensor pairing. -/
theorem strongFreeTensorEvaluation_mixedProjection (u v : strongFree) (w : W ⊗[ℂ] W) :
    strongFreeTensorEvaluation u v
      (TensorProduct.map mixedRelativeProjection mixedRelativeProjection w) =
      tensorSquarePairing
        (strongModel (StrongMacdonald.Gmap u.val) ⊗ₜ[ℂ] strongModel (StrongMacdonald.Gmap v.val)) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w t hw ht => simp only [map_add,hw,ht]
  | tmul a b =>
    rw [TensorProduct.map_tmul,strongFreeTensorEvaluation_tmul,
      strongFreeRelativeEvaluation_mixedProjection,strongFreeRelativeEvaluation_mixedProjection,
      tensorSquarePairing_tmul]

/-- The actual primitive/shuffle homology coproduct is dual to multiplication
of the specified Gmap harmonic cocycles, for every actual raw relative cycle. -/
theorem strongHomologyCoproduct_pairing_cycle (u v : strongFree)
    (z : RawChains SymmetricCoefficients)
    (hz : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0) :
    tensorSquarePairing (strongModel u.val ⊗ₜ[ℂ] strongModel v.val)
      (TensorProduct.map strongHomologyModel strongHomologyModel
        (symmetricHomologyCoproduct (totalSymmetricCycleClass z hz))) =
      pairing (strongModel (StrongMacdonald.Gmap (u.val*v.val))) (chainModel z) := by
  change tensorSquarePairing (strongModel u.val ⊗ₜ[ℂ] strongModel v.val)
    (TensorProduct.map strongHomologyModel strongHomologyModel
      ((totalKunnethEquiv SymmetricCoefficients SymmetricCoefficients).symm
        (symmetricCoproductTotalHomology (totalSymmetricCycleClass z hz)))) = _
  rw [← strongFreeTensorHomologyEvaluation_inverse]
  change strongFreeTensorEvaluation u v (symmetricChainCoproduct (Submodule.Quotient.mk z)) = _
  rw [← mixedRelativeProjection_chainModel,← mixedRelativeProjection_coproduct,
    strongFreeTensorEvaluation_mixedProjection,← pairing_mul_mixedCoproduct,
    ← strongModel_mul,← map_mul]

end KhanSL2.Macdonald
