module

public import KhanSL2.Macdonald.StrongBridgeHomologyCoproduct
public import KhanSL2.Macdonald.StrongBridgeHomologyCoproductFree

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The specified harmonic homology equivalence preserves the actual primitive
coproduct. Both coproducts are independently constructed from the original CE
and polynomial/exterior operations. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization BGGBridge

/-- Actual multiplication preserves the colour-zero free source. -/
def strongFreeProduct (u v : strongFree) : strongFree :=
  ⟨u.val*v.val,by
    change StrongMacdonald.projFull (u.val*v.val) = u.val*v.val
    rw [map_mul,u.property,v.property]⟩

/-- The coproduct pairing is valid for every actual homology class. -/
theorem strongHomologyCoproduct_pairing (u v : strongFree)
    (h : TotalHomology SymmetricCoefficients) :
    tensorSquarePairing (strongModel u.val ⊗ₜ[ℂ] strongModel v.val)
      (TensorProduct.map strongHomologyModel strongHomologyModel (symmetricHomologyCoproduct h)) =
      pairing (strongModel (u.val*v.val)) (strongModel (strongTotalHomologyFreeEquiv h).val) := by
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (Factorization.differential SymmetricCoefficients)
      (Factorization.differential SymmetricCoefficients)) h
  obtain ⟨w,hw⟩ := Submodule.mkQ_surjective (relC SymmetricCoefficients) z.val
  have hd : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk w) = 0 := by
    change Factorization.differential SymmetricCoefficients ((relC SymmetricCoefficients).mkQ w) = 0
    rw [hw]
    exact z.property
  have he : totalSymmetricCycleClass w hd = (PerfectDuality.pairBoundaries
      (Factorization.differential SymmetricCoefficients)
      (Factorization.differential SymmetricCoefficients)).mkQ z := by
    have hh : (⟨Submodule.Quotient.mk w,hd⟩ :
        LinearMap.ker (Factorization.differential SymmetricCoefficients)) = z :=
      Subtype.ext hw
    exact congrArg (squareZeroClass (Factorization.differential SymmetricCoefficients)) hh
  rw [← he,strongHomologyCoproduct_pairing_cycle]
  exact (strongTotalHomologyFreeEquiv_pairing_cycle (strongFreeProduct u v) w hd).symm

/-- Include the specified homology coordinates in the original mixed algebra. -/
theorem strongHomologyModel_tensor (h : TotalHomology SymmetricCoefficients ⊗[ℂ]
    TotalHomology SymmetricCoefficients) :
    TensorProduct.map strongFreeEmbedding strongFreeEmbedding
      (TensorProduct.map strongTotalHomologyFreeEquiv.toLinearMap
        strongTotalHomologyFreeEquiv.toLinearMap h) =
      TensorProduct.map strongHomologyModel strongHomologyModel h := by
  induction h using TensorProduct.induction_on with
  | zero => simp
  | add h k hh hk => simp only [map_add,hh,hk]
  | tmul h k => rfl

/-- The original relative CE homology coproduct becomes precisely the primitive
coproduct on the specified free generators under the proved harmonic equivalence. -/
theorem strongTotalHomologyFreeEquiv_coproduct (h : TotalHomology SymmetricCoefficients) :
    TensorProduct.map strongTotalHomologyFreeEquiv.toLinearMap
      strongTotalHomologyFreeEquiv.toLinearMap (symmetricHomologyCoproduct h) =
      strongFreePrimitiveCoproduct (strongTotalHomologyFreeEquiv h) := by
  apply strongFree_tensor_pairing_ext
  intro u v
  rw [strongHomologyModel_tensor,strongFreePrimitiveCoproduct_embedding]
  simp only [strongFreeEmbedding_apply]
  rw [strongHomologyCoproduct_pairing,← pairing_mul_mixedCoproduct,← strongModel_mul]

end KhanSL2.Macdonald
