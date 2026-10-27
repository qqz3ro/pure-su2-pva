module

public import KhanSL2.Macdonald.StrongBridgeFixedRootInclusion
public import KhanSL2.Factorization.KunnethTotalNaturality

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Exact compatibility of the fixed symmetric-coefficient homology model
with the already defined raising coefficient operators. -/
noncomputable section
open scoped DirectSum TensorProduct
namespace KhanSL2.Macdonald
open Factorization

/-- The original raising power sum on the actual fixed-degree homology. -/
def symmetricPowerHomologyShift (m s : ℕ) :
    Module.End ℂ (TotalHomology (symmetricPower s)) :=
  coefficientTotalHomologyMap (symmetricPowerCoefficientEnd m s)

/-- Actual coefficient inclusion commutes with the original raising operator. -/
theorem symmetricChainInclusion_coefficientShift (m s : ℕ)
    (z : RelativeChains (symmetricPower s)) :
    symmetricChainInclusion s
      (Factorization.coefficientMap (symmetricPowerCoefficientEnd m s).toLinearMap
        (constantEquivariant_of_lieHom (symmetricPowerCoefficientEnd m s)) z) =
      Factorization.coefficientMap (symmetricCoefficientEnd m).toLinearMap
        (constantEquivariant_of_lieHom (symmetricCoefficientEnd m))
          (symmetricChainInclusion s z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk
      (rawMap (symmetricPower s).incl.toLinearMap
        (rawMap (symmetricPowerCoefficientEnd m s).toLinearMap z)) =
      Submodule.Quotient.mk (rawMap (symmetricCoefficientEnd m).toLinearMap
        (rawMap (symmetricPower s).incl.toLinearMap z))
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z t hz ht => simp only [map_add,hz,ht]
    | tmul ω p => rfl

/-- The fixed-degree homology action is the restriction of the original total action. -/
theorem symmetricHomologyInclusion_shift (m s : ℕ)
    (u : TotalHomology (symmetricPower s)) :
    symmetricHomologyInclusion s (symmetricPowerHomologyShift m s u) =
      totalSymmetricShift m (symmetricHomologyInclusion s u) := by
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (Factorization.differential (symmetricPower s))
      (Factorization.differential (symmetricPower s))) u
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  exact symmetricChainInclusion_coefficientShift m s z.val

/-- Actual raising on fixed symmetric homology is precisely weighted root multiplication. -/
theorem symmetricPowerRootEquiv_shift (m s : ℕ)
    (u : TotalHomology (symmetricPower s)) :
    symmetricPowerRootEquiv s (symmetricPowerHomologyShift m s u) =
      fixedRootPowerSumEnd m s (symmetricPowerRootEquiv s u) := by
  apply fixedRootInclusion_injective s
  rw [← strongTotalHomologyRootEquiv_symmetricInclusion,symmetricHomologyInclusion_shift,
    strongTotalHomologyRootEquiv_shift,strongTotalHomologyRootEquiv_symmetricInclusion,
    fixedRootInclusion_shift]

end KhanSL2.Macdonald
