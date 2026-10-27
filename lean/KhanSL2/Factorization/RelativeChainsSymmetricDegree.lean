module

public import KhanSL2.Factorization.RelativeChainsWeightTotalHomology
public import KhanSL2.Factorization.CoefficientMaps
public import KhanSL2.Macdonald.SymmetricCoefficientsProjection

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual coefficient inclusion and projection for a fixed symmetric power,
identified with symmetric-degree projection in the finite mixed chain blocks. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization
open Macdonald BGGBridge

def symmetricChainInclusion (s : ℕ) :
    RelativeChains (symmetricPower s) →ₗ[ℂ] RelativeChains SymmetricCoefficients :=
  coefficientMap (symmetricPower s).incl.toLinearMap
    (constantEquivariant_of_lieHom (symmetricPower s).incl)

def symmetricChainProjection (s : ℕ) :
    RelativeChains SymmetricCoefficients →ₗ[ℂ] RelativeChains (symmetricPower s) :=
  coefficientMap (symmetricPowerProjection s).toLinearMap
    (constantEquivariant_of_lieHom (symmetricPowerProjection s))

@[simp] theorem symmetricChainProjection_inclusion (s : ℕ)
    (z : RelativeChains (symmetricPower s)) :
    symmetricChainProjection s (symmetricChainInclusion s z) = z := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk
      (rawMap (symmetricPowerProjection s).toLinearMap
        (rawMap (symmetricPower s).incl.toLinearMap z)) = Submodule.Quotient.mk z
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add,hu,hv]
    | tmul ω p =>
      rw [rawMap_tmul,rawMap_tmul]
      change ω ⊗ₜ[ℂ] symmetricPowerProjection s ((symmetricPower s).incl p) = ω ⊗ₜ[ℂ] p
      rw [symmetricPowerProjection_incl]

theorem symmetricChainInclusion_differential (s : ℕ)
    (z : RelativeChains (symmetricPower s)) :
    symmetricChainInclusion s (differential (symmetricPower s) z) =
      differential SymmetricCoefficients (symmetricChainInclusion s z) :=
  coefficientMap_differential (symmetricPower s).incl z

theorem symmetricChainProjection_differential (s : ℕ)
    (z : RelativeChains SymmetricCoefficients) :
    symmetricChainProjection s (differential SymmetricCoefficients z) =
      differential (symmetricPower s) (symmetricChainProjection s z) :=
  coefficientMap_differential (symmetricPowerProjection s) z

/-- The original polynomial homogeneous projection in mixed chain coordinates. -/
def mixedSymmetricProjection (s : ℕ) : Module.End ℂ W :=
  LinearMap.rTensor Exterior (MvPolynomial.homogeneousComponent s)

@[simp] theorem mixedSymmetricProjection_basis (s : ℕ) (b : BasisIndex) :
    mixedSymmetricProjection s (basis b) = if symmetricDegree b=s then basis b else 0 := by
  obtain ⟨d,t⟩ := b
  rw [basis_apply]
  change MvPolynomial.homogeneousComponent s (MvPolynomial.monomial d (1 : ℂ)) ⊗ₜ[ℂ]
    FiniteExterior.monomial t = _
  rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial 1 rfl)]
  have hd : d.degree = polynomialDegree d := rfl
  rw [hd]
  change (if s=polynomialDegree d then MvPolynomial.monomial d (1 : ℂ) else 0) ⊗ₜ[ℂ]
    FiniteExterior.monomial t = if polynomialDegree d=s then _ else 0
  by_cases h : polynomialDegree d=s
  · rw [if_pos h,if_pos h.symm]
  · rw [if_neg h,if_neg (Ne.symm h),TensorProduct.zero_tmul]

theorem mixedSymmetricProjection_of_mem {w t : ℕ} {u : W}
    (hu : u ∈ weightDegreePiece w t) (s : ℕ) :
    mixedSymmetricProjection s u = if t=s then u else 0 := by
  rw [eq_sum_basis u,map_sum]
  by_cases h : t=s
  · rw [if_pos h]
    apply Finset.sum_congr rfl
    intro b hb
    have hbt := ((mem_weightDegreePiece_iff u w t).mp hu b hb).2
    rw [map_smul,mixedSymmetricProjection_basis,hbt,if_pos h]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    have hbt := ((mem_weightDegreePiece_iff u w t).mp hu b hb).2
    rw [map_smul,mixedSymmetricProjection_basis,hbt,if_neg h,smul_zero]

theorem chainModel_rawSymmetricProjection (s : ℕ) (z : RawChains SymmetricCoefficients) :
    chainModel (rawMap (symmetricPower s).incl.toLinearMap
      (rawMap (symmetricPowerProjection s).toLinearMap z)) =
        mixedSymmetricProjection s (chainModel z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul ω p => rfl

/-- The actual coefficient projection equals the mixed polynomial degree projection. -/
theorem symmetricChainInclusion_projection_mk (s : ℕ) (u : W) :
    symmetricChainInclusion s (symmetricChainProjection s
      (Submodule.Quotient.mk (chainModel.symm u))) =
        Submodule.Quotient.mk (chainModel.symm (mixedSymmetricProjection s u)) := by
  change Submodule.Quotient.mk
    (rawMap (symmetricPower s).incl.toLinearMap
      (rawMap (symmetricPowerProjection s).toLinearMap (chainModel.symm u))) = _
  congr 1
  apply chainModel.injective
  rw [chainModel_rawSymmetricProjection,chainModel.apply_symm_apply,chainModel.apply_symm_apply]

/-- The coefficient-degree splitting acts diagonally on the actual relative weight blocks. -/
theorem symmetricChainProjection_weightInclusion (s w t : ℕ) (u : WeightChains w t) :
    symmetricChainInclusion s (symmetricChainProjection s (weightInclusion w t u)) =
      if t=s then weightInclusion w t u else 0 := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    rw [weightInclusion_mk,symmetricChainInclusion_projection_mk,
      mixedSymmetricProjection_of_mem u.property]
    split <;> simp

end KhanSL2.Factorization
