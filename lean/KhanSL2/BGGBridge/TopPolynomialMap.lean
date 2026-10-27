module

public import KhanSL2.BGGBridge.TopAlternantsMap
public import KhanSL2.BGGBridge.TopGeneratorWindow
public import KhanSL2.BGGBridge.CoefficientOps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # The specified polynomial map into top BGG coinvariants -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- Tensor an exterior coefficient with the bottom standard harmonic vector,
then take the actual diagonal constant-action quotient. -/
def topCoefficientClass (B : ℕ) : NB →ₗ[ℂ] (HarmN NB ⧸ relH NB) :=
  (relH NB).mkQ.comp
    (standardTensorMap B (TauCeti.Sl2Std.basisVector ℂ (2*B) (2*B)))

@[simp] theorem topCoefficientClass_apply (B : ℕ) (ν : NB) :
    topCoefficientClass B ν = Submodule.Quotient.mk
      (standardTensorMap B (TauCeti.Sl2Std.basisVector ℂ (2*B) (2*B)) ν) := rfl

/-- A polynomial monomial records the root modes in the exterior coefficient
word; the harmonic coefficient is the bottom vector of V(2B). -/
def topPolynomialMap (B : ℕ) :
    MvPolynomial (Fin B) ℂ →ₗ[ℂ] (HarmN NB ⧸ relH NB) :=
  (topCoefficientClass B).comp (TopAlternants.rootPolynomialMap B)

@[simp] theorem topPolynomialMap_apply (B : ℕ) (p : MvPolynomial (Fin B) ℂ) :
    topPolynomialMap B p = topCoefficientClass B (TopAlternants.rootPolynomialMap B p) := rfl

/-- The polynomial map sends a variable-power word to the specified top tensor. -/
theorem topPolynomialMap_product (B : ℕ) (d : Fin B → ℕ) :
    topPolynomialMap B (∏ i : Fin B, (MvPolynomial.X i : MvPolynomial (Fin B) ℂ) ^ d i) =
      topCoefficientClass B
        (ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (d i, 0))) := by
  rw [topPolynomialMap_apply, TopAlternants.rootPolynomialMap_product]
  rfl

/-- Permuting coefficient slots changes the coinvariant class by the sign. -/
theorem topPolynomialMap_rename (B : ℕ) (e : Equiv.Perm (Fin B))
    (p : MvPolynomial (Fin B) ℂ) :
    topPolynomialMap B (MvPolynomial.rename e p) = e.sign • topPolynomialMap B p := by
  rw [topPolynomialMap_apply, TopAlternants.rootPolynomialMap_rename, topPolynomialMap_apply]
  simp only [Units.smul_def, map_zsmul]

/-- Power-sum multiplication is exactly the specified coefficient-shift operator. -/
theorem topPolynomialMap_powerSum (m B : ℕ) (p : MvPolynomial (Fin B) ℂ) :
    topPolynomialMap B (MvPolynomial.psum (Fin B) ℂ m * p) =
      coefficientBGGPower m (topPolynomialMap B p) := by
  simp only [topPolynomialMap_apply, TopAlternants.rootPolynomialMap_powerSum,
    topCoefficientClass_apply, coefficientBGGPower_mk, standardTensorMap_apply,
    coefficientHarmPower_tmul]

/-- The consecutive-word value comes from the explicit actual top spin window. -/
theorem topGeneratorWindow_coe (B : ℕ) :
    (topGeneratorWindow B : HarmN NB ⧸ relH NB) =
      topPolynomialMap B
        (∏ i : Fin B, (MvPolynomial.X i : MvPolynomial (Fin B) ℂ) ^ i.val) := by
  rw [topPolynomialMap_product]
  rfl

end KhanSL2.BGGBridge
