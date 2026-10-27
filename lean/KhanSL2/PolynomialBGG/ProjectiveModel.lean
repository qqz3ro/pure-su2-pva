module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Splittings used by the labelled polynomial model

The color relations are imposed on a complex vector space before extending
coefficients. Their quotient remains projective over the coefficient ring.
The normalized alternating map gives the canonical section from exterior
powers back to labelled tensor powers.
-/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.PolynomialBGG

section ColorQuotient

variable {R P C : Type*} [CommRing R] [Algebra ℂ R]
  [AddCommGroup P] [Module ℂ P] [Module R P] [IsScalarTower ℂ R P]
  [AddCommGroup C] [Module ℂ C]

/-- The polynomial extensions of all color relations. -/
def extendedColorRelations (W : Submodule ℂ C) : Submodule R (P ⊗[ℂ] C) :=
  LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor R P W.subtype)

/-- Color quotient and extension of polynomial coefficients commute. -/
def colorQuotientEquiv (W : Submodule ℂ C) :
    P ⊗[ℂ] (C ⧸ W) ≃ₗ[R] (P ⊗[ℂ] C) ⧸ extendedColorRelations (R := R) (P := P) W :=
  TensorProduct.AlgebraTensorModule.tensorQuotientEquiv R ℂ P W

@[simp] theorem colorQuotientEquiv_tmul (W : Submodule ℂ C) (f : P) (c : C) :
    colorQuotientEquiv (R := R) (P := P) W (f ⊗ₜ[ℂ] Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (f ⊗ₜ[ℂ] c) := rfl

/-- Quotienting the color factor introduces no projectivity assumption
on that quotient: every complex vector space is free. -/
theorem colorQuotient_projective [Module.Projective R P] (W : Submodule ℂ C) :
    Module.Projective R ((P ⊗[ℂ] C) ⧸ extendedColorRelations (R := R) (P := P) W) :=
  Module.Projective.of_equiv' (colorQuotientEquiv (R := R) (P := P) W)

theorem colorQuotient_free [Module.Free R P] (W : Submodule ℂ C) :
    Module.Free R ((P ⊗[ℂ] C) ⧸ extendedColorRelations (R := R) (P := P) W) :=
  Module.Free.of_equiv (colorQuotientEquiv (R := R) (P := P) W)

end ColorQuotient

section ExteriorSection

variable (M : Type*) [AddCommGroup M] [Module ℂ M]

/-- The canonical quotient from labelled tensors to exterior products. -/
def tensorToExterior (n : ℕ) : (⨂[ℂ]^n M) →ₗ[ℂ] ⋀[ℂ]^n M :=
  PiTensorProduct.lift (exteriorPower.ιMulti ℂ n).toMultilinearMap

@[simp] theorem tensorToExterior_tprod (n : ℕ) (v : Fin n → M) :
    tensorToExterior M n (PiTensorProduct.tprod ℂ v) = exteriorPower.ιMulti ℂ n v :=
  PiTensorProduct.lift.tprod _

/-- Alternating back into labelled tensors, normalized by the factorial. -/
def exteriorToTensor (n : ℕ) : (⋀[ℂ]^n M) →ₗ[ℂ] ⨂[ℂ]^n M :=
  ((Nat.factorial n : ℂ)⁻¹) • exteriorPower.toTensorPower ℂ M n

theorem tensorToExterior_toTensorPower (n : ℕ) :
    (tensorToExterior M n).comp (exteriorPower.toTensorPower ℂ M n) =
      (Nat.factorial n : ℂ) • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change tensorToExterior M n
    (exteriorPower.toTensorPower ℂ M n (exteriorPower.ιMulti ℂ n v)) = _
  have h := congrArg (fun f : M [⋀^Fin n]→ₗ[ℂ] ⋀[ℂ]^n M => f v)
    (LinearMap.compMultilinearMap_alternatization (tensorToExterior M n)
      (PiTensorProduct.tprod ℂ))
  have heq : (tensorToExterior M n).compMultilinearMap (PiTensorProduct.tprod ℂ) =
      (exteriorPower.ιMulti ℂ n).toMultilinearMap := by
    apply MultilinearMap.ext
    intro v
    exact tensorToExterior_tprod M n v
  rw [heq, AlternatingMap.coe_alternatization] at h
  simpa [exteriorPower.toTensorPower, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul] using h.symm

theorem tensorToExterior_exteriorToTensor (n : ℕ) :
    (tensorToExterior M n).comp (exteriorToTensor M n) = LinearMap.id := by
  rw [exteriorToTensor, LinearMap.comp_smul, tensorToExterior_toTensorPower, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) :
      (Nat.factorial n : ℂ) ≠ 0), one_smul]

theorem exteriorToTensor_injective (n : ℕ) : Function.Injective (exteriorToTensor M n) :=
  (show Function.LeftInverse (tensorToExterior M n) (exteriorToTensor M n) from
    fun x => LinearMap.congr_fun (tensorToExterior_exteriorToTensor M n) x).injective

end ExteriorSection

end KhanSL2.PolynomialBGG
