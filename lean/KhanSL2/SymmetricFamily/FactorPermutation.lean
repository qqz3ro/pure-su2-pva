module

public import KhanSL2.SymmetricFamily.FactorCoefficients
public import KhanSL2.SymmetricFamily.FixedReindex
public import KhanSL2.SymmetricFamily.RootAssignmentTransport
public import KhanSL2.SymmetricFamily.ColorPermutation
public import KhanSL2.Factorization.OrbitStabilizerTensorInvariants

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-! The genuine simultaneous group action on a factor's roots and colors,
and its fixed module identified with the original symmetric specialization. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization
open scoped FactorRootScalars

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Honest root relabelling on the prescribed factor algebra. -/
def factorRootPermutationRepresentation (n : ℕ) (f : Polynomial A) :
    Equiv.Perm (Fin n) →* (FactorRoots n f ≃ₐ[A] FactorRoots n f) := by
  letI := factorCoefficientAlgebra n f
  exact baseRootPermutationRepresentation n A

/-- The simultaneous honest group action on actual root/color tensors. -/
def factorLabelledRepresentation (n : ℕ) (f : Polynomial A) :
    Equiv.Perm (Fin n) →* Module.End A (FactorColors n f) where
  toFun σ := TensorProduct.AlgebraTensorModule.map
    (factorRootPermutationRepresentation n f σ).toLinearMap (colorPermutationRepresentation n σ).toLinearMap
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q v
    simp only [map_one,TensorProduct.AlgebraTensorModule.map_tmul]
    rfl
  map_mul' σ τ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q v
    simp only [map_mul,TensorProduct.AlgebraTensorModule.map_tmul,Module.End.mul_apply]
    rfl

theorem factorLabelledRepresentation_eq (n : ℕ) (f : Polynomial A) (σ : Equiv.Perm (Fin n)) :
    factorLabelledRepresentation n f σ = factorLabelledPermute n f σ.symm := by
  change TensorProduct.AlgebraTensorModule.map
    (factorRootPermutation n f σ).toLinearMap (colorPermutationEquiv σ).toLinearMap = _
  rw [colorPermutationEquiv_toLinearMap]
  rfl

/-- Reindexing inverse-slot invariance gives the honest simultaneous fixed module. -/
def factorFixedEquiv (n : ℕ) (f : Polynomial A) :
    fixedOperators (factorLabelledPermute n f) ≃ₗ[A]
      FiberTransport.fixedVectors (fun σ => factorLabelledRepresentation n f σ) :=
  fixedReindexEquiv (factorLabelledPermute n f) (fun σ => factorLabelledRepresentation n f σ)
    (Equiv.inv _) (fun σ => by
      change factorLabelledRepresentation n f σ.symm = factorLabelledPermute n f σ
      rw [factorLabelledRepresentation_eq n f σ.symm,Equiv.symm_symm])
/-- Original factor coefficients are the fixed module of the honest simultaneous action. -/
def factorSymmetricFixedEquiv (n : ℕ) (f : Polynomial A) :
    FactorSymmetric n f ≃ₗ[A] FiberTransport.fixedVectors (fun σ => factorLabelledRepresentation n f σ) :=
  (factorSymmetricRootEquiv n f).trans (factorFixedEquiv n f)
/-- Every finite permutation-group cardinal is invertible over an arbitrary complex algebra. -/
theorem permutationCard_inverse (n : ℕ) :
    algebraMap ℂ A ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
      (Fintype.card (Equiv.Perm (Fin n)) : A) = 1 := by
  have hn : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [← map_natCast (algebraMap ℂ A),← map_mul,inv_mul_cancel₀ hn,map_one]

end KhanSL2.SymmetricFamily
