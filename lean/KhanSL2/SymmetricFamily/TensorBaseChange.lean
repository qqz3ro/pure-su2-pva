module

public import KhanSL2.SymmetricFamily.AverageBaseChange
public import KhanSL2.SymmetricFamily.ExteriorCurrent

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-! Actual symmetric and exterior current families commute with arbitrary
coefficient base change as ordinary and signed tensor invariants. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open Macdonald PolynomialBGG Conditional
open scoped KhanSL2.Conditional

/-- Actual tensor-slot permutation is linear over the prescribed coefficient ring. -/
def tensorPermutationLinear (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Module.End (CoefficientRing k) (⨂[ℂ]^k BGG.Current) where
  __ := (tensorPermute σ).toAddHom
  map_smul' r x := by
    apply Modules.polynomialCoordinates_intertwines
      (M := ⨂[ℂ]^k BGG.Current) (V := ⨂[ℂ]^k BGG.Current)
      (coefficientCoordinates k) (tensorPermute σ).toLinearMap _ r x
    intro i y
    rw [tensorCoefficientCoordinates_smul, tensorCoefficientCoordinates_smul]
    exact tensorPermute_tensorDeriv σ (Modules.coefficientShift (i.val+1)) y

/-- The scalar used for both normalized finite-group projectors. -/
def permutationNormalization (k : ℕ) : CoefficientRing k :=
  algebraMap ℂ (CoefficientRing k) ((Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹)

theorem permutationNormalization_card (k : ℕ) :
    permutationNormalization k * (Fintype.card (Equiv.Perm (Fin k)) : CoefficientRing k) = 1 := by
  simpa only [permutationNormalization, map_mul, map_natCast, map_one] using
    congrArg (algebraMap ℂ (CoefficientRing k)) (inv_mul_cancel₀ (permutationCard_ne_zero k))

/-- The actual symmetric quotient-section composite is normalized slot averaging over R_k. -/
theorem symmetric_tensor_average (k : ℕ) :
    (symmetricToTensorLinear k).comp (tensorToSymmetricLinear k) =
      permutationNormalization k • ∑ σ : Equiv.Perm (Fin k), tensorPermutationLinear k σ := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  change symmetricToTensor k (tensorToSymmetric k x) =
    permutationNormalization k • ∑ σ : Equiv.Perm (Fin k), tensorPermute σ x
  rw [permutationNormalization, IsScalarTower.algebraMap_smul]
  apply (currentWordBasis k).repr.injective
  simp only [tensorToSymmetric, symmetricToTensor, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [relabel_unlabel]
  simp only [wordAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, currentWordBasis_repr_permute]

/-- Signed tensor-slot permutation over the fixed coefficient ring. -/
def tensorSignedPermutationLinear (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Module.End (CoefficientRing k) (⨂[ℂ]^k BGG.Current) :=
  (algebraMap ℂ (CoefficientRing k) (σ.sign : ℂ)) • tensorPermutationLinear k σ

@[simp] theorem tensorSignedPermutationLinear_apply (k : ℕ) (σ : Equiv.Perm (Fin k))
    (x : ⨂[ℂ]^k BGG.Current) :
    tensorSignedPermutationLinear k σ x = signedSlot BGG.Current σ x := by
  change algebraMap ℂ (CoefficientRing k) (σ.sign : ℂ) • tensorPermute σ x = _
  rw [IsScalarTower.algebraMap_smul]
  rfl

/-- The actual exterior quotient-section composite is the signed average over R_k. -/
theorem exterior_tensor_average (k : ℕ) :
    (exteriorToTensorLinear k).comp (tensorToExteriorLinear k) =
      permutationNormalization k • ∑ σ : Equiv.Perm (Fin k), tensorSignedPermutationLinear k σ := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  change exteriorToTensor BGG.Current k (tensorToExterior BGG.Current k x) =
    permutationNormalization k • ∑ σ : Equiv.Perm (Fin k), tensorSignedPermutationLinear k σ x
  simp only [tensorSignedPermutationLinear_apply, permutationNormalization,
    IsScalarTower.algebraMap_smul]
  simpa only [LinearMap.comp_apply, signedAverage, LinearMap.smul_apply,
    LinearMap.sum_apply] using
    LinearMap.congr_fun (alternatingProjection_eq_signedAverage BGG.Current k) x

/-- Slot permutations fix the actual normalized symmetric section over R_k. -/
theorem tensorPermutation_symmetricToTensor (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (tensorPermutationLinear k σ).comp (symmetricToTensorLinear k) = symmetricToTensorLinear k := by
  apply LinearMap.ext
  intro x
  change tensorPermute σ (symmetricToTensor k x) = symmetricToTensor k x
  exact (mem_invariantTensors_iff k _).mp (symmetricToTensor_mem k x) σ

/-- Signed slot permutations fix the original normalized exterior section over R_k. -/
theorem tensorSignedPermutation_exteriorToTensor (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (tensorSignedPermutationLinear k σ).comp (exteriorToTensorLinear k) = exteriorToTensorLinear k := by
  apply LinearMap.ext
  intro x
  change tensorSignedPermutationLinear k σ (exteriorToTensor BGG.Current k x) = _
  rw [tensorSignedPermutationLinear_apply]
  exact exteriorToTensor_mem_signed BGG.Current k x σ

/-- Arbitrary base change of the actual symmetric family is the actual invariant tensor family. -/
def symmetricBaseChangeTensorEquiv (k : ℕ) (A : Type*) [CommRing A]
    [Algebra (CoefficientRing k) A] :
    A ⊗[CoefficientRing k] symmetricPower k ≃ₗ[A]
      fixedOperators (fun σ : Equiv.Perm (Fin k) => (tensorPermutationLinear k σ).baseChange A) :=
  splitAverageBaseChangeEquiv (R := CoefficientRing k)
    (M := ⨂[ℂ]^k BGG.Current) (N := symmetricPower k) (ι := Equiv.Perm (Fin k)) A
    (symmetricToTensorLinear k) (tensorToSymmetricLinear k)
    (tensorPermutationLinear k) (permutationNormalization k) (permutationNormalization_card k)
    (symmetric_tensor_split k) (symmetric_tensor_average k) (tensorPermutation_symmetricToTensor k)

/-- Arbitrary base change of the original exterior family is the actual signed invariant tensor family. -/
def exteriorBaseChangeTensorEquiv (k : ℕ) (A : Type*) [CommRing A]
    [Algebra (CoefficientRing k) A] :
    A ⊗[CoefficientRing k] (⋀[ℂ]^k BGG.Current) ≃ₗ[A]
      fixedOperators (fun σ : Equiv.Perm (Fin k) =>
        (tensorSignedPermutationLinear k σ).baseChange A) :=
  splitAverageBaseChangeEquiv (R := CoefficientRing k)
    (M := ⨂[ℂ]^k BGG.Current) (N := ⋀[ℂ]^k BGG.Current) (ι := Equiv.Perm (Fin k)) A
    (exteriorToTensorLinear k) (tensorToExteriorLinear k)
    (tensorSignedPermutationLinear k) (permutationNormalization k) (permutationNormalization_card k)
    (tensorToExteriorLinear_exteriorToTensorLinear k) (exterior_tensor_average k)
    (tensorSignedPermutation_exteriorToTensor k)

end KhanSL2.SymmetricFamily
