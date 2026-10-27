module

public import KhanSL2.SymmetricFamily.TensorMultiplication
public import KhanSL2.SymmetricFamily.DerivationProduct
public import KhanSL2.PolynomialBGG.ProjectiveModelDeriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The symmetric tensor comparison intertwines every induced derivation.
This includes both the full current action and every raising coefficient shift. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open Macdonald PolynomialBGG

/-- Slot permutation commutes with a derivation acting on every tensor slot. -/
theorem tensorPermute_tensorDeriv {k : ℕ} (σ : Equiv.Perm (Fin k))
    (D : Module.End ℂ BGG.Current) (x : ⨂[ℂ]^k BGG.Current) :
    tensorPermute σ (tensorDeriv k D x) = tensorDeriv k D (tensorPermute σ x) := by
  have h : (tensorPermute σ).toLinearMap.comp (tensorDeriv k D) =
      (tensorDeriv k D).comp (tensorPermute σ).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, tensorDeriv_tprod, map_sum, tensorPermute_tprod]
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact Function.update_comp_eq_of_injective v σ.injective i (D (v (σ i)))
  exact LinearMap.congr_fun h x

/-- The actual tensor derivation preserves permutation-invariant tensors. -/
theorem tensorDeriv_mem_invariant {k : ℕ} (D : Module.End ℂ BGG.Current)
    {x : ⨂[ℂ]^k BGG.Current} (hx : x ∈ invariantTensors k) :
    tensorDeriv k D x ∈ invariantTensors k := by
  rw [mem_invariantTensors_iff] at hx ⊢
  intro σ
  rw [tensorPermute_tensorDeriv, hx σ]

/-- Restrict the induced polynomial derivation to its actual homogeneous degree. -/
def symmetricDegreeDeriv (k : ℕ) (D : Module.End ℂ BGG.Current) :
    Module.End ℂ (symmetricPower k) :=
  (show Module.End ℂ SymmetricCoefficients from (symmetricDerivation D).toLinearMap).restrict
    (fun _ h => symmetricDerivation_preserves_degree D h)

@[simp] theorem symmetricDegreeDeriv_coe (k : ℕ) (D : Module.End ℂ BGG.Current)
    (p : symmetricPower k) :
    (symmetricDegreeDeriv k D p : SymmetricCoefficients) = symmetricDerivation D p.val := rfl

/-- Actual multiplication of current variables intertwines induced derivations. -/
theorem tensorProductPolynomial_tensorDeriv (k : ℕ) (D : Module.End ℂ BGG.Current)
    (x : ⨂[ℂ]^k BGG.Current) :
    tensorProductPolynomial k (tensorDeriv k D x) =
      symmetricDerivation D (tensorProductPolynomial k x) := by
  have h : (tensorProductPolynomial k).comp (tensorDeriv k D) =
      (symmetricDerivation D).toLinearMap.comp (tensorProductPolynomial k) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      tensorDeriv_tprod, map_sum, tensorProductPolynomial_tprod, Derivation.coeFn_coe]
    rw [derivation_prod_update]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    by_cases hji : j = i
    · subst j
      simp [symmetricDerivation_currentVariable]
    · simp [Function.update_of_ne hji]
  exact LinearMap.congr_fun h x

/-- The homogeneous quotient intertwines all induced derivations. -/
theorem tensorToSymmetric_tensorDeriv (k : ℕ) (D : Module.End ℂ BGG.Current)
    (x : ⨂[ℂ]^k BGG.Current) :
    tensorToSymmetric k (tensorDeriv k D x) = symmetricDegreeDeriv k D (tensorToSymmetric k x) := by
  apply Subtype.ext
  simp only [tensorToSymmetric_coe, symmetricDegreeDeriv_coe]
  exact tensorProductPolynomial_tensorDeriv k D x

/-- Normalized symmetrization also intertwines every actual induced derivation. -/
theorem symmetricToTensor_symmetricDegreeDeriv (k : ℕ) (D : Module.End ℂ BGG.Current)
    (p : symmetricPower k) :
    symmetricToTensor k (symmetricDegreeDeriv k D p) =
      tensorDeriv k D (symmetricToTensor k p) := by
  calc
    symmetricToTensor k (symmetricDegreeDeriv k D p) =
        symmetricToTensor k (tensorToSymmetric k (tensorDeriv k D (symmetricToTensor k p))) := by
          rw [tensorToSymmetric_tensorDeriv, tensorToSymmetric_symmetricToTensor]
    _ = _ := symmetricToTensor_tensorToSymmetric k _
      (tensorDeriv_mem_invariant D (symmetricToTensor_mem k p))

end KhanSL2.SymmetricFamily
