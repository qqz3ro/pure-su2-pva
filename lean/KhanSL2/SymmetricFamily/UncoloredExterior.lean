module

public import KhanSL2.SymmetricFamily.UncoloredTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! One-color exterior polynomial coefficients as actual alternating root polynomials. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

/-- Actual root polynomials fixed by signed permutations of the labelled roots. -/
def alternatingRootPolynomials (k : ℕ) : Submodule ℂ (MvPolynomial (Fin k) ℂ) where
  carrier := {p | ∀ σ : Equiv.Perm (Fin k),
    (σ.sign : ℂ) • MvPolynomial.rename σ.symm p = p}
  zero_mem' := by simp
  add_mem' hp hq σ := by rw [map_add, smul_add, hp σ, hq σ]
  smul_mem' c _ hp σ := by rw [map_smul, smul_comm, hp σ]

theorem polynomialTensorEquiv_signedSlot {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : ⨂[ℂ]^k (Polynomial ℂ)) :
    polynomialTensorEquiv k (signedSlot (Polynomial ℂ) σ x) =
      (σ.sign : ℂ) • MvPolynomial.rename σ.symm (polynomialTensorEquiv k x) := by
  change polynomialTensorEquiv k ((σ.sign : ℂ) • slotPermute (Polynomial ℂ) σ x) = _
  rw [map_smul, polynomialTensorEquiv_permute]

/-- The polynomial tensor/root comparison restricts to actual signed invariants. -/
def signedPolynomialTensorEquiv (k : ℕ) :
    signedInvariantTensors (Polynomial ℂ) k ≃ₗ[ℂ] alternatingRootPolynomials k where
  toFun x := ⟨polynomialTensorEquiv k x.val, by
    intro σ
    rw [← polynomialTensorEquiv_signedSlot, x.property σ]⟩
  invFun x := ⟨(polynomialTensorEquiv k).symm x.val, by
    intro σ
    apply (polynomialTensorEquiv k).injective
    rw [polynomialTensorEquiv_signedSlot, LinearEquiv.apply_symm_apply]
    exact x.property σ⟩
  left_inv x := by
    apply Subtype.ext
    exact (polynomialTensorEquiv k).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    exact (polynomialTensorEquiv k).apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact map_add (polynomialTensorEquiv k) x.val y.val
  map_smul' c x := by apply Subtype.ext; exact map_smul (polynomialTensorEquiv k) c x.val

/-- The normalized exterior polynomial power is precisely the alternating root-polynomial module. -/
def exteriorPolynomialEquiv (k : ℕ) :
    (⋀[ℂ]^k (Polynomial ℂ)) ≃ₗ[ℂ] alternatingRootPolynomials k :=
  (exteriorSignedTensorEquiv (Polynomial ℂ) k).trans (signedPolynomialTensorEquiv k)

/-- The normalization on an ordered exterior monomial is the explicit signed average. -/
theorem exteriorPolynomialEquiv_ιMulti (k : ℕ) (u : Fin k → ℕ) :
    (exteriorPolynomialEquiv k (exteriorPower.ιMulti ℂ k
      (fun i => (Polynomial.X : Polynomial ℂ)^u i))).val =
      ((Nat.factorial k : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k),
        (σ.sign : ℂ) • MvPolynomial.monomial
          (Finsupp.equivFunOnFinite.symm (u ∘ σ)) 1 := by
  change polynomialTensorEquiv k (exteriorToTensor (Polynomial ℂ) k
    (exteriorPower.ιMulti ℂ k (fun i => (Polynomial.X : Polynomial ℂ)^u i))) = _
  simp only [exteriorToTensor, LinearMap.smul_apply, map_smul,
    exteriorPower.toTensorPower_apply_ιMulti, map_sum, Units.smul_def,
    ← Int.cast_smul_eq_zsmul ℂ, map_smul, polynomialTensorEquiv_word, Function.comp_def]

/-- Original raising operators become actual root power-sum multiplication. -/
theorem exteriorPolynomialEquiv_shift (m k : ℕ) (x : ⋀[ℂ]^k (Polynomial ℂ)) :
    (exteriorPolynomialEquiv k (exteriorDeriv k
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) x)).val =
      MvPolynomial.psum (Fin k) ℂ m * (exteriorPolynomialEquiv k x).val := by
  change polynomialTensorEquiv k (exteriorToTensor (Polynomial ℂ) k
    (exteriorDeriv k (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) x)) = _
  have h := LinearMap.congr_fun (exteriorToTensor_exteriorDeriv k
    (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m))) x
  simp only [LinearMap.comp_apply] at h
  exact (congrArg (polynomialTensorEquiv k) h).trans (polynomialTensorEquiv_shift m k _)

end KhanSL2.SymmetricFamily
