module

public import KhanSL2.PolynomialBGG.RootRing
public import KhanSL2.PolynomialBGG.ProjectiveModelDeriv
public import KhanSL2.BGG.CurrentBasis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG
open BGG Current

/-- The finite-dimensional vector space recording the colors of the labelled slots. -/
abbrev Color (B : ℕ) := (Fin B → Fin 3) → ℂ

/-- Separate each mode-color tuple into its polynomial exponent and color word. -/
def tensorIndexEquiv (B : ℕ) :
    (Fin B → ℕ × Fin 3) ≃ (Fin B →₀ ℕ) × (Fin B → Fin 3) where
  toFun q := (Finsupp.equivFunOnFinite.symm (fun i => (q i).1), fun i => (q i).2)
  invFun q i := (q.1 i, q.2 i)
  left_inv q := by funext i; simp
  right_inv q := by apply Prod.ext <;> simp

/-- The monomial basis, transported to the root-ring type synonym. -/
def rootMonomialBasis (B : ℕ) : Module.Basis (Fin B →₀ ℕ) ℂ (RootPolynomial B) :=
  (MvPolynomial.basisMonomials (Fin B) ℂ).map (rootPolynomialEquiv B).symm.toLinearEquiv

@[simp] theorem rootMonomialBasis_apply (B : ℕ) (d : Fin B →₀ ℕ) :
    rootMonomialBasis B d = (show RootPolynomial B from MvPolynomial.monomial d 1) := rfl

/-- The labelled current-tensor basis. -/
def tensorCurrentBasis (B : ℕ) :
    Module.Basis (Fin B → ℕ × Fin 3) ℂ (⨂[ℂ]^B Cur) :=
  Basis.piTensorProduct (fun _ : Fin B => currentBasis)

@[simp] theorem tensorCurrentBasis_apply (B : ℕ) (q : Fin B → ℕ × Fin 3) :
    tensorCurrentBasis B q = PiTensorProduct.tprod ℂ (fun i => currentBasis (q i)) :=
  Basis.piTensorProduct_apply _ _

/-- Labelled current tensors are root polynomials with a finite color factor. -/
def rootTensorEquiv (B : ℕ) :
    (⨂[ℂ]^B Cur) ≃ₗ[ℂ] RootPolynomial B ⊗[ℂ] Color B :=
  (tensorCurrentBasis B).equiv
    ((rootMonomialBasis B).tensorProduct (Pi.basisFun ℂ (Fin B → Fin 3)))
    (tensorIndexEquiv B)

@[simp] theorem rootTensorEquiv_tprod (B : ℕ) (q : Fin B → ℕ × Fin 3) :
    rootTensorEquiv B (PiTensorProduct.tprod ℂ (fun i => currentBasis (q i))) =
      (show RootPolynomial B from MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i => (q i).1)) 1) ⊗ₜ[ℂ]
        Pi.basisFun ℂ (Fin B → Fin 3) (fun i => (q i).2) := by
  rw [← tensorCurrentBasis_apply, rootTensorEquiv, Module.Basis.equiv_apply,
    Module.Basis.tensorProduct_apply]
  rfl

@[simp] theorem rootTensorEquiv_word (B : ℕ) (a : Fin B → ℕ) (c : Fin B → Fin 3) :
    rootTensorEquiv B (PiTensorProduct.tprod ℂ (fun i => currentBasis (a i, c i))) =
      (show RootPolynomial B from MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm a) 1) ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin B → Fin 3) c :=
  rootTensorEquiv_tprod B (fun i => (a i, c i))

/-- A coefficient shift acts independently on each labelled mode. -/
theorem tensorDeriv_currentWord (m B : ℕ) (a : Fin B → ℕ) (c : Fin B → Fin 3) :
    tensorDeriv B (Modules.coefficientShift m)
        (PiTensorProduct.tprod ℂ (fun i => currentBasis (a i, c i))) =
      ∑ i : Fin B, PiTensorProduct.tprod ℂ
        (fun j => currentBasis (Function.update a i (a i + m) j, c j)) := by
  rw [tensorDeriv_tprod]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases hij : j = i
  · subst j
    simp [BGGBridge.TopAlternants.coefficientShift_currentBasis, Nat.add_comm, pow_add]
  · simp [Function.update_of_ne hij]

/-- Coefficient shifting is multiplication by the corresponding power sum. -/
theorem rootTensorEquiv_shift_word (m B : ℕ) (a : Fin B → ℕ) (c : Fin B → Fin 3) :
    rootTensorEquiv B (tensorDeriv B (Modules.coefficientShift m)
      (PiTensorProduct.tprod ℂ (fun i => currentBasis (a i, c i)))) =
      (show RootPolynomial B from MvPolynomial.psum (Fin B) ℂ m *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1) ⊗ₜ[ℂ]
        Pi.basisFun ℂ (Fin B → Fin 3) c := by
  rw [tensorDeriv_currentWord, map_sum]
  simp only [rootTensorEquiv_word]
  change (∑ i : Fin B, (MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (Function.update a i (a i + m))) 1 : RootPolynomial B)
      ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin B → Fin 3) c) = _
  simp only [MvPolynomial.psum, Finset.sum_mul, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro i _
  have he : Finsupp.equivFunOnFinite.symm (Function.update a i (a i + m)) =
      Finsupp.single i m + Finsupp.equivFunOnFinite.symm a := by
    ext j
    by_cases h : j = i
    · subst j; simp [Nat.add_comm]
    · simp [h, Ne.symm h, Function.update_of_ne h]
  rw [he]

/-- The polynomial tensor model intertwines the existing shift operators. -/
theorem rootTensorEquiv_coefficientShift (m B : ℕ) (x : ⨂[ℂ]^B Cur) :
    rootTensorEquiv B (tensorDeriv B (Modules.coefficientShift m) x) =
      LinearMap.rTensor (Color B)
        (LinearMap.mulLeft ℂ (show RootPolynomial B from MvPolynomial.psum (Fin B) ℂ m))
        (rootTensorEquiv B x) := by
  have he : (rootTensorEquiv B).toLinearMap.comp (tensorDeriv B (Modules.coefficientShift m)) =
      (LinearMap.rTensor (Color B)
        (LinearMap.mulLeft ℂ (show RootPolynomial B from MvPolynomial.psum (Fin B) ℂ m))).comp
        (rootTensorEquiv B).toLinearMap := by
    apply (tensorCurrentBasis B).ext
    intro q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorCurrentBasis_apply]
    rw [rootTensorEquiv_tprod, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply]
    exact rootTensorEquiv_shift_word m B (fun i => (q i).1) (fun i => (q i).2)
  exact LinearMap.congr_fun he x
end KhanSL2.PolynomialBGG
