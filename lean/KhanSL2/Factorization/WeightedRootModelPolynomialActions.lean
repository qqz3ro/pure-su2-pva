module

public import KhanSL2.Factorization.WeightedRootModelInvariants
public import KhanSL2.Factorization.OrbitStabilizerTensorInvariants
public import KhanSL2.Macdonald.StrongBridgeRootModel
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open MvPolynomial FiberTransport

/-- Honest renaming action on one alphabet of ordinary root polynomials. -/
def polynomialAction (k : ℕ) : Equiv.Perm (Fin k) →* Module.End ℂ (MvPolynomial (Fin k) ℂ) where
  toFun σ := (rename σ).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    exact rename_id_apply p
  map_mul' σ τ := by
    apply LinearMap.ext
    intro p
    exact (rename_rename τ σ p).symm

/-- The odd alphabet carries its actual alternating character. -/
def alternatingPolynomialAction (k : ℕ) :
    Equiv.Perm (Fin k) →* Module.End ℂ (MvPolynomial (Fin k) ℂ) where
  toFun σ := (σ.sign : ℂ) • (rename σ).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    change ((1 : Equiv.Perm (Fin k)).sign : ℂ) • rename (1 : Equiv.Perm (Fin k)) p = p
    simp only [map_one,Units.val_one,Int.cast_one,one_smul]
    exact rename_id_apply p
  map_mul' σ τ := by
    apply LinearMap.ext
    intro p
    change ((σ*τ).sign : ℂ) • rename (σ*τ) p =
      (σ.sign : ℂ) • rename σ ((τ.sign : ℂ) • rename τ p)
    rw [map_smul,smul_smul,rename_rename]
    congr 1
    simp only [map_mul,Units.val_mul,Int.cast_mul]

/-- The existing alternating root space is exactly the fixed module for the honest signed action. -/
def alternatingFixedEquiv (q : ℕ) : SymmetricFamily.alternatingRootPolynomials q ≃ₗ[ℂ]
    fixedVectors (fun σ => alternatingPolynomialAction q σ) where
  toFun p := ⟨p.val,fun σ => by
    change (σ.sign : ℂ) • rename σ p.val = p.val
    simpa only [Equiv.Perm.sign_symm,Equiv.symm_symm] using p.property σ.symm⟩
  invFun p := ⟨p.val,fun σ => by
    have h := p.property σ.symm
    change (Equiv.Perm.sign σ.symm : ℂ) • rename σ.symm p.val = p.val at h
    simpa only [Equiv.Perm.sign_symm] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The existing symmetric root ring, viewed as its actual fixed vector space. -/
def symmetricFixedEquiv (r : ℕ) : symmetricSubalgebra (Fin r) ℂ ≃ₗ[ℂ]
    fixedVectors (fun σ => polynomialAction r σ) where
  toFun p := ⟨p.val,p.property⟩
  invFun p := ⟨p.val,p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The genuine product of two polynomial algebras, with its labelled sum alphabet. -/
def rawTensorEquiv (q r : ℕ) :
    (MvPolynomial (Fin q) ℂ ⊗[ℂ] MvPolynomial (Fin r) ℂ) ≃ₐ[ℂ] LabelledWeightedRing q r :=
  tensorEquivSum ℂ (Fin q) (Fin r) ℂ

theorem rawTensorEquiv_left (q r : ℕ) (p : MvPolynomial (Fin q) ℂ) :
    rawTensorEquiv q r (p ⊗ₜ[ℂ] 1) = rename Sum.inl p := by
  have h : (rawTensorEquiv q r).toAlgHom.comp Algebra.TensorProduct.includeLeft =
      (rename Sum.inl : MvPolynomial (Fin q) ℂ →ₐ[ℂ] LabelledWeightedRing q r) := by
    apply MvPolynomial.algHom_ext
    intro i
    change rawTensorEquiv q r (X i ⊗ₜ[ℂ] 1) = rename Sum.inl (X i)
    rw [rename_X]
    exact tensorEquivSum_X_tmul_one (R:=ℂ) (S:=ℂ) (σ:=Fin q) (ι:=Fin r) i
  exact AlgHom.congr_fun h p

theorem rawTensorEquiv_right (q r : ℕ) (p : MvPolynomial (Fin r) ℂ) :
    rawTensorEquiv q r (1 ⊗ₜ[ℂ] p) = rename Sum.inr p := by
  have h : (rawTensorEquiv q r).toAlgHom.comp Algebra.TensorProduct.includeRight =
      (rename Sum.inr : MvPolynomial (Fin r) ℂ →ₐ[ℂ] LabelledWeightedRing q r) := by
    apply MvPolynomial.algHom_ext
    intro i
    change rawTensorEquiv q r (1 ⊗ₜ[ℂ] X i) = rename Sum.inr (X i)
    rw [rename_X]
    exact tensorEquivSum_one_tmul_X (R:=ℂ) (S:=ℂ) (σ:=Fin q) (ι:=Fin r) i
  exact AlgHom.congr_fun h p

/-- The comparison is the specified rename-product map on pure tensors. -/
@[simp] theorem rawTensorEquiv_tmul (q r : ℕ) (p : MvPolynomial (Fin q) ℂ)
    (t : MvPolynomial (Fin r) ℂ) :
    rawTensorEquiv q r (p ⊗ₜ[ℂ] t) =
      (rename Sum.inl p : LabelledWeightedRing q r) * (rename Sum.inr t : LabelledWeightedRing q r) := by
  calc
    _ = rawTensorEquiv q r ((p ⊗ₜ[ℂ] 1)*(1 ⊗ₜ[ℂ] t)) := by simp
    _ = _ := by rw [map_mul,rawTensorEquiv_left,rawTensorEquiv_right]

end KhanSL2.Factorization.WeightedRootModel


