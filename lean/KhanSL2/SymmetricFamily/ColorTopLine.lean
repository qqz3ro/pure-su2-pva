module

public import KhanSL2.SymmetricFamily.ColorAnnihilator
public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The top Cartan eigenvectors of any root/color multiplicity module are
exactly the coefficient multiples of the single all-e color tensor. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

variable (k : ℕ) (Q : Type*) [AddCommGroup Q] [Module ℂ Q]

/-- Read the literal finite color coefficients of a root/color tensor. -/
def colorCoordinates : (Q ⊗[ℂ] Color k) ≃ₗ[ℂ] ((Fin k → Fin 3) → Q) :=
  TensorProduct.piScalarRight ℂ ℂ Q (Fin k → Fin 3)

@[simp] theorem colorCoordinates_tmul (q : Q) (v : Color k) (c : Fin k → Fin 3) :
    colorCoordinates k Q (q ⊗ₜ[ℂ] v) c = v c • q := by
  rw [colorCoordinates, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

@[simp] theorem colorCoordinates_basis_tmul (q : Q) (c j : Fin k → Fin 3) :
    colorCoordinates k Q (q ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin k → Fin 3) c) j =
      if j = c then q else 0 := by
  classical
  rw [colorCoordinates_tmul]
  by_cases h : j = c
  · subst j
    simp
  · simp [Pi.basisFun_apply, h, Ne.symm h]

/-- The concrete color coordinate has its specified even Cartan eigenvalue. -/
theorem colorCoordinates_cartan (x : Q ⊗[ℂ] Color k) (c : Fin k → Fin 3) :
    colorCoordinates k Q
      (LinearMap.lTensor Q (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)) x) c =
        (2*(colorWordHalfWeight c : ℂ)) • colorCoordinates k Q x c := by
  have h : ((LinearMap.proj c).comp (colorCoordinates k Q).toLinearMap).comp
      (LinearMap.lTensor Q (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h))) =
      (2*(colorWordHalfWeight c : ℂ)) •
        ((LinearMap.proj c).comp (colorCoordinates k Q).toLinearMap) := by
    apply ((Module.Free.chooseBasis ℂ Q).tensorProduct (Pi.basisFun ℂ (Fin k → Fin 3))).ext
    rintro ⟨i,j⟩
    simp only [Module.Basis.tensorProduct_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe, LinearMap.lTensor_tmul, colorCartan_basis,
      TensorProduct.tmul_smul, map_smul, Pi.smul_apply, LinearMap.smul_apply,
      colorCoordinates_basis_tmul]
    by_cases hj : c = j
    · subst j
      simp
    · simp [hj]
  exact LinearMap.congr_fun h x

/-- All non-top color coordinates of a top eigenvector vanish. -/
theorem colorCoordinates_top_eq_zero (x : Q ⊗[ℂ] Color k)
    (hx : LinearMap.lTensor Q (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)) x =
      (2*(k : ℂ)) • x) (c : Fin k → Fin 3) (hc : c ≠ fun _ => 0) :
    colorCoordinates k Q x c = 0 := by
  have h := congrArg (fun y => colorCoordinates k Q y c) hx
  rw [colorCoordinates_cartan, map_smul, Pi.smul_apply] at h
  have hw : (colorWordHalfWeight c : ℂ) ≠ (k : ℂ) := by
    exact_mod_cast (ne_of_lt (colorWordHalfWeight_lt_top c hc))
  have hs : 2*(colorWordHalfWeight c : ℂ) ≠ 2*(k : ℂ) := by
    intro he
    exact hw (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he)
  have hz : (2*(colorWordHalfWeight c : ℂ)-2*(k : ℂ)) • colorCoordinates k Q x c = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hs)

/-- The top color eigenspace is the coefficient space times the one all-e word. -/
theorem exists_root_tmul_top_of_cartan (x : Q ⊗[ℂ] Color k)
    (hx : LinearMap.lTensor Q (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)) x =
      (2*(k : ℂ)) • x) :
    ∃ q : Q, x = q ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin k → Fin 3) (fun _ => 0) := by
  classical
  refine ⟨colorCoordinates k Q x (fun _ => 0),?_⟩
  apply (colorCoordinates k Q).injective
  funext c
  rw [colorCoordinates_basis_tmul]
  by_cases hc : c = fun _ => 0
  · simp only [hc, ite_true]
  · rw [if_neg hc]
    exact colorCoordinates_top_eq_zero k Q x hx c hc

end KhanSL2.SymmetricFamily
