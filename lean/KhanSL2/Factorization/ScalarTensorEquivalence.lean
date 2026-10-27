module

public import KhanSL2.Factorization.ScalarTensorDegrees

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization.NonnegativeCone

variable {R : Type} [CommRing R]
variable (A : Type) [CommRing A] [Algebra R A]
variable (C D : ChainComplex (ModuleCat R) ℕ)
attribute [local instance] scalarTensorRestrictModule scalarTensorRestrictTower scalarTensorRestrictComm

/-- The inverse takes the coefficient unit back to the coefficient unit. -/
theorem scalarTensorDegreeInverse_unit (n:ℕ) (z:(tensorObj C D).X n) :
    scalarTensorDegreeInverse A C D n (scalarTensorDegreeUnit A C D n z) = 1⊗ₜ[R]z := by
  have he : ModuleCat.ofHom (((scalarTensorDegreeInverse A C D n).restrictScalars R).comp
      (scalarTensorDegreeUnit A C D n)) =
        ModuleCat.ofHom (TensorProduct.mk R A ((tensorObj C D).X n) 1) := by
    apply mapBifunctor.hom_ext
    intro p q h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change scalarTensorDegreeInverse A C D n
      (scalarTensorDegreeUnit A C D n (ιTensorObj C D p q n h t)) =
        1⊗ₜ[R]ιTensorObj C D p q n h t
    rw [scalarTensorDegreeUnit_inclusion, scalarTensorDegreeInverse_inclusion,
      LinearEquiv.symm_apply_apply]
    rfl
  exact congrArg (fun f => f.hom z) he

/-- The two explicit scalar/tensor maps are inverse on the scalar-extended source. -/
theorem scalarTensorDegreeInverse_map (n:ℕ) (z:A⊗[R](tensorObj C D).X n) :
    scalarTensorDegreeInverse A C D n (scalarTensorDegreeMap A C D n z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a z =>
    change scalarTensorDegreeInverse A C D n (a • scalarTensorDegreeUnit A C D n z) = a⊗ₜ[R]z
    rw [map_smul,scalarTensorDegreeInverse_unit, TensorProduct.smul_tmul',smul_eq_mul,mul_one]

/-- The two explicit scalar/tensor maps are inverse on the actual tensor degree sum. -/
theorem scalarTensorDegreeMap_inverse (n:ℕ) (z:(scalarTensorComplex A C D).X n) :
    scalarTensorDegreeMap A C D n (scalarTensorDegreeInverse A C D n z) = z := by
  have he : ModuleCat.ofHom ((scalarTensorDegreeMap A C D n).comp
      (scalarTensorDegreeInverse A C D n)) = 𝟙 ((scalarTensorComplex A C D).X n) := by
    apply mapBifunctor.hom_ext
    intro p q h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    obtain ⟨u,rfl⟩ :=
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q)).surjective t
    change scalarTensorDegreeMap A C D n
      (scalarTensorDegreeInverse A C D n
        (ιTensorObj (scalarComplex A C) (scalarComplex A D) p q n h
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q) u))) =
        ιTensorObj (scalarComplex A C) (scalarComplex A D) p q n h
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q) u)
    rw [scalarTensorDegreeInverse_inclusion,LinearEquiv.symm_apply_apply]
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add,hu,hv]
    | tmul a t =>
      change scalarTensorDegreeMap A C D n (a⊗ₜ[R]ιTensorObj C D p q n h t) = _
      exact scalarTensorDegreeMap_tmul_inclusion A C D p q n h a t
  exact congrArg (fun f => f.hom z) he

/-- Actual base change of the tensor degree sum, valid without flatness. -/
def scalarTensorDegreeEquiv (n:ℕ) :
    A⊗[R](tensorObj C D).X n ≃ₗ[A] (scalarTensorComplex A C D).X n where
  __ := scalarTensorDegreeMap A C D n
  invFun := scalarTensorDegreeInverse A C D n
  left_inv := scalarTensorDegreeInverse_map A C D n
  right_inv := scalarTensorDegreeMap_inverse A C D n

end KhanSL2.Factorization.NonnegativeCone

