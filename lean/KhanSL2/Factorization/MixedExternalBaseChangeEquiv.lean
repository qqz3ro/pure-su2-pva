module

public import KhanSL2.Factorization.MixedExternalBaseChangeInverse

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Factorization.MixedExternal

variable (R S A : Type) [CommRing R] [CommRing S] [CommRing A]
  [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ A]
  [Algebra R A] [Algebra S A] [Algebra (R ⊗[ℂ] S) A]
  [IsScalarTower ℂ R A] [IsScalarTower ℂ S A]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
variable (h : ∀ r : R, ∀ s : S, algebraMap (R ⊗[ℂ] S) A (r ⊗ₜ[ℂ] s) =
  algebraMap R A r * algebraMap S A s)

include h

theorem inverse_forward (z : Source R S A M N) :
    inverse R S A M N h (forward R S A M N h z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul a z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [TensorProduct.tmul_add,map_add,hz,hw]
    | tmul m n => rw [forward_tmul,inverse_tmul,mul_one]

theorem forward_inverse (z : Target R S A M N) :
    forward R S A M N h (inverse R S A M N h z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul z w =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z t hz ht => simp only [TensorProduct.add_tmul,map_add,hz,ht]
    | tmul a m =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w t hw ht => simp only [TensorProduct.tmul_add,map_add,hw,ht]
      | tmul b n =>
        rw [inverse_tmul,forward_tmul]
        have ha : (a*b) ⊗ₜ[R] m = b • (a ⊗ₜ[R] m) := by
          simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_comm]
        rw [ha,TensorProduct.smul_tmul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]

/-- Base change of the tensor with independent original coefficient actions is the
balanced tensor of the two original scalar extensions, by the literal elementary formula. -/
def equiv : Source R S A M N ≃ₗ[A] Target R S A M N where
  toLinearMap := forward R S A M N h
  invFun := inverse R S A M N h
  left_inv := inverse_forward R S A M N h
  right_inv := forward_inverse R S A M N h

@[simp] theorem equiv_tmul (a : A) (m : M) (n : N) :
    equiv R S A M N h (a ⊗ₜ[R ⊗[ℂ] S] (m ⊗ₜ[ℂ] n)) =
      (a ⊗ₜ[R] m) ⊗ₜ[A] ((1:A) ⊗ₜ[S] n) := forward_tmul R S A M N h a m n

@[simp] theorem equiv_symm_tmul (a b : A) (m : M) (n : N) :
    (equiv R S A M N h).symm ((a ⊗ₜ[R] m) ⊗ₜ[A] (b ⊗ₜ[S] n)) =
      (a*b) ⊗ₜ[R ⊗[ℂ] S] (show ExternalTensor R S M N from m ⊗ₜ[ℂ] n) := inverse_tmul R S A M N h a b m n

end KhanSL2.Factorization.MixedExternal
