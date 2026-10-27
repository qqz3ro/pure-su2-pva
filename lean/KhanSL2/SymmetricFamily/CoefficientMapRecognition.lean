module

public import KhanSL2.Factorization.RelativeChainsScalarExtension

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Recognize current-equivariance of an actual coefficient-linear map by its
values on the original coefficient tensors. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Factorization

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
  [CoefficientLinearCurrent R M]
variable (A : Type) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]
variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module A N]
  [IsScalarTower ℂ A N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
  [CoefficientLinearCurrent A N]

omit [LieModule ℂ BGG.Current M] in
/-- Pure coefficient tensors are coefficient multiples of their canonical unit insertion. -/
theorem coefficientBaseChange_tmul_eq_smul_unit (a : A) (m : M) :
    (show CoefficientBaseChange R M A from a ⊗ₜ[R] m) =
      a • coefficientBaseChangeUnit R M A m := by
  change a ⊗ₜ[R] m = a • ((1:A) ⊗ₜ[R] m)
  rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

/-- Current-equivariance on the original inputs proves current-equivariance
on the genuine full scalar extension. -/
def coefficientMapRecognition (f : CoefficientBaseChange R M A →ₗ[A] N)
    (hf : ∀ (x : BGG.Current) (m : M),
      f (coefficientBaseChangeUnit R M A ⁅x,m⁆) = ⁅x,f (coefficientBaseChangeUnit R M A m)⁆) :
    CoefficientBaseChange R M A →ₗ⁅ℂ,BGG.Current⁆ N where
  toLinearMap := f.restrictScalars ℂ
  map_lie' {x z} := by
    change f ⁅x,z⁆ = ⁅x,f z⁆
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [lie_add,map_add,hz,hw]
    | tmul a m =>
      change f (show CoefficientBaseChange R M A from a ⊗ₜ[R] ⁅x,m⁆) =
        ⁅x,f (show CoefficientBaseChange R M A from a ⊗ₜ[R] m)⁆
      calc
        f (show CoefficientBaseChange R M A from a ⊗ₜ[R] ⁅x,m⁆) =
            a • f (coefficientBaseChangeUnit R M A ⁅x,m⁆) :=
          (congrArg f (coefficientBaseChange_tmul_eq_smul_unit R M A a ⁅x,m⁆)).trans (f.map_smul a _)
        _ = a • ⁅x,f (coefficientBaseChangeUnit R M A m)⁆ := congrArg (fun n => a • n) (hf x m)
        _ = ⁅x,a • f (coefficientBaseChangeUnit R M A m)⁆ :=
          (CoefficientLinearCurrent.lie_smul x a _).symm
        _ = ⁅x,f (show CoefficientBaseChange R M A from a ⊗ₜ[R] m)⁆ :=
          congrArg (fun n : N => ⁅x,n⁆) ((f.map_smul a _).symm.trans
            (congrArg f (coefficientBaseChange_tmul_eq_smul_unit R M A a m).symm))

end KhanSL2.SymmetricFamily
