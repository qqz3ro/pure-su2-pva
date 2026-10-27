module

public import KhanSL2.Factorization.BalancedCoefficients

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
variable (K : Type) [CommRing K] [Algebra A K] [Algebra ℂ K] [IsScalarTower ℂ A K]

/-- Scalar extension commutes with balanced tensor coefficients, retaining the
actual current actions on both sides. -/
def balancedBaseChangeLinearEquiv : CoefficientBaseChange A (BalancedCoefficients A M N) K ≃ₗ[K]
    BalancedCoefficients K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) :=
  TensorProduct.AlgebraTensorModule.distribBaseChange A K M N

omit [Algebra ℂ A] [Module ℂ M] [IsScalarTower ℂ A M] [LieModule ℂ Current M]
  [Module ℂ N] [IsScalarTower ℂ A N] [LieModule ℂ Current N]
  [Algebra ℂ K] [IsScalarTower ℂ A K] in
theorem balancedBaseChangeLinearEquiv_lie (x:Current)
    (z:CoefficientBaseChange A (BalancedCoefficients A M N) K) :
    balancedBaseChangeLinearEquiv A M N K ⁅x,z⁆ =
      ⁅x,balancedBaseChangeLinearEquiv A M N K z⁆ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [lie_add,map_add,hz,hw]
  | tmul k z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [TensorProduct.tmul_add,lie_add,map_add,hz,hw]
    | tmul m n =>
      change TensorProduct.AlgebraTensorModule.distribBaseChange A K M N
        (k⊗ₜ[A](⁅x,m⁆⊗ₜ[A]n+m⊗ₜ[A]⁅x,n⁆)) =
          (k⊗ₜ[A]⁅x,m⁆)⊗ₜ[K](1⊗ₜ[A]n)+(k⊗ₜ[A]m)⊗ₜ[K](1⊗ₜ[A]⁅x,n⁆)
      rw [TensorProduct.tmul_add,map_add,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

/-- The genuine scalar/tensor comparison as an actual current-module equivalence. -/
def balancedBaseChangeEquiv : CoefficientBaseChange A (BalancedCoefficients A M N) K ≃ₗ⁅ℂ,Current⁆
    BalancedCoefficients K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) where
  __ := (balancedBaseChangeLinearEquiv A M N K).restrictScalars ℂ
  map_lie' {x z} := balancedBaseChangeLinearEquiv_lie A M N K x z

omit [Module ℂ M] [IsScalarTower ℂ A M] [LieModule ℂ Current M]
  [Module ℂ N] [IsScalarTower ℂ A N] [LieModule ℂ Current N] in
@[simp] theorem balancedBaseChangeEquiv_tmul (k:K) (m:M) (n:N) :
    balancedBaseChangeEquiv A M N K
      (show CoefficientBaseChange A (BalancedCoefficients A M N) K from k⊗ₜ[A](m⊗ₜ[A]n)) =
        (show BalancedCoefficients K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)
          from (k⊗ₜ[A]m)⊗ₜ[K](1⊗ₜ[A]n)) := rfl

end KhanSL2.Factorization


