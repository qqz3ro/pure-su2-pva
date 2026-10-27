module

public import KhanSL2.SymmetricFamily.CoefficientBaseChange

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Actual current coefficient scalar extension is transitive. The equivalence
is the canonical tensor cancellation, with the original current actions. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M] [CoefficientLinearCurrent R M]
variable (A : Type) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]
variable (K : Type) [CommRing K] [Algebra A K] [Algebra R K] [Algebra ℂ K]
  [IsScalarTower R A K] [IsScalarTower ℂ A K] [IsScalarTower ℂ R K]

def coefficientBaseChangeAssocLinearEquiv :
    CoefficientBaseChange A (CoefficientBaseChange R M A) K ≃ₗ[K] CoefficientBaseChange R M K :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R A K K M

omit [Algebra ℂ R] [Module ℂ M] [IsScalarTower ℂ R M]
  [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M] [CoefficientLinearCurrent R M]
  [Algebra ℂ A] [IsScalarTower ℂ R A] [Algebra ℂ K] [IsScalarTower ℂ A K]
  [IsScalarTower ℂ R K] in
@[simp] theorem coefficientBaseChangeAssocLinearEquiv_tmul (k : K) (a : A) (m : M) :
    coefficientBaseChangeAssocLinearEquiv R M A K
      (show CoefficientBaseChange A (CoefficientBaseChange R M A) K from
        k ⊗ₜ[A] (show CoefficientBaseChange R M A from a ⊗ₜ[R] m)) =
      (show CoefficientBaseChange R M K from (a • k) ⊗ₜ[R] m) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R A K k m a

omit [Algebra ℂ R] [Module ℂ M] [IsScalarTower ℂ R M]
  [LieModule ℂ BGG.Current M] [Algebra ℂ A] [IsScalarTower ℂ R A]
  [Algebra ℂ K] [IsScalarTower ℂ A K] [IsScalarTower ℂ R K] in
theorem coefficientBaseChangeAssocLinearEquiv_lie (x : BGG.Current)
    (z : CoefficientBaseChange A (CoefficientBaseChange R M A) K) :
    coefficientBaseChangeAssocLinearEquiv R M A K ⁅x,z⁆ =
      ⁅x,coefficientBaseChangeAssocLinearEquiv R M A K z⁆ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [lie_add,map_add,hz,hw]
  | tmul k z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [lie_add,TensorProduct.tmul_add,map_add,hz,hw]
    | tmul a m =>
      change coefficientBaseChangeAssocLinearEquiv R M A K
        (show CoefficientBaseChange A (CoefficientBaseChange R M A) K from
          k ⊗ₜ[A] (show CoefficientBaseChange R M A from a ⊗ₜ[R] ⁅x,m⁆)) = _
      rw [coefficientBaseChangeAssocLinearEquiv_tmul,coefficientBaseChangeAssocLinearEquiv_tmul]
      rfl

def coefficientBaseChangeAssocEquiv :
    CoefficientBaseChange A (CoefficientBaseChange R M A) K ≃ₗ⁅ℂ,BGG.Current⁆
      CoefficientBaseChange R M K where
  __ := (coefficientBaseChangeAssocLinearEquiv R M A K).restrictScalars ℂ
  map_lie' {x z} := coefficientBaseChangeAssocLinearEquiv_lie R M A K x z

end KhanSL2.SymmetricFamily
