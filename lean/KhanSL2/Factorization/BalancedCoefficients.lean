module

public import KhanSL2.Factorization.RelativeChainsScalarExtension
public import Mathlib.Algebra.Lie.TensorProduct

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]

/-- The genuine tensor of coefficient families over their common base algebra. -/
def BalancedCoefficients : Type := M ⊗[A] N

instance : AddCommGroup (BalancedCoefficients A M N) := inferInstanceAs (AddCommGroup (M ⊗[A] N))
instance : Module A (BalancedCoefficients A M N) := inferInstanceAs (Module A (M ⊗[A] N))
instance : Module ℂ (BalancedCoefficients A M N) := inferInstanceAs (Module ℂ (M ⊗[A] N))
instance : IsScalarTower ℂ A (BalancedCoefficients A M N) :=
  inferInstanceAs (IsScalarTower ℂ A (M ⊗[A] N))

def balancedCurrentEnd (x : Current) : Module.End A (BalancedCoefficients A M N) :=
  TensorProduct.map (currentCoefficientEnd A M x) LinearMap.id +
    TensorProduct.map LinearMap.id (currentCoefficientEnd A N x)

omit [Algebra ℂ A] [Module ℂ M] [IsScalarTower ℂ A M] [LieModule ℂ Current M]
  [Module ℂ N] [IsScalarTower ℂ A N] [LieModule ℂ Current N] in
@[simp] theorem balancedCurrentEnd_tmul (x : Current) (m : M) (n : N) :
    balancedCurrentEnd A M N x (m ⊗ₜ[A] n) = ⁅x,m⁆ ⊗ₜ[A] n + m ⊗ₜ[A] ⁅x,n⁆ := rfl

instance balancedCoefficientsLieRingModule : LieRingModule Current (BalancedCoefficients A M N) where
  bracket x z := balancedCurrentEnd A M N x z
  add_lie x y z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,hz,hw]; abel
    | tmul m n => simp only [balancedCurrentEnd_tmul,add_lie,TensorProduct.add_tmul,TensorProduct.tmul_add]; abel
  lie_add x z w := map_add (balancedCurrentEnd A M N x) z w
  leibniz_lie x y z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,hz,hw]; abel
    | tmul m n =>
      simp only [balancedCurrentEnd_tmul,map_add]
      rw [leibniz_lie x y m,leibniz_lie x y n]
      simp only [TensorProduct.add_tmul,TensorProduct.tmul_add]
      abel

omit [Algebra ℂ A] [Module ℂ M] [IsScalarTower ℂ A M] [LieModule ℂ Current M]
  [Module ℂ N] [IsScalarTower ℂ A N] [LieModule ℂ Current N] in
@[simp] theorem balancedCoefficients_lie_tmul (x : Current) (m : M) (n : N) :
    ⁅x,(show BalancedCoefficients A M N from m ⊗ₜ[A] n)⁆ =
      (show BalancedCoefficients A M N from ⁅x,m⁆ ⊗ₜ[A] n + m ⊗ₜ[A] ⁅x,n⁆) := rfl

instance balancedCoefficientsLieModule : LieModule ℂ Current (BalancedCoefficients A M N) where
  lie_smul c x z := (balancedCurrentEnd A M N x).map_smul_of_tower c z
  smul_lie c x z := by
    change balancedCurrentEnd A M N (c • x) z = c • balancedCurrentEnd A M N x z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,smul_add,hz,hw]
    | tmul m n =>
      rw [balancedCurrentEnd_tmul,balancedCurrentEnd_tmul,
        LieModule.smul_lie (R:=ℂ) c x m,LieModule.smul_lie (R:=ℂ) c x n]
      simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_add]

instance balancedCoefficientsCoefficientLinear : CoefficientLinearCurrent A (BalancedCoefficients A M N) where
  lie_smul x a z := (balancedCurrentEnd A M N x).map_smul a z

/-- The canonical balancing quotient on the actual tensor coefficients. -/
def balancedCoefficientMap : M ⊗[ℂ] N →ₗ[ℂ] BalancedCoefficients A M N :=
  TensorProduct.lift
    { toFun m :=
        { toFun n := m ⊗ₜ[A] n
          map_add' n n' := TensorProduct.tmul_add m n n'
          map_smul' c n := TensorProduct.tmul_smul c m n }
      map_add' m m' := LinearMap.ext fun n => TensorProduct.add_tmul m m' n
      map_smul' c m := LinearMap.ext fun n => (TensorProduct.smul_tmul' c m n).symm }

omit [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N] in
@[simp] theorem balancedCoefficientMap_tmul (m : M) (n : N) :
    balancedCoefficientMap A M N (m ⊗ₜ[ℂ] n) = m ⊗ₜ[A] n := rfl

/-- Balancing the coefficients commutes with the original current action. -/
def balancedCoefficientLieHom : M ⊗[ℂ] N →ₗ⁅ℂ,Current⁆ BalancedCoefficients A M N where
  toLinearMap := balancedCoefficientMap A M N
  map_lie' {x z} := by
    change balancedCoefficientMap A M N ⁅x,z⁆ = ⁅x,balancedCoefficientMap A M N z⁆
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [lie_add,map_add,hz,hw]
    | tmul m n =>
      rw [TensorProduct.LieModule.lie_tmul_right,map_add,balancedCoefficientMap_tmul,
        balancedCoefficientMap_tmul,balancedCoefficientMap_tmul]
      rfl

omit [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N] in
theorem balancedCoefficientMap_surjective : Function.Surjective (balancedCoefficientMap A M N) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0,map_zero _⟩
  | add z w hz hw =>
    obtain ⟨u,rfl⟩ := hz
    obtain ⟨v,rfl⟩ := hw
    exact ⟨u+v,map_add _ _ _⟩
  | tmul m n => exact ⟨m ⊗ₜ[ℂ] n,rfl⟩

end KhanSL2.Factorization


