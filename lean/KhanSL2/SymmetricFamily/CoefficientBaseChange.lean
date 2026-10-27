module

public import KhanSL2.SymmetricFamily.ExteriorCurrent

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Genuine scalar extension of current coefficient modules. The action is
induced from the original coefficient-linear current action on every tensor. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily

variable (R : Type*) [CommRing R] [Algebra ℂ R]
variable (M : Type*) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]

/-- The original current action respects the specified coefficient scalars. -/
class CoefficientLinearCurrent : Prop where
  lie_smul : ∀ (x : BGG.Current) (r : R) (m : M), ⁅x,r • m⁆ = r • ⁅x,m⁆

variable [CoefficientLinearCurrent R M]

/-- The original current endomorphism bundled over its coefficient ring. -/
def currentCoefficientEnd (x : BGG.Current) : Module.End R M where
  toFun m := ⁅x,m⁆
  map_add' m n := lie_add x m n
  map_smul' r m := CoefficientLinearCurrent.lie_smul x r m

variable (A : Type*) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]

/-- A separate interpretation of the actual scalar-extended tensor module. -/
def CoefficientBaseChange : Type _ := A ⊗[R] M

instance : AddCommGroup (CoefficientBaseChange R M A) :=
  inferInstanceAs (AddCommGroup (A ⊗[R] M))
instance : Module A (CoefficientBaseChange R M A) :=
  inferInstanceAs (Module A (A ⊗[R] M))
instance : Module R (CoefficientBaseChange R M A) :=
  inferInstanceAs (Module R (A ⊗[R] M))
instance : Module ℂ (CoefficientBaseChange R M A) :=
  inferInstanceAs (Module ℂ (A ⊗[R] M))
instance : IsScalarTower ℂ A (CoefficientBaseChange R M A) :=
  inferInstanceAs (IsScalarTower ℂ A (A ⊗[R] M))
instance : IsScalarTower ℂ R (CoefficientBaseChange R M A) :=
  inferInstanceAs (IsScalarTower ℂ R (A ⊗[R] M))

/-- Forget only the current-module wrapper. -/
def coefficientBaseChangeEquiv : CoefficientBaseChange R M A ≃ₗ[A] A ⊗[R] M := LinearEquiv.refl A _

/-- Extend the actual coefficient-linear current endomorphism. -/
def currentBaseChangeEnd (x : BGG.Current) : Module.End A (CoefficientBaseChange R M A) :=
  (currentCoefficientEnd R M x).baseChange A

instance coefficientBaseChangeLieRingModule : LieRingModule BGG.Current (CoefficientBaseChange R M A) where
  bracket x v := currentBaseChangeEnd R M A x v
  add_lie x y v := by
    have h : currentCoefficientEnd R M (x+y) = currentCoefficientEnd R M x + currentCoefficientEnd R M y := by
      apply LinearMap.ext
      intro m
      exact add_lie x y m
    have hh := congrArg (fun f : Module.End R M => f.baseChange A) h
    rw [LinearMap.baseChange_add] at hh
    exact LinearMap.congr_fun hh v
  lie_add x v w := map_add (currentBaseChangeEnd R M A x) v w
  leibniz_lie x y v := by
    have h : currentCoefficientEnd R M x * currentCoefficientEnd R M y =
        currentCoefficientEnd R M ⁅x,y⁆ + currentCoefficientEnd R M y * currentCoefficientEnd R M x := by
      apply LinearMap.ext
      intro m
      exact leibniz_lie x y m
    have hh := congrArg (fun f : Module.End R M => f.baseChange A) h
    simp only [LinearMap.baseChange_mul, LinearMap.baseChange_add] at hh
    exact LinearMap.congr_fun hh v

instance coefficientBaseChangeLieModule : LieModule ℂ BGG.Current (CoefficientBaseChange R M A) where
  lie_smul c x v := (currentBaseChangeEnd R M A x).map_smul_of_tower c v
  smul_lie c x v := by
    have h : currentCoefficientEnd R M (c • x) =
        algebraMap ℂ R c • currentCoefficientEnd R M x := by
      apply LinearMap.ext
      intro m
      change ⁅c • x,m⁆ = algebraMap ℂ R c • ⁅x,m⁆
      rw [IsScalarTower.algebraMap_smul]
      exact LieModule.smul_lie (R := ℂ) c x m
    have hh := congrArg (fun f : Module.End R M => f.baseChange A) h
    rw [LinearMap.baseChange_smul] at hh
    have he := LinearMap.congr_fun hh v
    change (currentCoefficientEnd R M (c • x)).baseChange A v =
      c • (currentCoefficientEnd R M x).baseChange A v
    simpa only [LinearMap.smul_apply, IsScalarTower.algebraMap_smul] using he

omit [Algebra ℂ R] [Module ℂ M] [IsScalarTower ℂ R M]
  [LieModule ℂ BGG.Current M] [Algebra ℂ A] [IsScalarTower ℂ R A] in
/-- The extended action is exactly the original action in the coefficient tensor factor. -/
theorem coefficientBaseChange_lie_tmul (x : BGG.Current) (a : A) (m : M) :
    ⁅x,(show CoefficientBaseChange R M A from a ⊗ₜ[R] m)⁆ =
      (show CoefficientBaseChange R M A from a ⊗ₜ[R] ⁅x,m⁆) := rfl

/-- The extended current action is linear over the new coefficient ring. -/
instance coefficientBaseChangeCoefficientLinear :
    CoefficientLinearCurrent A (CoefficientBaseChange R M A) where
  lie_smul x a v := (currentBaseChangeEnd R M A x).map_smul a v

instance coefficientBaseChange_finite [Module.Finite R M] :
    Module.Finite A (CoefficientBaseChange R M A) :=
  inferInstanceAs (Module.Finite A (A ⊗[R] M))

/-- The actual symmetric coefficients satisfy the required coefficient linearity. -/
instance symmetricPower_coefficientLinear (k : ℕ) :
    CoefficientLinearCurrent (Conditional.CoefficientRing k) (Macdonald.symmetricPower k) where
  lie_smul := current_lie_symmetricCoefficient_smul k

/-- The original degree-k NB coefficients satisfy the same condition. -/
instance exteriorPower_coefficientLinear (k : ℕ) :
    CoefficientLinearCurrent (Conditional.CoefficientRing k) (⋀[ℂ]^k BGG.Current) where
  lie_smul := current_lie_exteriorCoefficient_smul k

end KhanSL2.SymmetricFamily
