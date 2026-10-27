module

public import KhanSL2.SymmetricFamily.ExteriorCoefficients

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The coefficient degree of the original NB representation is an actual current
submodule. Its induced Lie action and coefficient action are the original ones. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Conditional
open scoped KhanSL2.Conditional

/-- Degree-k exterior coefficients inside the already defined NB current module. -/
def exteriorCurrentSubmodule (k : ℕ) : LieSubmodule ℂ BGG.Current Current.NB where
  __ := (⋀[ℂ]^k BGG.Current)
  lie_mem hx := LieChains.derivExt_mem_exteriorPower _ hx

instance exteriorCurrentLieRingModule (k : ℕ) :
    LieRingModule BGG.Current (⋀[ℂ]^k BGG.Current) :=
  inferInstanceAs (LieRingModule BGG.Current (exteriorCurrentSubmodule k))

instance exteriorCurrentLieModule (k : ℕ) :
    LieModule ℂ BGG.Current (⋀[ℂ]^k BGG.Current) :=
  inferInstanceAs (LieModule ℂ BGG.Current (exteriorCurrentSubmodule k))

/-- The degree-restricted current action is exactly the original exterior derivation. -/
theorem exteriorCurrent_lie (k : ℕ) (x : BGG.Current) (v : ⋀[ℂ]^k BGG.Current) :
    ⁅x,v⁆ = exteriorDeriv k (LieAlgebra.ad ℂ BGG.Current x) v := rfl

/-- The original coefficient operator is a genuine current-module endomorphism. -/
def exteriorCurrentCoefficientEnd (m k : ℕ) :
    (⋀[ℂ]^k BGG.Current) →ₗ⁅ℂ,BGG.Current⁆ (⋀[ℂ]^k BGG.Current) where
  toLinearMap := exteriorDeriv k (Modules.coefficientShift m)
  map_lie' {x v} := by
    apply Subtype.ext
    exact Modules.coefficientPower_lie m x v.val

/-- The complete original current action commutes with the fixed coefficient ring. -/
theorem current_lie_exteriorCoefficient_smul (k : ℕ) (x : BGG.Current)
    (r : CoefficientRing k) (v : ⋀[ℂ]^k BGG.Current) : ⁅x,r • v⁆ = r • ⁅x,v⁆ := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates k)
    (LieModule.toEnd ℂ BGG.Current (⋀[ℂ]^k BGG.Current) x) _ r v
  intro i w
  simp only [LieModule.toEnd_apply_apply, exteriorCoefficientCoordinates_smul]
  exact ((exteriorCurrentCoefficientEnd (i.val+1) k).map_lie x w).symm

end KhanSL2.SymmetricFamily
