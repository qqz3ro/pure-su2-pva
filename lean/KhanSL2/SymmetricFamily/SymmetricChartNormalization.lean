module

public import KhanSL2.SymmetricFamily.SymmetricChartCurrent

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The normalized original coefficient map is precisely the actual chart
current equivalence, with the inverse binomial factor made explicit. -/
noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

theorem symmetricChartCurrentMap_unit (c : Collision.ChartData (r+s) r s A)
    (p : symmetricPower (r+s)) :
    symmetricChartCurrentMap c
      (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A p) =
        (Nat.choose (r+s) r : ℂ)⁻¹ • specializedSymmetricCoproduct c p := by
  have hc : (Nat.choose (r+s) r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_right r s)))
  have h := congrArg
    (fun z : BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) =>
      (Nat.choose (r+s) r : ℂ)⁻¹ • z) (specializedSymmetricCoproduct_chart c p)
  change (show BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) from
    symmetricChartEquiv c (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A p)) = _
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using h.symm

/-- The normalized original map is bijective on every actual coprime coefficient chart. -/
theorem symmetricChartCurrentMap_bijective (c : Collision.ChartData (r+s) r s A) :
    Function.Bijective (symmetricChartCurrentMap c) := (symmetricChartCurrentEquiv c).toLinearEquiv.bijective

end KhanSL2.SymmetricFamily
