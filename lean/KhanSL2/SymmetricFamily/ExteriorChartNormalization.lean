module

public import KhanSL2.SymmetricFamily.ExteriorChartCurrent

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The normalized original coefficient map is precisely the actual chart
current equivalence, with the inverse binomial factor made explicit. -/
noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

theorem exteriorChartCurrentMap_unit (c : Collision.ChartData (r+s) r s A)
    (p : (⋀[ℂ]^(r+s) BGG.Current)) :
    exteriorChartCurrentMap c
      (coefficientBaseChangeUnit (Depth.RB (r+s)) ((⋀[ℂ]^(r+s) BGG.Current)) A p) =
        (Nat.choose (r+s) r : ℂ)⁻¹ • specializedExteriorCoproduct c p := by
  have hc : (Nat.choose (r+s) r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_right r s)))
  have h := congrArg
    (fun z : BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) =>
      (Nat.choose (r+s) r : ℂ)⁻¹ • z) (specializedExteriorCoproduct_chart c p)
  change (show BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) from
    exteriorChartEquiv c (coefficientBaseChangeUnit (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A p)) = _
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using h.symm

/-- The normalized original map is bijective on every actual coprime coefficient chart. -/
theorem exteriorChartCurrentMap_bijective (c : Collision.ChartData (r+s) r s A) :
    Function.Bijective (exteriorChartCurrentMap c) := (exteriorChartCurrentEquiv c).toLinearEquiv.bijective

end KhanSL2.SymmetricFamily
