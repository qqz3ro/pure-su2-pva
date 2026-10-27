module

public import KhanSL2.SymmetricFamily.LocalCoefficients
public import KhanSL2.SymmetricFamily.ExteriorBaseChangedAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The literal normalized root/color inclusion of the original one-point
exterior coefficient fibre, including its actual Current action. -/

noncomputable section
namespace KhanSL2.SymmetricFamily

/-- The original alternating section specialized at the divisor k[a]. -/
def localExteriorRootInclusion (k : ℕ) (a : ℂ) :
    LocalExteriorFibre k a →ₗ[ℂ] LocalRootColors k a := by
  letI := localCoefficientAlgebra k a
  letI : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  exact exteriorCoefficientRootInclusion k ℂ

theorem localExteriorRootInclusion_injective (k : ℕ) (a : ℂ) :
    Function.Injective (localExteriorRootInclusion k a) := by
  let := localCoefficientAlgebra k a
  let : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  exact exteriorCoefficientRootInclusion_injective k ℂ

theorem localExteriorRootInclusion_mode (k : ℕ) (a : ℂ) (n : ℕ) (x : BGG.G)
    (v : LocalExteriorFibre k a) :
    localExteriorRootInclusion k a ⁅BGG.mode n x,v⁆ =
      localRootColorMode k a n (LieAlgebra.ad ℂ BGG.G x)
        (localExteriorRootInclusion k a v) := by
  let := localCoefficientAlgebra k a
  let : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  exact exteriorCoefficientRootInclusion_mode k ℂ n x v

end KhanSL2.SymmetricFamily
