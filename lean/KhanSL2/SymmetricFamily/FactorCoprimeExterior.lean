module

public import KhanSL2.SymmetricFamily.FactorCoprime
public import KhanSL2.SymmetricFamily.ExteriorChartCurrent

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Coprime splitting of the original exterior coefficient fibres, with their
unchanged current actions and the specified alternating coproduct. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Factorization

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Genuine exterior current-module factorization over the prescribed coefficient algebra. -/
def factorExteriorCoprimeEquiv (r s : ℕ) (f g : Polynomial A)
    (hf : f.Monic) (hg : g.Monic) (hfr : f.natDegree=r) (hgs : g.natDegree=s)
    (hcop : IsCoprime f g) :
    FactorExterior (r+s) (f*g) ≃ₗ⁅ℂ,BGG.Current⁆
      BalancedCoefficients A (FactorExterior r f) (FactorExterior s g) := by
  letI := factorCoefficientAlgebra (r+s) (f*g)
  letI : IsScalarTower ℂ (Depth.RB (r+s)) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (r+s) (f*g)).commutes z).symm
  exact exteriorChartCurrentEquiv (factorCoprimeChart r s f g hf hg hfr hgs hcop)

/-- At a complex point, the target is the actual ordinary tensor of the two exterior fibres. -/
def factorExteriorCoprimeComplexEquiv (r s : ℕ) (f g : Polynomial ℂ)
    (hf : f.Monic) (hg : g.Monic) (hfr : f.natDegree=r) (hgs : g.natDegree=s)
    (hcop : IsCoprime f g) :
    FactorExterior (r+s) (f*g) ≃ₗ⁅ℂ,BGG.Current⁆
      FactorExterior r f ⊗[ℂ] FactorExterior s g :=
  (factorExteriorCoprimeEquiv r s f g hf hg hfr hgs hcop).trans
    (balancedComplexEquiv (FactorExterior r f) (FactorExterior s g))

end KhanSL2.SymmetricFamily
