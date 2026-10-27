module

public import KhanSL2.SymmetricFamily.SymmetricChartCurrent

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Coprime factorization of the actual coefficient specialization at a
prescribed product polynomial, retaining the original current action. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The actual coefficient chart of a prescribed coprime monic product. -/
def factorCoprimeChart (r s : ℕ) (f g : Polynomial A)
    (hf : f.Monic) (hg : g.Monic) (hfr : f.natDegree=r) (hgs : g.natDegree=s)
    (hcop : IsCoprime f g) :
    letI := factorCoefficientAlgebra (r+s) (f*g)
    Collision.ChartData (r+s) r s A := by
  letI := factorCoefficientAlgebra (r+s) (f*g)
  exact
    { f₁ := f
      f₂ := g
      monic₁ := hf
      monic₂ := hg
      degree₁ := hfr
      degree₂ := hgs
      factor := Collision.univPoly_map_coeffHom (hf.mul hg) (by rw [hf.natDegree_mul hg,hfr,hgs])
      coprime := hcop }

/-- The genuine normalized current-module factorization over the common coefficient algebra. -/
def factorSymmetricCoprimeEquiv (r s : ℕ) (f g : Polynomial A)
    (hf : f.Monic) (hg : g.Monic) (hfr : f.natDegree=r) (hgs : g.natDegree=s)
    (hcop : IsCoprime f g) :
    FactorSymmetric (r+s) (f*g) ≃ₗ⁅ℂ,BGG.Current⁆
      BalancedCoefficients A (FactorSymmetric r f) (FactorSymmetric s g) := by
  letI := factorCoefficientAlgebra (r+s) (f*g)
  letI : IsScalarTower ℂ (Depth.RB (r+s)) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (r+s) (f*g)).commutes z).symm
  exact symmetricChartCurrentEquiv (factorCoprimeChart r s f g hf hg hfr hgs hcop)

/-- At a complex point, this is an equivalence with the actual ordinary tensor of the two fibres. -/
def factorSymmetricCoprimeComplexEquiv (r s : ℕ) (f g : Polynomial ℂ)
    (hf : f.Monic) (hg : g.Monic) (hfr : f.natDegree=r) (hgs : g.natDegree=s)
    (hcop : IsCoprime f g) :
    FactorSymmetric (r+s) (f*g) ≃ₗ⁅ℂ,BGG.Current⁆
      FactorSymmetric r f ⊗[ℂ] FactorSymmetric s g :=
  (factorSymmetricCoprimeEquiv r s f g hf hg hfr hgs hcop).trans
    (balancedComplexEquiv (FactorSymmetric r f) (FactorSymmetric s g))

end KhanSL2.SymmetricFamily
