module

public import KhanSL2.SymmetricFamily.FactorCoprime
public import KhanSL2.Factorization.ResultantChartFactorFlat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The universal ordered coprime chart is a genuine nonzero coefficient
algebra in every pair of degrees, including degree zero. -/
noncomputable section
open Polynomial
namespace KhanSL2.SymmetricFamily
open Factorization.ChartBridge

instance productChart_nontrivial (r s : ℕ) : Nontrivial (ProductChart r s) := by
  have hf : (X ^ r : Polynomial ℂ).Monic := monic_X.pow r
  have hg : ((X - C (1:ℂ)) ^ s).Monic := (monic_X_sub_C (1:ℂ)).pow s
  have hcop : IsCoprime (X ^ r : Polynomial ℂ) ((X - C (1:ℂ)) ^ s) := by
    apply IsCoprime.pow
    refine ⟨1,-1,?_⟩
    simp
  let := factorCoefficientAlgebra (r+s) ((X ^ r : Polynomial ℂ) * (X-C (1:ℂ)) ^ s)
  let c := factorCoprimeChart r s (X^r) ((X-C (1:ℂ))^s) hf hg
    (by simp) (by rw [natDegree_pow,natDegree_X_sub_C,mul_one]) hcop
  exact (productChartSpecialization c).toRingHom.domain_nontrivial

/-- The literal universal factors form chart data for the original product action. -/
def productChartData (r s : ℕ) : Collision.ChartData (r+s) r s (ProductChart r s) where
  f₁ := (firstOnProductChart r s).val
  f₂ := (secondOnProductChart r s).val
  monic₁ := (firstOnProductChart r s).monic
  monic₂ := (secondOnProductChart r s).monic
  degree₁ := (firstOnProductChart r s).natDegree
  degree₂ := (secondOnProductChart r s).natDegree
  factor := (productChart_factorization r s).symm
  coprime := productChart_isCoprime r s

end KhanSL2.SymmetricFamily
