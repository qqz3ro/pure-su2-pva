module
public import KhanSL2.Factorization.KunnethTotalNaturality
@[expose] public section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG
variable {M N M' N' : Type}
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M'] [Module ℂ M'] [LieRingModule Current M'] [LieModule ℂ Current M']
  [AddCommGroup N'] [Module ℂ N'] [LieRingModule Current N'] [LieModule ℂ Current N']

/-- A named linear inverse keeps the canonical Künneth inverse opaque in naturality calculations. -/
def totalKunnethInverse (M N : Type)
    [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
    [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N] :
    TensorTotalHomology M N →ₗ[ℂ] TotalHomology M ⊗[ℂ] TotalHomology N :=
  (totalKunnethEquiv M N).symm.toLinearMap

theorem totalKunnethInverse_natural (f : M →ₗ⁅ℂ,Current⁆ M')
    (g : N →ₗ⁅ℂ,Current⁆ N') (z : TensorTotalHomology M N) :
    totalKunnethInverse M' N' (tensorCoefficientTotalHomologyMap f g z) =
      TensorProduct.map (coefficientTotalHomologyMap f) (coefficientTotalHomologyMap g)
        (totalKunnethInverse M N z) := totalKunnethEquiv_symm_natural f g z

end KhanSL2.Factorization
