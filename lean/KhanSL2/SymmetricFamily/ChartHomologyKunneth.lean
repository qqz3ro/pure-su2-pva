module

public import KhanSL2.Factorization.ExternalFlatBalancedKunneth
public import KhanSL2.Factorization.ResultantChartProductScalars
public import KhanSL2.Macdonald.SpecializedHomologyCoproduct
public import KhanSL2.SymmetricFamily.SymmetricChartChainUnit

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open BGG Macdonald Factorization Factorization.ChartBridge
open scoped FactorHomologyScalars
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientTotalHomologyModule coefficientTotalHomologyIsScalarTower coefficientTotalHomologySMulCommClass
variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]
variable (c : Collision.ChartData (r+s) r s A)

/-- Künneth on a genuine etale chart uses exactly the original factor coefficient actions. -/
def symmetricChartBalancedKunnethEquiv [Algebra.Etale (Depth.RB (r+s)) A] :
    FactorSymmetricHomology r c.f₁ ⊗[A] FactorSymmetricHomology s c.f₂ ≃ₗ[A]
      BalancedTensorTotalHomology A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) := by
  let := factorCoefficientAlgebra r c.f₁
  let := factorCoefficientAlgebra s c.f₂
  let : IsScalarTower ℂ (Depth.RB r) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom r c.f₁).commutes z).symm
  let : IsScalarTower ℂ (Depth.RB s) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom s c.f₂).commutes z).symm
  let : Algebra (Depth.RB r ⊗[ℂ] Depth.RB s) A := chartProductAlgebra c
  let : Module.Flat (Depth.RB r ⊗[ℂ] Depth.RB s) A := chart_flat_product c
  exact externalBalancedKunnethEquiv (Depth.RB r) (Depth.RB s) (symmetricPower r) (symmetricPower s) A
    (chartProduct_tmul c)

/-- A tensor cycle inserted into the two actual factor coefficient families. -/
def symmetricChartTensorCycle
    (z : LinearMap.ker (relativeTensorDifferential (symmetricPower r) (symmetricPower s))) :
    LinearMap.ker (balancedTensorDifferential A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)) := by
  let := factorCoefficientAlgebra r c.f₁
  let := factorCoefficientAlgebra s c.f₂
  let : IsScalarTower ℂ (Depth.RB r) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom r c.f₁).commutes z).symm
  let : IsScalarTower ℂ (Depth.RB s) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom s c.f₂).commutes z).symm
  let : Algebra (Depth.RB r ⊗[ℂ] Depth.RB s) A := chartProductAlgebra c
  exact externalBaseChangedCycle (Depth.RB r) (Depth.RB s) (symmetricPower r) (symmetricPower s) A
    (externalBalancedChainEquiv (Depth.RB r) (Depth.RB s) (symmetricPower r) (symmetricPower s) A
      (chartProduct_tmul c))
    (externalBalancedChainEquiv_tmul (Depth.RB r) (Depth.RB s) (symmetricPower r) (symmetricPower s) A
      (chartProduct_tmul c)) 1 z

/-- Its underlying chain is literally the unchanged factor-unit tensor map. -/
theorem symmetricChartTensorCycle_val
    (z : LinearMap.ker (relativeTensorDifferential (symmetricPower r) (symmetricPower s))) :
    (symmetricChartTensorCycle c z).val = factorSymmetricChainTensorUnit r s c.f₁ c.f₂ z.val := by
  let := factorCoefficientAlgebra r c.f₁
  let := factorCoefficientAlgebra s c.f₂
  let : IsScalarTower ℂ (Depth.RB r) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom r c.f₁).commutes z).symm
  let : IsScalarTower ℂ (Depth.RB s) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom s c.f₂).commutes z).symm
  let : Algebra (Depth.RB r ⊗[ℂ] Depth.RB s) A := chartProductAlgebra c
  have hu : ∀ w : RelativeChains (symmetricPower r) ⊗[ℂ] RelativeChains (symmetricPower s),
      externalBalancedChainEquiv (Depth.RB r) (Depth.RB s) (symmetricPower r) (symmetricPower s) A
        (chartProduct_tmul c) (1 ⊗ₜ[Depth.RB r ⊗[ℂ] Depth.RB s] w) =
          factorSymmetricChainTensorUnit r s c.f₁ c.f₂ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [TensorProduct.tmul_add,map_add,hu,hv]
    | tmul u v =>
      rw [externalBalancedChainEquiv_tmul,one_smul]
      rfl
  exact hu z.val

/-- The specialized Künneth map sends the original inverse-Künneth class to the
class of precisely that tensor cycle inserted into the original factor families. -/
theorem symmetricChartBalancedKunnethEquiv_unit_inverse_mk [Algebra.Etale (Depth.RB (r+s)) A]
    (z : LinearMap.ker (relativeTensorDifferential (symmetricPower r) (symmetricPower s))) :
    symmetricChartBalancedKunnethEquiv c
      (tensorOverMap (factorSymmetricHomologyUnit r c.f₁) (factorSymmetricHomologyUnit s c.f₂)
        ((totalKunnethEquiv (symmetricPower r) (symmetricPower s)).symm (Submodule.Quotient.mk z))) =
      Submodule.Quotient.mk (symmetricChartTensorCycle c z) := by
  let := factorCoefficientAlgebra r c.f₁
  let := factorCoefficientAlgebra s c.f₂
  let : IsScalarTower ℂ (Depth.RB r) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom r c.f₁).commutes z).symm
  let : IsScalarTower ℂ (Depth.RB s) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom s c.f₂).commutes z).symm
  let : Algebra (Depth.RB r ⊗[ℂ] Depth.RB s) A := chartProductAlgebra c
  let : Module.Flat (Depth.RB r ⊗[ℂ] Depth.RB s) A := chart_flat_product c
  exact externalBalancedKunnethEquiv_unit_inverse_mk (Depth.RB r) (Depth.RB s)
    (symmetricPower r) (symmetricPower s) A (chartProduct_tmul c) z

end KhanSL2.SymmetricFamily
