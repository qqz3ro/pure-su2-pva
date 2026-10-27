module

public import KhanSL2.Factorization.FiniteBGGChartQuasiIso
public import KhanSL2.Factorization.FiniteBGGChartHomology
public import KhanSL2.Factorization.FiniteBGGFactorSide
public import KhanSL2.Factorization.DegreeBalancedKunneth
public import KhanSL2.Factorization.ResultantChartProductScalars

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open CategoryTheory
open scoped TensorProduct DirectSum
namespace KhanSL2.Factorization.BGGTransfer
open BGG Conditional SymmetricFamily ChartBridge
attribute [local instance] coefficientHomogeneousHomologyModule
  coefficientHomogeneousHomologyIsScalarTower coefficientHomogeneousHomologySMulCommClass

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra.Etale (Depth.RB (r+s)) A]

/-- The original K-module factors on every etale coprime chart. The construction
uses the actual exterior shuffle, the proved finite BGG contraction, and
external-variable Kunneth with joint chart flatness. -/
def chartFactorizationEquiv (hSym : SymmetricTensorShuffle) (hr : 0<r) (hs : 0<s)
    (c : Collision.ChartData (r+s) r s A) (p : ℕ) :
    (A ⊗[Depth.RB (r+s)] K (r+s) p) ≃ₗ[A] Collision.FactorSide c (K r) (K s) p := by
  letI : Algebra ℂ A := Collision.chartComplexAlgebra (B:=r+s)
  letI : IsScalarTower ℂ (Depth.RB (r+s)) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI := factorCoefficientAlgebra r c.f₁
  letI := factorCoefficientAlgebra s c.f₂
  letI : IsScalarTower ℂ (Depth.RB r) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom r c.f₁).commutes z).symm
  letI : IsScalarTower ℂ (Depth.RB s) A := IsScalarTower.of_algebraMap_eq
    fun z => ((Collision.coeffHom s c.f₂).commutes z).symm
  letI : Algebra (Depth.RB r ⊗[ℂ] Depth.RB s) A := chartProductAlgebra c
  letI : Module.Flat (Depth.RB r ⊗[ℂ] Depth.RB s) A := chart_flat_product c
  exact (sourceHomologyEquiv (r+s) A p).trans
    ((chartHomologyEquiv hSym hr hs c p).trans
      ((degreeBalancedKunnethEquiv (Depth.RB r) (Depth.RB s) A
        (⋀[ℂ]^r Current) (⋀[ℂ]^s Current) (chartProduct_tmul c) p).trans
          (exteriorFactorSideEquivK r s c.f₁ c.f₂ p)))

end KhanSL2.Factorization.BGGTransfer
namespace KhanSL2.Collision
open Conditional Factorization

/-- The only input here is the separately proved symmetric coefficient comparison;
every finite BGG, root-chart, fibre-detection and Kunneth step is discharged. -/
theorem kFactor_of_symmetricTensorShuffle (hSym : SymmetricTensorShuffle) (B : ℕ) : KFactor B := by
  intro r s hr hs h A _ _ _ c p
  subst B
  exact ⟨BGGTransfer.chartFactorizationEquiv hSym hr hs c p⟩

end KhanSL2.Collision
