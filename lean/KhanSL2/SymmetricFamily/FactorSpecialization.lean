module

public import KhanSL2.SymmetricFamily.CoefficientBaseChangeAssoc
public import KhanSL2.SymmetricFamily.FactorCurrent
public import KhanSL2.Factorization.ResultantChartTensorEvaluation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! Further specialization of the actual coefficient family agrees with
specializing the coefficients of its defining polynomial. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald

variable {A K : Type} [CommRing A] [Algebra ℂ A] [CommRing K]
  [Algebra A K] [Algebra ℂ K] [IsScalarTower ℂ A K]

def factorSymmetricBaseChangeLinearEquiv (n : ℕ) (f : Polynomial A) :
    CoefficientBaseChange A (FactorSymmetric n f) K ≃ₗ[K]
      FactorSymmetric n (f.map (algebraMap A K)) := by
  letI := factorCoefficientAlgebra n f
  letI := factorCoefficientAlgebra n (f.map (algebraMap A K))
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  letI : IsScalarTower ℂ (Depth.RB n) K :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom n (f.map (algebraMap A K))).commutes z).symm
  letI : IsScalarTower (Depth.RB n) A K := IsScalarTower.of_algebraMap_eq fun z => by
    exact (AlgHom.congr_fun (Factorization.ChartBridge.coeffHom_map n f
      (IsScalarTower.toAlgHom ℂ A K)) z)
  exact coefficientBaseChangeAssocLinearEquiv (Depth.RB n) (symmetricPower n) A K

theorem factorSymmetricBaseChangeLinearEquiv_lie (n : ℕ) (f : Polynomial A)
    (x : BGG.Current) (z : CoefficientBaseChange A (FactorSymmetric n f) K) :
    factorSymmetricBaseChangeLinearEquiv (K:=K) n f ⁅x,z⁆ =
      ⁅x,factorSymmetricBaseChangeLinearEquiv (K:=K) n f z⁆ := by
  let := factorCoefficientAlgebra n f
  let := factorCoefficientAlgebra n (f.map (algebraMap A K))
  let : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  let : IsScalarTower ℂ (Depth.RB n) K :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom n (f.map (algebraMap A K))).commutes z).symm
  let : IsScalarTower (Depth.RB n) A K := IsScalarTower.of_algebraMap_eq fun z => by
    exact (AlgHom.congr_fun (Factorization.ChartBridge.coeffHom_map n f
      (IsScalarTower.toAlgHom ℂ A K)) z)
  exact coefficientBaseChangeAssocLinearEquiv_lie (Depth.RB n) (symmetricPower n) A K x z

def factorSymmetricBaseChangeEquiv (n : ℕ) (f : Polynomial A) :
    CoefficientBaseChange A (FactorSymmetric n f) K ≃ₗ⁅ℂ,BGG.Current⁆
      FactorSymmetric n (f.map (algebraMap A K)) where
  __ := (factorSymmetricBaseChangeLinearEquiv (K:=K) n f).restrictScalars ℂ
  map_lie' {x z} := factorSymmetricBaseChangeLinearEquiv_lie n f x z

end KhanSL2.SymmetricFamily
