module

public import KhanSL2.SymmetricFamily.SymmetricChartSpecialization
public import KhanSL2.SymmetricFamily.SymmetricFibreShuffle
public import KhanSL2.SymmetricFamily.SymmetricUniversalChart
public import KhanSL2.SymmetricFamily.FactorSymmetricTensorWords
public import KhanSL2.Factorization.BalancedScalarDiagram
public import KhanSL2.Factorization.EvenTensorShuffle

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-! The universal coprime-chart comparison implies the actual shuffle for
all disjoint complex polynomial fibres, and hence for the prescribed distinct
local tensor words. Specialization uses flat chain cones, never fibre homology. -/
noncomputable section
open CategoryTheory HomologicalComplex
namespace KhanSL2.SymmetricFamily
open Factorization Factorization.ChartBridge

/-- Specialize the genuine universal comparison to a specified coprime pair. -/
theorem factorSymmetric_shuffle_of_universalChart (r s : ℕ) (f g : Polynomial ℂ)
    (hf : f.Monic) (hg : g.Monic) (hfr : f.natDegree=r) (hgs : g.natDegree=s)
    (hcop : IsCoprime f g)
    [QuasiIso (symmetricChartComplex (productChartData r s))] :
    QuasiIso (shuffleComplex (FactorSymmetric r f) (FactorSymmetric s g)) := by
  let := factorCoefficientAlgebra (r+s) (f*g)
  let : IsScalarTower ℂ (Depth.RB (r+s)) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom (r+s) (f*g)).commutes z).symm
  let c := factorCoprimeChart r s f g hf hg hfr hgs hcop
  let := productChartSpecializationAlgebra c
  let : IsScalarTower ℂ (ProductChart r s) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      (((productChartSpecialization c).restrictScalars ℂ).commutes z).symm
  have hScalar := balancedShuffle_scalar_quasiIso_of_chart (productChartData r s) ℂ
  change QuasiIso (NonnegativeCone.scalarMap ℂ
    (balancedShuffleComplex (ProductChart r s)
      (FactorSymmetric r (firstOnProductChart r s).val)
      (FactorSymmetric s (secondOnProductChart r s).val))) at hScalar
  let := hScalar
  have := balancedShuffleComplex_quasiIso_of_scalar (ProductChart r s)
    (FactorSymmetric r (firstOnProductChart r s).val)
    (FactorSymmetric s (secondOnProductChart r s).val) ℂ
  have h := factorSymmetric_shuffle_of_baseChanged r s
    (firstOnProductChart r s).val (secondOnProductChart r s).val
  change QuasiIso (shuffleComplex
    (FactorSymmetric r ((firstOnProductChart r s).val.map (productChartSpecialization c).toRingHom))
    (FactorSymmetric s ((secondOnProductChart r s).val.map (productChartSpecialization c).toRingHom))) at h
  rw [productChartSpecialization_first,productChartSpecialization_second] at h
  exact h

/-- This isolates exactly the universal chart comparison needed by the already
proved finite-filtration and strict highest-weight induction. -/
theorem symmetricTensorShuffle_of_universalCharts
    (hCharts : ∀ r s, QuasiIso (symmetricChartComplex (productChartData r s))) :
    SymmetricTensorShuffle := by
  intro u v hu hv huv
  let := hCharts u.weight v.weight
  have := factorSymmetric_shuffle_of_universalChart u.weight v.weight u.polynomial v.polynomial
    u.polynomial_monic v.polynomial_monic u.polynomial_natDegree v.polynomial_natDegree
    (u.polynomial_isCoprime v huv)
  have := shuffle_quasiIso_of_equiv_first (FactorSymmetric v.weight v.polynomial)
    (factorSymmetricWordEquiv u hu).symm
  exact shuffle_quasiIso_of_equiv_second u.symmetricModule (factorSymmetricWordEquiv v hv).symm

end KhanSL2.SymmetricFamily
