module

public import KhanSL2.Macdonald.FactorHomologyRootChart
public import KhanSL2.Macdonald.RootHomologyFactorSpecialization

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel
open scoped WeightedFactorScalars
variable {A : Type} [CommRing A] [Algebra ℂ A]

namespace FactorHomologyScalars
scoped instance factorHomologyComplexModule (s : ℕ) (f : Polynomial A) :
    Module ℂ (FactorSymmetricHomology s f) := by
  unfold FactorSymmetricHomology
  letI : Algebra (Depth.RB s) A := (Collision.coeffHom s f).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Depth.RB s) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom s f).commutes z).symm
  infer_instance
scoped instance factorHomologyComplexTower (s : ℕ) (f : Polynomial A) :
    IsScalarTower ℂ A (FactorSymmetricHomology s f) := by
  unfold FactorSymmetricHomology
  let : Algebra (Depth.RB s) A := (Collision.coeffHom s f).toRingHom.toAlgebra
  let : IsScalarTower ℂ (Depth.RB s) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom s f).commutes z).symm
  infer_instance
end FactorHomologyScalars
open scoped FactorHomologyScalars

/-- Canonical insertion into the original factor-specialized homology module. -/
def factorSymmetricHomologyUnit (s : ℕ) (f : Polynomial A) :
    TotalHomology (symmetricPower s) →ₗ[ℂ] FactorSymmetricHomology s f := by
  letI : Algebra (Depth.RB s) A := (Collision.coeffHom s f).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Depth.RB s) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom s f).commutes z).symm
  exact (TensorProduct.mk (Depth.RB s) A (TotalHomology (symmetricPower s)) 1).restrictScalars ℂ

/-- The original homology root equivalence commutes with canonical factor insertion. -/
theorem factorSymmetricHomologyRootEquiv_unit (s : ℕ) (f : Polynomial A)
    (h : TotalHomology (symmetricPower s)) (d : RootHomologyDegrees s) :
    factorSymmetricHomologyRootEquiv s f (factorSymmetricHomologyUnit s f h) d =
      weightedRootHomologyFactorUnit d.val.1 d.val.2 f (fixedRootHomologyComponent s d h) := by
  obtain ⟨⟨q,r⟩,hd⟩ := d
  have hs : s=q+2*r := by omega
  cases hs
  let : Algebra (Depth.RB (q+2*r)) A := (Collision.coeffHom (q+2*r) f).toRingHom.toAlgebra
  change symmetricPowerRootBaseChangeEquiv (q+2*r) A
    (1 ⊗ₜ[Depth.RB (q+2*r)] h) ⟨(q,r),hd⟩ = _
  rw [symmetricPowerRootBaseChangeEquiv_tmul]
  rfl

/-- Evaluation of the actual reindexing at a specified pair of factor degrees. -/
theorem fixedRootChartPairsEquiv_apply {s₁ s₂ : ℕ} [Algebra (Depth.RB (s₁+s₂)) A]
    (c : Collision.ChartData (s₁+s₂) s₁ s₂ A)
    (z : ⨁ d : RootHomologyDegrees (s₁+s₂),
      (∀ j : OrbitIndex d.val.1 d.val.2 s₁, FixedRootOrbitFactor c d j))
    (d : RootHomologyDegrees s₁ × RootHomologyDegrees s₂) :
    fixedRootChartPairsEquiv c z d =
      rootPairFactorEquiv c d
        (z ((rootDegreeAllocationEquiv s₁ s₂).symm d).1
          ((rootDegreeAllocationEquiv s₁ s₂).symm d).2) := rfl

/-- The root-chart equivalence has the prescribed literal normalized restriction in every factor component. -/
theorem normalizedHomologyRootChartEquiv_tmul_component {s₁ s₂ : ℕ}
    [Algebra (Depth.RB (s₁+s₂)) A] (c : Collision.ChartData (s₁+s₂) s₁ s₂ A)
    (a : A) (h : TotalHomology (symmetricPower (s₁+s₂)))
    (d : RootHomologyDegrees s₁ × RootHomologyDegrees s₂) :
    factorSymmetricHomologyTensorRootEquiv s₁ s₂ c.f₁ c.f₂
      (normalizedHomologyRootChartEquiv c (a ⊗ₜ[Depth.RB (s₁+s₂)] h)) d =
      rootPairFactorEquiv c d
        (fixedRootBlockChartEquiv c rfl ((rootDegreeAllocationEquiv s₁ s₂).symm d).1
          (a ⊗ₜ[Depth.RB (s₁+s₂)]
            fixedSignedRootBlockEquiv (s₁+s₂) ((rootDegreeAllocationEquiv s₁ s₂).symm d).1
              (fixedRootHomologyComponent (s₁+s₂) ((rootDegreeAllocationEquiv s₁ s₂).symm d).1 h))
          ((rootDegreeAllocationEquiv s₁ s₂).symm d).2) := by
  simp only [normalizedHomologyRootChartEquiv,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
    fixedRootChartPairsEquiv_apply]
  congr 1
  change fixedRootBlockChartEquiv c rfl _
    (symmetricPowerRootBaseChangeEquiv (s₁+s₂) A (a ⊗ₜ[Depth.RB (s₁+s₂)] h) _) _ = _
  rw [symmetricPowerRootBaseChangeEquiv_tmul]

end KhanSL2.Macdonald
