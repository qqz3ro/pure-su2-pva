module

public import KhanSL2.Macdonald.StrongBridgeRootCoefficientLinear
public import KhanSL2.Macdonald.FixedHomologyRootCoproduct
public import KhanSL2.Macdonald.NormalizedSignedRootFactorization
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel Conditional

/-- Scalar extension of the original coefficient-linear homology equivalence, retaining every root component. -/
def symmetricPowerRootBaseChangeEquiv (s : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB s) A] :
    (A ⊗[Depth.RB s] TotalHomology (symmetricPower s)) ≃ₗ[A]
      ⨁ d : RootHomologyDegrees s, A ⊗[Depth.RB s] FixedSignedRootModel s d := by
  classical
  exact ((symmetricPowerRootLinearEquiv s).baseChange (Depth.RB s) A _ _).trans
    (TensorProduct.directSumRight (Depth.RB s) A A (FixedSignedRootModel s))

@[simp] theorem symmetricPowerRootBaseChangeEquiv_tmul (s : ℕ) (A : Type)
    [CommRing A] [Algebra (Depth.RB s) A] (a : A)
    (h : TotalHomology (symmetricPower s)) (d : RootHomologyDegrees s) :
    symmetricPowerRootBaseChangeEquiv s A (a ⊗ₜ[Depth.RB s] h) d =
      a ⊗ₜ[Depth.RB s] fixedSignedRootBlockEquiv s d (fixedRootHomologyComponent s d h) := by
  simp only [symmetricPowerRootBaseChangeEquiv,LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul,TensorProduct.directSumRight_tmul]
  rfl

/-- An actual pair of specialized weighted-root factors associated to one input component and allocation. -/
abbrev FixedRootOrbitFactor {s s₁ s₂ : ℕ} {A : Type} [CommRing A]
    [Algebra (Depth.RB s) A] [Algebra ℂ A]
    (c : Collision.ChartData s s₁ s₂ A) (d : RootHomologyDegrees s)
    (j : OrbitIndex d.val.1 d.val.2 s₁) :=
  FactorSignedModule j.val.1 j.val.2 c.f₁ ⊗[A]
    FactorSignedModule (d.val.1-j.val.1) (d.val.2-j.val.2) c.f₂

/-- The exact normalized literal chart restriction on one retained fixed-degree root block. -/
def fixedRootBlockChartEquiv {s s₁ s₂ : ℕ} {A : Type} [CommRing A]
    [Algebra (Depth.RB s) A] [Algebra ℂ A]
    (c : Collision.ChartData s s₁ s₂ A) (htotal : s₁+s₂=s) (d : RootHomologyDegrees s) :
    (A ⊗[Depth.RB s] FixedSignedRootModel s d) ≃ₗ[A]
      ∀ j : OrbitIndex d.val.1 d.val.2 s₁, FixedRootOrbitFactor c d j := by
  obtain ⟨⟨q,r⟩,hd⟩ := d
  have hs : s=q+2*r := by omega
  cases hs
  exact normalizedSignedRootFactorizationEquiv c htotal

/-- Every original fixed root component splits by the actual normalized quotient restriction. -/
def fixedRootBlocksChartEquiv {s s₁ s₂ : ℕ} {A : Type} [CommRing A]
    [Algebra (Depth.RB s) A] [Algebra ℂ A]
    (c : Collision.ChartData s s₁ s₂ A) (htotal : s₁+s₂=s) :
    (⨁ d : RootHomologyDegrees s, A ⊗[Depth.RB s] FixedSignedRootModel s d) ≃ₗ[A]
      ⨁ d : RootHomologyDegrees s, (∀ j : OrbitIndex d.val.1 d.val.2 s₁, FixedRootOrbitFactor c d j) :=
  DFinsupp.mapRange.linearEquiv (fixedRootBlockChartEquiv c htotal)

/-- Original scalar-extended symmetric homology in its normalized literal root-chart coordinates.
The actual homology coproduct comparison is proved separately by the component diagram. -/
def symmetricPowerRootChartCoordinatesEquiv {s s₁ s₂ : ℕ} {A : Type} [CommRing A]
    [Algebra (Depth.RB s) A] [Algebra ℂ A]
    (c : Collision.ChartData s s₁ s₂ A) (htotal : s₁+s₂=s) :
    (A ⊗[Depth.RB s] TotalHomology (symmetricPower s)) ≃ₗ[A]
      ⨁ d : RootHomologyDegrees s, (∀ j : OrbitIndex d.val.1 d.val.2 s₁, FixedRootOrbitFactor c d j) :=
  (symmetricPowerRootBaseChangeEquiv s A).trans (fixedRootBlocksChartEquiv c htotal)

end KhanSL2.Macdonald

