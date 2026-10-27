module

public import KhanSL2.Macdonald.StrongBridgeWeightEvaluation
public import KhanSL2.Macdonald.StrongBridgeFreePieceCoordinates
public import Mathlib.LinearAlgebra.Finsupp.LSum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Finite-dimensional duality identifies actual relative homology with
specified coordinates, evaluated on the original free harmonic representatives. -/
noncomputable section
namespace KhanSL2.Macdonald
open Factorization

/-- Evaluation, followed by the specified perfect harmonic pairing. -/
def strongWeightHomologyFreeDualEquiv (w s : ℕ) :
    WeightHomology w s ≃ₗ[ℂ] Module.Dual ℂ (strongFreePiece w s) :=
  (Module.evalEquiv ℂ (WeightHomology w s)).trans
    (strongFreePieceHomologyDualEquiv w s).dualMap

@[simp] theorem strongWeightHomologyFreeDualEquiv_apply (w s : ℕ)
    (v : WeightHomology w s) (u : strongFreePiece w s) :
    strongWeightHomologyFreeDualEquiv w s v u =
      strongFreePieceHomologyDualEquiv w s u v := rfl

/-- Dual coordinates on a finite, specified monomial index set. -/
def finiteFinsuppDualEquiv (ι : Type*) [Finite ι] :
    Module.Dual ℂ (ι →₀ ℂ) ≃ₗ[ℂ] (ι →₀ ℂ) :=
  (Finsupp.llift ℂ ℂ ℂ ι).symm.trans (Finsupp.linearEquivFunOnFinite ℂ ℂ ι).symm

@[simp] theorem finiteFinsuppDualEquiv_apply {ι : Type*} [Finite ι]
    (f : Module.Dual ℂ (ι →₀ ℂ)) (i : ι) :
    finiteFinsuppDualEquiv ι f i = f (Finsupp.single i 1) := by
  simp [finiteFinsuppDualEquiv]

/-- Coordinates of actual finite relative homology, with no chosen homology basis. -/
def strongWeightHomologyCoordinateEquiv (w s : ℕ) :
    WeightHomology w s ≃ₗ[ℂ] (strongFreePieceIndices w s) →₀ ℂ :=
  (strongWeightHomologyFreeDualEquiv w s).trans
    ((strongFreePieceCoordinateEquiv w s).symm.dualMap.trans
      (finiteFinsuppDualEquiv (strongFreePieceIndices w s)))

@[simp] theorem strongWeightHomologyCoordinateEquiv_apply (w s : ℕ)
    (v : WeightHomology w s) (b : strongFreePieceIndices w s) :
    strongWeightHomologyCoordinateEquiv w s v b =
      strongFreePieceHomologyDualEquiv w s
        ((strongFreePieceCoordinateEquiv w s).symm (Finsupp.single b 1)) v := by
  simp [strongWeightHomologyCoordinateEquiv]

/-- A coordinate is the original factorial pairing against the specified -S/2E
monomial, not an abstract dimension comparison. -/
theorem strongWeightHomologyCoordinateEquiv_evaluate (w s : ℕ)
    (v : weightDegreePiece w s)
    (hv : weightBoundary w s (Submodule.Quotient.mk v) = 0)
    (b : strongFreePieceIndices w s) :
    strongWeightHomologyCoordinateEquiv w s
      (Submodule.Quotient.mk (⟨Submodule.Quotient.mk v,hv⟩ : LinearMap.ker (weightBoundary w s))) b =
      pairing (strongModel (StrongMacdonald.Gmap
        ((strongFreePieceCoordinateEquiv w s).symm (Finsupp.single b 1)).val)) v.val := by
  rw [strongWeightHomologyCoordinateEquiv_apply, strongFreePieceHomologyDualEquiv_evaluate]

end KhanSL2.Macdonald
