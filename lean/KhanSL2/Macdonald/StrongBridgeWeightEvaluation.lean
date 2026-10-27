module

public import KhanSL2.Macdonald.StrongBridgeWeightCohomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Exact evaluation formula for the finite Macdonald homology calculation. -/
noncomputable section
namespace KhanSL2.Macdonald
open Factorization

/-- The canonical free model evaluates the fixed -S/2E representative against
an actual relative chain cycle with the original factorial pairing. -/
theorem strongFreePieceHomologyDualEquiv_evaluate (w s : ℕ)
    (u : strongFreePiece w s) (v : weightDegreePiece w s)
    (hv : weightBoundary w s (Submodule.Quotient.mk v) = 0) :
    strongFreePieceHomologyDualEquiv w s u
      (Submodule.Quotient.mk (⟨Submodule.Quotient.mk v,hv⟩ : LinearMap.ker (weightBoundary w s))) =
        pairing (strongModel (StrongMacdonald.Gmap u.val)) v.val := by
  change weightHomologyDualEquiv w s
    (Submodule.Quotient.mk (strongWeightHarmonicCycle w s (strongFreePieceHarmonicEquiv w s u)))
    (Submodule.Quotient.mk (⟨Submodule.Quotient.mk v,hv⟩ : LinearMap.ker (weightBoundary w s))) = _
  rw [weightHomologyDualEquiv_mk, weightRelativeDualEquiv_mk]
  rfl

end KhanSL2.Macdonald
