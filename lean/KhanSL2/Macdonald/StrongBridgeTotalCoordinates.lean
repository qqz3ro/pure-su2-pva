module

public import KhanSL2.Macdonald.StrongBridgeHomologyCoordinates
public import KhanSL2.Factorization.RelativeChainsWeightTotalHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The finite-block harmonic calculation assembles into specified finite-support
coordinates on actual total relative symmetric-coefficient homology. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.Macdonald
open Factorization

/-- Partition the actual free monomial indices by their unique two weights. -/
def strongFreeGradedIndexEquiv :
    (Σ d : ℕ × ℕ, strongFreePieceIndices d.1 d.2) ≃ strongFreeIndices where
  toFun b := ⟨b.2.val,b.2.property.1⟩
  invFun b := ⟨(StrongMacdonald.wtVal b.val.1 b.val.2,
    StrongMacdonald.diagVal (fun _ => 2) (fun _ => 1) b.val.1 b.val.2),
      ⟨b.val,b.property,rfl,rfl⟩⟩
  left_inv b := by
    obtain ⟨⟨w,s⟩,b,hb⟩ := b
    rcases hb with ⟨hb,hw,hs⟩
    dsimp only
    cases hw
    cases hs
    rfl
  right_inv b := rfl

/-- Each coordinate is assembled from the actual finite homogeneous homology block. -/
def strongTotalHomologyGradedCoordinateEquiv :
    TotalHomology SymmetricCoefficients ≃ₗ[ℂ]
      (Σ d : ℕ × ℕ, strongFreePieceIndices d.1 d.2) →₀ ℂ :=
  weightHomologySumEquiv.symm.trans
    ((DFinsupp.mapRange.linearEquiv (fun d : ℕ × ℕ =>
      strongWeightHomologyCoordinateEquiv d.1 d.2)).trans
        (sigmaFinsuppLequivDFinsupp ℂ).symm)

/-- The actual total homology, expressed in the specified color-zero coordinates. -/
def strongTotalHomologyCoordinateEquiv :
    TotalHomology SymmetricCoefficients ≃ₗ[ℂ] strongFreeIndices →₀ ℂ :=
  strongTotalHomologyGradedCoordinateEquiv.trans
    (Finsupp.domLCongr strongFreeGradedIndexEquiv)

/-- Actual symmetric relative homology has finite coordinates indexed by
uncolored even multiplicities and odd finite sets. -/
def strongTotalHomologyUncoloredEquiv :
    TotalHomology SymmetricCoefficients ≃ₗ[ℂ] FreeMonomialIndex →₀ ℂ :=
  strongTotalHomologyCoordinateEquiv.trans (Finsupp.domLCongr strongFreeIndexEquiv)

@[simp] theorem strongTotalHomologyGradedCoordinateEquiv_apply
    (v : TotalHomology SymmetricCoefficients) (d : ℕ × ℕ)
    (b : strongFreePieceIndices d.1 d.2) :
    strongTotalHomologyGradedCoordinateEquiv v ⟨d,b⟩ =
      strongWeightHomologyCoordinateEquiv d.1 d.2 (weightHomologyComponent d.1 d.2 v) b := by
  change strongWeightHomologyCoordinateEquiv d.1 d.2
    (weightHomologySumEquiv.symm v d) b = _
  have h := weightHomologyComponent_sumMap (weightHomologySumEquiv.symm v) d
  rw [show weightHomologySumMap (weightHomologySumEquiv.symm v) = v from
    weightHomologySumEquiv.apply_symm_apply v] at h
  rw [h]

end KhanSL2.Macdonald
