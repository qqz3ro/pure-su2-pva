module

public import KhanSL2.Macdonald.StrongBridgeNormalization

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual cycle evaluation of the assembled homology coordinates. -/
noncomputable section
namespace KhanSL2.Macdonald
open Factorization BGGBridge

@[simp] theorem strongCoordinates_mono (e : StrongMacdonald.Exp) (t : Finset Mode) :
    strongCoordinates (StrongMacdonald.mono e t) = Finsupp.single (e,t) 1 := by
  ext ⟨f,u⟩
  simp only [strongCoordinates_apply, StrongMacdonald.coefW_mono,
    Finsupp.single_apply, Prod.mk.injEq]

theorem strongFreePiece_mono_mem (w s : ℕ) (b : strongFreePieceIndices w s) :
    StrongMacdonald.mono b.val.1 b.val.2 ∈ strongFreePiece w s := by
  apply (strongCoordinates_supportedPiece w s _).mp
  rw [strongCoordinates_mono]
  intro c hc
  have he : c = b.val := by simpa using hc
  subst c
  exact b.property

/-- The finite source coordinate basis is the original monomial itself. -/
@[simp] theorem strongFreePieceCoordinateEquiv_symm_single_val (w s : ℕ)
    (b : strongFreePieceIndices w s) :
    ((strongFreePieceCoordinateEquiv w s).symm (Finsupp.single b 1)).val =
      StrongMacdonald.mono b.val.1 b.val.2 := by
  let u : strongFreePiece w s := ⟨_,strongFreePiece_mono_mem w s b⟩
  have he : strongFreePieceCoordinateEquiv w s u = Finsupp.single b 1 := by
    ext c
    rw [strongFreePieceCoordinateEquiv_apply]
    simp only [u, StrongMacdonald.coefW_mono, Finsupp.single_apply]
    have hi : (b.val.1 = c.val.1 ∧ b.val.2 = c.val.2) ↔ b = c := by
      rw [← Prod.ext_iff, Subtype.ext_iff]
    simp only [hi]
  exact congrArg Subtype.val ((strongFreePieceCoordinateEquiv w s).symm_apply_eq.mpr he.symm)

/-- The total homology class of a genuine raw relative cycle. -/
def totalSymmetricCycleClass (z : RawChains SymmetricCoefficients)
    (hz : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0) :
    TotalHomology SymmetricCoefficients :=
  Submodule.Quotient.mk (⟨Submodule.Quotient.mk z,hz⟩ :
    LinearMap.ker (Factorization.differential SymmetricCoefficients))

/-- Every assembled coordinate evaluates the specified harmonic representative
on the original raw CE cycle, without imposing homogeneous representatives. -/
theorem strongTotalHomologyGradedCoordinateEquiv_evaluate (w s : ℕ)
    (z : RawChains SymmetricCoefficients)
    (hz : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0)
    (b : strongFreePieceIndices w s) :
    strongTotalHomologyGradedCoordinateEquiv (totalSymmetricCycleClass z hz) ⟨(w,s),b⟩ =
      pairing (strongModel (StrongMacdonald.Gmap
        (StrongMacdonald.mono b.val.1 b.val.2))) (chainModel z) := by
  rw [strongTotalHomologyGradedCoordinateEquiv_apply]
  let v := (weightChainComponentPair w s).cyclesMap
    (⟨Submodule.Quotient.mk z,hz⟩ : LinearMap.ker
      (Factorization.differential SymmetricCoefficients))
  have hv : weightBoundary w s (Submodule.Quotient.mk (rawWeightComponent w s z)) = 0 :=
    v.property
  change strongWeightHomologyCoordinateEquiv w s
    (Submodule.Quotient.mk (⟨Submodule.Quotient.mk (rawWeightComponent w s z),hv⟩ :
      LinearMap.ker (weightBoundary w s))) b = _
  rw [strongWeightHomologyCoordinateEquiv_evaluate,
    strongFreePieceCoordinateEquiv_symm_single_val, rawWeightComponent_val]
  apply pairing_weightProjection
  apply (strongModel_mem_weightDegreePiece _ w s).mpr
  exact (strongFreePieceToHarmonic w s
    ⟨_,strongFreePiece_mono_mem w s b⟩).property.2

/-- The ungraded coordinate formula retains the same specific harmonic map. -/
theorem strongTotalHomologyCoordinateEquiv_evaluate
    (z : RawChains SymmetricCoefficients)
    (hz : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0)
    (b : strongFreeIndices) :
    strongTotalHomologyCoordinateEquiv (totalSymmetricCycleClass z hz) b =
      pairing (strongModel (StrongMacdonald.Gmap
        (StrongMacdonald.mono b.val.1 b.val.2))) (chainModel z) := by
  obtain ⟨⟨⟨w,s⟩,c⟩,rfl⟩ := strongFreeGradedIndexEquiv.surjective b
  have hc : (strongFreeGradedIndexEquiv ⟨(w,s),c⟩).val = c.val := rfl
  simpa only [strongTotalHomologyCoordinateEquiv, LinearEquiv.trans_apply,
    Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply, hc] using
      strongTotalHomologyGradedCoordinateEquiv_evaluate w s z hz c

end KhanSL2.Macdonald
