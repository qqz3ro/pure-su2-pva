module

public import KhanSL2.Macdonald.StrongBridgeGrading
public import KhanSL2.Macdonald.StrongBridgeCohomology
public import KhanSL2.Macdonald.StrongBridgeFreePieces
public import KhanSL2.Factorization.RelativeChainsWeightHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The imported finite-piece Hodge theorem computes the actual finite
relative cohomology blocks under their specified coordinate map. -/
noncomputable section
namespace KhanSL2.Macdonald
open Factorization

/-- A specified harmonic representative in the actual finite relative complex. -/
def strongWeightHarmonicCycle (w s : ℕ) :
    ↥(StrongMacdonald.harm ⊓ StrongMacdonald.piece w s) →ₗ[ℂ]
      LinearMap.ker (weightCoboundary w s) where
  toFun h := ⟨⟨⟨strongModel h.val,
    (strongModel_mem_weightDegreePiece h.val w s).mpr h.property.2⟩,
      (strongModel_mem_relativeCochains h.val).mpr (StrongMacdonald.mem_harm.mp h.property.1).1⟩, by
    apply Subtype.ext
    apply Subtype.ext
    change differential (strongModel h.val) = 0
    rw [← strongModel_dbar, (StrongMacdonald.mem_harm.mp h.property.1).2.1, map_zero]⟩
  map_add' h k := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    exact map_add strongModel h.val k.val
  map_smul' c h := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    exact map_smul strongModel c h.val

def strongWeightHarmonicMap (w s : ℕ) :
    ↥(StrongMacdonald.harm ⊓ StrongMacdonald.piece w s) →ₗ[ℂ] WeightCohomology w s :=
  (PerfectDuality.pairBoundaries (weightCoboundary w s) (weightCoboundary w s)).mkQ.comp
    (strongWeightHarmonicCycle w s)

theorem strongWeightHarmonicMap_bijective (w s : ℕ) :
    Function.Bijective (strongWeightHarmonicMap w s) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro h hh
    rw [LinearMap.mem_ker, strongWeightHarmonicMap, LinearMap.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hh
    obtain ⟨u,hu⟩ := hh
    have he : StrongMacdonald.dbar (strongModel.symm u.val.val) = h.val := by
      apply strongModel.injective
      rw [strongModel_dbar, strongModel.apply_symm_apply]
      exact congrArg (fun t : weightCochains w s => t.val.val) hu
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact StrongMacdonald.eq_zero_of_mem_harm_of_eq_dbar h.property.1 he.symm
  · intro c
    obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective
      (PerfectDuality.pairBoundaries (weightCoboundary w s) (weightCoboundary w s)) c
    let v := strongModel.symm z.val.val.val
    have hv : v ∈ StrongMacdonald.invPiece w s := by
      constructor
      · apply (strongModel_mem_weightDegreePiece v w s).mp
        simpa only [v, strongModel.apply_symm_apply] using z.val.val.property
      · apply (strongModel_mem_relativeCochains v).mp
        change strongModel (strongModel.symm z.val.val.val) ∈ relativeCochains
        rw [strongModel.apply_symm_apply]
        exact z.val.property
    have hdv : StrongMacdonald.dbar v = 0 := by
      apply strongModel.injective
      rw [map_zero, strongModel_dbar]
      change differential (strongModel (strongModel.symm z.val.val.val)) = 0
      rw [strongModel.apply_symm_apply]
      exact congrArg (fun t : weightCochains w s => t.val.val) (LinearMap.mem_ker.mp z.property)
    obtain ⟨h,hh,u,hu,he⟩ := StrongMacdonald.exists_harm_add_dbar hv hdv
    refine ⟨⟨h,hh⟩, ?_⟩
    rw [strongWeightHarmonicMap, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    refine ⟨⟨⟨-strongModel u,
      Submodule.neg_mem _ ((strongModel_mem_weightDegreePiece u w s).mpr hu.1)⟩,
      Submodule.neg_mem _ ((strongModel_mem_relativeCochains u).mpr hu.2)⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change differential (-strongModel u) = strongModel h - z.val.val.val
    have hz : z.val.val.val = strongModel h + strongModel (StrongMacdonald.dbar u) := by
      simpa only [v, strongModel.apply_symm_apply, map_add] using congrArg strongModel he
    rw [map_neg, ← strongModel_dbar, hz]
    abel

/-- Exact Hodge normal forms for the actual finite relative cohomology block. -/
def strongWeightHarmonicEquiv (w s : ℕ) :
    ↥(StrongMacdonald.harm ⊓ StrongMacdonald.piece w s) ≃ₗ[ℂ] WeightCohomology w s :=
  LinearEquiv.ofBijective (strongWeightHarmonicMap w s) (strongWeightHarmonicMap_bijective w s)

/-- The already proved harmonic calculation now evaluates actual finite homology. -/
def strongWeightHarmonicDualEquiv (w s : ℕ) :
    ↥(StrongMacdonald.harm ⊓ StrongMacdonald.piece w s) ≃ₗ[ℂ]
      Module.Dual ℂ (WeightHomology w s) :=
  (strongWeightHarmonicEquiv w s).trans (weightHomologyDualEquiv w s)

/-- The explicit free-generator model of the dual of actual finite CE homology. -/
def strongFreePieceHomologyDualEquiv (w s : ℕ) :
    strongFreePiece w s ≃ₗ[ℂ] Module.Dual ℂ (WeightHomology w s) :=
  (strongFreePieceHarmonicEquiv w s).trans (strongWeightHarmonicDualEquiv w s)

end KhanSL2.Macdonald
