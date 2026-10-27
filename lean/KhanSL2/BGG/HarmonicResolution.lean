module

public import KhanSL2.BGG.PositiveTransfer
public import KhanSL2.BGG.FreeCEExactness
public import KhanSL2.BGG.ContractionGradedExactness

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.HarmonicResolution

open PositiveTransfer

/-- The actual augmentation of the transferred harmonic complex. -/
def augmentation : HarmonicChain →ₗ[ℂ] ℂ :=
  FreeCE.augmentation.comp (contraction.incl.restrictScalars ℂ)

@[simp] theorem augmentation_apply (u : HarmonicChain) :
    augmentation u = FreeCE.augmentation (contraction.incl u) := rfl

@[simp] theorem augmentation_differential (u : HarmonicChain) :
    augmentation (differential u) = 0 := by
  rw [augmentation_apply, ← contraction.dM_incl_apply, FreeCE.augmentation_differential]

/-- Exactness is transferred from the independently proved actual free CE resolution. -/
theorem augmented_exactness (u : HarmonicChain) (hu : differential u = 0)
    (hε : augmentation u = 0) : ∃ v, differential v = u := by
  obtain ⟨v, hv⟩ := FreeCE.augmented_exactness (contraction.incl u)
    (by rw [contraction.dM_incl_apply, hu, map_zero]) hε
  exact ⟨contraction.proj v, by rw [← contraction.proj_dM_apply, hv, contraction.proj_incl_apply]⟩

/-- A scalar section of the transferred augmentation; it is only asserted to be complex-linear. -/
def scalarSection : ℂ →ₗ[ℂ] HarmonicChain :=
  (contraction.proj.restrictScalars ℂ).comp FreeCE.scalarInclusion

@[simp] theorem augmentation_scalarSection (r : ℂ) : augmentation (scalarSection r) = r := by
  apply contraction_augmentation_section_additive contraction
    FreeCE.augmentation.toAddMonoidHom FreeCE.scalarInclusion
    FreeCE.augmentation_differential _ FreeCE.augmentation_scalarInclusion r
  intro z
  simp only [FreeCE.scalarInclusion, LinearMap.toSpanSingleton_apply,
    LinearMap.map_smul_of_tower, FreeCE.differential_tmul_one, smul_zero]

/-- The transferred complex resolves the scalar augmentation in total-module form. -/
theorem augmentation_surjective : Function.Surjective augmentation :=
  fun r => ⟨scalarSection r, augmentation_scalarSection r⟩

end KhanSL2.BGG.HarmonicResolution