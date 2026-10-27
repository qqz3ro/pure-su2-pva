module

public import KhanSL2.BGG.HarmonicResolution
public import KhanSL2.BGG.PositiveTransferDegree
public import KhanSL2.BGG.FreeCEActualDegree

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.HarmonicResolution
open PositiveTransfer

/-- The transferred augmented resolution is exact in each actual exterior degree. -/
theorem augmented_exactness_degree (p : ℕ) (u : HarmonicChain)
    (hp : u ∈ harmonicTensorDegree p) (hu : differential u = 0)
    (hε : augmentation u = 0) :
    ∃ v ∈ harmonicTensorDegree (p+1), differential v = u := by
  obtain ⟨v, hvP, hv⟩ := FreeCE.augmented_exactness_baseChangedDegree p (contraction.incl u)
    (contraction_incl_mem_degree hp)
    (by rw [contraction.dM_incl_apply, hu, map_zero]) hε
  exact ⟨contraction.proj v, contraction_proj_mem_degree hvP,
    by rw [← contraction.proj_dM_apply, hv, contraction.proj_incl_apply]⟩

/-- The transferred augmentation vanishes in every positive degree. -/
theorem augmentation_eq_zero_of_positive_degree {p : ℕ} {u : HarmonicChain}
    (hp : u ∈ harmonicTensorDegree (p+1)) : augmentation u = 0 :=
  FreeCE.augmentation_eq_zero_of_baseChangedDegree p _ (contraction_incl_mem_degree hp)

/-- Every cycle of positive degree in the actual harmonic complex is a boundary. -/
theorem exactness_positive_degree (p : ℕ) (u : HarmonicChain)
    (hp : u ∈ harmonicTensorDegree (p+1)) (hu : differential u = 0) :
    ∃ v ∈ harmonicTensorDegree (p+2), differential v = u :=
  augmented_exactness_degree (p+1) u hp hu (augmentation_eq_zero_of_positive_degree hp)

/-- The scalar section is in the zeroth chain group. -/
theorem scalarSection_mem_degree_zero (r : ℂ) : scalarSection r ∈ harmonicTensorDegree 0 := by
  change contraction.proj (FreeCE.scalarInclusion r) ∈ harmonicTensorDegree 0
  apply contraction_proj_mem_degree
  change r • ((1 : PositiveEnveloping) ⊗ₜ[ℂ] (1 : PositiveCE.Cochain)) ∈ sourceDegree 0
  rw [← TensorProduct.tmul_smul]
  apply Submodule.tmul_mem_baseChange_of_mem
  apply Submodule.smul_mem
  exact Finsupp.single_mem_supported ℂ 1 (by simp)

end KhanSL2.BGG.HarmonicResolution