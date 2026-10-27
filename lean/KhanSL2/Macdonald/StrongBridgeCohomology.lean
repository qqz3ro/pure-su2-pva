module

public import KhanSL2.Macdonald.StrongBridgeInvariants
public import KhanSL2.Macdonald.StrongBridgeHodge
public import KhanSL2.StrongMacdonald.SliceRing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Reuse of the proved Macdonald harmonic calculation for the actual
restricted relative CE cohomology, retaining its specified generator map. -/
noncomputable section
namespace KhanSL2.Macdonald

def strongHarmonicCycle : StrongMacdonald.harm →ₗ[ℂ] relativeCycles where
  toFun h := ⟨⟨strongModel h.val,
    (strongModel_mem_relativeCochains h.val).mpr (StrongMacdonald.mem_harm.mp h.property).1⟩, by
      apply Subtype.ext
      change differential (strongModel h.val) = 0
      rw [← strongModel_dbar, (StrongMacdonald.mem_harm.mp h.property).2.1, map_zero]⟩
  map_add' h k := by apply Subtype.ext; apply Subtype.ext; exact map_add strongModel h.val k.val
  map_smul' c h := by apply Subtype.ext; apply Subtype.ext; exact map_smul strongModel c h.val

def strongHarmonicCohomologyMap : StrongMacdonald.harm →ₗ[ℂ] Cohomology :=
  relativeBoundaries.mkQ.comp strongHarmonicCycle

theorem strongHarmonicCohomologyMap_bijective : Function.Bijective strongHarmonicCohomologyMap := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro h hh
    rw [LinearMap.mem_ker, strongHarmonicCohomologyMap, LinearMap.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hh
    obtain ⟨u,hu⟩ := hh
    have he : StrongMacdonald.dbar (strongModel.symm u.val) = h.val := by
      apply strongModel.injective
      rw [strongModel_dbar, strongModel.apply_symm_apply]
      exact congrArg Subtype.val hu
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact StrongMacdonald.eq_zero_of_mem_harm_of_eq_dbar h.property he.symm
  · intro c
    obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective relativeBoundaries c
    let v := strongModel.symm z.val.val
    have hv : v ∈ StrongMacdonald.inv :=
      (strongModel_mem_relativeCochains v).mp (by simp [v])
    have hdv : StrongMacdonald.dbar v = 0 := by
      apply strongModel.injective
      rw [map_zero, strongModel_dbar]
      change differential (strongModel (strongModel.symm z.val.val)) = 0
      rw [strongModel.apply_symm_apply]
      exact congrArg (fun t : relativeCochains => t.val) (LinearMap.mem_ker.mp z.property)
    obtain ⟨h,hh,u,hu,he⟩ := strong_exists_harm_add_dbar hv hdv
    refine ⟨⟨h,hh⟩, ?_⟩
    rw [strongHarmonicCohomologyMap, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    change strongHarmonicCycle ⟨h,hh⟩ - z ∈ relativeBoundaries
    refine ⟨⟨-strongModel u, Submodule.neg_mem _ ((strongModel_mem_relativeCochains u).mpr hu)⟩, ?_⟩
    apply Subtype.ext
    change differential (-strongModel u) = strongModel h - z.val.val
    have hz : z.val.val = strongModel h + strongModel (StrongMacdonald.dbar u) := by
      simpa [v] using congrArg strongModel he
    rw [map_neg, ← strongModel_dbar, hz]
    abel

/-- Actual cohomology classes have unique representatives in the proved
Macdonald harmonic space. -/
def strongHarmonicCohomologyEquiv : StrongMacdonald.harm ≃ₗ[ℂ] Cohomology :=
  LinearEquiv.ofBijective strongHarmonicCohomologyMap strongHarmonicCohomologyMap_bijective

/-- The existing free algebra is the colour-zero polynomial/exterior subspace. -/
def strongFree : Submodule ℂ StrongMacdonald.W where
  carrier := {u | StrongMacdonald.projFull u = u}
  zero_mem' := by
    change StrongMacdonald.projFull 0 = 0
    exact map_zero _
  add_mem' := by
    intro u v hu hv
    change StrongMacdonald.projFull u = u at hu
    change StrongMacdonald.projFull v = v at hv
    change StrongMacdonald.projFull (u+v) = u+v
    rw [map_add, hu, hv]
  smul_mem' := by
    intro c u hu
    change StrongMacdonald.projFull u = u at hu
    change StrongMacdonald.projFull (c • u) = c • u
    rw [map_smul, hu]

/-- The fixed generator map of the imported theorem, restricted to its free algebra. -/
def strongFreeToHarmonic : strongFree →ₗ[ℂ] StrongMacdonald.harm where
  toFun u := ⟨StrongMacdonald.Gmap u.val, StrongMacdonald.Gmap_mem_harm u.val⟩
  map_add' u v := by apply Subtype.ext; exact map_add StrongMacdonald.Gmap u.val v.val
  map_smul' c u := by apply Subtype.ext; exact map_smul StrongMacdonald.Gmap c u.val

theorem strongFreeToHarmonic_bijective : Function.Bijective strongFreeToHarmonic := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact StrongMacdonald.Gmap_injOn u.property (congrArg Subtype.val (LinearMap.mem_ker.mp hu))
  · intro h
    obtain ⟨u,hu,he⟩ := StrongMacdonald.exists_free_preimage h.property
    exact ⟨⟨u,hu⟩, Subtype.ext he⟩

/-- The already proved Theorem B, now interpreted by its canonical map into
our actual relative CE cohomology. -/
def strongFreeCohomologyEquiv : strongFree ≃ₗ[ℂ] Cohomology :=
  (LinearEquiv.ofBijective strongFreeToHarmonic strongFreeToHarmonic_bijective).trans
    strongHarmonicCohomologyEquiv

end KhanSL2.Macdonald
