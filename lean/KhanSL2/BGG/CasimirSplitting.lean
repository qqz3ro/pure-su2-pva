module

public import KhanSL2.BGG.ColorCasimir
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Kernel/range splitting for the concrete Casimir spectral operators. -/
noncomputable section
namespace KhanSL2.BGG

/-- An invariant complement to the kernel of a finite-dimensional endomorphism
is its range. This proves the splitting needed by the algebraic Green operator. -/
theorem isCompl_ker_range_of_invariant_complement
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : Module.End K M) (C : Submodule K M) (hC : IsCompl (LinearMap.ker f) C)
    (hfC : ∀ u ∈ C, f u ∈ C) : IsCompl (LinearMap.ker f) (LinearMap.range f) := by
  let fC : Module.End K C :=
    (f.comp C.subtype).codRestrict C (fun u => hfC u u.property)
  have hinj : Function.Injective fC := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    have hh : fC u = 0 := hu
    have hzero : f (u : M) = 0 := congrArg Subtype.val hh
    have hmem : (u : M) ∈ LinearMap.ker f ⊓ C := ⟨hzero, u.property⟩
    rw [hC.inf_eq_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hsurj : Function.Surjective fC := LinearMap.surjective_of_injective hinj
  have hrange : LinearMap.range f = C := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      have hu : u ∈ LinearMap.ker f ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
      rw [← hab, map_add, show f a = 0 from ha, zero_add]
      exact hfC b hb
    · intro u hu
      obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
      exact ⟨v, congrArg Subtype.val hv⟩
  rw [hrange]
  exact hC

/-- Any affine scalar polynomial in the actual sl₂ Casimir has complementary
kernel and range on every finite-dimensional complex sl₂ module. -/
theorem casimir_affine_isCompl_ker_range
    (M : Type*) [AddCommGroup M] [Module ℂ M] [LieRingModule G M] [LieModule ℂ G M]
    [FiniteDimensional ℂ M] (a b : ℂ) :
    IsCompl (LinearMap.ker (a • (LinearMap.id : Module.End ℂ M) +
      b • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f M))
      (LinearMap.range (a • (LinearMap.id : Module.End ℂ M) +
      b • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f M)) := by
  let F : M →ₗ⁅ℂ,G⁆ M := a • LieModuleHom.id +
    b • TauCeti.sl2CasimirHom rootSl2Triple rootSl2Triple_top M
  have hF : F.toLinearMap = a • (LinearMap.id : Module.End ℂ M) +
      b • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f M := by
    apply LinearMap.ext
    intro u
    simp [F]
  obtain ⟨C, hC⟩ := TauCeti.exists_isCompl_sl_fin_two F.ker
  apply isCompl_ker_range_of_invariant_complement _ C.toSubmodule
  · rw [← hF]
    exact (LieSubmodule.isCompl_toSubmodule).mpr hC
  · intro u hu
    change a • u + b • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f M u ∈ C
    rw [TauCeti.sl2Casimir_apply]
    exact C.add_mem (C.smul_mem a hu) (C.smul_mem b
      (C.add_mem (C.add_mem (C.lie_mem (C.lie_mem hu)) (C.lie_mem (C.lie_mem hu)))
        (C.smul_mem _ (C.lie_mem (C.lie_mem hu)))))

namespace PositiveCE

/-- The proved kernel/range splitting for each actual finite CE spectral operator. -/
theorem spectralOperator_isCompl_ker_range (d N : ℕ) :
    IsCompl (LinearMap.ker (spectralOperator d N).toLinearMap)
      (LinearMap.range (spectralOperator d N).toLinearMap) := by
  have heq : (spectralOperator d N).toLinearMap =
      (N : ℂ) • (LinearMap.id : Module.End ℂ (liePiece d N)) +
      (-1 / 4 : ℂ) • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f (liePiece d N) := by
    apply LinearMap.ext
    intro u
    change spectralOperator d N u = _
    rw [spectralOperator_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    module
  rw [heq]
  exact casimir_affine_isCompl_ker_range (liePiece d N) (N : ℂ) (-1 / 4 : ℂ)

end PositiveCE
end KhanSL2.BGG
