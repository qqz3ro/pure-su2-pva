module

public import KhanSL2.BGG.ColorCasimir
public import KhanSL2.BGG.RootCasimirKernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The completely computed spectral kernels in the actual positive-current
CE coordinates. The Laplacian identification is proved in a separate file. -/

noncomputable section
namespace KhanSL2.BGG.PositiveCE

/-- Away from triangular energy, the actual finite CE spectral kernel is zero. -/
theorem spectralKernel_eq_bot_of_energy_ne {d N : ℕ} (hN : N ≠ triangular d) :
    spectralKernel d N = ⊥ := by
  apply (LieSubmodule.eq_bot_iff _).mpr
  intro u hu
  have hR : ColorRoot.liePieceEquiv d N u ∈ rootCasimirKernel d N := by
    change rootSpectralOperator d N (ColorRoot.liePieceEquiv d N u) = 0
    have hu0 : spectralOperator d N u = 0 := hu
    rw [← ColorRoot.liePieceEquiv_spectralOperator, hu0, map_zero]
  rw [rootCasimirKernel_eq_bot_of_energy_ne hN] at hR
  apply (ColorRoot.liePieceEquiv d N).injective
  simpa using hR

/-- At triangular energy, the actual finite CE spectral kernel is `V(2j)`. -/
theorem spectralKernel_nonempty_equiv_standard (j : ℕ) :
    Nonempty ((spectralKernel j (triangular j) : Type) ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2 * j)) := by
  obtain ⟨e⟩ := rootCasimirKernel_nonempty_equiv_standard j
  exact ⟨(ColorRoot.spectralKernelEquivRoot j (triangular j)).trans e⟩

/-- The complete finite-degree/energy dimension formula for the actual spectral kernel. -/
theorem spectralKernel_finrank (d N : ℕ) :
    Module.finrank ℂ (spectralKernel d N) = if N = triangular d then 2 * d + 1 else 0 := by
  split_ifs with hN
  · subst N
    calc
      Module.finrank ℂ (spectralKernel d (triangular d)) =
        Module.finrank ℂ (rootCasimirKernel d (triangular d)) :=
          (ColorRoot.spectralKernelEquivRoot d (triangular d)).toLinearEquiv.finrank_eq
      _ = 2 * d + 1 := rootCasimirKernel_finrank d
  · rw [spectralKernel_eq_bot_of_energy_ne hN]
    exact Module.finrank_zero_of_subsingleton

end KhanSL2.BGG.PositiveCE
