module

public import KhanSL2.BGGBridge.CoefficientOps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-!
# Coefficient shifts preserve BGG degree windows

The power-sum operator of index `m` preserves harmonic and coefficient degree,
and raises spin by `m`. The proof transports the already established CE
coefficient-shift grading through the specified BGG contraction.
-/

noncomputable section
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- Coefficient shifts raise spin by `m` in the CE model used for base change. -/
theorem coefficientChainModelPower_mem_win (m : ℕ) {p B : ℕ} {S : ℤ}
    {z : ChainN NB} (hz : z ∈ degWin p B S) :
    coefficientChainModelPower m z ∈ degWin p B (S + m) := by
  have hξ : J.symm z ∈ genPiece (kDegree p B S) := by
    apply (mem_genPiece_iff_J p B S (J.symm z)).mpr
    simpa only [LinearEquiv.apply_symm_apply] using hz
  have hshift := (mem_genPiece_iff_J p B (S + m)
    (Modules.coefficientChainPower m (J.symm z))).mp
    (Modules.coefficientChainPower_mem_piece m p B S hξ)
  simpa only [J_coefficientChainPower, LinearEquiv.apply_symm_apply] using hshift

/-- The actual harmonic coefficient operator has the prescribed spin shift. -/
theorem coefficientHarmPower_mem_win (m : ℕ) {p B : ℕ} {S : ℤ}
    {z : HarmN NB} (hz : z ∈ harmWin p B S) :
    coefficientHarmPower m z ∈ harmWin p B (S + m) := by
  have hshift := proj_mem_win
    (coefficientChainModelPower_mem_win m (incl_mem_win hz))
  rw [proj_coefficientChainModelPower] at hshift
  have hid := LinearMap.congr_fun (cN NB).proj_comp_incl z
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hid
  rw [hid] at hshift
  exact hshift

/-- Coefficient shifts descend to the actual relative BGG degree windows. -/
theorem coefficientBGGPower_mem_term (m : ℕ) {p B : ℕ} {S : ℤ}
    {x : HarmN NB ⧸ relH NB} (hx : x ∈ bggTerm p B S) :
    coefficientBGGPower m x ∈ bggTerm p B (S + m) := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨coefficientHarmPower m z, coefficientHarmPower_mem_win m hz, rfl⟩

/-- Restriction of the actual coefficient power sum to one BGG spin component. -/
def componentCoefficientPower (m B p : ℕ) (S : ℤ) :
    bggTerm p B S →ₗ[ℂ] bggTerm p B (S + m) :=
  (coefficientBGGPower m).restrict (fun _ hx => coefficientBGGPower_mem_term m hx)

@[simp] theorem componentCoefficientPower_coe (m B p : ℕ) (S : ℤ)
    (x : bggTerm p B S) :
    (componentCoefficientPower m B p S x : HarmN NB ⧸ relH NB) =
      coefficientBGGPower m x := rfl

end KhanSL2.BGGBridge
