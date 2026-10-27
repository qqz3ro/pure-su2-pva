module

public import KhanSL2.Modules.PolynomialComparison
public import KhanSL2.Modules.PolynomialSectors

@[expose] public section

/-! The concrete comparison `psiB : KTotal B p → J_{B,p}` in every sector. -/

noncomputable section

namespace KhanSL2.Modules

/-- Reindex the actual direct-sum homology along equality of coefficient degrees. -/
def kTotalCast {B C : ℕ} (h : B = C) (p : ℕ) : KTotal B p ≃ₗ[ℂ] KTotal C p := by
  subst C
  exact LinearEquiv.refl ℂ _

/-- The specified comparison into the concrete polynomial module `J_{B,p}`.
On valid sectors it is the Taylor map of the pairing with `phi`; in the other
sectors its target is the zero module. -/
def psiB (B p : ℕ) : KTotal B p →ₗ[ℂ] JB B p := by
  classical
  exact if h : ValidSector B p then
    (jToJB B p h).toLinearMap.comp
      ((psiPolynomial p (sectorS B p)).comp (kTotalCast h p).toLinearMap)
  else 0

/-- This identifies `psiB` with the explicit polynomial map in every valid sector. -/
theorem psiB_of_valid (B p : ℕ) (h : ValidSector B p) (x : KTotal B p) :
    psiB B p x =
      jToJB B p h (psiPolynomial p (sectorS B p) (kTotalCast h p x)) := by
  simp [psiB, h]

/-- The comparison vanishes outside the source sectors, as does its concrete target. -/
theorem psiB_of_invalid (B p : ℕ) (h : ¬ValidSector B p) : psiB B p = 0 := by
  simp [psiB, h]

end KhanSL2.Modules