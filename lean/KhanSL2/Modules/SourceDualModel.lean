module

public import KhanSL2.Modules.SourceDualAssembly

@[expose] public section

/-! The original restricted source dual, identified with `JB` compatibly with the specific map. -/

noncomputable section
set_option maxHeartbeats 1000000

namespace KhanSL2.Modules

/-- Reindex the restricted source dual along equality of coefficient degrees. -/
def sourceDualTotalCast {B C : ℕ} (h : B = C) (p : ℕ) :
    sourceDualTotal B p ≃ₗ[ℂ] sourceDualTotal C p := by
  subst C
  exact LinearEquiv.refl ℂ _

@[simp] theorem sourceDualTotalCast_psiTotal {B C : ℕ} (h : B = C) (p : ℕ) (x : KTotal B p) :
    sourceDualTotalCast h p (psiTotal B p x) = psiTotal C p (kTotalCast h p x) := by
  subst C
  rfl

/-- Invalid coefficient/form-degree pairs have zero restricted source dual. -/
theorem sourceDualTotal_eq_zero_of_invalid (B p : ℕ) (h : ¬ValidSector B p)
    (x : sourceDualTotal B p) : x = 0 := by
  apply DFinsupp.ext
  intro spin
  let : Subsingleton (Source.piece (Current.kDegree p B spin)) :=
    Submodule.subsingleton_iff_eq_bot.mpr (source_piece_eq_bot_of_invalid B p spin h)
  exact Subsingleton.elim _ _

/-- Polynomial realization for all coefficient/form-degree pairs. -/
def sourceDualB (B p : ℕ) : sourceDualTotal B p →ₗ[ℂ] JB B p := by
  classical
  exact if h : ValidSector B p then
    (jToJB B p h).toLinearMap.comp
      ((sourceDualPolynomial p (sectorS B p)).comp (sourceDualTotalCast h p).toLinearMap)
  else 0

/-- On valid sectors this is the proved Taylor equivalence; elsewhere both sides vanish. -/
theorem sourceDualB_bijective (B p : ℕ) : Function.Bijective (sourceDualB B p) := by
  classical
  by_cases h : ValidSector B p
  · rw [sourceDualB, dif_pos h]
    exact (jToJB B p h).bijective.comp
      ((sourceDualPolynomialEquiv p (sectorS B p)).bijective.comp (sourceDualTotalCast h p).bijective)
  · rw [sourceDualB, dif_neg h]
    constructor
    · intro x y _
      exact (sourceDualTotal_eq_zero_of_invalid B p h x).trans
        (sourceDualTotal_eq_zero_of_invalid B p h y).symm
    · intro q
      exact ⟨0, (jb_eq_zero_of_invalid h q).symm⟩

/-- The full, genuine identification with the original restricted source dual. -/
def sourceDualEquiv (B p : ℕ) : sourceDualTotal B p ≃ₗ[ℂ] JB B p :=
  LinearEquiv.ofBijective (sourceDualB B p) (sourceDualB_bijective B p)

/-- The previously specified comparison is exactly this source-dual model after transposing `phi`. -/
theorem sourceDualB_comp_psiTotal (B p : ℕ) :
    (sourceDualB B p).comp (psiTotal B p) = psiB B p := by
  classical
  by_cases h : ValidSector B p
  · apply LinearMap.ext
    intro x
    simp only [sourceDualB, dif_pos h, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact (congrArg (fun y => jToJB B p h (sourceDualPolynomial p (sectorS B p) y))
      (sourceDualTotalCast_psiTotal h p x)).trans
        ((congrArg (jToJB B p h)
          (LinearMap.congr_fun (sourceDualPolynomial_comp_psiTotal p (sectorS B p))
            (kTotalCast h p x))).trans (psiB_of_valid B p h x).symm)
  · apply LinearMap.ext
    intro x
    exact (jb_eq_zero_of_invalid h _).trans (jb_eq_zero_of_invalid h _).symm

/-- Public compatibility equation for the actual map and actual source-dual equivalence. -/
theorem psiB_eq_sourceDualEquiv_comp_psiTotal (B p : ℕ) :
    psiB B p = (sourceDualEquiv B p).toLinearMap.comp (psiTotal B p) :=
  (sourceDualB_comp_psiTotal B p).symm

/-- Surjectivity now holds for the specific polynomial comparison, with no model hypothesis. -/
theorem psiB_surjective (B p : ℕ) : Function.Surjective (psiB B p) := by
  rw [psiB_eq_sourceDualEquiv_comp_psiTotal]
  exact (sourceDualEquiv B p).surjective.comp (psiTotal_surjective B p)

end KhanSL2.Modules