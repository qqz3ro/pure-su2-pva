module

public import KhanSL2.Macdonald.EvaluationRecognition
public import Mathlib.Algebra.Lie.Quotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! A current module whose evaluation deviations lie in an invariant submodule
has a genuine evaluation action on the actual quotient. -/

noncomputable section
namespace KhanSL2.Macdonald

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]

/-- Evaluation of the original quotient action follows from the literal deviation relation. -/
theorem quotient_evaluation_mode (N : LieSubmodule ℂ BGG.Current M) (a : ℂ)
    (h : ∀ (n : ℕ) (x : BGG.G) (v : M),
      ⁅BGG.mode n x,v⁆ - a^n • ⁅BGG.constant x,v⁆ ∈ N)
    (n : ℕ) (x : BGG.G) (v : M ⧸ N) : ⁅BGG.mode n x,v⁆ = a^n • ⁅BGG.constant x,v⁆ := by
  obtain ⟨v,rfl⟩ := LieSubmodule.Quotient.surjective_mk' N v
  apply sub_eq_zero.mp
  rw [← LieModuleHom.map_lie,← LieModuleHom.map_lie,← map_smul,← map_sub]
  exact (LieSubmodule.Quotient.mk_eq_zero N).mpr (h n x v)

end KhanSL2.Macdonald
