module

public import KhanSL2.SymmetricFamily.LocalFiltration
public import KhanSL2.Macdonald.EvaluationRecognition

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The successive quotients of the original local symmetric coefficient
filtration are genuine finite-dimensional evaluation modules. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- The next filtration term as a submodule of the present actual current submodule. -/
def localSymmetricSuccessor (k : ℕ) (a : ℂ) (d : ℕ) :
    LieSubmodule ℂ BGG.Current (localSymmetricFiltration k a d) :=
  (localSymmetricFiltration k a (d+1)).comap (localSymmetricFiltration k a d).incl

/-- The actual successive quotient, with its quotient current action. -/
abbrev LocalSymmetricGraded (k : ℕ) (a : ℂ) (d : ℕ) :=
  (localSymmetricFiltration k a d) ⧸ localSymmetricSuccessor k a d

instance localSymmetricGraded_finite (k : ℕ) (a : ℂ) (d : ℕ) :
    FiniteDimensional ℂ (LocalSymmetricGraded k a d) := inferInstance

/-- The actual current action on each successive quotient evaluates at its support. -/
theorem localSymmetricGraded_mode (k : ℕ) (a : ℂ) (d n : ℕ) (x : BGG.G)
    (v : LocalSymmetricGraded k a d) : ⁅BGG.mode n x,v⁆ = a^n • ⁅BGG.constant x,v⁆ := by
  obtain ⟨v,rfl⟩ := LieSubmodule.Quotient.surjective_mk' (localSymmetricSuccessor k a d) v
  apply sub_eq_zero.mp
  rw [← LieModuleHom.map_lie,← LieModuleHom.map_lie,← map_smul,← map_sub]
  apply (LieSubmodule.Quotient.mk_eq_zero (localSymmetricSuccessor k a d)).mpr
  exact localSymmetricFiltration_deviation k a d n x v.property

/-- The literal evaluation equivalence, with no unproved local-evenness premise. -/
def localSymmetricGradedEvaluationEquiv (k : ℕ) (a : ℂ) (d : ℕ) :
    LocalSymmetricGraded k a d ≃ₗ⁅ℂ,BGG.Current⁆
      Evaluation a (ConstantRestriction (LocalSymmetricGraded k a d)) :=
  evaluationRecognition a (localSymmetricGraded_mode k a d)

end KhanSL2.SymmetricFamily
