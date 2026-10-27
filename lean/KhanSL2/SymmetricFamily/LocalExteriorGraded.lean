module

public import KhanSL2.SymmetricFamily.LocalExteriorFiltration
public import KhanSL2.Macdonald.EvaluationQuotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The successive quotients of the original local exterior coefficient
filtration are genuine finite-dimensional evaluation modules. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- The next filtration term as a submodule of the present actual current submodule. -/
def localExteriorSuccessor (k : ℕ) (a : ℂ) (d : ℕ) :
    LieSubmodule ℂ BGG.Current (localExteriorFiltration k a d) :=
  (localExteriorFiltration k a (d+1)).comap (localExteriorFiltration k a d).incl

/-- The actual successive quotient, with its quotient current action. -/
abbrev LocalExteriorGraded (k : ℕ) (a : ℂ) (d : ℕ) :=
  (localExteriorFiltration k a d) ⧸ localExteriorSuccessor k a d

instance localExteriorGraded_finite (k : ℕ) (a : ℂ) (d : ℕ) :
    FiniteDimensional ℂ (LocalExteriorGraded k a d) := inferInstance

/-- The actual current action on each successive quotient evaluates at its support. -/
theorem localExteriorGraded_mode (k : ℕ) (a : ℂ) (d n : ℕ) (x : BGG.G)
    (v : LocalExteriorGraded k a d) : ⁅BGG.mode n x,v⁆ = a^n • ⁅BGG.constant x,v⁆ :=
  quotient_evaluation_mode (localExteriorSuccessor k a d) a
    (fun n x v => localExteriorFiltration_deviation k a d n x v.property) n x v
/-- The literal evaluation equivalence, with no unproved local-evenness premise. -/
def localExteriorGradedEvaluationEquiv (k : ℕ) (a : ℂ) (d : ℕ) :
    LocalExteriorGraded k a d ≃ₗ⁅ℂ,BGG.Current⁆
      Evaluation a (ConstantRestriction (LocalExteriorGraded k a d)) :=
  evaluationRecognition a (localExteriorGraded_mode k a d)

end KhanSL2.SymmetricFamily
