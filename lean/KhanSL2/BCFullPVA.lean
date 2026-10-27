module

public import KhanSL2.BCFullBracketSesqui
public import KhanSL2.BCFullJacobi
public import KhanSL2.BCFullAlgebra

@[expose] public section

/-! The finite-mode exterior algebra with zero ghosts is a graded `bc` PVA. -/

noncomputable section

namespace KhanSL2

namespace FullBC

theorem bracket_super_jacobi (d e : Degree) (a b c : FullCochain)
    (ha : a ∈ fullPiece d) (hb : b ∈ fullPiece e) :
    bracket.jacobiLeft a b c =
      bracket.jacobiMiddle a b c + koszulSign d e • bracket.jacobiRight a b c := by
  apply full_jacobi_of_generators bracket_super_leibniz bracket_degree
    (fun a b => by
      simpa only [LambdaPolynomial.rightTranslation_apply, fullData]
        using bracket_right_translation a b)
    bracket_left_translation bracket_super_skew _ ha hb c
  intro i j k
  rw [LambdaBracket.jacobiator_eq_zero_iff]
  simp

end FullBC

/-- Every axiom of the specified PVA holds on the finite exterior algebra
including the three zero ghosts. -/
theorem full_isPVA : IsPVA fullData FullBC.bracket where
  algebra := full_algebra
  sesquilinear_left := FullBC.bracket_left_translation
  sesquilinear_right := fun a b => by
    simpa only [LambdaPolynomial.rightTranslation_apply, fullData]
      using FullBC.bracket_right_translation a b
  super_skew := FullBC.bracket_super_skew
  super_jacobi := FullBC.bracket_super_jacobi
  super_leibniz := FullBC.bracket_super_leibniz
  bracket_degree := FullBC.bracket_degree

end KhanSL2

