module

public import KhanSL2.BCBracketSesqui
public import KhanSL2.CochainJacobi
public import KhanSL2.CochainAlgebra

@[expose] public section

/-! The concrete finite-mode cochain algebra is a graded `bc` PVA. -/

noncomputable section

namespace KhanSL2

namespace BC

theorem bracket_super_jacobi (d e : Degree) (a b c : Cochain)
    (ha : a ∈ cochainPiece d) (hb : b ∈ cochainPiece e) :
    bracket.jacobiLeft a b c =
      bracket.jacobiMiddle a b c + koszulSign d e • bracket.jacobiRight a b c := by
  apply cochain_jacobi_of_generators bracket_super_leibniz bracket_degree
    (fun a b => by
      simpa only [LambdaPolynomial.rightTranslation_apply, cochainData]
        using bracket_right_translation a b)
    bracket_left_translation bracket_super_skew _ ha hb c
  intro i j k
  rw [LambdaBracket.jacobiator_eq_zero_iff]
  simp

end BC

/-- Every axiom of the specified PVA holds on the original finite cochain
space. This theorem does not claim that `q` is a PVA derivation outside the
relative invariant subcomplex. -/
theorem cochain_isPVA : IsPVA cochainData BC.bracket where
  algebra := cochain_algebra
  sesquilinear_left := BC.bracket_left_translation
  sesquilinear_right := fun a b => by
    simpa only [LambdaPolynomial.rightTranslation_apply, cochainData]
      using BC.bracket_right_translation a b
  super_skew := BC.bracket_super_skew
  super_jacobi := BC.bracket_super_jacobi
  super_leibniz := BC.bracket_super_leibniz
  bracket_degree := BC.bracket_degree

end KhanSL2
