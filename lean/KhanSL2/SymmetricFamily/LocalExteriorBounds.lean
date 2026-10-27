module

public import KhanSL2.SymmetricFamily.LocalExteriorGraded
public import KhanSL2.SymmetricFamily.LocalGradedBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual one-point exterior coefficient family is locally even: its
finite displacement filtration has bounded even evaluation quotients. -/

noncomputable section
open scoped DirectSum
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization.EvenWeightBounds

/-- The actual exterior graded quotients inherit the proved even Cartan annihilator. -/
theorem localExteriorGraded_annihilator (k : ℕ) (a : ℂ) (d : ℕ) :
    Polynomial.aeval (cartan (ConstantRestriction (LocalExteriorGraded k a d)))
      (evenBoundPolynomial k) = 0 :=
  currentCartan_annihilator_quotient (localExteriorSuccessor k a d) _
    (currentCartan_annihilator_submodule (localExteriorFiltration k a d) _
      (localExteriorCartan_annihilator k a))

/-- Every successive quotient of the actual finite exterior filtration is a
finite sum of bounded even evaluation modules. -/
theorem localExteriorGraded_even (k : ℕ) (a : ℂ) (d : ℕ) :
    ∃ (l : ℕ) (q : Fin l → ℕ), (∀ i, q i ≤ k) ∧
      Nonempty (LocalExteriorGraded k a d ≃ₗ⁅ℂ,BGG.Current⁆
        Evaluation a (⨁ i : Fin l, BGG.Coefficient (q i))) := by
  obtain ⟨l,q,hq,⟨e⟩⟩ := exists_bounded_lieModuleEquiv k (localExteriorGraded_annihilator k a d)
  exact ⟨l,q,hq,⟨(localExteriorGradedEvaluationEquiv k a d).trans (evaluationLieEquiv a e)⟩⟩

end KhanSL2.SymmetricFamily
