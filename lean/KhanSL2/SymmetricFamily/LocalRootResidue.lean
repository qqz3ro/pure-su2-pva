module

public import KhanSL2.SymmetricFamily.LocalRootAlgebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The quotient of the actual local labelled-root fibre by its displacement
ideal is the original ground field, with the explicit support-point evaluation. -/

noncomputable section
namespace KhanSL2.SymmetricFamily

abbrev LocalRootResidue (k : ℕ) (a : ℂ) := LocalRootAlgebra k a ⧸ localRootIdeal k a

/-- Evaluation on the residue algebra, induced by the actual root evaluation. -/
def localResidueEvaluation (k : ℕ) (a : ℂ) : LocalRootResidue k a →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ _ (localRootEvaluation k a)
    (fun _ hx => localRootIdeal_le_ker k a hx)

@[simp] theorem localResidueEvaluation_mk (k : ℕ) (a : ℂ) (x : LocalRootAlgebra k a) :
    localResidueEvaluation k a (Ideal.Quotient.mk _ x) = localRootEvaluation k a x := rfl

/-- Every original root becomes the given scalar in the residue quotient. -/
theorem localResidue_root (k : ℕ) (a : ℂ) (i : Fin k) :
    Ideal.Quotient.mk (localRootIdeal k a) (localRoot k a i) =
      algebraMap ℂ (LocalRootResidue k a) a := by
  rw [← Ideal.Quotient.mk_algebraMap]
  apply Ideal.Quotient.eq.mpr
  exact localDisplacement_mem k a i

theorem localResidue_scalar_evaluation (k : ℕ) (a : ℂ) :
    (Algebra.ofId ℂ (LocalRootResidue k a)).comp (localResidueEvaluation k a) =
      AlgHom.id ℂ (LocalRootResidue k a) := by
  apply Ideal.Quotient.algHom_ext
  apply factorRootsAlgHom_ext
  intro i
  change algebraMap ℂ (LocalRootResidue k a)
      (localResidueEvaluation k a (Ideal.Quotient.mk _ (localRoot k a i))) =
    Ideal.Quotient.mk _ (localRoot k a i)
  rw [localResidueEvaluation_mk, localRootEvaluation_root, localResidue_root]

theorem localResidue_evaluation_scalar (k : ℕ) (a : ℂ) :
    (localResidueEvaluation k a).comp (Algebra.ofId ℂ (LocalRootResidue k a)) =
      AlgHom.id ℂ ℂ := by
  ext

/-- The degree-zero residue of the actual local-root filtration is exactly ℂ. -/
def localRootResidueEquiv (k : ℕ) (a : ℂ) : LocalRootResidue k a ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofAlgHom (localResidueEvaluation k a) (Algebra.ofId ℂ (LocalRootResidue k a))
    (localResidue_evaluation_scalar k a) (localResidue_scalar_evaluation k a)

/-- The explicit support-point evaluation has exactly the displacement ideal as kernel. -/
theorem localRootIdeal_eq_ker (k : ℕ) (a : ℂ) :
    localRootIdeal k a = RingHom.ker (localRootEvaluation k a).toRingHom := by
  apply le_antisymm (localRootIdeal_le_ker k a)
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (localRootResidueEquiv k a).injective
  change localRootEvaluation k a x = localRootResidueEquiv k a 0
  rw [map_zero]
  exact hx

/-- Each current-mode coefficient differs from evaluation by a displacement-ideal element. -/
theorem localRoot_power_sub_mem (k n : ℕ) (a : ℂ) (i : Fin k) :
    localRoot k a i ^ n - algebraMap ℂ (LocalRootAlgebra k a) (a^n) ∈ localRootIdeal k a := by
  rw [localRootIdeal_eq_ker]
  change localRootEvaluation k a
    (localRoot k a i ^ n - algebraMap ℂ (LocalRootAlgebra k a) (a^n)) = 0
  simp only [map_sub, map_pow, localRootEvaluation_root, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, sub_self]

end KhanSL2.SymmetricFamily
