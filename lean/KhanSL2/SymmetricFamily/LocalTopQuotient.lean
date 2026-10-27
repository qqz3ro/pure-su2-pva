module

public import KhanSL2.SymmetricFamily.LocalTop
public import KhanSL2.Macdonald.EvaluationIrreducible

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-! The actual top evaluation quotient of the local symmetric coefficient fibre.
Its construction uses the proved degree-zero evaluation quotient and the unique
sl₂ top constituent, rather than assuming a current-module splitting. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization.EvenWeightBounds

/-- Proved constant-module top quotient data for the actual degree-zero fibre. -/
structure LocalTopQuotientData (k : ℕ) (a : ℂ) where
  quotient : ConstantRestriction (LocalSymmetricGraded k a 0) →ₗ⁅ℂ,BGG.G⁆ BGG.Coefficient k
  surjective : Function.Surjective quotient
  kernel_top : (cartan quotient.ker).eigenspace (2*(k:ℂ)) = ⊥

/-- This datum is constructed from the proved annihilator and unique-top theorems. -/
def localTopQuotientData (k : ℕ) (a : ℂ) : LocalTopQuotientData k a :=
  Classical.choice (by
    obtain ⟨f,j,hfj,hf,hker,_⟩ := exists_top_split_strict_kernel k
      (localSymmetricGraded_annihilator k a 0) (localSymmetricGradedZero_top_finrank k a)
    exact ⟨⟨f,hf,hker⟩⟩)

/-- The degree-zero top projection is an actual current map, because this quotient
has already been proved to evaluate at a. -/
def localSymmetricGradedTopQuotient (k : ℕ) (a : ℂ) :
    LocalSymmetricGraded k a 0 →ₗ⁅ℂ,BGG.Current⁆ EvenEvaluation a k :=
  (evaluationHom a (localTopQuotientData k a).quotient).comp
    (localSymmetricGradedEvaluationEquiv k a 0).toLieModuleHom

theorem localSymmetricGradedTopQuotient_surjective (k : ℕ) (a : ℂ) :
    Function.Surjective (localSymmetricGradedTopQuotient k a) := by
  intro w
  obtain ⟨v,hv⟩ := (localTopQuotientData k a).surjective (evaluationEquiv a (BGG.Coefficient k) w)
  exact ⟨constantRestrictionEquiv (LocalSymmetricGraded k a 0) v,hv⟩

/-- The requested surjection from the original fibre to its top even evaluation representation. -/
def localSymmetricTopQuotient (k : ℕ) (a : ℂ) :
    LocalSymmetricFibre k a →ₗ⁅ℂ,BGG.Current⁆ EvenEvaluation a k :=
  (localSymmetricGradedTopQuotient k a).comp (localSymmetricZeroProjection k a)

theorem localSymmetricTopQuotient_surjective (k : ℕ) (a : ℂ) :
    Function.Surjective (localSymmetricTopQuotient k a) :=
  (localSymmetricGradedTopQuotient_surjective k a).comp (localSymmetricZeroProjection_surjective k a)

/-- The degree-zero kernel has no top vector in its original constant action. -/
theorem localSymmetricGradedTopQuotient_top_eq_zero (k : ℕ) (a : ℂ)
    (v : LocalSymmetricGraded k a 0) (hv : localSymmetricGradedTopQuotient k a v = 0)
    (ht : ⁅BGG.constant MatrixSL2.h,v⁆ = (2*(k:ℂ)) • v) : v = 0 := by
  let w : (localTopQuotientData k a).quotient.ker := ⟨v,hv⟩
  have hw : w ∈ (cartan (localTopQuotientData k a).quotient.ker).eigenspace (2*(k:ℂ)) := by
    apply Module.End.mem_eigenspace_iff.mpr
    apply Subtype.ext
    exact ht
  rw [(localTopQuotientData k a).kernel_top] at hw
  exact congrArg Subtype.val (show w = 0 from hw)

end KhanSL2.SymmetricFamily
