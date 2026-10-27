module

public import KhanSL2.SymmetricFamily.LocalKernelFiltration

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Every successive quotient of the actual top-kernel filtration is a finite
sum of strictly smaller even evaluation representations. -/

noncomputable section
open scoped DirectSum
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization.EvenWeightBounds

/-- An injective constant intertwiner cannot add an absent eigenspace. -/
theorem cartan_eigenspace_eq_bot_of_injective {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [LieRingModule BGG.G V] [LieModule ℂ BGG.G V]
    [AddCommGroup W] [Module ℂ W] [LieRingModule BGG.G W] [LieModule ℂ BGG.G W]
    (f : V →ₗ⁅ℂ,BGG.G⁆ W) (hf : Function.Injective f) (z : ℂ)
    (hz : (cartan W).eigenspace z = ⊥) : (cartan V).eigenspace z = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  apply hf
  rw [map_zero]
  have hfv : f v ∈ (cartan W).eigenspace z := by
    apply Module.End.mem_eigenspace_iff.mpr
    change ⁅MatrixSL2.h,f v⁆ = _
    rw [← f.map_lie]
    have hv' : ⁅MatrixSL2.h,v⁆ = z • v := Module.End.mem_eigenspace_iff.mp hv
    rw [hv',map_smul]
  rw [hz] at hfv
  exact hfv

/-- The original kernel graded quotients inherit the actual even Cartan bound. -/
theorem localTopKernelGraded_annihilator (k : ℕ) (a : ℂ) (d : ℕ) :
    Polynomial.aeval (cartan (ConstantRestriction (LocalTopKernelGraded k a d)))
      (evenBoundPolynomial k) = 0 :=
  cartan_annihilator_of_injective (constantRestrictionHom (localTopKernelGradedMap k a d))
    (localTopKernelGradedMap_injective k a d) _ (localSymmetricGraded_annihilator k a d)

/-- A zero test for top eigenvectors through an actual injective current map. -/
theorem currentCartan_top_eq_bot_of_injective {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [LieRingModule BGG.Current V] [LieModule ℂ BGG.Current V]
    [AddCommGroup W] [Module ℂ W] [LieRingModule BGG.Current W] [LieModule ℂ BGG.Current W]
    (f : V →ₗ⁅ℂ,BGG.Current⁆ W) (hf : Function.Injective f) (z : ℂ)
    (hz : ∀ v : V, ⁅BGG.constant MatrixSL2.h,v⁆ = z • v → f v = 0) :
    (cartan (ConstantRestriction V)).eigenspace z = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  apply (constantRestrictionEquiv V).injective
  apply hf
  rw [map_zero,map_zero]
  apply hz
  exact Module.End.mem_eigenspace_iff.mp hv

/-- The degree-zero kernel has no remaining top constituent. -/
theorem localTopKernelGradedZero_top_eigenspace_eq_bot (k : ℕ) (a : ℂ) :
    (cartan (ConstantRestriction (LocalTopKernelGraded k a 0))).eigenspace (2*(k:ℂ)) = ⊥ := by
  apply currentCartan_top_eq_bot_of_injective (localTopKernelGradedMap k a 0)
    (localTopKernelGradedMap_injective k a 0)
  intro v hv
  apply localSymmetricGradedTopQuotient_top_eq_zero k a _
    (localTopKernelGradedMap_zero_killed k a v)
  rw [← LieModuleHom.map_lie,hv,map_smul]
/-- All degrees of the actual top-kernel filtration have strictly smaller top weight. -/
theorem localTopKernelGraded_top_eigenspace_eq_bot (k : ℕ) (a : ℂ) (d : ℕ) :
    (cartan (ConstantRestriction (LocalTopKernelGraded k a d))).eigenspace (2*(k:ℂ)) = ⊥ := by
  cases d with
  | zero => exact localTopKernelGradedZero_top_eigenspace_eq_bot k a
  | succ d =>
    exact cartan_eigenspace_eq_bot_of_injective
      (constantRestrictionHom (localTopKernelGradedMap k a (d+1)))
      (localTopKernelGradedMap_injective k a (d+1)) _
      (localSymmetricGraded_top_eigenspace_eq_bot k a (d+1) (Nat.le_add_left 1 d))

/-- Each actual kernel quotient is the evaluation of its genuine constant restriction. -/
def localTopKernelGradedEvaluationEquiv (k : ℕ) (a : ℂ) (d : ℕ) :
    LocalTopKernelGraded k a d ≃ₗ⁅ℂ,BGG.Current⁆
      Evaluation a (ConstantRestriction (LocalTopKernelGraded k a d)) :=
  evaluationRecognition a (localTopKernelGraded_mode k a d)

/-- The strict finite evaluation decomposition required by rank induction is proved
for every successive quotient of the actual top kernel. -/
theorem localTopKernelGraded_strict (k : ℕ) (a : ℂ) (d : ℕ) :
    ∃ (l : ℕ) (q : Fin l → ℕ), (∀ i, q i < k) ∧
      Nonempty (LocalTopKernelGraded k a d ≃ₗ⁅ℂ,BGG.Current⁆
        Evaluation a (⨁ i : Fin l, BGG.Coefficient (q i))) := by
  obtain ⟨l,q,hq,⟨e⟩⟩ := exists_strict_lieModuleEquiv k
    (localTopKernelGraded_annihilator k a d) (localTopKernelGraded_top_eigenspace_eq_bot k a d)
  exact ⟨l,q,hq,⟨(localTopKernelGradedEvaluationEquiv k a d).trans (evaluationLieEquiv a e)⟩⟩

end KhanSL2.SymmetricFamily
