module

public import KhanSL2.SymmetricFamily.LocalGraded
public import KhanSL2.Macdonald.EvaluationFunctor
public import KhanSL2.Factorization.EvenWeightBoundsDecomposition

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Evenness and strict extremal-weight bounds on the actual evaluation quotients
of the local symmetric family. No jet-module classification is assumed. -/

noncomputable section
open scoped DirectSum
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization.EvenWeightBounds

/-- Restricting the literal current Cartan to an invariant subspace preserves its annihilator. -/
theorem currentCartan_annihilator_submodule {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    (N : LieSubmodule ℂ BGG.Current M) (p : Polynomial ℂ)
    (hp : Polynomial.aeval (cartan (ConstantRestriction M)) p = 0) :
    Polynomial.aeval (cartan (ConstantRestriction N)) p = 0 :=
  cartan_annihilator_of_injective (constantRestrictionHom N.incl) Subtype.val_injective p hp

/-- The original quotient Cartan likewise preserves the actual annihilator. -/
theorem currentCartan_annihilator_quotient {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    (N : LieSubmodule ℂ BGG.Current M) (p : Polynomial ℂ)
    (hp : Polynomial.aeval (cartan (ConstantRestriction M)) p = 0) :
    Polynomial.aeval (cartan (ConstantRestriction (M ⧸ N))) p = 0 :=
  cartan_annihilator_of_surjective (constantRestrictionHom (LieSubmodule.Quotient.mk' N))
    (LieSubmodule.Quotient.surjective_mk' N) p hp

/-- Each genuine local evaluation quotient has only the asserted bounded even weights. -/
theorem localSymmetricGraded_annihilator (k : ℕ) (a : ℂ) (d : ℕ) :
    Polynomial.aeval (cartan (ConstantRestriction (LocalSymmetricGraded k a d)))
      (evenBoundPolynomial k) = 0 :=
  currentCartan_annihilator_quotient (localSymmetricSuccessor k a d) _
    (currentCartan_annihilator_submodule (localSymmetricFiltration k a d) _
      (localSymmetricCartan_annihilator k a))

/-- The positive actual filtration subspaces have no top constant eigenvector. -/
theorem localSymmetricFiltration_top_eigenspace_eq_bot (k : ℕ) (a : ℂ)
    (d : ℕ) (hd : 1 ≤ d) :
    (cartan (ConstantRestriction (localSymmetricFiltration k a d))).eigenspace (2*(k:ℂ)) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  apply Subtype.ext
  apply localSymmetricFiltration_positive_top_eq_zero k a v.val
    (localSymmetricFiltration_antitone k a hd v.property)
  exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv)

/-- A surjective map of finite complex sl₂ modules cannot create a missing weight. -/
theorem cartan_eigenspace_eq_bot_of_surjective {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [LieRingModule BGG.G V] [LieModule ℂ BGG.G V]
    [AddCommGroup W] [Module ℂ W] [LieRingModule BGG.G W] [LieModule ℂ BGG.G W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (f : V →ₗ⁅ℂ,BGG.G⁆ W) (hf : Function.Surjective f) (z : ℂ)
    (hz : (cartan V).eigenspace z = ⊥) : (cartan W).eigenspace z = ⊥ := by
  obtain ⟨s,hs⟩ := BGG.exists_lie_generalizedInverse f
  have hfs (w : W) : f (s w) = w := by
    obtain ⟨v,rfl⟩ := hf w
    exact hs v
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  have hsw : s w ∈ (cartan V).eigenspace z := by
    apply Module.End.mem_eigenspace_iff.mpr
    change ⁅MatrixSL2.h,s w⁆ = _
    rw [← s.map_lie]
    have hw' : ⁅MatrixSL2.h,w⁆ = z • w := Module.End.mem_eigenspace_iff.mp hw
    rw [hw',map_smul]
  have hsz : s w = 0 := by rw [hz] at hsw; exact hsw
  rw [← hfs w,hsz,map_zero]

/-- Every positive actual evaluation quotient has strictly smaller extremal weight. -/
theorem localSymmetricGraded_top_eigenspace_eq_bot (k : ℕ) (a : ℂ)
    (d : ℕ) (hd : 1 ≤ d) :
    (cartan (ConstantRestriction (LocalSymmetricGraded k a d))).eigenspace (2*(k:ℂ)) = ⊥ :=
  cartan_eigenspace_eq_bot_of_surjective
    (constantRestrictionHom (LieSubmodule.Quotient.mk' (localSymmetricSuccessor k a d)))
    (LieSubmodule.Quotient.surjective_mk' (localSymmetricSuccessor k a d)) _
    (localSymmetricFiltration_top_eigenspace_eq_bot k a d hd)

/-- The actual graded pieces are finite sums of bounded even evaluation modules. -/
theorem localSymmetricGraded_even (k : ℕ) (a : ℂ) (d : ℕ) :
    ∃ (l : ℕ) (q : Fin l → ℕ), (∀ i, q i ≤ k) ∧
      Nonempty (LocalSymmetricGraded k a d ≃ₗ⁅ℂ,BGG.Current⁆
        Evaluation a (⨁ i : Fin l, BGG.Coefficient (q i))) := by
  obtain ⟨l,q,hq,⟨e⟩⟩ := exists_bounded_lieModuleEquiv k (localSymmetricGraded_annihilator k a d)
  exact ⟨l,q,hq,⟨(localSymmetricGradedEvaluationEquiv k a d).trans (evaluationLieEquiv a e)⟩⟩

/-- Positive graded pieces are sums of strictly lower even evaluation modules. -/
theorem localSymmetricGraded_strict (k : ℕ) (a : ℂ) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (l : ℕ) (q : Fin l → ℕ), (∀ i, q i < k) ∧
      Nonempty (LocalSymmetricGraded k a d ≃ₗ⁅ℂ,BGG.Current⁆
        Evaluation a (⨁ i : Fin l, BGG.Coefficient (q i))) := by
  obtain ⟨l,q,hq,⟨e⟩⟩ := exists_strict_lieModuleEquiv k (localSymmetricGraded_annihilator k a d)
    (localSymmetricGraded_top_eigenspace_eq_bot k a d hd)
  exact ⟨l,q,hq,⟨(localSymmetricGradedEvaluationEquiv k a d).trans (evaluationLieEquiv a e)⟩⟩

end KhanSL2.SymmetricFamily
