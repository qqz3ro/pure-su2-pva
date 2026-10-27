module

public import KhanSL2.BGG.Induced

@[expose] public section

/-! Scalar-linear descent from the induced quotient using all balancing relations. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG.Induced

variable {R A G M N : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem relations_le_ker_scalar (inc : G → A) (act : G → M →ₗ[R] M)
    (F : A ⊗[R] M →ₗ[R] N)
    (hF : ∀ a x m, F ((a * inc x) ⊗ₜ[R] m) = F (a ⊗ₜ[R] act x m)) :
    (relations inc act).restrictScalars R ≤ LinearMap.ker F := by
  intro t ht
  change t ∈ relations inc act at ht
  have h : ∀ a : A, F (a • t) = 0 := by
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨⟨x, m⟩, rfl⟩ := ht
      intro a
      change F (a • relation inc act x m) = 0
      rw [relation, smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul', map_sub]
      change F ((a * inc x) ⊗ₜ[R] m) - F ((a * 1) ⊗ₜ[R] act x m) = 0
      rw [mul_one, hF, sub_self]
    | zero => intro a; simp
    | add t u ht hu it iu =>
      intro a
      rw [smul_add, map_add, it, iu, add_zero]
    | smul b t ht ih =>
      intro a
      rw [← mul_smul]
      exact ih _
  exact (show F t = 0 from by simpa only [one_smul] using h 1)

/-- A scalar-linear balanced map descends, even without an `A`-action on its target. -/
def descend (inc : G → A) (act : G → M →ₗ[R] M)
    (F : A ⊗[R] M →ₗ[R] N)
    (hF : ∀ a x m, F ((a * inc x) ⊗ₜ[R] m) = F (a ⊗ₜ[R] act x m)) :
    Model inc act →ₗ[R] N :=
  ((relations inc act).restrictScalars R).liftQ F (relations_le_ker_scalar inc act F hF)

@[simp] theorem descend_mk (inc : G → A) (act : G → M →ₗ[R] M)
    (F : A ⊗[R] M →ₗ[R] N)
    (hF : ∀ a x m, F ((a * inc x) ⊗ₜ[R] m) = F (a ⊗ₜ[R] act x m)) (t : A ⊗[R] M) :
    descend inc act F hF (mk inc act t) = F t := rfl

end KhanSL2.BGG.Induced
