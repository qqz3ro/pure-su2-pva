module

public import KhanSL2.SymmetricFamily.Assignments
public import KhanSL2.SymmetricFamily.WordInvariants

@[expose] public section

/-! Uniform averaging on root assignments, with the exact binomial factor.
This avoids a choice of shuffle representatives or any assumed normalization. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.SymmetricFamily

@[simp] theorem assignmentPermute_one {k r : ℕ} (S : Assignment k r) :
    assignmentPermute 1 S = S := by
  apply Subtype.ext
  exact Finset.map_refl (s := S.val)

theorem assignmentPermute_mul {k r : ℕ} (σ τ : Equiv.Perm (Fin k)) (S : Assignment k r) :
    assignmentPermute σ (assignmentPermute τ S) = assignmentPermute (σ*τ) S := by
  apply Subtype.ext
  change (S.val.map τ.toEmbedding).map σ.toEmbedding = S.val.map (σ*τ).toEmbedding
  rw [Finset.map_map]
  rfl

/-- Actual permutation of the finite root-assignment index. -/
def assignmentPermuteEquiv {k r : ℕ} (σ : Equiv.Perm (Fin k)) : Assignment k r ≃ Assignment k r where
  toFun := assignmentPermute σ
  invFun := assignmentPermute σ⁻¹
  left_inv S := by rw [assignmentPermute_mul, inv_mul_cancel, assignmentPermute_one]
  right_inv S := by rw [assignmentPermute_mul, mul_inv_cancel, assignmentPermute_one]

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Uniform full-symmetric-group averaging from one assignment component. -/
def assignmentAverage {k r : ℕ} (f : Assignment k r → M) (S : Assignment k r) : M :=
  (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), f (assignmentPermute σ S)

theorem assignmentAverage_permute {k r : ℕ} (f : Assignment k r → M)
    (τ : Equiv.Perm (Fin k)) (S : Assignment k r) :
    assignmentAverage f (assignmentPermute τ S) = assignmentAverage f S := by
  simp only [assignmentAverage, assignmentPermute_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ => f (assignmentPermute σ S))

/-- Transitivity makes the average independent of the initial root assignment. -/
theorem assignmentAverage_eq {k r : ℕ} (f : Assignment k r → M)
    (S T : Assignment k r) : assignmentAverage f S = assignmentAverage f T := by
  obtain ⟨σ,rfl⟩ := assignment_transitive S T
  exact (assignmentAverage_permute f σ S).symm

theorem sum_assignmentAverage {k r : ℕ} (f : Assignment k r → M) :
    ∑ S, assignmentAverage f S = ∑ S, f S := by
  simp only [assignmentAverage, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  have hσ (σ : Equiv.Perm (Fin k)) :
      ∑ S : Assignment k r, f (assignmentPermute σ S) = ∑ S, f S :=
    Equiv.sum_comp (assignmentPermuteEquiv σ) f
  simp only [hσ, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (permutationCard_ne_zero k), one_smul]

/-- Exact binomial normalization: the subset sum is choose(k,r) times one group average. -/
theorem choose_smul_assignmentAverage {k r : ℕ} (f : Assignment k r → M) (S : Assignment k r) :
    (Nat.choose k r : ℂ) • assignmentAverage f S = ∑ T, f T := by
  rw [← sum_assignmentAverage f]
  have h : ∀ T : Assignment k r, assignmentAverage f T = assignmentAverage f S :=
    fun T => assignmentAverage_eq f T S
  simp only [h, Finset.sum_const, Finset.card_univ, assignment_card,
    Nat.cast_smul_eq_nsmul]

end KhanSL2.SymmetricFamily
