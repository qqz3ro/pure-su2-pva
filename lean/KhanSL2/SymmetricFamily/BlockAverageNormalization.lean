module

public import KhanSL2.SymmetricFamily.AssignmentAveraging
public import KhanSL2.SymmetricFamily.SignedTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Exact binomial normalization for a block component of a normalized
permutation average. The common statement applies to ordinary and signed
slot actions once the actual block-map equivariance has been verified. -/
noncomputable section
open scoped BigOperators
namespace KhanSL2.SymmetricFamily

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Apply a specified full permutation average, with its exact factorial factor. -/
def permutationAverage (k : ℕ) (T : Equiv.Perm (Fin k) → Module.End ℂ V) : Module.End ℂ V :=
  (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ • ∑ σ, T σ

/-- A block component of the full normalized average is the average over assignments. -/
theorem block_permutationAverage {k r : ℕ}
    (T : Equiv.Perm (Fin k) → Module.End ℂ V)
    (F : Assignment k r → V →ₗ[ℂ] W)
    (hF : ∀ σ S x, F S (T σ x) = F (assignmentPermute σ S) x)
    (S : Assignment k r) (x : V) :
    F S (permutationAverage k T x) = assignmentAverage (fun U => F U x) S := by
  simp only [permutationAverage,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,hF]
  rfl

/-- The primitive assignment sum carries exactly the binomial coefficient
relative to the normalized block map, with no choice of shuffle representatives. -/
theorem sum_block_eq_choose_average {k r : ℕ}
    (T : Equiv.Perm (Fin k) → Module.End ℂ V)
    (F : Assignment k r → V →ₗ[ℂ] W)
    (hF : ∀ σ S x, F S (T σ x) = F (assignmentPermute σ S) x)
    (S : Assignment k r) (x : V) :
    ∑ U, F U x = (Nat.choose k r : ℂ) • F S (permutationAverage k T x) := by
  rw [block_permutationAverage T F hF]
  exact (choose_smul_assignmentAverage (fun U => F U x) S).symm

/-- The binomial factor is invertible on every actual root-assignment component. -/
theorem assignment_choose_ne_zero {k r : ℕ} (S : Assignment k r) :
    (Nat.choose k r : ℂ) ≠ 0 := by
  apply Nat.cast_ne_zero.mpr
  apply Nat.ne_of_gt
  apply Nat.choose_pos
  have h := Finset.card_le_univ S.val
  simpa only [S.property,Fintype.card_fin] using h

/-- Divide only by the proved nonzero binomial normalization. -/
theorem block_average_eq_inv_choose_sum {k r : ℕ}
    (T : Equiv.Perm (Fin k) → Module.End ℂ V)
    (F : Assignment k r → V →ₗ[ℂ] W)
    (hF : ∀ σ S x, F S (T σ x) = F (assignmentPermute σ S) x)
    (S : Assignment k r) (x : V) :
    F S (permutationAverage k T x) =
      (Nat.choose k r : ℂ)⁻¹ • ∑ U, F U x := by
  rw [sum_block_eq_choose_average T F hF S x,smul_smul,
    inv_mul_cancel₀ (assignment_choose_ne_zero S),one_smul]

end KhanSL2.SymmetricFamily
