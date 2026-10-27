module

public import KhanSL2.SymmetricFamily.BlockAverageNormalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Generic symmetric primitive coproduct and actual labelled subset maps.
These apply to both current-mode variables and the uncolored even generators. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily

variable {α : Type*}

/-- The ordinary primitive coproduct on the actual polynomial algebra. -/
def polynomialPrimitive : MvPolynomial α ℂ →ₐ[ℂ]
    MvPolynomial α ℂ ⊗[ℂ] MvPolynomial α ℂ :=
  MvPolynomial.aeval (fun a => (MvPolynomial.X a : MvPolynomial α ℂ) ⊗ₜ[ℂ] 1 +
    1 ⊗ₜ[ℂ] (MvPolynomial.X a : MvPolynomial α ℂ))

@[simp] theorem polynomialPrimitive_X (a : α) :
    polynomialPrimitive (MvPolynomial.X a) =
      (MvPolynomial.X a : MvPolynomial α ℂ) ⊗ₜ[ℂ] 1 +
        1 ⊗ₜ[ℂ] (MvPolynomial.X a : MvPolynomial α ℂ) := MvPolynomial.aeval_X _ _

/-- Multiply the actual variables in a specified subset of labelled slots. -/
def subsetPolynomial {k : ℕ} (u : Fin k → α) (S : Finset (Fin k)) : MvPolynomial α ℂ :=
  ∏ i ∈ S, MvPolynomial.X (u i)

theorem subsetPolynomial_mem_degree {k : ℕ} (u : Fin k → α) (S : Finset (Fin k)) :
    (subsetPolynomial u S).IsHomogeneous S.card := by
  simpa only [subsetPolynomial,Finset.sum_const,smul_eq_mul,mul_one] using
    (MvPolynomial.IsHomogeneous.prod S (fun i => (MvPolynomial.X (u i) : MvPolynomial α ℂ))
      (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X ℂ (u i)))

theorem subsetPolynomial_permute {k : ℕ} (σ : Equiv.Perm (Fin k))
    (u : Fin k → α) (S : Finset (Fin k)) :
    subsetPolynomial (u ∘ σ) S = subsetPolynomial u (S.map σ.toEmbedding) := by
  simp [subsetPolynomial,Finset.prod_map,Function.comp_def]

theorem assignment_map_compl {k : ℕ} (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    Sᶜ.map σ.toEmbedding = (S.map σ.toEmbedding)ᶜ := by
  ext i
  simp [Finset.mem_map,Equiv.apply_eq_iff_eq_symm_apply]

/-- The original multiplication map from labelled polynomial words. -/
def polynomialWordMap (k : ℕ) : WordSpace α k →ₗ[ℂ] MvPolynomial α ℂ :=
  Finsupp.linearCombination ℂ (fun u => subsetPolynomial u Finset.univ)

/-- The actual two-block multiplication map belonging to an assignment. -/
def polynomialBlockWordMap {k r : ℕ} (S : Assignment k r) :
    WordSpace α k →ₗ[ℂ] MvPolynomial α ℂ ⊗[ℂ] MvPolynomial α ℂ :=
  Finsupp.linearCombination ℂ (fun u => subsetPolynomial u S.val ⊗ₜ[ℂ] subsetPolynomial u S.valᶜ)

@[simp] theorem polynomialWordMap_single (k : ℕ) (u : Fin k → α) (c : ℂ) :
    polynomialWordMap k (Finsupp.single u c) = c • subsetPolynomial u Finset.univ :=
  Finsupp.linearCombination_single _ _ _

@[simp] theorem polynomialBlockWordMap_single {k r : ℕ} (S : Assignment k r)
    (u : Fin k → α) (c : ℂ) :
    polynomialBlockWordMap S (Finsupp.single u c) =
      c • (subsetPolynomial u S.val ⊗ₜ[ℂ] subsetPolynomial u S.valᶜ) :=
  Finsupp.linearCombination_single _ _ _

/-- Actual block multiplication transforms by the literal permutation of assignments. -/
theorem polynomialBlockWordMap_permute {k r : ℕ} (σ : Equiv.Perm (Fin k))
    (S : Assignment k r) (x : WordSpace α k) :
    polynomialBlockWordMap S (wordPermute σ x) =
      polynomialBlockWordMap (assignmentPermute σ S) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single u c =>
    rw [wordPermute_single,polynomialBlockWordMap_single,polynomialBlockWordMap_single,
      subsetPolynomial_permute,subsetPolynomial_permute,assignment_map_compl]
    rfl

/-- Exact normalization for generic symmetric block multiplication. -/
theorem polynomialBlockWordMap_average {k r : ℕ} (S : Assignment k r) (x : WordSpace α k) :
    ∑ U : Assignment k r, polynomialBlockWordMap U x =
      (Nat.choose k r : ℂ) • polynomialBlockWordMap S (wordAverage k x) :=
  sum_block_eq_choose_average (fun σ => wordPermute σ) polynomialBlockWordMap
    polynomialBlockWordMap_permute S x

private theorem prod_tmul_left_polynomial {k : ℕ} (u : Fin k → α) (S : Finset (Fin k)) :
    (∏ i ∈ S, (MvPolynomial.X (u i) : MvPolynomial α ℂ) ⊗ₜ[ℂ] (1 : MvPolynomial α ℂ)) =
      subsetPolynomial u S ⊗ₜ[ℂ] (1 : MvPolynomial α ℂ) := by
  induction S using Finset.induction_on with
  | empty => simp [subsetPolynomial,Algebra.TensorProduct.one_def]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi,subsetPolynomial,ih,Algebra.TensorProduct.tmul_mul_tmul,one_mul]

private theorem prod_tmul_right_polynomial {k : ℕ} (u : Fin k → α) (S : Finset (Fin k)) :
    (∏ i ∈ S, (1 : MvPolynomial α ℂ) ⊗ₜ[ℂ] (MvPolynomial.X (u i) : MvPolynomial α ℂ)) =
      (1 : MvPolynomial α ℂ) ⊗ₜ[ℂ] subsetPolynomial u S := by
  induction S using Finset.induction_on with
  | empty => simp [subsetPolynomial,Algebra.TensorProduct.one_def]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi,subsetPolynomial,ih,Algebra.TensorProduct.tmul_mul_tmul,one_mul]

/-- The primitive coproduct is exactly the sum over all labelled subsets. -/
theorem polynomialPrimitive_word (k : ℕ) (u : Fin k → α) :
    polynomialPrimitive (subsetPolynomial u Finset.univ) =
      ∑ S : Finset (Fin k), subsetPolynomial u S ⊗ₜ[ℂ] subsetPolynomial u Sᶜ := by
  rw [subsetPolynomial,map_prod]
  simp only [polynomialPrimitive_X]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [prod_tmul_left_polynomial,prod_tmul_right_polynomial,
    Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]

end KhanSL2.SymmetricFamily
