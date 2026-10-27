module

public import KhanSL2.Macdonald.Basic
public import KhanSL2.Injectivity.FiniteSupport

@[expose] public section

/-! Actual monomial degrees. Index-zero polynomial variables have weight zero,
so symmetric degree must be fixed separately from weight. -/

noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.Macdonald

def polynomialDegree (d : Exponent) : ℕ := d.sum fun _ n => n
def polynomialWeight (d : Exponent) : ℕ := d.sum fun m n => m.index * n
def exteriorWeight (t : Finset Mode) : ℕ := t.sum (fun m => m.index + 1)
def weight (b : BasisIndex) : ℕ := polynomialWeight b.1 + exteriorWeight b.2
def symmetricDegree (b : BasisIndex) : ℕ := polynomialDegree b.1
def exteriorDegree (b : BasisIndex) : ℕ := b.2.card
def basisDegree (b : BasisIndex) : ℕ × ℕ × ℕ :=
  (weight b, symmetricDegree b, exteriorDegree b)

/-- The span of monomials of the specified weight and two degrees. -/
def piece (w s k : ℕ) : Submodule ℂ W :=
  (Finsupp.supported ℂ ℂ
    {b : BasisIndex | weight b = w ∧ symmetricDegree b = s ∧ exteriorDegree b = k}).comap
      basis.repr.toLinearMap

theorem mem_piece_iff (u : W) (w s k : ℕ) :
    u ∈ piece w s k ↔ ∀ b ∈ (basis.repr u).support,
      weight b = w ∧ symmetricDegree b = s ∧ exteriorDegree b = k := Iff.rfl

theorem basis_mem_piece (b : BasisIndex) :
    basis b ∈ piece (weight b) (symmetricDegree b) (exteriorDegree b) := by
  change basis.repr (basis b) ∈ Finsupp.supported ℂ ℂ _
  rw [Module.Basis.repr_self]
  exact Finsupp.single_mem_supported ℂ 1 ⟨rfl, rfl, rfl⟩

theorem eq_sum_basis (u : W) :
    u = ∑ b ∈ (basis.repr u).support, basis.repr u b • basis b := by
  symm
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using basis.linearCombination_repr u

@[simp] theorem polynomialDegree_zero : polynomialDegree 0 = 0 := by simp [polynomialDegree]
@[simp] theorem polynomialWeight_zero : polynomialWeight 0 = 0 := by simp [polynomialWeight]
@[simp] theorem exteriorWeight_empty : exteriorWeight ∅ = 0 := by simp [exteriorWeight]
@[simp] theorem polynomialDegree_single (m : Mode) (n : ℕ) :
    polynomialDegree (Finsupp.single m n) = n := by simp [polynomialDegree]
@[simp] theorem polynomialWeight_single (m : Mode) (n : ℕ) :
    polynomialWeight (Finsupp.single m n) = m.index * n := by simp [polynomialWeight]
@[simp] theorem exteriorWeight_singleton (m : Mode) :
    exteriorWeight {m} = m.index + 1 := by simp [exteriorWeight]

theorem polynomialDegree_add (d e : Exponent) :
    polynomialDegree (d + e) = polynomialDegree d + polynomialDegree e := by
  unfold polynomialDegree
  apply Finsupp.sum_add_index <;> intros <;> rfl

theorem polynomialWeight_add (d e : Exponent) :
    polynomialWeight (d + e) = polynomialWeight d + polynomialWeight e := by
  unfold polynomialWeight
  apply Finsupp.sum_add_index <;> intros <;> simp [Nat.mul_add]

theorem exteriorWeight_union {t v : Finset Mode} (h : Disjoint t v) :
    exteriorWeight (t ∪ v) = exteriorWeight t + exteriorWeight v := by
  unfold exteriorWeight
  exact Finset.sum_union h

theorem sigma_mem_piece (a : Fin 3) (n : ℕ) : sigma a n ∈ piece n 1 0 := by
  have h := basis_mem_piece (Finsupp.single (⟨n,a⟩ : Mode) 1, ∅)
  simpa [weight, symmetricDegree, exteriorDegree, basis, BGG.PolynomialKoszul.basis_apply,
    sigma, MvPolynomial.X, FiniteExterior.one_def, FiniteExterior.monomial] using h

theorem psi_mem_piece (a : Fin 3) (i : ℕ) : psi a i ∈ piece (i+1) 0 1 := by
  have h := basis_mem_piece (0, {(⟨i,a⟩ : Mode)})
  simpa [weight, symmetricDegree, exteriorDegree, basis, BGG.PolynomialKoszul.basis_apply,
    psi, FiniteExterior.generator, FiniteExterior.monomial] using h

theorem one_mem_piece : (1 : W) ∈ piece 0 0 0 := by
  have h := basis_mem_piece (0, ∅)
  simpa [weight, symmetricDegree, exteriorDegree, basis, BGG.PolynomialKoszul.basis_apply,
    FiniteExterior.one_def, FiniteExterior.monomial, Algebra.TensorProduct.one_def] using h

private theorem basis_mul_mem_piece (b c : BasisIndex) :
    basis b * basis c ∈ piece (weight b + weight c)
      (symmetricDegree b + symmetricDegree c) (exteriorDegree b + exteriorDegree c) := by
  obtain ⟨d,t⟩ := b
  obtain ⟨e,v⟩ := c
  rw [basis_apply, basis_apply]
  rw [Algebra.TensorProduct.tmul_mul_tmul, MvPolynomial.monomial_mul_monomial, one_mul]
  change MvPolynomial.monomial (d+e) (1 : ℂ) ⊗ₜ[ℂ]
    FiniteExterior.wedge BGG.PositiveCE.Mode.code
      (FiniteExterior.monomial t) (FiniteExterior.monomial v) ∈ (piece _ _ _)
  rw [FiniteExterior.wedge_monomial, FiniteExterior.monomialWedge]
  split
  next h =>
    have hs (r : ℂ) : Finsupp.single (t ∪ v) r = r • FiniteExterior.monomial (t ∪ v) := by
      simp [FiniteExterior.monomial]
    rw [hs]
    rw [TensorProduct.tmul_smul]
    apply Submodule.smul_mem
    have ht := basis_mem_piece (d+e,t∪v)
    simpa only [weight, symmetricDegree, exteriorDegree, polynomialDegree_add,
      polynomialWeight_add, exteriorWeight_union h, Finset.card_union_of_disjoint h,
      basis, BGG.PolynomialKoszul.basis_apply, add_assoc, add_left_comm, add_comm] using ht
  next h => simp

theorem mul_mem_piece {w s k w' s' k' : ℕ} {u v : W}
    (hu : u ∈ piece w s k) (hv : v ∈ piece w' s' k') :
    u * v ∈ piece (w+w') (s+s') (k+k') := by
  rw [eq_sum_basis u]
  simp only [Finset.sum_mul, smul_mul_assoc]
  apply Submodule.sum_mem
  intro b hb
  apply Submodule.smul_mem
  rw [eq_sum_basis v]
  simp only [Finset.mul_sum, mul_smul_comm]
  apply Submodule.sum_mem
  intro c hc
  apply Submodule.smul_mem
  obtain ⟨hbw,hbs,hbk⟩ := (mem_piece_iff u w s k).mp hu b hb
  obtain ⟨hcw,hcs,hck⟩ := (mem_piece_iff v w' s' k').mp hv c hc
  simpa only [hbw,hbs,hbk,hcw,hcs,hck] using basis_mul_mem_piece b c

end KhanSL2.Macdonald




