module

public import KhanSL2.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Finite averaging separates the two symmetric alphabets. -/

noncomputable section
open MvPolynomial Finset

namespace KhanSL2.Injectivity

variable {r s : ℕ}

def symmetricMean (n : ℕ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
    ∑ e : Equiv.Perm (Fin n), (rename e).toLinearMap

theorem symmetricMean_symmetric (n : ℕ) (p : MvPolynomial (Fin n) ℂ) :
    (symmetricMean n p).IsSymmetric := by
  classical
  intro e
  simp only [symmetricMean, LinearMap.smul_apply, LinearMap.sum_apply, AlgHom.toLinearMap_apply, map_smul, map_sum]
  congr 1
  calc
    _ = ∑ f : Equiv.Perm (Fin n), rename (e * f) p := by
      apply sum_congr rfl
      intro f _
      simp [rename_rename, Equiv.Perm.coe_mul]
    _ = _ := (Group.mulLeft_bijective e).sum_comp (fun f : Equiv.Perm (Fin n) => rename f p)

def blockMean (r s : ℕ) :
    MvPolynomial (Fin r ⊕ Fin s) ℂ →ₗ[ℂ] MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  (Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹ •
    ((Fintype.card (Equiv.Perm (Fin s)) : ℂ)⁻¹ •
      ∑ e : Equiv.Perm (Fin r), ∑ f : Equiv.Perm (Fin s),
        (rename (Equiv.sumCongr e f)).toLinearMap)

theorem blockMean_fixed (p : MvPolynomial (Fin r ⊕ Fin s) ℂ)
    (hp : ∀ (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)),
      rename (Equiv.sumCongr e f) p = p) : blockMean r s p = p := by
  classical
  have hr : (Fintype.card (Equiv.Perm (Fin r)) : ℂ) ≠ 0 := by simp
  have hs : (Fintype.card (Equiv.Perm (Fin s)) : ℂ) ≠ 0 := by simp
  simp only [blockMean, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgHom.toLinearMap_apply, hp, sum_const, card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hc : (Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹ *
      ((Fintype.card (Equiv.Perm (Fin s)) : ℂ)⁻¹ *
        ((Fintype.card (Equiv.Perm (Fin r)) : ℂ) *
          (Fintype.card (Equiv.Perm (Fin s)) : ℂ))) = 1 := by field_simp
  simp only [mul_assoc, hc, one_smul]

theorem rename_block_product (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s))
    (p : MvPolynomial (Fin r) ℂ) (q : MvPolynomial (Fin s) ℂ) :
    rename (Equiv.sumCongr e f) (rename Sum.inl p * rename Sum.inr q) =
      rename Sum.inl (rename e p) * rename Sum.inr (rename f q) := by
  simp only [map_mul, rename_rename]
  rfl

theorem blockMean_product (p : MvPolynomial (Fin r) ℂ) (q : MvPolynomial (Fin s) ℂ) :
    blockMean r s (rename Sum.inl p * rename Sum.inr q) =
      rename Sum.inl (symmetricMean r p) * rename Sum.inr (symmetricMean s q) := by
  classical
  simp only [blockMean, symmetricMean, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgHom.toLinearMap_apply, rename_block_product, map_smul, map_sum,
    smul_mul_smul_comm, sum_mul, mul_sum, smul_smul]
  congr 1
  exact sum_comm

def separatedProductSpan (r s : ℕ) : Submodule ℂ (MvPolynomial (Fin r ⊕ Fin s) ℂ) :=
  Submodule.span ℂ (Set.range fun pq : MvPolynomial (Fin r) ℂ × MvPolynomial (Fin s) ℂ =>
    rename Sum.inl pq.1 * rename Sum.inr pq.2)

theorem separatedProduct_mem (p : MvPolynomial (Fin r) ℂ) (q : MvPolynomial (Fin s) ℂ) :
    rename Sum.inl p * rename Sum.inr q ∈ separatedProductSpan r s :=
  Submodule.subset_span ⟨(p, q), rfl⟩

theorem separatedProductSpan_mul_X (p : MvPolynomial (Fin r ⊕ Fin s) ℂ)
    (hp : p ∈ separatedProductSpan r s) (i : Fin r ⊕ Fin s) :
    p * X i ∈ separatedProductSpan r s := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hp
    cases i with
    | inl i =>
      have h := separatedProduct_mem (r := r) (s := s) (p * X i) q
      rw [map_mul, rename_X] at h
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    | inr i =>
      have h := separatedProduct_mem (r := r) (s := s) p (q * X i)
      rw [map_mul, rename_X] at h
      simpa only [mul_assoc] using h
  | zero => simp
  | add a b _ _ ha hb => simpa only [add_mul] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ha

theorem mem_separatedProductSpan (p : MvPolynomial (Fin r ⊕ Fin s) ℂ) :
    p ∈ separatedProductSpan r s := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using separatedProduct_mem (C c : MvPolynomial (Fin r) ℂ) (1 : MvPolynomial (Fin s) ℂ)
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | mul_X p i hp => exact separatedProductSpan_mul_X p hp i

def symmetricProductSpan (r s : ℕ) : Submodule ℂ (MvPolynomial (Fin r ⊕ Fin s) ℂ) :=
  Submodule.span ℂ (Set.range fun pq :
    {p : MvPolynomial (Fin r) ℂ // p.IsSymmetric} ×
      {q : MvPolynomial (Fin s) ℂ // q.IsSymmetric} =>
        rename Sum.inl pq.1.val * rename Sum.inr pq.2.val)

theorem symmetricProduct_mem (p : MvPolynomial (Fin r) ℂ) (q : MvPolynomial (Fin s) ℂ)
    (hp : p.IsSymmetric) (hq : q.IsSymmetric) :
    rename Sum.inl p * rename Sum.inr q ∈ symmetricProductSpan r s :=
  Submodule.subset_span ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩

theorem blockMean_mem_symmetricProductSpan (p : MvPolynomial (Fin r ⊕ Fin s) ℂ) :
    blockMean r s p ∈ symmetricProductSpan r s := by
  have hp := mem_separatedProductSpan p
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hp
    rw [blockMean_product]
    exact symmetricProduct_mem _ _ (symmetricMean_symmetric r p) (symmetricMean_symmetric s q)
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- Every polynomial invariant under the two permutation groups is a finite
linear combination of products of symmetric polynomials in the separate blocks. -/
theorem block_symmetric_mem_productSpan (p : MvPolynomial (Fin r ⊕ Fin s) ℂ)
    (hp : ∀ (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)),
      rename (Equiv.sumCongr e f) p = p) : p ∈ symmetricProductSpan r s := by
  rw [← blockMean_fixed p hp]
  exact blockMean_mem_symmetricProductSpan p

end KhanSL2.Injectivity
