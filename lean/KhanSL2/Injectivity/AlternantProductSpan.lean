module

public import KhanSL2.Injectivity.BlockSymmetry
public import KhanSL2.Injectivity.SchurAlternants
public import KhanSL2.Injectivity.VandermondeFactors

@[expose] public section

/-! The explicit polynomial family required from the closed Cartan chains. -/

noncomputable section
open MvPolynomial Finset

namespace KhanSL2.Injectivity

def cyclePolynomial (r s : ℕ) (e : Fin r → ℕ) (p : MvPolynomial (Fin s) ℂ) :
    MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  xVandermonde r s * yVandermonde r s ^ 3 * crossFactor r s ^ 2 *
    rename Sum.inl (TauCeti.alternant (Fin r) ℂ e) * rename Sum.inr p

def cyclePolynomialSpan (r s : ℕ) : Submodule ℂ (MvPolynomial (Fin r ⊕ Fin s) ℂ) :=
  Submodule.span ℂ (Set.range fun ep : (Fin r → ℕ) ×
    {p : MvPolynomial (Fin s) ℂ // p.IsSymmetric} => cyclePolynomial r s ep.1 ep.2.val)

theorem cyclePolynomial_mem (r s : ℕ) (e : Fin r → ℕ) (p : MvPolynomial (Fin s) ℂ)
    (hp : p.IsSymmetric) : cyclePolynomial r s e p ∈ cyclePolynomialSpan r s :=
  Submodule.subset_span ⟨(e, ⟨p, hp⟩), rfl⟩

def alternantLift (r s : ℕ) (q : MvPolynomial (Fin s) ℂ) :
    MvPolynomial (Fin r) ℂ →ₗ[ℂ] MvPolynomial (Fin r ⊕ Fin s) ℂ where
  toFun p := xVandermonde r s * yVandermonde r s ^ 3 * crossFactor r s ^ 2 *
    rename Sum.inl p * rename Sum.inr q
  map_add' p t := by simp [map_add, mul_add, add_mul]
  map_smul' c p := by simp [map_smul, mul_smul_comm, smul_mul_assoc]

theorem alternantLift_mem (r s : ℕ) (q : MvPolynomial (Fin s) ℂ) (hq : q.IsSymmetric)
    (p : MvPolynomial (Fin r) ℂ) (hp : p ∈ orderedAlternantSpan r ℂ) :
    alternantLift r s q p ∈ cyclePolynomialSpan r s := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨e, rfl⟩ := hp
    exact cyclePolynomial_mem r s e q hq
  | zero => simp
  | add p t _ _ hp ht => simpa only [map_add] using Submodule.add_mem _ hp ht
  | smul c p _ hp => simpa only [map_smul] using Submodule.smul_mem _ c hp

theorem rename_vandermonde (r s : ℕ) :
    rename Sum.inl (∏ i : Fin r, ∏ j ∈ Ioi i, (X j - X i : MvPolynomial (Fin r) ℂ)) =
      xVandermonde r s := by
  simp [xVandermonde, Matrix.det_vandermonde]

theorem discriminant_symmetricProduct_mem (r s : ℕ)
    (p : MvPolynomial (Fin r) ℂ) (q : MvPolynomial (Fin s) ℂ)
    (hp : p.IsSymmetric) (hq : q.IsSymmetric) :
    discriminantFactor r s * (rename Sum.inl p * rename Sum.inr q) ∈
      cyclePolynomialSpan r s := by
  have h := alternantLift_mem r s q hq _
    (symmetric_mul_vandermonde_mem_orderedSpan r p hp)
  change xVandermonde r s * yVandermonde r s ^ 3 * crossFactor r s ^ 2 *
    rename Sum.inl (p * ∏ i : Fin r, ∏ j ∈ Ioi i, (X j - X i)) * rename Sum.inr q ∈ _ at h
  rw [map_mul, rename_vandermonde] at h
  rw [discriminantFactor_eq]
  convert h using 1; ring

theorem discriminant_mul_mem_cyclePolynomialSpan (r s : ℕ)
    (q : MvPolynomial (Fin r ⊕ Fin s) ℂ)
    (hq : ∀ (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)),
      rename (Equiv.sumCongr e f) q = q) :
    discriminantFactor r s * q ∈ cyclePolynomialSpan r s := by
  have hq' := block_symmetric_mem_productSpan q hq
  clear hq
  induction hq' using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, rfl⟩ := hp
    exact discriminant_symmetricProduct_mem r s p q hp hq
  | zero => simp
  | add p q _ _ hp hq => simpa only [mul_add] using Submodule.add_mem _ hp hq
  | smul c p _ hp => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hp

end KhanSL2.Injectivity
