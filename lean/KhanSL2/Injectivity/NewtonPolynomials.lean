module

public import KhanSL2.Injectivity.NewtonCycles
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! # Polynomial specialization of the finite Newton cycles -/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

open Finset MvPolynomial

variable (σ : Type*) [Fintype σ] (R : Type*) [CommRing R]

/-- Coefficients of the elementary polynomial `∏ᵢ (1 - uᵢ t)`. -/
def signedElementary (k : ℕ) : MvPolynomial σ R := (-1) ^ k * esymm σ R k

@[simp] theorem signedElementary_zero : signedElementary σ R 0 = 1 := by
  simp [signedElementary]

theorem signedElementary_eq_zero {k : ℕ} (hk : Fintype.card σ < k) :
    signedElementary σ R k = 0 := by
  classical
  simp only [signedElementary, esymm]
  rw [powersetCard_eq_empty.mpr (by simpa using hk), sum_empty, mul_zero]

/-- The library's Newton identity, expressed in the finite-recursion convention. -/
theorem signedElementary_satisfiesNewton :
    SatisfiesNewton (signedElementary σ R) (psum σ R) := by
  classical
  intro n
  have hsum :
      (∑ b ∈ {b ∈ antidiagonal (n + 1) | b.1 < n + 1},
        (-1 : MvPolynomial σ R) ^ b.1 * esymm σ R b.1 * psum σ R b.2) =
      ∑ j ∈ range (n + 1), psum σ R (j + 1) * signedElementary σ R (n - j) := by
    symm
    apply sum_bij (fun j _ => (n - j, j + 1))
    · intro j hj
      have hj' := mem_range.mp hj
      simp only [mem_filter, mem_antidiagonal]
      constructor <;> omega
    · intro i _hi j _hj hij
      have := congrArg Prod.snd hij
      simpa using this
    · intro b hb
      simp only [mem_filter, mem_antidiagonal] at hb
      refine ⟨b.2 - 1, mem_range.mpr (by omega), ?_⟩
      ext <;> simp only <;> omega
    · intro j _hj
      simp only [signedElementary]
      ring
  have hnew := mul_esymm_eq_sum σ R (n + 1)
  rw [hsum] at hnew
  have hsign :
      (-1 : MvPolynomial σ R) ^ (n + 1) * (-1) ^ (n + 1 + 1) = -1 := by
    rw [pow_succ (-1 : MvPolynomial σ R) (n + 1), ← mul_assoc, ← mul_pow]
    simp
  calc
    ((n + 1 : ℕ) : MvPolynomial σ R) * signedElementary σ R (n + 1) =
        (-1) ^ (n + 1) * (((n + 1 : ℕ) : MvPolynomial σ R) * esymm σ R (n + 1)) := by
          simp only [signedElementary]
          ring
    _ = (-1) ^ (n + 1) * ((-1) ^ (n + 1 + 1) *
        ∑ j ∈ range (n + 1), psum σ R (j + 1) * signedElementary σ R (n - j)) := by
          rw [hnew]
    _ = _ := by rw [← mul_assoc, hsign, neg_one_mul]

end KhanSL2.Injectivity
