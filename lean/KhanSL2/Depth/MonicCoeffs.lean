module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Operations

@[expose] public section

/-!
# Monic polynomials in coefficient coordinates

* `monicOf n f = X^n + Σ_{k<n} f k X^k`, the monic polynomial with lower coefficients `f`.
* Over a field, a monic divisor of `(X - C a)^n` is a power of `X - C a`
  (`eq_X_sub_C_pow_of_dvd`).
* **Full collision in coefficients**: a monic polynomial `F` of degree `B ≥ 1` over a field of
  characteristic zero with `F_{B-i} = C(B,i) (F_{B-1}/B)^i` for `2 ≤ i ≤ B` is
  `(X + C (F_{B-1}/B))^B` (`eq_X_add_C_pow_of_collision`).
-/

noncomputable section

open Polynomial

namespace KhanSL2.Depth

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The monic polynomial `X^n + Σ_{k<n} f k X^k`. -/
def monicOf (n : ℕ) (f : Fin n → R) : R[X] := X ^ n + ∑ k : Fin n, C (f k) * X ^ (k : ℕ)

theorem monicOf_monic [Nontrivial R] (n : ℕ) (f : Fin n → R) : (monicOf n f).Monic :=
  monic_X_pow_add (degree_sum_fin_lt f)

theorem natDegree_monicOf [Nontrivial R] (n : ℕ) (f : Fin n → R) :
    (monicOf n f).natDegree = n := by
  rw [monicOf, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt f

theorem coeff_monicOf (n : ℕ) (f : Fin n → R) (k : Fin n) : (monicOf n f).coeff k = f k := by
  classical
  rw [monicOf, coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt k.isLt), zero_add, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem map_monicOf (φ : R →+* S) (n : ℕ) (f : Fin n → R) :
    (monicOf n f).map φ = monicOf n (φ ∘ f) := by
  simp [monicOf, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sum]

end Ring

section Field

variable {K : Type*} [Field K]

/-- A monic divisor of `(X - C a)^n` is a power of `X - C a`. -/
theorem eq_X_sub_C_pow_of_dvd {p : K[X]} (hp : p.Monic) {a : K} {n : ℕ}
    (h : p ∣ (X - C a) ^ n) : p = (X - C a) ^ p.natDegree := by
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow (prime_X_sub_C a) n).mp h
  have heq := eq_of_monic_of_associated hp ((monic_X_sub_C a).pow i) hi
  rw [heq, natDegree_pow, natDegree_X_sub_C, mul_one]

variable [CharZero K]

/-- **Full collision, in coefficients.** -/
theorem eq_X_add_C_pow_of_collision {F : K[X]} {B : ℕ} (hB : 1 ≤ B) (hF : F.Monic)
    (hdeg : F.natDegree = B)
    (h : ∀ i, 2 ≤ i → i ≤ B →
      F.coeff (B - i) = (B.choose i : K) * (F.coeff (B - 1) / B) ^ i) :
    F = (X + C (F.coeff (B - 1) / B)) ^ B := by
  set b := F.coeff (B - 1) / B
  have hBK : (B : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  ext n
  rw [coeff_X_add_C_pow]
  rcases lt_trichotomy n B with hn | rfl | hn
  · obtain ⟨i, hi1, hiB, rfl⟩ : ∃ i, 1 ≤ i ∧ i ≤ B ∧ n = B - i :=
      ⟨B - n, by omega, by omega, by omega⟩
    rw [show B - (B - i) = i by omega, Nat.choose_symm hiB]
    rcases hi1.eq_or_lt with rfl | hi2
    · rw [pow_one, Nat.choose_one_right, mul_comm, show b = F.coeff (B - 1) / B from rfl,
        mul_div_cancel₀ _ hBK]
    · rw [h i hi2 hiB, mul_comm]
  · rw [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
    have := hF.leadingCoeff
    rwa [leadingCoeff, hdeg] at this
  · rw [coeff_eq_zero_of_natDegree_lt (hdeg ▸ hn), Nat.choose_eq_zero_of_lt hn, Nat.cast_zero,
      mul_zero]

omit [CharZero K] in
theorem X_add_C_eq_X_sub_C (b : K) : X + C b = X - C (-b) := by
  rw [C_neg, sub_neg_eq_add]

end Field

end KhanSL2.Depth
