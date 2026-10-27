module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

/-! Finite polynomial diagonal specialization and its divisibility consequences. -/

noncomputable section

namespace KhanSL2.Injectivity

open MvPolynomial

variable {σ R : Type*} [DecidableEq σ] [CommRing R]

/-- Set the variable `i` equal to the variable `j`. -/
def diagonal (i j : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := by
  classical
  exact aeval (fun k => if k = i then X j else X k)

@[simp] theorem diagonal_X (i j k : σ) :
    diagonal (R := R) i j (X k) = (if k = i then X j else X k) := by
  classical
  simp [diagonal]

@[simp] theorem diagonal_C (i j : σ) (r : R) :
    diagonal i j (C r) = C r := by
  simp [diagonal]

/-- The difference from diagonal specialization is divisible by the diagonal equation. -/
theorem diagonal_dvd_sub (i j : σ) (p : MvPolynomial σ R) :
    (X i - X j : MvPolynomial σ R) ∣ p - diagonal i j p := by
  classical
  refine MvPolynomial.induction_on (motive := fun p : MvPolynomial σ R => (X i - X j) ∣ p - diagonal i j p) p (fun r => ?_) (fun p q hp hq => ?_) (fun p k hp => ?_)
  · simp
  ·
      simpa only [map_add, add_sub_add_comm] using dvd_add hp hq
  ·
      have hk : (X i - X j : MvPolynomial σ R) ∣ X k - diagonal i j (X k) := by
        by_cases h : k = i
        · subst k
          simp
        · simp [h]
      have hd := dvd_add (dvd_mul_of_dvd_left hp (X k))
        (dvd_mul_of_dvd_right hk (diagonal i j p))
      change (X i - X j : MvPolynomial σ R) ∣ p * X k - diagonal i j (p * X k)
      rw [map_mul]
      convert hd using 1
      ring

/-- Vanishing on a diagonal is exactly divisibility by its linear equation. -/
theorem diagonal_eq_zero_iff_dvd {i j : σ} (hij : i ≠ j)
    (p : MvPolynomial σ R) :
    diagonal i j p = 0 ↔ (X i - X j : MvPolynomial σ R) ∣ p := by
  classical
  constructor
  · intro hp
    simpa [hp] using diagonal_dvd_sub i j p
  · rintro ⟨q, rfl⟩
    simp [Ne.symm hij]

/-- Vanishing of both value and first normal derivative gives a double diagonal factor. -/
theorem diagonal_sq_dvd {i j : σ} (hij : i ≠ j) (p : MvPolynomial σ R)
    (hp : diagonal i j p = 0) (hdp : diagonal i j (pderiv i p) = 0) :
    (X i - X j : MvPolynomial σ R) ^ 2 ∣ p := by
  classical
  obtain ⟨q, rfl⟩ := (diagonal_eq_zero_iff_dvd hij p).mp hp
  have hq : diagonal i j q = 0 := by
    simpa [map_sub, pderiv_mul, hij, Ne.symm hij] using hdp
  obtain ⟨r, hr⟩ := (diagonal_eq_zero_iff_dvd hij q).mp hq
  exact ⟨r, by rw [hr]; ring⟩

/-- Swapping the two identified variables has no effect after specialization. -/
theorem diagonal_rename_swap (i j : σ) (p : MvPolynomial σ R) :
    diagonal i j (rename (Equiv.swap i j) p) = diagonal i j p := by
  classical
  have h : (diagonal (R := R) i j).comp (rename (Equiv.swap i j)) = diagonal i j := by
    ext k
    by_cases hi : k = i
    · subst k
      simp
    · by_cases hj : k = j
      · subst k
        simp
      · simp [Equiv.swap_apply_of_ne_of_ne hi hj, hi]
  exact AlgHom.congr_fun h p

/-- An alternating complex polynomial vanishes when the exchanged variables coincide. -/
theorem diagonal_eq_zero_of_antisymmetric (i j : σ) (p : MvPolynomial σ ℂ)
    (hp : rename (Equiv.swap i j) p = -p) : diagonal i j p = 0 := by
  have h := diagonal_rename_swap i j p
  rw [hp, map_neg] at h
  have ht : (2 : ℂ) • diagonal i j p = 0 := by
    calc
      (2 : ℂ) • diagonal i j p = diagonal i j p + diagonal i j p := by
        rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
      _ = 0 := by exact neg_eq_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

/-- A symmetric polynomial that vanishes on a diagonal has at least a double zero. -/
theorem diagonal_sq_dvd_of_symmetric {i j : σ} (hij : i ≠ j)
    (p : MvPolynomial σ ℂ) (hp : diagonal i j p = 0)
    (hs : rename (Equiv.swap i j) p = p) : (X i - X j : MvPolynomial σ ℂ) ^ 2 ∣ p := by
  obtain ⟨q, rfl⟩ := (diagonal_eq_zero_iff_dvd hij p).mp hp
  have hn : (X i - X j : MvPolynomial σ ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hij (MvPolynomial.X_injective h))
  have hq : rename (Equiv.swap i j) q = -q := by
    have hh : (X i - X j : MvPolynomial σ ℂ) * rename (Equiv.swap i j) q =
        (X i - X j) * (-q) := by
      have hs' : (X j - X i : MvPolynomial σ ℂ) * rename (Equiv.swap i j) q =
          (X i - X j) * q := by simpa using hs
      calc
        (X i - X j) * rename (Equiv.swap i j) q =
            -((X j - X i) * rename (Equiv.swap i j) q) := by ring
        _ = -((X i - X j) * q) := by rw [hs']
        _ = (X i - X j) * (-q) := by ring
    exact mul_left_cancel₀ hn hh
  obtain ⟨r, hr⟩ := (diagonal_eq_zero_iff_dvd hij q).mp
    (diagonal_eq_zero_of_antisymmetric i j q hq)
  exact ⟨r, by rw [hr]; ring⟩

/-- An alternating polynomial with vanishing normal derivative has a triple zero. -/
theorem diagonal_cube_dvd_of_antisymmetric {i j : σ} (hij : i ≠ j)
    (p : MvPolynomial σ ℂ) (hs : rename (Equiv.swap i j) p = -p)
    (hdp : diagonal i j (pderiv i p) = 0) :
    (X i - X j : MvPolynomial σ ℂ) ^ 3 ∣ p := by
  obtain ⟨q, hq⟩ := diagonal_sq_dvd hij p
    (diagonal_eq_zero_of_antisymmetric i j p hs) hdp
  have hn : (X i - X j : MvPolynomial σ ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (fun h => hij (MvPolynomial.X_injective h)))
  have hqs : rename (Equiv.swap i j) q = -q := by
    rw [hq, map_mul, map_pow, map_sub, rename_X, rename_X,
      Equiv.swap_apply_left, Equiv.swap_apply_right] at hs
    have he : (X j - X i : MvPolynomial σ ℂ) ^ 2 = (X i - X j) ^ 2 := by ring
    rw [he, ← mul_neg] at hs
    exact mul_left_cancel₀ hn hs
  obtain ⟨r, hr⟩ := (diagonal_eq_zero_iff_dvd hij q).mp
    (diagonal_eq_zero_of_antisymmetric i j q hqs)
  exact ⟨r, by rw [hq, hr]; ring⟩

/-- Every genuine diagonal equation is prime. -/
theorem diagonal_prime {i j : σ} (hij : i ≠ j) :
    Prime (X i - X j : MvPolynomial σ ℂ) := by
  refine ⟨sub_ne_zero.mpr (fun h => hij (MvPolynomial.X_injective h)), ?_, ?_⟩
  · intro hu
    have hu' := hu.map (diagonal (R := ℂ) i j).toMonoidHom
    change IsUnit (diagonal (R := ℂ) i j (X i - X j)) at hu'
    have hz : diagonal (R := ℂ) i j (X i - X j) = 0 := by simp [Ne.symm hij]
    rw [hz] at hu'
    exact not_isUnit_zero hu'
  · intro a b hab
    have h := (diagonal_eq_zero_iff_dvd hij (a * b)).mpr hab
    rw [map_mul] at h
    exact (mul_eq_zero.mp h).imp
      ((diagonal_eq_zero_iff_dvd hij a).mp)
      ((diagonal_eq_zero_iff_dvd hij b).mp)

/-- Distinct diagonals can divide one another only by reversing their endpoints. -/
theorem diagonal_dvd_diagonal_iff {i j k l : σ} (hij : i ≠ j) (hkl : k ≠ l) :
    (X i - X j : MvPolynomial σ ℂ) ∣ X k - X l ↔
      (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
  rw [← diagonal_eq_zero_iff_dvd hij]
  constructor
  · intro h
    have he : (if k = i then j else k) = (if l = i then j else l) := by
      apply MvPolynomial.X_injective (R := ℂ)
      apply sub_eq_zero.mp
      simpa only [map_sub, diagonal_X, apply_ite] using h
    by_cases hk : k = i
    · by_cases hl : l = i
      · exact (hkl (hk.trans hl.symm)).elim
      · simp only [hk, ite_eq_right hl] at he
        exact Or.inl ⟨hk, he.symm⟩
    · by_cases hl : l = i
      · simp only [ite_eq_right hk, hl] at he
        exact Or.inr ⟨he, hl⟩
      · simp only [ite_eq_right hk, ite_eq_right hl] at he
        exact (hkl he).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [Ne.symm hij]

/-- Two distinct unoriented diagonal equations have no nonunit common factor. -/
theorem diagonal_isRelPrime {i j k l : σ} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ¬ ((k = i ∧ l = j) ∨ (k = j ∧ l = i))) :
    IsRelPrime (X i - X j : MvPolynomial σ ℂ) (X k - X l) := by
  have hnot : ¬ (X i - X j : MvPolynomial σ ℂ) ∣ X k - X l :=
    fun h => hne ((diagonal_dvd_diagonal_iff hij hkl).mp h)
  intro d hd hd'
  obtain ⟨e, he⟩ := hd
  rcases (diagonal_prime hij).irreducible.isUnit_or_isUnit he with hu | hu
  · exact hu
  · have hback : (X i - X j : MvPolynomial σ ℂ) ∣ d := by
      rw [he]
      exact hu.mul_right_dvd.mpr dvd_rfl
    exact (hnot (hback.trans hd')).elim

/-- The separate multiplicity conditions combine into the full product divisor. -/
theorem diagonal_product_dvd (edges : Finset (σ × σ)) (multiplicity : σ × σ → ℕ)
    (p : MvPolynomial σ ℂ)
    (hloop : ∀ e ∈ edges, e.1 ≠ e.2)
    (hreverse : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f → e ≠ (f.2, f.1))
    (hdiv : ∀ e ∈ edges, (X e.1 - X e.2 : MvPolynomial σ ℂ) ^ multiplicity e ∣ p) :
    (∏ e ∈ edges, (X e.1 - X e.2 : MvPolynomial σ ℂ) ^ multiplicity e) ∣ p := by
  apply Finset.prod_dvd_of_isRelPrime ?_ hdiv
  intro e he f hf hef
  apply IsRelPrime.pow
  apply diagonal_isRelPrime (hloop e he) (hloop f hf)
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · exact hef (Prod.ext h₁.symm h₂.symm)
  · exact hreverse e he f hf hef (Prod.ext h₂.symm h₁.symm)

end KhanSL2.Injectivity








