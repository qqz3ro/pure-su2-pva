module

public import KhanSL2.Injectivity.TaylorOddRelations
public import KhanSL2.Injectivity.TaylorVanishing
public import KhanSL2.Injectivity.DiagonalCovariance

@[expose] public section

/-! All source Taylor diagonal identities, transported from the leading-coordinate calculations. -/

noncomputable section

namespace KhanSL2.SourceDual

open Source Injectivity MvPolynomial

theorem permSign_scalar_ne_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (((Equiv.Perm.sign σ : ℤ) : ℂ)) ≠ 0 := by
  exact_mod_cast Units.ne_zero (Equiv.Perm.sign σ)

theorem taylorPolynomial_diagonal_x_eq_zero {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    {i j : Fin r} (hij : i ≠ j) :
    diagonal (Sum.inl i) (Sum.inl j) (taylorPolynomial r s N ell) = 0 := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r =>
    cases r with
    | zero => exact (hij (Fin.ext (by omega))).elim
    | succ r =>
      let σ : Equiv.Perm (Fin (r + 2)) := pairPermutation 0 (Fin.succ 0) i j
      have hi : σ 0 = i := pairPermutation_first (by simp) hij
      have hj : σ (Fin.succ 0) = j := pairPermutation_second _ _ _ _
      have h := diagonal_zero_transport (xPermutation σ) (firstX r s) (secondX r s)
        (taylorPolynomial (r + 2) s N ell) 1 (by norm_num)
        (by simpa only [one_smul] using taylorPolynomial_symmetric_x ell σ)
        (taylorPolynomial_diagonal_headXX_eq_zero r s N ell)
      change diagonal (Sum.inl (σ 0)) (Sum.inl (σ (Fin.succ 0)))
        (taylorPolynomial (r + 2) s N ell) = 0 at h
      simpa only [hi, hj] using h

theorem taylorPolynomial_diagonal_xy_eq_zero {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    (i : Fin r) (j : Fin s) :
    diagonal (Sum.inl i) (Sum.inr j) (taylorPolynomial r s N ell) = 0 := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r =>
    cases s with
    | zero => exact Fin.elim0 j
    | succ s =>
      let σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap 0 i
      let τ : Equiv.Perm (Fin (s + 1)) := Equiv.swap 0 j
      have hx := diagonal_zero_transport (xPermutation σ) (mixedX r s) (mixedY r s)
        (taylorPolynomial (r + 1) (s + 1) N ell) 1 (by norm_num)
        (by simpa only [one_smul] using taylorPolynomial_symmetric_x ell σ)
        (taylorPolynomial_diagonal_headXY_eq_zero r s N ell)
      have hx' : diagonal (Sum.inl i) (mixedY r s)
          (taylorPolynomial (r + 1) (s + 1) N ell) = 0 := by
        change diagonal (Sum.inl (σ 0)) (Sum.inr 0)
          (taylorPolynomial (r + 1) (s + 1) N ell) = 0 at hx
        simpa only [σ, mixedY, Equiv.swap_apply_left] using hx
      have hy := diagonal_zero_transport (yPermutation τ) (Sum.inl i) (mixedY r s)
        (taylorPolynomial (r + 1) (s + 1) N ell) (((Equiv.Perm.sign τ : ℤ) : ℂ))
        (permSign_scalar_ne_zero τ) (taylorPolynomial_alternating_y ell τ) hx'
      change diagonal (Sum.inl i) (Sum.inr (τ 0))
        (taylorPolynomial (r + 1) (s + 1) N ell) = 0 at hy
      simpa only [τ, Equiv.swap_apply_left] using hy

theorem taylorPolynomial_diagonal_pderiv_xy_eq_zero {r s N : ℕ}
    (ell : Source →ₗ[ℂ] ℂ) (i : Fin r) (j : Fin s) :
    diagonal (Sum.inl i) (Sum.inr j)
      (pderiv (Sum.inl i) (taylorPolynomial r s N ell)) = 0 := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r =>
    cases s with
    | zero => exact Fin.elim0 j
    | succ s =>
      let σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap 0 i
      let τ : Equiv.Perm (Fin (s + 1)) := Equiv.swap 0 j
      have hx := diagonal_pderiv_zero_transport (xPermutation σ) (mixedX r s) (mixedY r s)
        (taylorPolynomial (r + 1) (s + 1) N ell) 1 (by norm_num)
        (by simpa only [one_smul] using taylorPolynomial_symmetric_x ell σ)
        (taylorPolynomial_diagonal_pderiv_headXY_eq_zero r s N ell)
      have hx' : diagonal (Sum.inl i) (mixedY r s)
          (pderiv (Sum.inl i) (taylorPolynomial (r + 1) (s + 1) N ell)) = 0 := by
        change diagonal (Sum.inl (σ 0)) (Sum.inr 0)
          (pderiv (Sum.inl (σ 0)) (taylorPolynomial (r + 1) (s + 1) N ell)) = 0 at hx
        simpa only [σ, mixedY, Equiv.swap_apply_left] using hx
      have hy := diagonal_pderiv_zero_transport (yPermutation τ) (Sum.inl i) (mixedY r s)
        (taylorPolynomial (r + 1) (s + 1) N ell) (((Equiv.Perm.sign τ : ℤ) : ℂ))
        (permSign_scalar_ne_zero τ) (taylorPolynomial_alternating_y ell τ) hx'
      change diagonal (Sum.inl i) (Sum.inr (τ 0))
        (pderiv (Sum.inl i) (taylorPolynomial (r + 1) (s + 1) N ell)) = 0 at hy
      simpa only [τ, Equiv.swap_apply_left] using hy

theorem taylorPolynomial_diagonal_pderiv_y_eq_zero {r s N : ℕ}
    (ell : Source →ₗ[ℂ] ℂ) {i j : Fin s} (hij : i ≠ j) :
    diagonal (Sum.inr i) (Sum.inr j)
      (pderiv (Sum.inr i) (taylorPolynomial r s N ell)) = 0 := by
  cases s with
  | zero => exact Fin.elim0 i
  | succ s =>
    cases s with
    | zero => exact (hij (Fin.ext (by omega))).elim
    | succ s =>
      let σ : Equiv.Perm (Fin (s + 2)) := pairPermutation 0 (Fin.succ 0) i j
      have hi : σ 0 = i := pairPermutation_first (by simp) hij
      have hj : σ (Fin.succ 0) = j := pairPermutation_second _ _ _ _
      have h := diagonal_pderiv_zero_transport (yPermutation σ) (firstY r s) (secondY r s)
        (taylorPolynomial r (s + 2) N ell) (((Equiv.Perm.sign σ : ℤ) : ℂ))
        (permSign_scalar_ne_zero σ) (taylorPolynomial_alternating_y ell σ)
        (taylorPolynomial_diagonal_pderiv_headYY_eq_zero r s N ell)
      change diagonal (Sum.inr (σ 0)) (Sum.inr (σ (Fin.succ 0)))
        (pderiv (Sum.inr (σ 0)) (taylorPolynomial r (s + 2) N ell)) = 0 at h
      simpa only [hi, hj] using h

end KhanSL2.SourceDual
