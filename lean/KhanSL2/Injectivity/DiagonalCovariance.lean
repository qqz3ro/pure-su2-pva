module

public import KhanSL2.Injectivity.DiagonalDivisibility

@[expose] public section

/-! Transport of diagonal identities from chosen coordinates to any distinct pair. -/

noncomputable section

namespace KhanSL2.Injectivity

open MvPolynomial

variable {σ : Type*} [DecidableEq σ]

theorem diagonal_rename_equiv (e : Equiv.Perm σ) (i j : σ) (p : MvPolynomial σ ℂ) :
    diagonal (e i) (e j) (rename e p) = rename e (diagonal i j p) := by
  have h : (diagonal (R := ℂ) (e i) (e j)).comp (rename e) =
      (rename e).comp (diagonal i j) := by
    ext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk, e.injective.ne hk]
  exact AlgHom.congr_fun h p

theorem diagonal_pderiv_rename_equiv (e : Equiv.Perm σ) (i j : σ)
    (p : MvPolynomial σ ℂ) :
    diagonal (e i) (e j) (pderiv (e i) (rename e p)) =
      rename e (diagonal i j (pderiv i p)) := by
  rw [pderiv_rename e.injective, diagonal_rename_equiv]

/-- A scalar permutation character does not affect diagonal vanishing. -/
theorem diagonal_zero_transport (e : Equiv.Perm σ) (i j : σ)
    (p : MvPolynomial σ ℂ) (c : ℂ) (hc : c ≠ 0)
    (he : rename e p = c • p) (hp : diagonal i j p = 0) :
    diagonal (e i) (e j) p = 0 := by
  have h := diagonal_rename_equiv e i j p
  rw [he, map_smul, hp, map_zero] at h
  exact (smul_eq_zero.mp h).resolve_left hc

/-- The first normal derivative transports along the same permutation. -/
theorem diagonal_pderiv_zero_transport (e : Equiv.Perm σ) (i j : σ)
    (p : MvPolynomial σ ℂ) (c : ℂ) (hc : c ≠ 0)
    (he : rename e p = c • p) (hp : diagonal i j (pderiv i p) = 0) :
    diagonal (e i) (e j) (pderiv (e i) p) = 0 := by
  have h := diagonal_pderiv_rename_equiv e i j p
  rw [he, Derivation.map_smul, map_smul, hp, map_zero] at h
  exact (smul_eq_zero.mp h).resolve_left hc

/-- A concrete permutation carrying an ordered distinct pair to another. -/
def pairPermutation (a b i j : σ) : Equiv.Perm σ :=
  (Equiv.swap a i).trans (Equiv.swap ((Equiv.swap a i) b) j)

theorem pairPermutation_first {a b i j : σ} (hab : a ≠ b) (hij : i ≠ j) :
    pairPermutation a b i j a = i := by
  have hne : (Equiv.swap a i) b ≠ i := by
    intro h
    have he : (Equiv.swap a i) b = (Equiv.swap a i) a :=
      h.trans (Equiv.swap_apply_left a i).symm
    exact hab ((Equiv.swap a i).injective he).symm
  simp only [pairPermutation, Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne hne.symm hij

@[simp] theorem pairPermutation_second (a b i j : σ) : pairPermutation a b i j b = j := by
  simp [pairPermutation]

end KhanSL2.Injectivity
