module

public import KhanSL2.Injectivity.DiagonalDivisibility
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finset.NatAntidiagonal

@[expose] public section

/-! Coefficients of identifying two polynomial variables, expressed as a finite convolution. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.Injectivity

open MvPolynomial

variable {σ R : Type*} [DecidableEq σ] [CommRing R]

def collapseVariable (i j k : σ) : σ := if k = i then j else k

theorem diagonal_eq_rename (i j : σ) :
    diagonal (R := R) i j = rename (collapseVariable i j) := by
  ext k
  simp only [diagonal_X, rename_X, collapseVariable]
  split <;> rfl

theorem mapDomain_collapseVariable (i j : σ) (d : σ →₀ ℕ) :
    d.mapDomain (collapseVariable i j) = d.erase i + Finsupp.single j (d i) := by
  have he : (d.erase i).mapDomain (collapseVariable i j) = d.erase i := by
    calc
      _ = (d.erase i).mapDomain id := Finsupp.mapDomain_congr fun k hk => by
        have hk' : k ∈ d.support.erase i := by simpa only [Finsupp.support_erase] using hk
        have hki : k ≠ i := (Finset.mem_erase.mp hk').1
        simp [collapseVariable, hki]
      _ = _ := Finsupp.mapDomain_id
  calc
    _ = (d.erase i + Finsupp.single i (d i)).mapDomain (collapseVariable i j) := by
      rw [Finsupp.erase_add_single]
    _ = _ := by rw [Finsupp.mapDomain_add, he, Finsupp.mapDomain_single]; simp [collapseVariable]

theorem collapseExponent_apply (i j k : σ) (hij : i ≠ j) (d : σ →₀ ℕ) :
    d.mapDomain (collapseVariable i j) k =
      if k = i then 0 else if k = j then d i + d j else d k := by
  rw [mapDomain_collapseVariable]
  by_cases hki : k = i
  · subst k
    simp [hij, Ne.symm hij]
  · by_cases hkj : k = j
    · subst k
      simp [hki, add_comm]
    · simp [hki, hkj, Finsupp.erase_apply, Finsupp.single_apply, Ne.symm hkj]

def splitExponent (d : σ →₀ ℕ) (i j : σ) (a b : ℕ) : σ →₀ ℕ :=
  (d.update i a).update j b

theorem splitExponent_add_single_left (d : σ →₀ ℕ) (i j : σ) (hij : i ≠ j)
    (a b : ℕ) :
    splitExponent d i j a b + Finsupp.single i 1 = splitExponent d i j (a + 1) b := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [splitExponent, Finsupp.update_apply, hij]
  · by_cases hkj : k = j
    · subst k
      simp [splitExponent, Finsupp.update_apply, hki]
    · simp [splitExponent, Finsupp.update_apply, hki, hkj, Finsupp.single_eq_of_ne hki]

theorem splitExponent_collapse (i j : σ) (hij : i ≠ j) (d : σ →₀ ℕ) :
    splitExponent (d.mapDomain (collapseVariable i j)) i j (d i) (d j) = d := by
  ext k
  simp only [splitExponent, Finsupp.update_apply, collapseExponent_apply i j k hij d]
  split_ifs <;> simp_all

theorem splitExponent_eq_iff (i j : σ) (hij : i ≠ j) (d u : σ →₀ ℕ)
    (hd : d i = 0) (a b : ℕ) (hab : a + b = d j) :
    splitExponent d i j a b = u ↔
      u.mapDomain (collapseVariable i j) = d ∧ a = u i ∧ b = u j := by
  constructor
  · intro h
    subst u
    refine ⟨?_, ?_, ?_⟩
    · ext k
      rw [collapseExponent_apply i j k hij]
      by_cases hki : k = i
      · subst k
        simp [hd]
      · by_cases hkj : k = j
        · subst k
          simp [splitExponent, Finsupp.update_apply, hki, hij, hab]
        · simp [splitExponent, Finsupp.update_apply, hki, hkj]
    · simp [splitExponent, Finsupp.update_apply, hij]
    · simp [splitExponent, Finsupp.update_apply]
  · rintro ⟨h, rfl, rfl⟩
    rw [← h, splitExponent_collapse i j hij]

theorem coeff_diagonal (i j : σ) (hij : i ≠ j)
    (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (diagonal i j p).coeff d =
      if d i = 0 then
        ∑ ab ∈ Finset.antidiagonal (d j), p.coeff (splitExponent d i j ab.1 ab.2)
      else 0 := by
  classical
  rw [diagonal_eq_rename]
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp [Finset.sum_add_distrib]
  | monomial u c =>
    rw [rename_monomial, coeff_monomial]
    by_cases hd : d i = 0
    · rw [if_pos hd]
      by_cases hu : u.mapDomain (collapseVariable i j) = d
      · have hab : u i + u j = d j := by
          have hj := DFunLike.congr_fun hu j
          simpa [collapseExponent_apply i j j hij u, Ne.symm hij] using hj
        rw [if_pos hu]
        rw [Finset.sum_eq_single (u i, u j)]
        · rw [← hu, splitExponent_collapse i j hij, coeff_monomial]
          simp
        · intro ab hab' hne
          rw [coeff_monomial]
          apply if_neg
          intro heq
          have hs := (splitExponent_eq_iff i j hij d u hd ab.1 ab.2
            (Finset.mem_antidiagonal.mp hab')).mp heq.symm
          exact hne (Prod.ext hs.2.1 hs.2.2)
        · intro hn
          exact (hn (Finset.mem_antidiagonal.mpr hab)).elim
      · rw [if_neg hu]
        symm
        apply Finset.sum_eq_zero
        intro ab hab
        rw [coeff_monomial]
        apply if_neg
        intro heq
        exact hu ((splitExponent_eq_iff i j hij d u hd ab.1 ab.2
          (Finset.mem_antidiagonal.mp hab)).mp heq.symm).1
    · rw [if_neg hd]
      apply if_neg
      intro hu
      have hi := DFunLike.congr_fun hu i
      simp only [collapseExponent_apply i j i hij u, if_pos rfl] at hi
      exact hd hi.symm

theorem diagonal_eq_zero_of_coefficient_convolutions (i j : σ) (hij : i ≠ j)
    (p : MvPolynomial σ R)
    (h : ∀ d : σ →₀ ℕ, d i = 0 →
      (∑ ab ∈ Finset.antidiagonal (d j), p.coeff (splitExponent d i j ab.1 ab.2)) = 0) :
    diagonal i j p = 0 := by
  ext d
  rw [coeff_diagonal i j hij, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with hd
  · exact h d hd
  · rfl

end KhanSL2.Injectivity
