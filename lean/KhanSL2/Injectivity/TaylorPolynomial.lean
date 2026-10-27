module

public import KhanSL2.Injectivity.SourceSectors
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Finite Taylor polynomials of source functionals

The sum is finite from the outset.  The source jets are ordinary derivatives,
so the coefficient of a labelled monomial includes a factorial for each jet.
An ambient functional is sufficient: its Taylor polynomial determines its
restriction to the selected sector.
-/

noncomputable section

open scoped BigOperators

namespace KhanSL2.SourceDual

open Source

abbrev Variables (r s : ℕ) := Fin r ⊕ Fin s

abbrev TaylorIndex (r s N : ℕ) := Variables r s → Fin (N + 1)

def xIndices {r s N : ℕ} (a : TaylorIndex r s N) : List ℕ :=
  List.ofFn fun i => (a (Sum.inl i)).val

def yIndices {r s N : ℕ} (a : TaylorIndex r s N) : List ℕ :=
  List.ofFn fun i => (a (Sum.inr i)).val

@[simp] theorem xIndices_length {r s N : ℕ} (a : TaylorIndex r s N) :
    (xIndices a).length = r := by simp [xIndices]

@[simp] theorem yIndices_length {r s N : ℕ} (a : TaylorIndex r s N) :
    (yIndices a).length = s := by simp [yIndices]

def indexWeight {r s N : ℕ} (a : TaylorIndex r s N) : ℕ :=
  (xIndices a).sum + (yIndices a).sum

theorem indexWeight_eq_sum {r s N : ℕ} (a : TaylorIndex r s N) :
    indexWeight a = ∑ i, (a i).val := by
  simp [indexWeight, xIndices, yIndices, List.sum_ofFn, Fintype.sum_sum_type]

def exponent {r s N : ℕ} (a : TaylorIndex r s N) : Variables r s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (a i).val

@[simp] theorem exponent_apply {r s N : ℕ} (a : TaylorIndex r s N)
    (i : Variables r s) : exponent a i = (a i).val := by simp [exponent]

theorem exponent_injective {r s N : ℕ} :
    Function.Injective (exponent (r := r) (s := s) (N := N)) := by
  intro a b h
  funext i
  apply Fin.ext
  simpa only [exponent_apply] using congrArg (fun d : Variables r s →₀ ℕ => d i) h

def jetFactorial {r s N : ℕ} (a : TaylorIndex r s N) : ℂ :=
  ∏ i, (Nat.factorial (a i).val : ℂ)

theorem jetFactorial_ne_zero {r s N : ℕ} (a : TaylorIndex r s N) :
    jetFactorial a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (a i).val

def taylorPolynomial (r s N : ℕ) (ell : Source →ₗ[ℂ] ℂ) :
    MvPolynomial (Variables r s) ℂ :=
  ∑ a : TaylorIndex r s N,
    if indexWeight a = N then
      MvPolynomial.monomial (exponent a)
        (ell (jetMonomial (xIndices a) (yIndices a)) / jetFactorial a)
    else 0

theorem coeff_taylorPolynomial {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    (a : TaylorIndex r s N) (ha : indexWeight a = N) :
    (taylorPolynomial r s N ell).coeff (exponent a) =
      ell (jetMonomial (xIndices a) (yIndices a)) / jetFactorial a := by
  classical
  rw [taylorPolynomial, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single a]
  · simp [ha]
  · intro b _ hba
    have h : exponent b ≠ exponent a := fun h => hba (exponent_injective h)
    by_cases hb : indexWeight b = N <;> simp [hb, h]
  · simp

theorem mem_le_sum {xs : List ℕ} {n : ℕ} (hmem : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at hmem
  | cons a xs ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp
    · have := ih hmem
      simp only [List.sum_cons]
      omega

theorem get_le_sum (xs : List ℕ) (i : Fin xs.length) : xs.get i ≤ xs.sum :=
  mem_le_sum (List.getElem_mem i.isLt)

def indexOfLists (xs ys : List ℕ) : TaylorIndex xs.length ys.length (xs.sum + ys.sum) :=
  Sum.elim
    (fun i => ⟨xs.get i, by have := get_le_sum xs i; omega⟩)
    (fun i => ⟨ys.get i, by have := get_le_sum ys i; omega⟩)

@[simp] theorem xIndices_indexOfLists (xs ys : List ℕ) :
    xIndices (indexOfLists xs ys) = xs := by
  simpa only [xIndices, indexOfLists, Sum.elim_inl] using List.ofFn_get xs

@[simp] theorem yIndices_indexOfLists (xs ys : List ℕ) :
    yIndices (indexOfLists xs ys) = ys := by
  simpa only [yIndices, indexOfLists, Sum.elim_inr] using List.ofFn_get ys

@[simp] theorem indexWeight_indexOfLists (xs ys : List ℕ) :
    indexWeight (indexOfLists xs ys) = xs.sum + ys.sum := by
  simp [indexWeight]

/-- Equality of finite Taylor polynomials determines a functional on the sector. -/
theorem eq_on_sector_of_taylorPolynomial_eq {r s N : ℕ}
    (ell μ : Source →ₗ[ℂ] ℂ) (h : taylorPolynomial r s N ell = taylorPolynomial r s N μ)
    {a : Source} (ha : a ∈ sector r s N) : ell a = μ a := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs, ys, rfl, rfl, rfl, rfl⟩ := ha
    have hc := congrArg (fun p : MvPolynomial (Variables xs.length ys.length) ℂ =>
      p.coeff (exponent (indexOfLists xs ys))) h
    rw [coeff_taylorPolynomial ell _ (indexWeight_indexOfLists xs ys),
      coeff_taylorPolynomial μ _ (indexWeight_indexOfLists xs ys)] at hc
    have he := (div_left_inj' (jetFactorial_ne_zero (indexOfLists xs ys))).mp hc
    simpa using he
  | zero => simp
  | add a b _ _ ia ib => simp only [map_add, ia, ib]
  | smul k a _ ia => simp only [map_smul, ia]

@[simp] theorem taylorPolynomial_zero (r s N : ℕ) :
    taylorPolynomial r s N (0 : Source →ₗ[ℂ] ℂ) = 0 := by
  classical
  simp [taylorPolynomial]

theorem zero_on_sector_of_taylorPolynomial_eq_zero {r s N : ℕ}
    (ell : Source →ₗ[ℂ] ℂ) (h : taylorPolynomial r s N ell = 0)
    {a : Source} (ha : a ∈ sector r s N) : ell a = 0 := by
  have he : taylorPolynomial r s N ell = taylorPolynomial r s N 0 := by simpa using h
  exact eq_on_sector_of_taylorPolynomial_eq ell 0 he ha

end KhanSL2.SourceDual
