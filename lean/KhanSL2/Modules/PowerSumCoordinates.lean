module

public import KhanSL2.Modules.WeightedRoots
public import KhanSL2.Injectivity.NewtonPolynomials
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

@[expose] public section

/-!
# Power sums as coordinates on the symmetric coefficient ring

The finite Newton recursion provides an explicit triangular change of variables
between the first `B` power sums and the elementary symmetric functions.
-/

noncomputable section

namespace KhanSL2.Modules

open Finset MvPolynomial Injectivity

section Newton

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Signed elementary coefficients, recursively reconstructed from power sums. -/
def newtonCoefficient (p : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => -rationalInvNat (n + 1) *
      ∑ j ∈ range (n + 1), p (j + 1) * newtonCoefficient p (n - j)
termination_by n => n
 decreasing_by omega

@[simp] theorem newtonCoefficient_zero (p : ℕ → A) : newtonCoefficient p 0 = 1 := by
  rw [newtonCoefficient]

theorem newtonCoefficient_succ (p : ℕ → A) (n : ℕ) :
    newtonCoefficient p (n + 1) = -rationalInvNat (n + 1) *
      ∑ j ∈ range (n + 1), p (j + 1) * newtonCoefficient p (n - j) := by
  rw [newtonCoefficient]

theorem newtonCoefficient_satisfiesNewton (p : ℕ → A) :
    SatisfiesNewton (newtonCoefficient p) p := by
  intro n
  rw [newtonCoefficient_succ]
  have hi := rationalInvNat_mul_natCast (R := A) (Nat.succ_ne_zero n)
  calc
    _ = -(rationalInvNat (n + 1) * ((n + 1 : ℕ) : A)) *
        ∑ j ∈ range (n + 1), p (j + 1) * newtonCoefficient p (n - j) := by ring
    _ = _ := by rw [hi]; ring

private theorem coefficient_of_newton {a p : ℕ → A}
    (h : SatisfiesNewton a p) (n : ℕ) :
    a (n + 1) = -rationalInvNat (n + 1) *
      ∑ j ∈ range (n + 1), p (j + 1) * a (n - j) := by
  have hi := rationalInvNat_mul_natCast (R := A) (Nat.succ_ne_zero n)
  calc
    a (n + 1) = (rationalInvNat (n + 1) * ((n + 1 : ℕ) : A)) * a (n + 1) := by
      rw [hi, one_mul]
    _ = _ := by rw [mul_assoc, h n]; ring

theorem newtonCoefficient_eq {a p : ℕ → A}
    (h : SatisfiesNewton a p) (hzero : a 0 = 1) (k : ℕ) :
    newtonCoefficient p k = a k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [newtonCoefficient_zero] using hzero.symm
    | succ n =>
      rw [newtonCoefficient_succ, coefficient_of_newton h]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [ih (n - j) (by omega)]

theorem newtonCoefficient_map {D : Type*} [CommRing D] [Algebra ℚ D]
    (f : A →+* D) (p : ℕ → A) (k : ℕ) :
    f (newtonCoefficient p k) = newtonCoefficient (fun j => f (p j)) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp
    | succ n =>
      rw [newtonCoefficient_succ, newtonCoefficient_succ]
      simp only [map_mul, map_neg, map_sum, rationalInvNat, RingHom.map_rat_algebraMap]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [ih (n - j) (by omega)]

theorem newtonCoefficient_congr {p q : ℕ → A} (k : ℕ)
    (h : ∀ j, 0 < j → j ≤ k → p j = q j) :
    newtonCoefficient p k = newtonCoefficient q k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp
    | succ n =>
      rw [newtonCoefficient_succ, newtonCoefficient_succ]
      congr 1
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      rw [h (j + 1) (by omega) (by omega)]
      congr 1
      apply ih (n - j) (by omega)
      intro t ht htk
      exact h t ht (by omega)

omit [Algebra ℚ A] in
private theorem power_of_newton {a p : ℕ → A}
    (h : SatisfiesNewton a p) (hzero : a 0 = 1) (n : ℕ) :
    p (n + 1) = -((n + 1 : ℕ) : A) * a (n + 1) -
      ∑ j ∈ range n, p (j + 1) * a (n - j) := by
  have hn := h n
  rw [sum_range_succ] at hn
  simp only [Nat.sub_self, hzero, mul_one] at hn
  linear_combination hn

end Newton

/-- Elementary coordinates on the actual symmetric subalgebra. -/
def elementaryAlgEquiv (B : ℕ) : MvPolynomial (Fin B) ℂ ≃ₐ[ℂ] R B :=
  MvPolynomial.esymmAlgEquiv (Fin B) ℂ (Fintype.card_fin B)

@[simp] theorem elementaryAlgEquiv_X (B : ℕ) (i : Fin B) :
    elementaryAlgEquiv B (X i) =
      ⟨esymm (Fin B) ℂ (i.val + 1), esymm_isSymmetric (Fin B) ℂ _⟩ := by
  change (MvPolynomial.esymmAlgHom (Fin B) ℂ B) (X i) = _
  exact aeval_X _ _

/-- The first `B` formal power-sum variables, extended by zero outside their range. -/
def powerVariables (B k : ℕ) : MvPolynomial (Fin B) ℂ :=
  if h : 0 < k ∧ k ≤ B then X ⟨k - 1, by omega⟩ else 0

@[simp] theorem powerVariables_succ (B : ℕ) (i : Fin B) :
    powerVariables B (i.val + 1) = X i := by
  simp [powerVariables, i.isLt]

def powerSumHom (B : ℕ) : MvPolynomial (Fin B) ℂ →ₐ[ℂ] R B :=
  aeval fun i => powerSum B (i.val + 1)

@[simp] theorem powerSumHom_X (B : ℕ) (i : Fin B) :
    powerSumHom B (X i) = powerSum B (i.val + 1) := aeval_X _ _

private def powerSumRaw (B : ℕ) :
    MvPolynomial (Fin B) ℂ →ₐ[ℂ] MvPolynomial (Fin B) ℂ :=
  (symmetricSubalgebra (Fin B) ℂ).val.comp (powerSumHom B)

private theorem powerSumRaw_variables (B k : ℕ) (hk : 0 < k) (hkB : k ≤ B) :
    powerSumRaw B (powerVariables B k) = psum (Fin B) ℂ k := by
  rw [powerVariables, dif_pos ⟨hk, hkB⟩]
  change (powerSumHom B (X ⟨k - 1, by omega⟩)).val = _
  rw [powerSumHom_X]
  change psum (Fin B) ℂ (k - 1 + 1) = psum (Fin B) ℂ k
  congr 1
  omega

private theorem powerSumRaw_newton (B k : ℕ) (hk : k ≤ B) :
    powerSumRaw B (newtonCoefficient (powerVariables B) k) =
      signedElementary (Fin B) ℂ k := by
  change (powerSumRaw B).toRingHom (newtonCoefficient (powerVariables B) k) = _
  rw [newtonCoefficient_map]
  change newtonCoefficient (fun j => powerSumRaw B (powerVariables B j)) k = _
  rw [newtonCoefficient_congr k (q := psum (Fin B) ℂ)
    (fun j hj hjk => powerSumRaw_variables B j hj (by omega))]
  exact newtonCoefficient_eq (signedElementary_satisfiesNewton (Fin B) ℂ)
    (signedElementary_zero (Fin B) ℂ) k

/-- The explicit polynomial change from elementary coordinates to power-sum coordinates. -/
def newtonCoordinates (B : ℕ) :
    MvPolynomial (Fin B) ℂ →ₐ[ℂ] MvPolynomial (Fin B) ℂ :=
  aeval fun i => (-1) ^ (i.val + 1) * newtonCoefficient (powerVariables B) (i.val + 1)

@[simp] theorem newtonCoordinates_X (B : ℕ) (i : Fin B) :
    newtonCoordinates B (X i) = (-1) ^ (i.val + 1) *
      newtonCoefficient (powerVariables B) (i.val + 1) := aeval_X _ _

theorem powerSumHom_comp_newtonCoordinates (B : ℕ) :
    (powerSumHom B).comp (newtonCoordinates B) = (elementaryAlgEquiv B).toAlgHom := by
  ext i : 1
  apply Subtype.ext
  change powerSumRaw B (newtonCoordinates B (X i)) = _
  simp only [newtonCoordinates, aeval_X, map_mul, map_pow, map_neg, map_one]
  rw [powerSumRaw_newton B _ (by omega)]
  change (-1) ^ (i.val + 1) * ((-1) ^ (i.val + 1) * esymm (Fin B) ℂ (i.val + 1)) = _
  rw [← mul_assoc, ← mul_pow]
  simp

private theorem newtonCoefficient_mem_range (B k : ℕ) (hk : k ≤ B) :
    newtonCoefficient (powerVariables B) k ∈ (newtonCoordinates B).range := by
  cases k with
  | zero => simp
  | succ n =>
    let i : Fin B := ⟨n, by omega⟩
    have hh : newtonCoordinates B ((-1) ^ (n + 1) * X i) =
        newtonCoefficient (powerVariables B) (n + 1) := by
      rw [map_mul, map_pow, map_neg, map_one, newtonCoordinates_X]
      change (-1) ^ (n + 1) * ((-1) ^ (n + 1) * newtonCoefficient (powerVariables B) (n + 1)) = _
      rw [← mul_assoc, ← mul_pow]
      simp
    exact ⟨_, hh⟩

private theorem powerVariables_mem_range (B k : ℕ) (hk : k ≤ B) :
    powerVariables B k ∈ (newtonCoordinates B).range := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [powerVariables]
    | succ n =>
      rw [power_of_newton (newtonCoefficient_satisfiesNewton (powerVariables B))
        (newtonCoefficient_zero _) n]
      apply (newtonCoordinates B).range.sub_mem
      · apply (newtonCoordinates B).range.mul_mem
        · exact (newtonCoordinates B).range.neg_mem ((newtonCoordinates B).range.natCast_mem _)
        · exact newtonCoefficient_mem_range B _ hk
      · apply (newtonCoordinates B).range.sum_mem
        intro j hj
        have hj' := mem_range.mp hj
        apply (newtonCoordinates B).range.mul_mem
        · exact ih (j + 1) (by omega) (by omega)
        · exact newtonCoefficient_mem_range B _ (by omega)

theorem newtonCoordinates_surjective (B : ℕ) :
    Function.Surjective (newtonCoordinates B) := by
  intro q
  change q ∈ (newtonCoordinates B).range
  induction q using MvPolynomial.induction_on with
  | C c => exact (newtonCoordinates B).range.algebraMap_mem c
  | add p q hp hq => exact (newtonCoordinates B).range.add_mem hp hq
  | mul_X q i hq =>
    apply (newtonCoordinates B).range.mul_mem hq
    simpa using powerVariables_mem_range B (i.val + 1) (by omega)

theorem powerSumHom_bijective (B : ℕ) : Function.Bijective (powerSumHom B) := by
  have hcomp (q : MvPolynomial (Fin B) ℂ) :
      powerSumHom B (newtonCoordinates B q) = elementaryAlgEquiv B q :=
    DFunLike.congr_fun (powerSumHom_comp_newtonCoordinates B) q
  constructor
  · intro p q hpq
    obtain ⟨u, rfl⟩ := newtonCoordinates_surjective B p
    obtain ⟨v, rfl⟩ := newtonCoordinates_surjective B q
    have huv : u = v := (elementaryAlgEquiv B).injective (by simpa only [hcomp] using hpq)
    exact congrArg (newtonCoordinates B) huv
  · intro q
    obtain ⟨p, rfl⟩ := (elementaryAlgEquiv B).surjective q
    exact ⟨newtonCoordinates B p, hcomp p⟩

/-- The first `B` power sums are free algebraic coordinates on `R B`. -/
def powerSumAlgEquiv (B : ℕ) : MvPolynomial (Fin B) ℂ ≃ₐ[ℂ] R B :=
  AlgEquiv.ofBijective (powerSumHom B) (powerSumHom_bijective B)

@[simp] theorem powerSumAlgEquiv_X (B : ℕ) (i : Fin B) :
    powerSumAlgEquiv B (X i) = powerSum B (i.val + 1) := powerSumHom_X B i

@[simp] theorem powerSumAlgEquiv_symm_powerSum (B : ℕ) (i : Fin B) :
    (powerSumAlgEquiv B).symm (powerSum B (i.val + 1)) = X i := by
  rw [← powerSumAlgEquiv_X, AlgEquiv.symm_apply_apply]

end KhanSL2.Modules


