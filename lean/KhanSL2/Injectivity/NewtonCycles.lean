module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

/-!
# Finite Newton cycles

The separating cycles are constructed by a finite recursion. No formal
logarithms, exponentials, or completed modules enter the construction.
-/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

open Finset

section Recursion

variable {R M : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M]

/-- The inverse of a positive natural number, taken in the rational scalars. -/
def rationalInvNat (n : ℕ) : R := algebraMap ℚ R (n : ℚ)⁻¹

theorem rationalInvNat_mul_natCast {n : ℕ} (hn : n ≠ 0) :
    rationalInvNat (R := R) n * (n : R) = 1 := by
  have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [rationalInvNat, ← map_natCast (algebraMap ℚ R), ← map_mul, inv_mul_cancel₀ hq,
    map_one]

/-- The signed Newton identity for a sequence of elementary coefficients. -/
def SatisfiesNewton (a p : ℕ → R) : Prop :=
  ∀ n, ((n + 1 : ℕ) : R) * a (n + 1) =
    -∑ j ∈ range (n + 1), p (j + 1) * a (n - j)

omit [Algebra ℚ R] in
theorem SatisfiesNewton.map {S : Type*} [CommRing S] {a p : ℕ → R}
    (h : SatisfiesNewton a p) (f : R →+* S) :
    SatisfiesNewton (fun n => f (a n)) (fun n => f (p n)) := by
  intro n
  have hn := congrArg f (h n)
  simpa only [map_mul, map_natCast, map_neg, map_sum] using hn

/-- A finite recursively constructed degree-one chain. Its value at `k`
only involves the generators `xi 1, ..., xi k`. -/
def newtonCycle (a p : ℕ → R) (xi : ℕ → M) : ℕ → M
  | 0 => 0
  | n + 1 => -(rationalInvNat (R := R) (n + 1)) •
      ∑ j ∈ range (n + 1),
        (a (n - j) • xi (j + 1) + p (j + 1) • newtonCycle a p xi (n - j))
termination_by n => n
decreasing_by omega

@[simp] theorem newtonCycle_zero (a p : ℕ → R) (xi : ℕ → M) :
    newtonCycle a p xi 0 = 0 := by rw [newtonCycle]

theorem newtonCycle_succ (a p : ℕ → R) (xi : ℕ → M) (n : ℕ) :
    newtonCycle a p xi (n + 1) = -(rationalInvNat (R := R) (n + 1)) •
      ∑ j ∈ range (n + 1),
        (a (n - j) • xi (j + 1) + p (j + 1) • newtonCycle a p xi (n - j)) := by
  rw [newtonCycle]

/-- Newton's identities turn the differential of the recursively constructed
chain into a difference of elementary coefficients. -/
theorem map_newtonCycle (a b p q : ℕ → R) (xi : ℕ → M) (d : M →ₗ[R] R)
    (ha : SatisfiesNewton a p) (hb : SatisfiesNewton b q)
    (hzero : a 0 = b 0) (hxi : ∀ j, d (xi (j + 1)) = p (j + 1) - q (j + 1)) :
    ∀ k, d (newtonCycle a q xi k) = a k - b k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [hzero]
    | succ n =>
      rw [newtonCycle_succ, map_smul, map_sum]
      simp only [map_add, map_smul, hxi, smul_eq_mul]
      have hs :
          (∑ j ∈ range (n + 1),
            (a (n - j) * (p (j + 1) - q (j + 1)) +
              q (j + 1) * d (newtonCycle a q xi (n - j)))) =
          (∑ j ∈ range (n + 1), p (j + 1) * a (n - j)) -
            ∑ j ∈ range (n + 1), q (j + 1) * b (n - j) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro j _hj
        rw [ih (n - j) (by omega)]
        ring
      rw [hs, ← neg_eq_iff_eq_neg.mpr (ha n), ← neg_eq_iff_eq_neg.mpr (hb n)]
      have hi := rationalInvNat_mul_natCast (R := R) (Nat.succ_ne_zero n)
      calc
        -rationalInvNat (n + 1) *
              (-(((n + 1 : ℕ) : R) * a (n + 1)) -
                -(((n + 1 : ℕ) : R) * b (n + 1))) =
            (rationalInvNat (n + 1) * ((n + 1 : ℕ) : R)) *
              (a (n + 1) - b (n + 1)) := by ring
        _ = a (n + 1) - b (n + 1) := by rw [hi, one_mul]

/-- Coefficients past the number of roots vanish, so the corresponding
Newton chains are closed. -/
theorem map_newtonCycle_eq_zero (a b p q : ℕ → R) (xi : ℕ → M) (d : M →ₗ[R] R)
    (ha : SatisfiesNewton a p) (hb : SatisfiesNewton b q)
    (hzero : a 0 = b 0) (hxi : ∀ j, d (xi (j + 1)) = p (j + 1) - q (j + 1))
    (k : ℕ) (hak : a k = 0) (hbk : b k = 0) :
    d (newtonCycle a q xi k) = 0 := by
  rw [map_newtonCycle a b p q xi d ha hb hzero hxi, hak, hbk, sub_self]

/-- Construction commutes with linear maps of the coefficient module. -/
theorem linearMap_newtonCycle {N : Type*} [AddCommGroup N] [Module R N]
    (a p : ℕ → R) (xi : ℕ → M) (f : M →ₗ[R] N) (k : ℕ) :
    f (newtonCycle a p xi k) = newtonCycle a p (fun j => f (xi j)) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp
    | succ n =>
      rw [newtonCycle_succ, newtonCycle_succ, map_smul, map_sum]
      congr 1
      apply sum_congr rfl
      intro j _hj
      simp only [map_add, map_smul, ih (n - j) (by omega)]

/-- Scalar specialization commutes with the finite construction. -/
theorem semilinearMap_newtonCycle {S N : Type*} [CommRing S] [Algebra ℚ S]
    [AddCommGroup N] [Module S N] (σ : R →+* S) (f : M →ₛₗ[σ] N)
    (a p : ℕ → R) (xi : ℕ → M) (k : ℕ) :
    f (newtonCycle a p xi k) =
      newtonCycle (fun j => σ (a j)) (fun j => σ (p j)) (fun j => f (xi j)) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp
    | succ n =>
      rw [newtonCycle_succ, newtonCycle_succ, map_smulₛₗ, map_sum]
      simp only [map_neg, rationalInvNat, RingHom.map_rat_algebraMap]
      congr 1
      apply sum_congr rfl
      intro j _hj
      simp only [map_add, map_smulₛₗ, ih (n - j) (by omega)]

/-- Only the first `k` generators occur in the `k`-th Newton chain. -/
theorem newtonCycle_mem (a p : ℕ → R) (xi : ℕ → M) (P : Submodule R M)
    (k : ℕ) (hxi : ∀ j, 0 < j → j ≤ k → xi j ∈ P) :
    newtonCycle a p xi k ∈ P := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp
    | succ n =>
      rw [newtonCycle_succ]
      apply P.smul_mem
      apply P.sum_mem
      intro j hj
      have hj' := mem_range.mp hj
      apply P.add_mem
      · exact P.smul_mem _ (hxi _ (by omega) (by omega))
      · apply P.smul_mem
        apply ih (n - j) (by omega)
        intro i hi hik
        exact hxi i hi (by omega)

end Recursion

section DiagonalCoefficients

variable {R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
theorem SatisfiesNewton.sum_eq (a p : ℕ → R) (h : SatisfiesNewton a p) (n : ℕ) :
    (∑ j ∈ range n, p (j + 1) * a (n - 1 - j)) = -(n : R) * a n := by
  cases n with
  | zero => simp
  | succ n =>
    have hn := h n
    simpa only [Nat.add_sub_cancel, neg_mul] using (neg_eq_iff_eq_neg.mpr hn).symm

/-- Coefficients of a Newton chain when the two alphabets coincide. -/
theorem newtonCycle_single_apply (a p : ℕ → R) (ha : SatisfiesNewton a p)
    (k i : ℕ) :
    newtonCycle a p (fun j => Finsupp.single j (1 : R)) k i =
      if i = 0 then 0 else if i ≤ k then -rationalInvNat i * a (k - i) else 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => by_cases hi : i = 0 <;> simp [hi]
    | succ n =>
      rw [newtonCycle_succ]
      simp only [Finsupp.smul_apply, Finset.sum_apply', Finsupp.add_apply, smul_eq_mul]
      have hrec :
          (∑ j ∈ range (n + 1),
            (a (n - j) * Finsupp.single (j + 1) (1 : R) i +
              p (j + 1) * newtonCycle a p (fun j => Finsupp.single j (1 : R)) (n - j) i)) =
          (∑ j ∈ range (n + 1), a (n - j) * Finsupp.single (j + 1) (1 : R) i) +
          ∑ j ∈ range (n + 1), p (j + 1) *
            (if i = 0 then 0 else if i ≤ n - j then
              -rationalInvNat i * a (n - j - i) else 0) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro j _hj
        rw [ih (n - j) (by omega)]
      rw [hrec]
      by_cases hi : i = 0
      · subst i
        simp
      have hip : 0 < i := Nat.pos_of_ne_zero hi
      rw [ite_eq_right hi]
      simp only [ite_eq_right hi]
      by_cases hik : i ≤ n + 1
      · rw [ite_eq_left hik]
        have hfirst :
            (∑ j ∈ range (n + 1), a (n - j) * Finsupp.single (j + 1) (1 : R) i) =
              a (n + 1 - i) := by
          rw [sum_eq_single (i - 1)]
          · simp [show i - 1 + 1 = i by omega, show n - (i - 1) = n + 1 - i by omega]
          · intro j _hj hji
            have hne : j + 1 ≠ i := by omega
            simp [hne]
          · intro hnot
            exact (hnot (mem_range.mpr (by omega))).elim
        have hsecond :
            (∑ j ∈ range (n + 1), p (j + 1) *
              (if i ≤ n - j then -rationalInvNat i * a (n - j - i) else 0)) =
            rationalInvNat i * ((n + 1 - i : ℕ) : R) * a (n + 1 - i) := by
          have hsub : range (n + 1 - i) ⊆ range (n + 1) := range_mono (by omega)
          rw [← sum_subset hsub]
          · calc
              (∑ j ∈ range (n + 1 - i), p (j + 1) *
                    (if i ≤ n - j then -rationalInvNat i * a (n - j - i) else 0)) =
                  -rationalInvNat i *
                    ∑ j ∈ range (n + 1 - i), p (j + 1) * a (n + 1 - i - 1 - j) := by
                rw [mul_sum]
                apply sum_congr rfl
                intro j hj
                have hj' := mem_range.mp hj
                rw [ite_eq_left (by omega), show n - j - i = n + 1 - i - 1 - j by omega]
                ring
              _ = _ := by rw [ha.sum_eq]; ring
          · intro j hj hj'
            have hnot : ¬i ≤ n - j := by
              have := mem_range.mp hj
              have := not_lt.mp (by simpa only [mem_range] using hj')
              omega
            simp [hnot]
        rw [hfirst, hsecond]
        have hii := rationalInvNat_mul_natCast (R := R) hi
        have hik' := rationalInvNat_mul_natCast (R := R) (Nat.succ_ne_zero n)
        have hcast : ((n + 1 : ℕ) : R) = (i : R) + ((n + 1 - i : ℕ) : R) := by
          rw [← Nat.cast_add, Nat.add_sub_of_le hik]
        calc
          -rationalInvNat (n + 1) *
              (a (n + 1 - i) + rationalInvNat i * ↑(n + 1 - i) * a (n + 1 - i)) =
            -(rationalInvNat (n + 1) * ((n + 1 : ℕ) : R)) *
              rationalInvNat i * a (n + 1 - i) := by
                rw [hcast]
                linear_combination rationalInvNat (n + 1) * a (n + 1 - i) * hii
          _ = -rationalInvNat i * a (n + 1 - i) := by rw [hik']; ring
      · rw [ite_eq_right hik]
        have hfirst :
            (∑ j ∈ range (n + 1), a (n - j) * Finsupp.single (j + 1) (1 : R) i) = 0 := by
          apply sum_eq_zero
          intro j hj
          have hj' := mem_range.mp hj
          have hne : j + 1 ≠ i := by omega
          simp [hne]
        have hsecond :
            (∑ j ∈ range (n + 1), p (j + 1) *
              (if i ≤ n - j then -rationalInvNat i * a (n - j - i) else 0)) = 0 := by
          apply sum_eq_zero
          intro j _hj
          rw [ite_eq_right (by omega), mul_zero]
        rw [hfirst, hsecond, add_zero, mul_zero]

end DiagonalCoefficients

section ModePairing

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Pair a Cartan mode with the derivative field: `xi_j` pairs to `j z^(j-1)`. -/
def cartanModePairing (z : R) : (ℕ →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun j => (j : R) * z ^ (j - 1))

omit [Algebra ℚ R] in
@[simp] theorem cartanModePairing_single (z : R) (j : ℕ) :
    cartanModePairing z (Finsupp.single j 1) = (j : R) * z ^ (j - 1) := by
  simp [cartanModePairing]

/-- The exact finite polynomial obtained by pairing a diagonal Newton chain. -/
theorem cartanModePairing_newtonCycle (a p : ℕ → R) (ha : SatisfiesNewton a p)
    (z : R) (k : ℕ) :
    cartanModePairing z (newtonCycle a p (fun j => Finsupp.single j (1 : R)) k) =
      -∑ j ∈ range k, a (k - 1 - j) * z ^ j := by
  classical
  let c := newtonCycle a p (fun j => Finsupp.single j (1 : R)) k
  have hc : c.support ⊆ range (k + 1) := by
    intro i hi
    have hi' := Finsupp.mem_support_iff.mp hi
    rw [mem_range]
    by_contra h
    have hik : ¬i ≤ k := by omega
    exact hi' (by simp [c, newtonCycle_single_apply a p ha, hik])
  change cartanModePairing z c = _
  rw [cartanModePairing, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset c hc _ (by simp)]
  simp only [smul_eq_mul]
  rw [sum_range_succ']
  have hc0 : c 0 = 0 := by simp [c, newtonCycle_single_apply a p ha]
  rw [hc0, zero_mul, add_zero, ← sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  have hck : c (j + 1) = -rationalInvNat (j + 1) * a (k - (j + 1)) := by
    simp [c, newtonCycle_single_apply a p ha, show j + 1 ≤ k by omega]
  rw [hck, Nat.add_sub_cancel, show k - (j + 1) = k - 1 - j by omega]
  have hi := rationalInvNat_mul_natCast (R := R) (Nat.succ_ne_zero j)
  calc
    -rationalInvNat (j + 1) * a (k - 1 - j) * (((j + 1 : ℕ) : R) * z ^ j) =
      -(rationalInvNat (j + 1) * ((j + 1 : ℕ) : R)) * a (k - 1 - j) * z ^ j := by ring
    _ = -(a (k - 1 - j) * z ^ j) := by rw [hi]; ring

end ModePairing

end KhanSL2.Injectivity
