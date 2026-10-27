module

public import KhanSL2.StrongMacdonald.Operators
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# The Koszul differential `∂̄` squares to zero

The modes `σ^b(-k)` and `ψ^a(-(i+1))` are packaged into formal power series over `W`,
so that the triangular sums defining `∂̄` on generators become Cauchy products. On these
series `∂̄` acts as an odd derivation, and `∂̄² = 0` on generators reduces to the Jacobi
identity for `ε` together with the anticommutation of the odd series. Since `∂̄²` is half
the anticommutator `[∂̄, ∂̄]`, an even derivation, it vanishes identically.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

theorem dbar_mul (x y : W) : dbar (x * y) = dbar x * y + parity x * dbar y :=
  homDer_dbar.isDer x y

theorem psiOf_anticomm (i j : ℕ) (a b : Fin 3) :
    psiOf i a * psiOf j b = -(psiOf j b * psiOf i a) := by
  rw [psiOf, psiOf, mul_psi, parity_psi, mul_neg]

namespace DbarSeries

abbrev Series := PowerSeries W

def liftLinear (F : Module.End ℂ W) : Module.End ℂ Series where
  toFun u := PowerSeries.mk fun n => F (PowerSeries.coeff (R := W) n u)
  map_add' u v := by apply PowerSeries.ext; intro n; simp
  map_smul' r u := by apply PowerSeries.ext; intro n; simp [PowerSeries.coeff_smul]

@[simp] theorem coeff_liftLinear (F : Module.End ℂ W) (u : Series) (n : ℕ) :
    PowerSeries.coeff (R := W) n (liftLinear F u) = F (PowerSeries.coeff (R := W) n u) := by
  simp [liftLinear]

/-- `∂̄` acting coefficientwise on series. -/
def Q : Module.End ℂ Series := liftLinear dbar

/-- The parity automorphism acting coefficientwise on series. -/
def parityS : Series →+* Series := PowerSeries.map parity.toRingHom

/-- The even series `Σ_k σ^b(-k) X^k`. -/
def S (b : Fin 3) : Series := PowerSeries.mk fun k => sigOf k b

/-- The odd series `Σ_i ψ^a(-(i+1)) X^i`. -/
def P (a : Fin 3) : Series := PowerSeries.mk fun i => psiOf i a

@[simp] theorem coeff_S (b : Fin 3) (n : ℕ) :
    PowerSeries.coeff (R := W) n (S b) = sigOf n b := by simp [S]

@[simp] theorem coeff_P (a : Fin 3) (n : ℕ) :
    PowerSeries.coeff (R := W) n (P a) = psiOf n a := by simp [P]

@[simp] theorem coeff_Q (u : Series) (n : ℕ) :
    PowerSeries.coeff (R := W) n (Q u) = dbar (PowerSeries.coeff (R := W) n u) :=
  coeff_liftLinear dbar u n

@[simp] theorem coeff_parityS (u : Series) (n : ℕ) :
    PowerSeries.coeff (R := W) n (parityS u) = parity (PowerSeries.coeff (R := W) n u) :=
  PowerSeries.coeff_map _ _ _

@[simp] theorem parityS_P (a : Fin 3) : parityS (P a) = -P a := by
  apply PowerSeries.ext
  intro n
  simp [psiOf]

@[simp] theorem parityS_S (b : Fin 3) : parityS (S b) = S b := by
  apply PowerSeries.ext
  intro n
  simp [sigOf]

theorem Q_mul (u v : Series) : Q (u * v) = Q u * v + parityS u * Q v := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_Q, PowerSeries.coeff_mul, map_sum, dbar_mul, map_add, coeff_parityS]
  exact Finset.sum_add_distrib

@[simp] theorem Q_X : Q (PowerSeries.X : Series) = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_Q, PowerSeries.coeff_X, map_zero]
  split
  · exact homDer_dbar.map_one
  · exact map_zero dbar

@[simp] theorem parityS_X : parityS (PowerSeries.X : Series) = PowerSeries.X :=
  PowerSeries.map_X _

theorem Q_X_mul (u : Series) :
    Q ((PowerSeries.X : Series) * u) = PowerSeries.X * Q u := by
  rw [Q_mul, Q_X, parityS_X, zero_mul, zero_add]

theorem coeff_mul_range (u v : Series) (n : ℕ) :
    PowerSeries.coeff (R := W) n (u * v) =
      ∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff (R := W) i u * PowerSeries.coeff (R := W) (n - i) v := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  rfl

theorem P_anticomm (a b : Fin 3) : P a * P b = -(P b * P a) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, map_neg, PowerSeries.coeff_mul, ← Finset.sum_neg_distrib]
  conv_rhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp only [coeff_P, Prod.fst_swap, Prod.snd_swap]
  exact psiOf_anticomm _ _ _ _

theorem P_sq (a : Fin 3) : P a * P a = 0 := by
  have h := P_anticomm a a
  have h' : (2 : ℂ) • (P a * P a) = 0 := by
    simpa only [two_smul ℂ] using (eq_neg_iff_add_eq_zero.mp h)
  exact (smul_eq_zero.mp h').resolve_left (by norm_num)

theorem P_sq_mul (a : Fin 3) (u : Series) : P a * (P a * u) = 0 := by
  rw [← mul_assoc, P_sq, zero_mul]

theorem P_middle (a b : Fin 3) : P a * (P b * P a) = 0 := by
  rw [← mul_assoc, P_anticomm a b, neg_mul, mul_assoc, P_sq, mul_zero, neg_zero]

theorem mul_X_mul (u v : Series) : u * (PowerSeries.X * v) = PowerSeries.X * (u * v) := by
  rw [← mul_assoc, (PowerSeries.commute_X u).eq, mul_assoc]

theorem Q_S_formula (b : Fin 3) :
    Q (S b) = (PowerSeries.X : Series) *
      ∑ a : Fin 3, ∑ c : Fin 3, epsilon a b c • (P a * S c) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    simp only [coeff_Q, coeff_S, dbar_sigOf, PowerSeries.coeff_succ_X_mul, map_sum,
      PowerSeries.coeff_smul, coeff_mul_range, coeff_P, Nat.add_sub_cancel, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]

theorem Q_P_formula (b : Fin 3) :
    Q (P b) = (1 / 2 : ℂ) • ((PowerSeries.X : Series) *
      ∑ a : Fin 3, ∑ c : Fin 3, epsilon a b c • (P a * P c)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_smul]
  | succ n =>
    simp only [coeff_Q, coeff_P, dbar_psiOf, PowerSeries.coeff_succ_X_mul, map_sum,
      PowerSeries.coeff_smul, coeff_mul_range, Nat.add_sub_cancel, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]

theorem Q_P_zero : Q (P 0) = -(PowerSeries.X * (P 1 * P 2)) := by
  rw [Q_P_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  rw [P_anticomm 2 1]
  simp only [mul_add, mul_neg]
  module

theorem Q_P_one : Q (P 1) = -(PowerSeries.X * (P 2 * P 0)) := by
  rw [Q_P_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  rw [P_anticomm 0 2]
  simp only [mul_add, mul_neg]
  module

theorem Q_P_two : Q (P 2) = -(PowerSeries.X * (P 0 * P 1)) := by
  rw [Q_P_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  rw [P_anticomm 1 0]
  simp only [mul_add, mul_neg]
  module

theorem Q_S_zero : Q (S 0) = PowerSeries.X * (P 2 * S 1 - P 1 * S 2) := by
  rw [Q_S_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  noncomm_ring

theorem Q_S_one : Q (S 1) = PowerSeries.X * (P 0 * S 2 - P 2 * S 0) := by
  rw [Q_S_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  noncomm_ring

theorem Q_S_two : Q (S 2) = PowerSeries.X * (P 1 * S 0 - P 0 * S 1) := by
  rw [Q_S_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  noncomm_ring

theorem Q_square_P (b : Fin 3) : Q (Q (P b)) = 0 := by
  fin_cases b
  · change Q (Q (P 0)) = 0
    rw [Q_P_zero, map_neg, Q_X_mul, Q_mul, Q_P_one, Q_P_two, parityS_P]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc, mul_X_mul, P_middle, mul_zero, add_zero,
      neg_zero]
  · change Q (Q (P 1)) = 0
    rw [Q_P_one, map_neg, Q_X_mul, Q_mul, Q_P_two, Q_P_zero, parityS_P]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc, mul_X_mul, P_middle, mul_zero, add_zero,
      neg_zero]
  · change Q (Q (P 2)) = 0
    rw [Q_P_two, map_neg, Q_X_mul, Q_mul, Q_P_zero, Q_P_one, parityS_P]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc, mul_X_mul, P_middle, mul_zero, add_zero,
      neg_zero]

theorem Q_square_S (b : Fin 3) : Q (Q (S b)) = 0 := by
  fin_cases b
  · change Q (Q (S 0)) = 0
    rw [Q_S_zero, Q_X_mul, map_sub, Q_mul, Q_mul, Q_P_two, Q_P_one, Q_S_one, Q_S_two,
      parityS_P, parityS_P]
    simp only [neg_mul, mul_neg, mul_sub, sub_mul, mul_assoc, mul_X_mul, P_sq_mul]
    rw [← mul_assoc (P 1) (P 0), P_anticomm 1 0, neg_mul, mul_assoc]
    noncomm_ring
  · change Q (Q (S 1)) = 0
    rw [Q_S_one, Q_X_mul, map_sub, Q_mul, Q_mul, Q_P_zero, Q_P_two, Q_S_two, Q_S_zero,
      parityS_P, parityS_P]
    simp only [neg_mul, mul_neg, mul_sub, sub_mul, mul_assoc, mul_X_mul, P_sq_mul]
    rw [← mul_assoc (P 2) (P 1), P_anticomm 2 1, neg_mul, mul_assoc]
    noncomm_ring
  · change Q (Q (S 2)) = 0
    rw [Q_S_two, Q_X_mul, map_sub, Q_mul, Q_mul, Q_P_one, Q_P_zero, Q_S_zero, Q_S_one,
      parityS_P, parityS_P]
    simp only [neg_mul, mul_neg, mul_sub, sub_mul, mul_assoc, mul_X_mul, P_sq_mul]
    rw [← mul_assoc (P 0) (P 2), P_anticomm 0 2, neg_mul, mul_assoc]
    noncomm_ring

end DbarSeries

open DbarSeries in
theorem dbar_dbar_sigOf (k : ℕ) (b : Fin 3) : dbar (dbar (sigOf k b)) = 0 := by
  have h := congrArg (PowerSeries.coeff (R := W) k) (Q_square_S b)
  simpa using h

open DbarSeries in
theorem dbar_dbar_psiOf (k : ℕ) (b : Fin 3) : dbar (dbar (psiOf k b)) = 0 := by
  have h := congrArg (PowerSeries.coeff (R := W) k) (Q_square_P b)
  simpa using h

/-- `∂̄² = 0`. -/
theorem dbar_mul_dbar : dbar * dbar = 0 := by
  have h : dbar * dbar + dbar * dbar = 0 := by
    apply (HomDer.anticomm homDer_dbar homDer_dbar).isDer.ext (IsDer.zero 0)
    intro g
    rw [LinearMap.zero_apply, LinearMap.add_apply, Module.End.mul_apply]
    cases g with
    | s g =>
      obtain ⟨k, b⟩ := g
      change dbar (dbar (sigOf k b)) + dbar (dbar (sigOf k b)) = 0
      rw [dbar_dbar_sigOf, add_zero]
    | p n =>
      obtain ⟨k, b⟩ := n
      change dbar (dbar (psiOf k b)) + dbar (dbar (psiOf k b)) = 0
      rw [dbar_dbar_psiOf, add_zero]
  have h2 : (2 : ℂ) • (dbar * dbar) = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem dbar_dbar_apply (x : W) : dbar (dbar x) = 0 := by
  rw [← Module.End.mul_apply, dbar_mul_dbar, LinearMap.zero_apply]

end KhanSL2.StrongMacdonald
