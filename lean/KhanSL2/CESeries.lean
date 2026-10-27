module

public import KhanSL2.CELeibniz
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

@[expose] public section

/-!
# Formal series bookkeeping for the finite CE formulas

The series are used only to compare each finite coefficient. No completed
cochain algebra or new cohomology model is introduced.
-/

noncomputable section

namespace KhanSL2.CESeries

abbrev Series := PowerSeries Cochain

def liftLinear (F : Module.End ℂ Cochain) : Module.End ℂ Series where
  toFun u := PowerSeries.mk fun n => F (PowerSeries.coeff (R := Cochain) n u)
  map_add' u v := by apply PowerSeries.ext; intro n; simp
  map_smul' r u := by apply PowerSeries.ext; intro n; simp [PowerSeries.coeff_smul]

@[simp] theorem coeff_liftLinear (F : Module.End ℂ Cochain) (u : Series) (n : ℕ) :
    PowerSeries.coeff (R := Cochain) n (liftLinear F u) = F (PowerSeries.coeff (R := Cochain) n u) := by
  simp [liftLinear]

def Q : Module.End ℂ Series := liftLinear q

def parity : Series →+* Series := PowerSeries.map cochainParity.toRingHom

def C (a : Fin 3) : Series := PowerSeries.mk fun j => generator (.c j a)
def B (a : Fin 3) : Series := PowerSeries.mk fun j => generator (.b j a)

@[simp] theorem coeff_C (a : Fin 3) (n : ℕ) :
    PowerSeries.coeff (R := Cochain) n (C a) = generator (.c n a) := by simp [C]

@[simp] theorem coeff_B (a : Fin 3) (n : ℕ) :
    PowerSeries.coeff (R := Cochain) n (B a) = generator (.b n a) := by simp [B]

@[simp] theorem coeff_Q (u : Series) (n : ℕ) :
    PowerSeries.coeff (R := Cochain) n (Q u) = q (PowerSeries.coeff (R := Cochain) n u) :=
  coeff_liftLinear q u n

@[simp] theorem coeff_parity (u : Series) (n : ℕ) :
    PowerSeries.coeff (R := Cochain) n (parity u) = cochainParity (PowerSeries.coeff (R := Cochain) n u) := by
  exact PowerSeries.coeff_map _ _ _

@[simp] theorem parity_C (a : Fin 3) : parity (C a) = -C a := by
  apply PowerSeries.ext
  intro n
  simp

@[simp] theorem parity_B (a : Fin 3) : parity (B a) = -B a := by
  apply PowerSeries.ext
  intro n
  simp

theorem Q_mul (u v : Series) : Q (u * v) = Q u * v + parity u * Q v := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_Q, PowerSeries.coeff_mul, map_sum, q_mul, map_add, coeff_parity]
  exact Finset.sum_add_distrib

@[simp] theorem Q_X : Q (PowerSeries.X : Series) = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_Q, PowerSeries.coeff_X, map_zero]
  split <;> simp [cochain_one_eq]

@[simp] theorem parity_X : parity (PowerSeries.X : Series) = PowerSeries.X := by
  exact PowerSeries.map_X _

theorem Q_X_mul (u : Series) :
    Q ((PowerSeries.X : Series) * u) = PowerSeries.X * Q u := by
  rw [Q_mul, Q_X, parity_X, zero_mul, zero_add]

theorem coeff_mul_range (u v : Series) (n : ℕ) :
    PowerSeries.coeff (R := Cochain) n (u * v) =
      ∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff (R := Cochain) i u * PowerSeries.coeff (R := Cochain) (n - i) v := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  rfl

theorem C_anticomm (a b : Fin 3) : C a * C b = -(C b * C a) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, map_neg, PowerSeries.coeff_mul]
  rw [← Finset.sum_neg_distrib]
  conv_rhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  apply Finset.sum_congr rfl
  intro ij _
  have h := cochain_supercomm (cochain_generator_mem (.c ij.1 a))
    (cochain_generator_mem (.c ij.2 b))
  simpa [koszulSign, cochain_mul_eq_wedge] using h

theorem C_sq (a : Fin 3) : C a * C a = 0 := by
  have h := C_anticomm a a
  have h' : (2 : ℂ) • (C a * C a) = 0 := by
    simpa only [two_smul ℂ] using (eq_neg_iff_add_eq_zero.mp h)
  exact (smul_eq_zero.mp h').resolve_left (by norm_num)

theorem Q_C_formula (a : Fin 3) :
    Q (C a) = (- (1 / 2 : ℂ)) •
      ((PowerSeries.X : Series) *
        ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c • (C b * C c)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [PowerSeries.coeff_smul, PowerSeries.coeff_zero_X_mul]
  | succ j =>
    simp only [coeff_Q, coeff_C, q_generator, qGenerator,
      PowerSeries.coeff_smul, PowerSeries.coeff_succ_X_mul,
      map_sum, coeff_mul_range, Nat.add_sub_cancel, Nat.succ_eq_add_one]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl

theorem Q_B_formula (a : Fin 3) :
    Q (B a) = -((PowerSeries.X : Series) *
      ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c • (C b * B c)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [PowerSeries.coeff_zero_X_mul]
  | succ j =>
    simp only [coeff_Q, coeff_B, q_generator, qGenerator, map_neg,
      PowerSeries.coeff_succ_X_mul, map_sum, PowerSeries.coeff_smul,
      coeff_mul_range, Nat.add_sub_cancel, Nat.succ_eq_add_one]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [coeff_C]
    rfl

end KhanSL2.CESeries
