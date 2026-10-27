module

public import KhanSL2.CESquareZero
public import KhanSL2.CEInvariantBasics

@[expose] public section

/-! The CE differential commutes with every constant color action. -/

noncomputable section

namespace KhanSL2.CESeries

def L (a : Fin 3) : Module.End ℂ Series := liftLinear (colorAction a)

@[simp] theorem coeff_L (a : Fin 3) (u : Series) (n : ℕ) :
    PowerSeries.coeff (R := Cochain) n (L a u) =
      colorAction a (PowerSeries.coeff (R := Cochain) n u) := coeff_liftLinear _ _ _

theorem L_mul (a : Fin 3) (u v : Series) : L a (u * v) = L a u * v + u * L a v := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_L, PowerSeries.coeff_mul, map_sum, colorAction_mul, map_add]
  exact Finset.sum_add_distrib

@[simp] theorem L_X (a : Fin 3) : L a (PowerSeries.X : Series) = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_L, PowerSeries.coeff_X, map_zero]
  split <;> simp [cochain_one_eq]

theorem L_X_mul (a : Fin 3) (u : Series) :
    L a ((PowerSeries.X : Series) * u) = PowerSeries.X * L a u := by
  rw [L_mul, L_X, zero_mul, zero_add]

theorem L_C (a b : Fin 3) : L a (C b) = ∑ c : Fin 3, epsilon a b c • C c := by
  apply PowerSeries.ext
  intro n
  simp [colorGenerator, Mode.color, Mode.recolor, PowerSeries.coeff_smul]

theorem L_B (a b : Fin 3) : L a (B b) = ∑ c : Fin 3, epsilon a b c • B c := by
  apply PowerSeries.ext
  intro n
  simp [colorGenerator, Mode.color, Mode.recolor, PowerSeries.coeff_smul]

set_option maxHeartbeats 1000000 in
theorem Q_L_C (a b : Fin 3) : Q (L a (C b)) = L a (Q (C b)) := by
  fin_cases a <;> fin_cases b <;>
    simp [L_C, Q_C_zero, Q_C_one, Q_C_two, L_X_mul, L_mul,
      Fin.sum_univ_three, epsilon, C_sq, C_anticomm 1 0,
      C_anticomm 2 0, C_anticomm 2 1]

set_option maxHeartbeats 1000000 in
theorem Q_L_B (a b : Fin 3) : Q (L a (B b)) = L a (Q (B b)) := by
  fin_cases a <;> fin_cases b <;>
    simp [L_B, Q_B_zero, Q_B_one, Q_B_two, L_X_mul, L_mul,
      L_C, Fin.sum_univ_three, epsilon] <;> noncomm_ring

end KhanSL2.CESeries

namespace KhanSL2

theorem q_colorAction_generator (a : Fin 3) (m : Mode) :
    q (colorAction a (generator m)) = colorAction a (q (generator m)) := by
  cases m with
  | c j b =>
    have h := congrArg (PowerSeries.coeff (R := Cochain) j) (CESeries.Q_L_C a b)
    simpa using h
  | b j b =>
    have h := congrArg (PowerSeries.coeff (R := Cochain) j) (CESeries.Q_L_B a b)
    simpa using h

theorem q_colorAction (a : Fin 3) (u : Cochain) :
    q (colorAction a u) = colorAction a (q u) := by
  induction u using cochain_induction with
  | hzero => simp
  | hone => simp
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change q (colorAction a (generator m * u)) = colorAction a (q (generator m * u))
    simp only [q_mul, colorAction_mul, map_add, q_colorAction_generator, hu,
      colorAction_parity]
    abel

theorem invariant_q {u : Cochain} (hu : u ∈ relativeInvariants) :
    q u ∈ relativeInvariants := by
  rw [mem_relativeInvariants_iff] at hu ⊢
  intro a
  rw [← q_colorAction, hu a, map_zero]

end KhanSL2
