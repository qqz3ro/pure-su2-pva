module

public import KhanSL2.CEDegrees
public import KhanSL2.CochainSupercomm
public import KhanSL2.ExteriorDerivation

@[expose] public section

/-! Genuine product rules for the concrete finite CE operators. -/

noncomputable section

namespace KhanSL2

theorem qGenerator_parity (m : Mode) : cochainParity (qGenerator m) = qGenerator m := by
  simpa [koszulSign] using cochainParity_of_mem (qGenerator_degree m)

theorem colorGenerator_parity (a : Fin 3) (m : Mode) :
    cochainParity (colorGenerator a m) = -colorGenerator a m := by
  simpa [koszulSign] using cochainParity_of_mem (colorGenerator_degree a m)

theorem translationGenerator_parity (m : Mode) :
    cochainParity (translationGenerator m) = -translationGenerator m := by
  simpa [koszulSign] using cochainParity_of_mem (translationGenerator_degree m)

theorem q_wedge (u v : Cochain) :
    q (wedge u v) = wedge (q u) v + wedge (cochainParity u) (q v) := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
    qGenerator u v (cochainParity u)
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_even Mode.code Mode.code_injective
    (qGenerator m) (qGenerator_parity m) (cochainParity u)).symm

theorem colorAction_wedge (a : Fin 3) (u v : Cochain) :
    colorAction a (wedge u v) =
      wedge (colorAction a u) v + wedge u (colorAction a v) := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
    (colorGenerator a) u v u
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_odd Mode.code Mode.code_injective
    (colorGenerator a m) (colorGenerator_parity a m) u).symm

theorem translation_wedge (u v : Cochain) :
    translation (wedge u v) =
      wedge (translation u) v + wedge u (translation v) := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
    translationGenerator u v u
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_odd Mode.code Mode.code_injective
    (translationGenerator m) (translationGenerator_parity m) u).symm

theorem q_mul (u v : Cochain) :
    q (u * v) = q u * v + cochainParity u * q v := q_wedge u v

theorem colorAction_mul (a : Fin 3) (u v : Cochain) :
    colorAction a (u * v) = colorAction a u * v + u * colorAction a v :=
  colorAction_wedge a u v

theorem translation_mul (u v : Cochain) :
    translation (u * v) = translation u * v + u * translation v := translation_wedge u v

theorem q_odd_leibniz {d : Degree} {u : Cochain} (hu : u ∈ cochainPiece d)
    (v : Cochain) :
    q (wedge u v) = wedge (q u) v +
      (if d.1 % 2 = 0 then (1 : ℂ) else -1) • wedge u (q v) := by
  rw [q_wedge, cochainParity_of_mem hu]
  by_cases h : d.1 % 2 = 0 <;> simp [koszulSign, wedge, h]

theorem q_parity (u : Cochain) : q (cochainParity u) = -cochainParity (q u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv, neg_add]
  | single s r =>
    have hpar := cochainParity_of_mem (q_degree (cochain_single_mem s r))
    have hsign : koszulSign (1, 0, 0) (monomialDegree s + (1, 0, 0)) =
        (-1 : ℂ) ^ (s.card + 1) := by
      rw [nat_parity_sign]
      simp [koszulSign, monomialDegree, Nat.cast_add]
    rw [hpar, hsign]
    change q (FiniteExterior.parityLinear (Finsupp.single s r)) = _
    rw [FiniteExterior.parity_single, map_smul, pow_succ, mul_neg_one, neg_smul, neg_neg]

/-- Squaring the odd differential removes the Leibniz sign. -/
theorem q_square_mul (u v : Cochain) :
    q (q (u * v)) = q (q u) * v + u * q (q v) := by
  rw [q_mul, map_add, q_mul, q_mul, q_parity, cochainParity_involutive]
  simp only [neg_mul]
  abel

theorem q_square_zero_of_generators
    (h : ∀m, q (qGenerator m) = 0) (u : Cochain) : q (q u) = 0 := by
  induction u using cochain_induction with
  | hzero => simp
  | hone => simp
  | hadd u v hu hv => simp only [map_add, hu, hv, add_zero]
  | hsmul r u hu => simp only [map_smul, hu, smul_zero]
  | hgen m u hu =>
    change q (q (generator m * u)) = 0
    rw [q_square_mul, q_generator, h, hu, zero_mul, mul_zero, add_zero]

end KhanSL2
