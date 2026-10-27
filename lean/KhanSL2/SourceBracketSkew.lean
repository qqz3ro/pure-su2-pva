module

public import KhanSL2.SourceBracketParity

@[expose] public section

/-! Super-skew symmetry for the actual source bracket. -/

noncomputable section

namespace KhanSL2.Source

open LambdaPolynomial SourceBracketOperators BracketAction

/-- Reverse the two inputs with the parity sign, then substitute `-lambda-partial`.
Even/odd projections make this a linear action for arbitrary first inputs. -/
def reversedAction (a : Source) : HamiltonianAction :=
  -(K.comp (bracket.flip (evenPart a) -
    (coefficientsLinear parity.toLinearMap).comp (bracket.flip (oddPart a))))

theorem reversedAction_apply (a b : Source) :
    reversedAction a b =
      -K (bracket b (evenPart a) -
        mapCoefficients parity.toLinearMap (bracket b (oddPart a))) := rfl

private theorem K_left (a : Source) (p : LambdaPolynomial Source) :
    K (left a p) = mulLeft sourceData a (K p) := by
  rw [left_apply, K_K]

private theorem K_right (a : Source) (p : LambdaPolynomial Source) :
    K (right a p) = mulRight sourceData (K p) a := by
  rw [right_apply, K_K]

theorem parityConjugate_reversedAction (a : Source) :
    parityConjugate (reversedAction a) = reversedAction (parity a) := by
  apply LinearMap.ext
  intro b
  simp [parityConjugate_apply, reversedAction_apply, bracket_parity_action,
    K_mapParity, mapCoefficients_sub]

theorem reversedAction_generalLeibniz (a : Source) :
    GeneralLeibniz (reversedAction a) := by
  intro c d
  rw [parityConjugate_reversedAction]
  simp only [reversedAction_apply, bracket_mul_first, LinearMap.add_apply,
    rightAction_apply, leftAction_apply, evenPart_evenPart, oddPart_evenPart,
    evenPart_oddPart, oddPart_oddPart, map_zero, add_zero, zero_add,
    mapCoefficients_add, SourceBracketOperators.parity_right,
    SourceBracketOperators.parity_left, parity_parity, evenPart_parity,
    oddPart_parity, map_neg, mapCoefficients_neg, map_sub, K_left, K_right]
  ext n
  simp [sourceData, evenPart_apply, oddPart_apply, mapCoefficients_sub, K_left, K_right,
    smul_mul_assoc, mul_smul_comm, add_mul, sub_mul, mul_add, mul_sub,
    smul_add, smul_sub]
  module

private theorem mapParity_negativeShift (p : LambdaPolynomial Source) :
    mapCoefficients parity.toLinearMap (negativeShift p) =
      negativeShift (mapCoefficients parity.toLinearMap p) := by
  simp [negativeShift_apply, mapCoefficients_shift]

theorem reversedAction_right_translation (a b : Source) :
    reversedAction a (translation b) =
      rightTranslation translation (reversedAction a b) := by
  have h (u : Source) : bracket (translation b) u = negativeShift (bracket b u) :=
    bracket_left_translation b u
  rw [reversedAction_apply, h, h, mapParity_negativeShift, ← map_sub,
    ← rightTranslation_K, reversedAction_apply, map_neg]

theorem reversedAction_X0 (a : Source) :
    reversedAction a (X 0) = bracket a (X 0) := by
  rw [reversedAction_apply, bracket_X0, bracket_X0_right]
  congr 1
  simp [evenPart_apply, oddPart_apply, DX_parity, mapCoefficients_sub,
    smul_add, smul_sub]
  module

theorem reversedAction_Y0 (a : Source) :
    reversedAction a (Y 0) = bracket a (Y 0) := by
  rw [reversedAction_apply, bracket_Y0, bracket_Y0_right]
  congr 1
  simp [evenPart_apply, oddPart_apply, DY_parity, mapCoefficients_sub,
    smul_add, smul_sub]
  module

/-- The full inhomogeneous super-skew formula, proved by uniqueness of the
right superderivation with its two generator values. -/
theorem bracket_eq_reversedAction (a : Source) : bracket a = reversedAction a := by
  exact GeneralLeibniz.ext (bracket_generalLeibniz a) (reversedAction_generalLeibniz a)
    (bracket_right_translation a) (reversedAction_right_translation a)
    (reversedAction_X0 a).symm (reversedAction_Y0 a).symm

theorem bracket_parity_both (a b : Source) :
    bracket (parity a) (parity b) =
      mapCoefficients parity.toLinearMap (bracket a b) := by
  rw [bracket_parity_action, parityConjugate_apply, parity_parity]

private theorem koszul_reverse_identity (d e : Degree) :
    (1 / 2 : ℂ) * (1 + koszulSign (1, 0, 0) d) -
      ((1 / 2 : ℂ) * (1 - koszulSign (1, 0, 0) d)) *
        (koszulSign (1, 0, 0) e * koszulSign (1, 0, 0) d) =
      koszulSign d e := by
  have hd : d.1 % 2 = 0 ∨ d.1 % 2 = 1 := by omega
  have he : e.1 % 2 = 0 ∨ e.1 % 2 = 1 := by omega
  rcases hd with hd | hd <;> rcases he with he | he <;>
    norm_num [koszulSign, Int.mul_emod, hd, he]

theorem bracket_super_skew (d e : Degree) (a b : Source)
    (ha : a ∈ piece d) (hb : b ∈ piece e) :
    bracket a b = (-koszulSign d e) •
      minusVariableMinusTranslation translation (bracket b a) := by
  have hp : mapCoefficients parity.toLinearMap (bracket b a) =
      (koszulSign (1, 0, 0) e * koszulSign (1, 0, 0) d) • bracket b a := by
    rw [← bracket_parity_both, parity_of_mem hb, parity_of_mem ha]
    simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]
  have hi : bracket b (evenPart a) -
      mapCoefficients parity.toLinearMap (bracket b (oddPart a)) =
      koszulSign d e • bracket b a := by
    calc
      _ = ((1 / 2 : ℂ) * (1 + koszulSign (1, 0, 0) d) -
        ((1 / 2 : ℂ) * (1 - koszulSign (1, 0, 0) d)) *
          (koszulSign (1, 0, 0) e * koszulSign (1, 0, 0) d)) • bracket b a := by
        simp only [evenPart_apply, oddPart_apply, parity_of_mem ha,
          map_add, map_sub, map_smul, mapCoefficients_add, mapCoefficients_sub,
          mapCoefficients_smul, hp]
        module
      _ = _ := by rw [koszul_reverse_identity]
  rw [bracket_eq_reversedAction a, reversedAction_apply, hi, map_smul, K_apply,
    neg_smul]

end KhanSL2.Source
