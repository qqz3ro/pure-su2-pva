module

public import KhanSL2.SourceBracket
public import KhanSL2.SourceHamiltonianLeibniz
public import KhanSL2.SourceBracketOperatorParity

@[expose] public section

/-! # The general right Leibniz rule for the full raw source bracket -/

noncomputable section

namespace KhanSL2.Source

open LambdaPolynomial SourceBracketOperators

namespace BracketAction

theorem parityConjugate_leftAction (a : Source) (M : BracketAction) :
    parityConjugate (leftAction a M) = leftAction (parity a) (parityConjugate M) := by
  ext c
  simp only [parityConjugate_apply, leftAction_apply, parity_left]

theorem parityConjugate_rightAction (M : BracketAction) (a : Source) :
    parityConjugate (rightAction M a) = rightAction (parityConjugate M) (parity a) := by
  ext c
  simp only [parityConjugate_apply, rightAction_apply, mapCoefficients_add,
    parity_right, parity_parity, evenPart_parity, oddPart_parity,
    parity_evenPart, parity_oddPart, map_neg, mapCoefficients_neg]

theorem generalLeibniz_leftAction (a : Source) {M : BracketAction}
    (hM : GeneralLeibniz M) : GeneralLeibniz (leftAction a M) := by
  intro c d
  simp only [leftAction_apply, hM c d, map_add, parityConjugate_leftAction,
    left_mulRight, left_mulLeft_even, left_mulLeft_odd]

private theorem mulRight_even_odd (p : Poly) (d : Source) :
    mulRight sourceData p d =
      mulRight sourceData p (evenPart d) + mulRight sourceData p (oddPart d) := by
  ext n
  simp only [Finsupp.add_apply, mulRight_apply, sourceData, LinearMap.mul_apply']
  rw [← mul_add, evenPart_add_oddPart]

@[simp] private theorem zero_mulLeft (p : Poly) :
    mulLeft sourceData 0 p = 0 := by
  ext n
  simp [sourceData]

theorem generalLeibniz_rightAction {M : BracketAction} (hM : GeneralLeibniz M)
    (a : Source) : GeneralLeibniz (rightAction M a) := by
  intro c d
  rw [parityConjugate_rightAction]
  simp only [rightAction_apply, evenPart_mul, oddPart_mul, map_add]
  rw [hM (evenPart c) (evenPart d), hM (oddPart c) (oddPart d),
    hM (evenPart c) (oddPart d), hM (oddPart c) (evenPart d)]
  simp only [map_add,
    evenPart_evenPart, oddPart_oddPart, evenPart_oddPart, oddPart_evenPart]
  simp only [mulLeft_zero, zero_mulLeft, mulRight_zero, map_zero, add_zero, zero_add,
    right_mulRight_even, right_mulRight_odd, right_mulLeft, parity_parity,
    mulRight_add, mulLeft_add]
  rw [mulRight_even_odd _ d, mulRight_even_odd _ d]
  abel

end BracketAction

open SourcePresentation BracketAction

theorem rawBracket_generalLeibniz (a : Expression) : GeneralLeibniz (rawBracket a) := by
  induction a with
  | of g =>
    cases g with
    | X i => exact DX_generalLeibniz.negativeShift_pow i
    | Y i => exact DY_generalLeibniz.negativeShift_pow i
  | ofScalar _ => exact GeneralLeibniz.zero
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb =>
    exact (generalLeibniz_rightAction ha (mk b)).add (generalLeibniz_leftAction (mk a) hb)

end KhanSL2.Source
