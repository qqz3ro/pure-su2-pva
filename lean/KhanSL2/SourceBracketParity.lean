module

public import KhanSL2.SourceBracketQuotient

@[expose] public section

/-! Parity covariance and the homogeneous right Leibniz law for the source bracket. -/

noncomputable section

namespace KhanSL2.Source

open LambdaPolynomial SourceBracketOperators

theorem parityConjugate_right_translation (M : HamiltonianAction)
    (hM : ∀ a, M (translation a) = rightTranslation translation (M a))
    (a : Source) :
    parityConjugate M (translation a) =
      rightTranslation translation (parityConjugate M a) := by
  ext n
  cases n with
  | zero =>
    simp [parityConjugate_coeff, parity_translation, hM, rightTranslation_apply]
  | succ n =>
    simp [parityConjugate_coeff, parity_translation, hM, rightTranslation_apply]

theorem K_mapParity (p : LambdaPolynomial Source) :
    K (mapCoefficients parity.toLinearMap p) =
      mapCoefficients parity.toLinearMap (K p) := by
  simp only [K_apply]
  exact skew_mapCoefficients_of_commute translation parity.toLinearMap
    (fun a => (parity_translation a).symm) p

@[simp] theorem mapParity_mapParity (p : LambdaPolynomial Source) :
    mapCoefficients parity.toLinearMap (mapCoefficients parity.toLinearMap p) = p := by
  ext n
  simp

/-- The parity of the left input is exactly the parity of the corresponding
Hamiltonian action. -/
theorem bracket_parity_action (a : Source) :
    bracket (parity a) = parityConjugate (bracket a) := by
  apply GeneralLeibniz.ext (bracket_generalLeibniz (parity a))
    (bracket_generalLeibniz a).parityConjugate
    (bracket_right_translation (parity a))
    (parityConjugate_right_translation (bracket a) (bracket_right_translation a))
  · simp [bracket_X0_right, parityConjugate_apply, DX_parity, K_mapParity]
  · simp [bracket_Y0_right, parityConjugate_apply, DY_parity, K_mapParity]

theorem bracket_parity_of_mem {d : Degree} {a : Source} (ha : a ∈ piece d) :
    parityConjugate (bracket a) = koszulSign (1, 0, 0) d • bracket a := by
  rw [← bracket_parity_action, parity_of_mem ha, map_smul]

private theorem koszul_projection_identity (d e : Degree) :
    (1 / 2 : ℂ) * (1 + koszulSign (1, 0, 0) e) +
      ((1 / 2 : ℂ) * (1 - koszulSign (1, 0, 0) e)) *
        koszulSign (1, 0, 0) d = koszulSign d e := by
  have hd : d.1 % 2 = 0 ∨ d.1 % 2 = 1 := by omega
  have he : e.1 % 2 = 0 ∨ e.1 % 2 = 1 := by omega
  rcases hd with hd | hd <;> rcases he with he | he <;>
    norm_num [koszulSign, Int.mul_emod, hd, he]

theorem bracket_super_leibniz (d e : Degree) (a b c : Source)
    (ha : a ∈ piece d) (hb : b ∈ piece e) :
    bracket a (b * c) =
      mulRight sourceData (bracket a b) c +
        koszulSign d e • mulLeft sourceData b (bracket a c) := by
  rw [bracket_generalLeibniz a b c, bracket_parity_of_mem ha]
  ext n
  simp only [Finsupp.add_apply, Finsupp.smul_apply, mulLeft_apply, mulRight_apply,
    sourceData, LinearMap.mul_apply', LinearMap.smul_apply, Finsupp.smul_apply]
  have he : evenPart b * bracket a c n +
      oddPart b * (koszulSign (1, 0, 0) d • bracket a c n) =
      koszulSign d e • (b * bracket a c n) := by
    calc
      _ = ((1 / 2 : ℂ) * (1 + koszulSign (1, 0, 0) e) +
        ((1 / 2 : ℂ) * (1 - koszulSign (1, 0, 0) e)) *
          koszulSign (1, 0, 0) d) • (b * bracket a c n) := by
        simp only [evenPart_apply, oddPart_apply, parity_of_mem hb,
          smul_mul_assoc, mul_smul_comm, add_mul, sub_mul, smul_add, smul_sub]
        module
      _ = _ := by rw [koszul_projection_identity]
  rw [add_assoc, he]

end KhanSL2.Source
