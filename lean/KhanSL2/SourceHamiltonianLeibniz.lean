module

public import KhanSL2.SourceHamiltonianDegree
public import KhanSL2.SourceParityProjections

@[expose] public section

/-! # A right Leibniz formula without homogeneous-input restrictions -/

noncomputable section

namespace KhanSL2.Source

open LambdaPolynomial

abbrev HamiltonianAction := Source →ₗ[ℂ] LambdaPolynomial Source

/-- Conjugate an action by parity in its input and all its coefficients. -/
def parityConjugate (M : HamiltonianAction) : HamiltonianAction :=
  (coefficientsLinear parity.toLinearMap).comp (M.comp parity.toLinearMap)

theorem parityConjugate_apply (M : HamiltonianAction) (a : Source) :
    parityConjugate M a = mapCoefficients parity.toLinearMap (M (parity a)) := rfl

@[simp] theorem parityConjugate_coeff (M : HamiltonianAction) (a : Source) (n : ℕ) :
    parityConjugate M a n = parity (M (parity a) n) :=
  mapCoefficients_apply _ _ _

/-- The super right Leibniz identity, extended linearly to all inputs. -/
def GeneralLeibniz (M : HamiltonianAction) : Prop :=
  ∀ c d, M (c * d) =
    mulRight sourceData (M c) d +
      mulLeft sourceData (evenPart c) (M d) +
      mulLeft sourceData (oddPart c) (parityConjugate M d)

theorem evenPart_mul (a b : Source) :
    evenPart (a * b) = evenPart a * evenPart b + oddPart a * oddPart b := by
  simp only [evenPart_apply, oddPart_apply, map_mul, smul_mul_smul_comm,
    mul_add, mul_sub, add_mul, sub_mul]
  module

theorem oddPart_mul (a b : Source) :
    oddPart (a * b) = evenPart a * oddPart b + oddPart a * evenPart b := by
  simp only [evenPart_apply, oddPart_apply, map_mul, smul_mul_smul_comm,
    mul_add, mul_sub, add_mul, sub_mul]
  module

@[simp] theorem parityConjugate_zero : parityConjugate 0 = 0 := by
  ext a n
  simp

theorem parityConjugate_add (M N : HamiltonianAction) :
    parityConjugate (M + N) = parityConjugate M + parityConjugate N := by
  ext a n
  simp

theorem parityConjugate_smul (r : ℂ) (M : HamiltonianAction) :
    parityConjugate (r • M) = r • parityConjugate M := by
  ext a n
  simp

@[simp] theorem parityConjugate_parityConjugate (M : HamiltonianAction) :
    parityConjugate (parityConjugate M) = M := by
  ext a n
  simp

@[simp] theorem parityConjugate_DX : parityConjugate DX = DX := by
  ext a n
  simp only [parityConjugate_coeff, DX_parity, mapCoefficients_apply,
    AlgHom.toLinearMap_apply, parity_parity]

@[simp] theorem parityConjugate_DY : parityConjugate DY = -DY := by
  ext a n
  simp only [parityConjugate_coeff, DY_parity, Finsupp.neg_apply,
    mapCoefficients_apply, AlgHom.toLinearMap_apply, map_neg, parity_parity,
    LinearMap.neg_apply]

theorem DX_generalLeibniz : GeneralLeibniz DX := by
  intro c d
  rw [DX_mul, parityConjugate_DX]
  ext n
  simp only [Finsupp.add_apply, mulRight_apply, mulLeft_apply, sourceData,
    LinearMap.mul_apply']
  rw [add_assoc, ← add_mul, evenPart_add_oddPart]

theorem DY_generalLeibniz : GeneralLeibniz DY := by
  intro c d
  rw [DY_mul, parityConjugate_DY]
  ext n
  simp only [Finsupp.add_apply, mulRight_apply, mulLeft_apply, sourceData,
    LinearMap.mul_apply', LinearMap.neg_apply, Finsupp.neg_apply, mul_neg]
  have heo : evenPart c - oddPart c = parity c := by
    rw [evenPart_apply, oddPart_apply]
    module
  rw [add_assoc, ← sub_eq_add_neg, ← sub_mul, heo]

namespace GeneralLeibniz

theorem zero : GeneralLeibniz 0 := by
  intro c d
  ext n
  simp [sourceData]

theorem add {M N : HamiltonianAction} (hM : GeneralLeibniz M) (hN : GeneralLeibniz N) :
    GeneralLeibniz (M + N) := by
  intro c d
  rw [LinearMap.add_apply, hM, hN, parityConjugate_add]
  ext n
  simp [sourceData, mul_add, add_mul]
  abel

theorem smul (r : ℂ) {M : HamiltonianAction} (hM : GeneralLeibniz M) :
    GeneralLeibniz (r • M) := by
  intro c d
  rw [LinearMap.smul_apply, hM, parityConjugate_smul]
  ext n
  simp [sourceData, smul_add, mul_smul_comm, smul_mul_assoc]

theorem shift {M : HamiltonianAction} (hM : GeneralLeibniz M) :
    GeneralLeibniz (shiftLinear.comp M) := by
  intro c d
  ext n
  cases n with
  | zero =>
    simp [LinearMap.comp_apply, shiftLinear_apply, sourceData]
  | succ n =>
    simp [LinearMap.comp_apply, shiftLinear_apply, sourceData, hM c d]

theorem negativeShift {M : HamiltonianAction} (hM : GeneralLeibniz M) :
    GeneralLeibniz ((-shiftLinear).comp M) := by
  have h := hM.shift.smul (-1)
  have he : (-1 : ℂ) • shiftLinear.comp M = (-shiftLinear).comp M := by
    ext a n
    simp
  rw [← he]
  exact h

theorem negativeShift_pow {M : HamiltonianAction} (hM : GeneralLeibniz M) (i : ℕ) :
    GeneralLeibniz (((-shiftLinear) ^ i).comp M) := by
  induction i with
  | zero => simpa only [pow_zero, Module.End.one_eq_id, LinearMap.id_comp] using hM
  | succ i hi =>
    have h := hi.negativeShift
    simpa only [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc] using h

theorem parityConjugate {M : HamiltonianAction} (hM : GeneralLeibniz M) :
    GeneralLeibniz (Source.parityConjugate M) := by
  intro c d
  ext n
  simp only [parityConjugate_coeff, map_mul]
  rw [hM]
  simp [sourceData]

end GeneralLeibniz

end KhanSL2.Source
