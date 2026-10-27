module

public import KhanSL2.LambdaPolynomialLemmas

@[expose] public section

/-! Linear maps intertwining the fixed operations of differential PVAs. -/

noncomputable section
open scoped BigOperators

namespace KhanSL2

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

def coefficientMap {ι : Type*} (f : A →ₗ[ℂ] B) :
    (ι →₀ A) →ₗ[ℂ] (ι →₀ B) := Finsupp.mapRange.linearMap f

@[simp] theorem coefficientMap_apply {ι : Type*} (f : A →ₗ[ℂ] B)
    (p : ι →₀ A) (i : ι) : coefficientMap f p i = f (p i) := rfl

@[simp] theorem coefficientMap_single {ι : Type*} (f : A →ₗ[ℂ] B)
    (i : ι) (a : A) : coefficientMap f (Finsupp.single i a) =
      Finsupp.single i (f a) := by
  simp [coefficientMap]

theorem coefficientMap_injective {ι : Type*} (f : A →ₗ[ℂ] B)
    (hf : Function.Injective f) :
    Function.Injective (coefficientMap (ι := ι) f) := by
  intro u v h
  ext i
  apply hf
  exact congrArg (fun p : ι →₀ B => p i) h

theorem sum_coefficientMap {ι C : Type*} [AddCommMonoid C]
    (f : A →ₗ[ℂ] B) (p : ι →₀ A) (g : ι → B → C)
    (hg : ∀ i, g i 0 = 0) :
    (coefficientMap f p).sum g = p.sum (fun i a => g i (f a)) :=
  Finsupp.sum_mapRange_index (hf := f.map_zero) hg

theorem coefficientMap_sum {ι κ C : Type*} [Zero C]
    (f : A →ₗ[ℂ] B) (p : ι →₀ C) (g : ι → C → (κ →₀ A)) :
    coefficientMap f (p.sum g) = p.sum (fun i a => coefficientMap f (g i a)) := by
  simp only [Finsupp.sum, map_sum]

namespace LambdaPolynomial

theorem coefficientMap_shift (f : A →ₗ[ℂ] B) (p : LambdaPolynomial A) :
    coefficientMap f p.shift = shift (coefficientMap f p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [shift]
  | add p q hp hq => simp only [shift_add, map_add, hp, hq]
  | single i a => simp [shift]

theorem coefficientMap_mapCoefficients (f : A →ₗ[ℂ] B)
    (TA : Module.End ℂ A) (TB : Module.End ℂ B)
    (hT : ∀ a, f (TA a) = TB (f a)) (p : LambdaPolynomial A) :
    coefficientMap f (p.mapCoefficients TA) =
      mapCoefficients TB (coefficientMap f p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [mapCoefficients]
  | add p q hp hq => simp only [mapCoefficients_add, map_add, hp, hq]
  | single i a => simp [mapCoefficients, hT]

theorem intertwine_pow (f : A →ₗ[ℂ] B)
    (TA : Module.End ℂ A) (TB : Module.End ℂ B)
    (hT : ∀ a, f (TA a) = TB (f a)) (n : ℕ) (a : A) :
    f ((TA ^ n) a) = (TB ^ n) (f a) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', pow_succ']
    change f (TA ((TA ^ n) a)) = TB ((TB ^ n) (f a))
    rw [hT, hn]

theorem coefficientMap_skew (f : A →ₗ[ℂ] B)
    (TA : Module.End ℂ A) (TB : Module.End ℂ B)
    (hT : ∀ a, f (TA a) = TB (f a)) (p : LambdaPolynomial A) :
    coefficientMap f (p.minusVariableMinusTranslation TA) =
      minusVariableMinusTranslation TB (coefficientMap f p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [minusVariableMinusTranslation]
  | add p q hp hq => simp only [skew_add, map_add, hp, hq]
  | single i a =>
    simp only [skew_single, coefficientMap_single, map_sum, map_smul,
      intertwine_pow f TA TB hT]

end LambdaPolynomial

/-- Preservation of raw operations. It does not assume either set of PVA laws. -/
structure PVAMap (DA : DifferentialData A) (brA : LambdaBracket A)
    (DB : DifferentialData B) (brB : LambdaBracket B) where
  linear : A →ₗ[ℂ] B
  map_one : linear DA.one = DB.one
  map_mul : ∀ a b, linear (DA.mul a b) = DB.mul (linear a) (linear b)
  map_translation : ∀ a, linear (DA.translation a) = DB.translation (linear a)
  map_bracket : ∀ a b n, linear (brA a b n) = brB (linear a) (linear b) n

namespace PVAMap

variable {DA : DifferentialData A} {brA : LambdaBracket A}
  {DB : DifferentialData B} {brB : LambdaBracket B}
  (f : PVAMap DA brA DB brB)

theorem map_bracket_poly (a b : A) :
    coefficientMap f.linear (brA a b) = brB (f.linear a) (f.linear b) := by
  ext n
  exact f.map_bracket a b n

theorem map_mulRight (p : LambdaPolynomial A) (b : A) :
    coefficientMap f.linear (p.mulRight DA b) =
      LambdaPolynomial.mulRight DB (coefficientMap f.linear p) (f.linear b) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [LambdaPolynomial.mulRight]
  | add p q hp hq =>
    simp only [LambdaPolynomial.mulRight_add, map_add, hp, hq]
  | single i a => simp [LambdaPolynomial.mulRight, f.map_mul]

theorem map_mulLeft (a : A) (p : LambdaPolynomial A) :
    coefficientMap f.linear (p.mulLeft DA a) =
      LambdaPolynomial.mulLeft DB (f.linear a) (coefficientMap f.linear p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp [LambdaPolynomial.mulLeft]
  | add p q hp hq =>
    simp only [LambdaPolynomial.mulLeft_add, map_add, hp, hq]
  | single i b => simp [LambdaPolynomial.mulLeft, f.map_mul]

theorem map_jacobiLeft (a b c : A) :
    coefficientMap f.linear (brA.jacobiLeft a b c) =
      brB.jacobiLeft (f.linear a) (f.linear b) (f.linear c) := by
  unfold LambdaBracket.jacobiLeft
  rw [← f.map_bracket_poly b c, sum_coefficientMap _ _ _ (by intro; simp)]
  rw [coefficientMap_sum]
  apply Finsupp.sum_congr
  intro j _
  rw [← f.map_bracket_poly a (brA b c j),
    sum_coefficientMap _ _ _ (by intro; simp), coefficientMap_sum]
  simp only [coefficientMap_single]

theorem map_jacobiRight (a b c : A) :
    coefficientMap f.linear (brA.jacobiRight a b c) =
      brB.jacobiRight (f.linear a) (f.linear b) (f.linear c) := by
  unfold LambdaBracket.jacobiRight
  rw [← f.map_bracket_poly a c, sum_coefficientMap _ _ _ (by intro; simp)]
  rw [coefficientMap_sum]
  apply Finsupp.sum_congr
  intro i _
  rw [← f.map_bracket_poly b (brA a c i),
    sum_coefficientMap _ _ _ (by intro; simp), coefficientMap_sum]
  simp only [coefficientMap_single]

theorem map_jacobiMiddle (a b c : A) :
    coefficientMap f.linear (brA.jacobiMiddle a b c) =
      brB.jacobiMiddle (f.linear a) (f.linear b) (f.linear c) := by
  unfold LambdaBracket.jacobiMiddle
  rw [← f.map_bracket_poly a b, sum_coefficientMap _ _ _ (by intro; simp)]
  rw [coefficientMap_sum]
  apply Finsupp.sum_congr
  intro r _
  rw [← f.map_bracket_poly (brA a b r) c,
    sum_coefficientMap _ _ _ (by intro; simp), coefficientMap_sum]
  simp only [map_sum, coefficientMap_single, map_smul]

end PVAMap
end KhanSL2
