module

public import KhanSL2.SourceBracketLeibniz
public import KhanSL2.SourceHamiltonianExt

@[expose] public section

/-! The actual bilinear lambda bracket on the source differential quotient. -/

noncomputable section

namespace KhanSL2.Source

open SourcePresentation LambdaPolynomial SourceBracketOperators BracketAction

theorem rawBracket_eq_of_mk_eq {a b : Expression} (h : mk a = mk b) :
    rawBracket a = rawBracket b := by
  apply GeneralLeibniz.ext (rawBracket_generalLeibniz a) (rawBracket_generalLeibniz b)
    (rawBracket_right_translation a) (rawBracket_right_translation b)
  · rw [rawBracket_X0, rawBracket_X0, h]
  · rw [rawBracket_Y0, rawBracket_Y0, h]

/-- The concrete source lambda bracket. Both inputs are elements of the
original source quotient; no additional relations have been imposed. -/
def bracket : LambdaBracket Source where
  toFun := Quot.lift rawBracket
    (fun _ _ h => rawBracket_eq_of_mk_eq (Quot.sound h))
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    rfl
  map_smul' := by
    rintro r ⟨a⟩
    exact rawBracket_smul r a

@[simp] theorem bracket_mk (a : Expression) : bracket (mk a) = rawBracket a := rfl

@[simp] theorem bracket_X0 : bracket (X 0) = DX := by
  rw [show X 0 = mk (x 0) from rfl, bracket_mk]
  simp [rawBracket, x, Module.End.one_eq_id]

@[simp] theorem bracket_Y0 : bracket (Y 0) = DY := by
  rw [show Y 0 = mk (y 0) from rfl, bracket_mk]
  simp [rawBracket, y, Module.End.one_eq_id]

theorem bracket_generalLeibniz (a : Source) : GeneralLeibniz (bracket a) := by
  induction a using Quot.inductionOn with
  | _ a => exact rawBracket_generalLeibniz a

theorem bracket_right_translation (a b : Source) :
    bracket a (translation b) = rightTranslation translation (bracket a b) := by
  induction a using Quot.inductionOn with
  | _ a => exact rawBracket_right_translation a b

theorem bracket_left_translation (a b : Source) :
    bracket (translation a) b = -shift (bracket a b) := by
  induction a using Quot.inductionOn with
  | _ a =>
    change rawBracket (SourcePresentation.translate a) b = _
    rw [rawBracket_translate]
    rfl

theorem bracket_mul_first (a b : Source) :
    bracket (a * b) =
      rightAction (bracket a) b + leftAction a (bracket b) := by
  induction a using Quot.inductionOn
  induction b using Quot.inductionOn
  rfl

theorem bracket_X0_right (a : Source) : bracket a (X 0) = -K (DX a) := by
  induction a using Quot.inductionOn with
  | _ a => exact rawBracket_X0 a

theorem bracket_Y0_right (a : Source) : bracket a (Y 0) = -K (DY (parity a)) := by
  induction a using Quot.inductionOn with
  | _ a => exact rawBracket_Y0 a

theorem bracket_generator_formulas : IsSourceBracket bracket where
  xx := by
    rw [bracket_X0, DX_X]
    simp [XX, jetAction]
  xy := by
    rw [bracket_X0, DX_Y]
    simp [XY, jetAction]
  yy := by
    rw [bracket_Y0, DY_Y]

end KhanSL2.Source
