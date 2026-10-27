module

public import KhanSL2.SourceParity
public import KhanSL2.SourceJetActions
public import KhanSL2.SourceGeneratorChecks
public import KhanSL2.SourceData
public import KhanSL2.LambdaPolynomialLemmas
public import Mathlib.Tactic.Abel

@[expose] public section

/-! # Hamiltonian derivations on the presented source algebra -/

noncomputable section

namespace KhanSL2.Source

open SourcePresentation LambdaPolynomial

attribute [local instance] FreeAlgebra.Pre.hasCoeGenerator
  FreeAlgebra.Pre.hasCoeSemiring FreeAlgebra.Pre.hasMul
  FreeAlgebra.Pre.hasAdd FreeAlgebra.Pre.hasZero FreeAlgebra.Pre.hasOne
  FreeAlgebra.Pre.hasSMul

@[simp] theorem mk_scalar (r : ℂ) :
    mk (.ofScalar r) = algebraMap ℂ Source r := rfl

@[simp] theorem mk_translate (a : Expression) :
    mk (SourcePresentation.translate a) = translation (mk a) := rfl

@[simp] theorem mk_x (i : ℕ) : mk (x i) = X i := rfl
@[simp] theorem mk_y (i : ℕ) : mk (y i) = Y i := rfl

/-- Extend generator values by the twisted Leibniz rule on finite expressions. -/
def actionEval (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) : Expression → LambdaPolynomial Source
  | .of (.X i) => fX i
  | .of (.Y i) => fY i
  | .ofScalar _ => 0
  | .add a b => actionEval σ fX fY a + actionEval σ fX fY b
  | .mul a b =>
      mulRight sourceData (actionEval σ fX fY a) (mk b) +
      mulLeft sourceData (σ (mk a)) (actionEval σ fX fY b)

@[simp] theorem actionEval_zero (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) :
    actionEval σ fX fY 0 = 0 := rfl

@[simp] theorem actionEval_scalar (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) (r : ℂ) :
    actionEval σ fX fY (.ofScalar r) = 0 := rfl

@[simp] theorem actionEval_x (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) (i : ℕ) :
    actionEval σ fX fY (x i) = fX i := rfl

@[simp] theorem actionEval_y (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) (i : ℕ) :
    actionEval σ fX fY (y i) = fY i := rfl

@[simp] theorem actionEval_add (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) (a b : Expression) :
    actionEval σ fX fY (a + b) = actionEval σ fX fY a + actionEval σ fX fY b := rfl

@[simp] theorem actionEval_mul (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) (a b : Expression) :
    actionEval σ fX fY (a * b) =
      mulRight sourceData (actionEval σ fX fY a) (mk b) +
      mulLeft sourceData (σ (mk a)) (actionEval σ fX fY b) := rfl

theorem actionEval_algebra (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) {a b : Expression}
    (h : FreeAlgebra.Rel ℂ Generator a b) :
    actionEval σ fX fY a = actionEval σ fX fY b := by
  induction h with
  | @add_compat_left a b c _ ih =>
    simp only [actionEval_add, ih]
  | @add_compat_right a b c _ ih =>
    simp only [actionEval_add, ih]
  | @mul_compat_left a b c h ih =>
    have hm : mk a = mk b := Quot.sound (Relation.algebra h)
    simp only [actionEval_mul, ih, hm]
  | @mul_compat_right a b c h ih =>
    have hm : mk a = mk b := Quot.sound (Relation.algebra h)
    simp only [actionEval_mul, ih, hm]
  | central_scalar =>
    ext n
    simp only [actionEval_mul, actionEval_scalar, mk_scalar, AlgHom.commutes,
      Finsupp.add_apply, mulRight_apply, mulLeft_apply, Finsupp.zero_apply,
      sourceData, LinearMap.mul_apply', zero_mul, mul_zero, zero_add, add_zero]
    exact Algebra.commutes _ _
  | _ =>
    ext n
    simp [actionEval, sourceData, mk_scalar, mk_add, mk_mul, mk_zero, mk_one,
      mulRight_apply, mulLeft_apply, mul_add, add_mul, mul_assoc, add_assoc, add_comm,
      add_left_comm]

theorem actionEval_smul (σ : Source →ₐ[ℂ] Source)
    (fX fY : ℕ → LambdaPolynomial Source) (r : ℂ) (a : Expression) :
    actionEval σ fX fY (r • a) = r • actionEval σ fX fY a := by
  ext n
  change (mulRight sourceData 0 (mk a) +
    mulLeft sourceData (σ (algebraMap ℂ Source r)) (actionEval σ fX fY a)) n = _
  simp [sourceData, Algebra.smul_def]

theorem actionEval_translate (σ : Source →ₐ[ℂ] Source)
    (hσ : ∀ a, σ (translation a) = translation (σ a))
    (fX fY : ℕ → LambdaPolynomial Source)
    (hX : ∀ i, fX (i + 1) = rightTranslation translation (fX i))
    (hY : ∀ i, fY (i + 1) = rightTranslation translation (fY i))
    (a : Expression) :
    actionEval σ fX fY (SourcePresentation.translate a) =
      rightTranslation translation (actionEval σ fX fY a) := by
  induction a with
  | of g =>
    cases g with
    | X i => exact hX i
    | Y i => exact hY i
  | ofScalar _ => exact (map_zero _).symm
  | add a b ha hb =>
    simpa only [SourcePresentation.translate, actionEval, map_add] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb =>
    change
      (mulRight sourceData (actionEval σ fX fY (SourcePresentation.translate a)) (mk b) +
        mulLeft sourceData (σ (mk (SourcePresentation.translate a))) (actionEval σ fX fY b)) +
      (mulRight sourceData (actionEval σ fX fY a) (mk (SourcePresentation.translate b)) +
        mulLeft sourceData (σ (mk a)) (actionEval σ fX fY (SourcePresentation.translate b))) =
      rightTranslation translation
        (mulRight sourceData (actionEval σ fX fY a) (mk b) +
          mulLeft sourceData (σ (mk a)) (actionEval σ fX fY b))
    have hr (p : LambdaPolynomial Source) (c : Source) :
        rightTranslation translation (mulRight sourceData p c) =
          mulRight sourceData (rightTranslation translation p) c +
            mulRight sourceData p (translation c) :=
      rightTranslation_mulRight sourceData translation_mul p c
    have hl (c : Source) (p : LambdaPolynomial Source) :
        rightTranslation translation (mulLeft sourceData c p) =
          mulLeft sourceData (translation c) p +
            mulLeft sourceData c (rightTranslation translation p) :=
      rightTranslation_mulLeft sourceData translation_mul c p
    rw [map_add, hr, hl]
    simp only [ha, hb, mk_translate, hσ]
    abel

/-- Exactly the compatibility checks needed to descend a generator Hamiltonian.
All fields will be proved for the concrete actions; this structure does not
introduce any ambient assumption about the source. -/
structure ActionPresentation where
  σ : Source →ₐ[ℂ] Source
  sigma_translation : ∀ a, σ (translation a) = translation (σ a)
  fX : ℕ → LambdaPolynomial Source
  fY : ℕ → LambdaPolynomial Source
  shift_X : ∀ i, fX (i + 1) = rightTranslation translation (fX i)
  shift_Y : ∀ i, fY (i + 1) = rightTranslation translation (fY i)
  xx : ∀ i j, actionEval σ fX fY (x i * x j) = actionEval σ fX fY (x j * x i)
  xy : ∀ i j, actionEval σ fX fY (x i * y j) = actionEval σ fX fY (y j * x i)
  yy : ∀ i j, actionEval σ fX fY (y i * y j) =
    actionEval σ fX fY ((-1 : ℂ) • (y j * y i))
  yy_self : ∀ i, actionEval σ fX fY (y i * y i) = 0
  x0_sq : actionEval σ fX fY (x 0 * x 0) = 0
  x0_y0 : actionEval σ fX fY (x 0 * y 0) = 0
  x0_y1 : actionEval σ fX fY (x 0 * y 1) = 0
  y0_y1 : actionEval σ fX fY (y 0 * y 1) = 0

namespace ActionPresentation

theorem respects (D : ActionPresentation) {a b : Expression} (h : Relation a b) :
    actionEval D.σ D.fX D.fY a = actionEval D.σ D.fX D.fY b := by
  induction h with
  | algebra h => exact actionEval_algebra _ _ _ h
  | xx i j => exact D.xx i j
  | xy i j => exact D.xy i j
  | yy i j => exact D.yy i j
  | yy_self i => exact D.yy_self i
  | x0_sq => exact D.x0_sq
  | x0_y0 => exact D.x0_y0
  | x0_y1 => exact D.x0_y1
  | y0_y1 => exact D.y0_y1
  | translate _ ih =>
    simpa only [actionEval_translate D.σ D.sigma_translation D.fX D.fY D.shift_X D.shift_Y]
      using congrArg (rightTranslation translation) ih
  | add_left _ ih => simp only [actionEval_add, ih]
  | add_right _ ih => simp only [actionEval_add, ih]
  | @mul_left a b c h ih =>
    have hm : Source.mk a = Source.mk b := Quot.sound h
    simp only [actionEval_mul, ih, hm]
  | @mul_right a b c h ih =>
    have hm : Source.mk a = Source.mk b := Quot.sound h
    simp only [actionEval_mul, ih, hm]

/-- The descended, complex-linear generator Hamiltonian. -/
def lift (D : ActionPresentation) : Source →ₗ[ℂ] LambdaPolynomial Source where
  toFun := Quot.lift (actionEval D.σ D.fX D.fY) (fun _ _ h => D.respects h)
  map_add' := by rintro ⟨a⟩ ⟨b⟩; rfl
  map_smul' := by rintro r ⟨a⟩; exact actionEval_smul _ _ _ r a

@[simp] theorem lift_X (D : ActionPresentation) (i : ℕ) :
    D.lift (X i) = D.fX i := rfl

@[simp] theorem lift_Y (D : ActionPresentation) (i : ℕ) :
    D.lift (Y i) = D.fY i := rfl

theorem lift_mul (D : ActionPresentation) (a b : Source) :
    D.lift (a * b) =
      mulRight sourceData (D.lift a) b + mulLeft sourceData (D.σ a) (D.lift b) := by
  induction a using Quot.inductionOn
  induction b using Quot.inductionOn
  rfl

theorem lift_translation (D : ActionPresentation) (a : Source) :
    D.lift (translation a) = rightTranslation translation (D.lift a) := by
  induction a using Quot.inductionOn with
  | _ a => exact actionEval_translate _ D.sigma_translation _ _ D.shift_X D.shift_Y a

end ActionPresentation

open SourceGeneratorChecks

/-- The even Hamiltonian associated with `X` respects every defining relation. -/
def presentationX : ActionPresentation where
  σ := AlgHom.id ℂ Source
  sigma_translation _ := rfl
  fX := XX
  fY := XY
  shift_X _ := rfl
  shift_Y _ := rfl
  xx i j := by
    ext n
    simp only [actionEval_mul, actionEval_x, mk_x, AlgHom.id_apply,
      Finsupp.add_apply, mulRight_apply, mulLeft_apply, sourceData, LinearMap.mul_apply']
    rw [XX_commute_X i j, XX_commute_X j i, add_comm]
  xy i j := by
    ext n
    simp only [actionEval_mul, actionEval_x, actionEval_y, mk_x, mk_y, AlgHom.id_apply,
      Finsupp.add_apply, mulRight_apply, mulLeft_apply, sourceData, LinearMap.mul_apply']
    rw [XX_commute_Y i j, XY_commute_X j i, add_comm]
  yy i j := by
    ext n
    simp only [actionEval_smul, actionEval_mul, actionEval_y, mk_y, AlgHom.id_apply,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.neg_apply, mulRight_apply, mulLeft_apply,
      sourceData, LinearMap.mul_apply', neg_one_smul]
    rw [XY_anticommute_Y i j, XY_anticommute_Y j i]
    abel
  yy_self i := by
    ext n
    simp only [actionEval_mul, actionEval_y, mk_y, AlgHom.id_apply,
      Finsupp.add_apply, mulRight_apply, mulLeft_apply, sourceData, LinearMap.mul_apply',
      Finsupp.zero_apply, XY_anticommute_Y, neg_add_cancel]
  x0_sq := by
    ext n
    rcases n with _ | (_ | n) <;>
      simp [actionEval_mul, XX, jetAction, sourceData, smul_mul_assoc,
        mul_smul_comm, differentiated_X0_sq]
  x0_y0 := by
    ext n
    rcases n with _ | (_ | n) <;>
      simp [actionEval_mul, XX, XY, jetAction, sourceData, smul_mul_assoc,
        mul_smul_comm, differentiated_X0_Y0]
  x0_y1 := by
    ext n
    rcases n with _ | (_ | (_ | n)) <;>
      simp [actionEval_mul, XX, XY, jetAction, rightTranslation_apply,
        sourceData, smul_mul_assoc, mul_smul_comm, mul_add, differentiated_X0_Y1]
  y0_y1 := by
    ext n
    rcases n with _ | (_ | (_ | n)) <;>
      simp [actionEval_mul, XY, jetAction, rightTranslation_apply,
        sourceData, smul_mul_assoc, mul_smul_comm, mul_add]

/-- The odd Hamiltonian associated with `Y` respects every defining relation. -/
def presentationY : ActionPresentation where
  σ := parity
  sigma_translation := parity_translation
  fX := YX
  fY := fun _ => 0
  shift_X _ := rfl
  shift_Y _ := (map_zero _).symm
  xx i j := by
    ext n
    simp only [actionEval_mul, actionEval_x, mk_x, parity_X,
      Finsupp.add_apply, mulRight_apply, mulLeft_apply, sourceData, LinearMap.mul_apply']
    rw [YX_commute_X i j, YX_commute_X j i, add_comm]
  xy i j := by
    ext n
    simp [actionEval_mul, sourceData, YX_anticommute_Y]
  yy i j := by
    ext n
    simp [actionEval_mul, actionEval_smul, sourceData]
  yy_self i := by
    ext n
    simp [actionEval_mul, sourceData]
  x0_sq := by
    ext n
    rcases n with _ | (_ | n) <;>
      simp [actionEval_mul, YX, jetAction, sourceData, smul_mul_assoc,
        mul_smul_comm, ← X_mul_Y]
  x0_y0 := by
    ext n
    rcases n with _ | (_ | n) <;>
      simp [actionEval_mul, YX, jetAction, sourceData, smul_mul_assoc,
        mul_smul_comm, Y_mul_Y 1 0]
  x0_y1 := by
    ext n
    rcases n with _ | (_ | n) <;>
      simp [actionEval_mul, YX, jetAction, sourceData, smul_mul_assoc,
        mul_smul_comm]
  y0_y1 := by
    ext n
    simp [actionEval_mul, sourceData]

/-- The actual generator Hamiltonian `{X_lambda -}` on the differential quotient. -/
def DX : Source →ₗ[ℂ] LambdaPolynomial Source := presentationX.lift

/-- The actual generator Hamiltonian `{Y_lambda -}` on the differential quotient. -/
def DY : Source →ₗ[ℂ] LambdaPolynomial Source := presentationY.lift

@[simp] theorem DX_X (i : ℕ) : DX (X i) = XX i := rfl
@[simp] theorem DX_Y (i : ℕ) : DX (Y i) = XY i := rfl
@[simp] theorem DY_X (i : ℕ) : DY (X i) = YX i := rfl
@[simp] theorem DY_Y (i : ℕ) : DY (Y i) = 0 := rfl

theorem DX_mul (a b : Source) :
    DX (a * b) = mulRight sourceData (DX a) b + mulLeft sourceData a (DX b) :=
  presentationX.lift_mul a b

theorem DY_mul (a b : Source) :
    DY (a * b) = mulRight sourceData (DY a) b + mulLeft sourceData (parity a) (DY b) :=
  presentationY.lift_mul a b

theorem DX_translation (a : Source) :
    DX (translation a) = rightTranslation translation (DX a) :=
  presentationX.lift_translation a

theorem DY_translation (a : Source) :
    DY (translation a) = rightTranslation translation (DY a) :=
  presentationY.lift_translation a

end KhanSL2.Source
