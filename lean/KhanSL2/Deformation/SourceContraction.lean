module

public import KhanSL2.Deformation.PhiDelta
public import KhanSL2.SourceGeneratorChecks

@[expose] public section

/-!
# The source contractions `h₁`, `h₀` (paper Lemma 5.2, blueprint `lem:contractions`)

`h_ℓ` is the odd derivation of the source `A` with `h_ℓ X_j = 0` and
`h₁ Y_j = -X_j`, `h₀ Y_j = -(j/2) X_{j-1}` (`h₀ Y₀ = 0`). It is defined on finite expressions by
the twisted Leibniz rule and descends through the defining relation:
* the four relations are sent to elements of the differential ideal;
* `[h₁, ∂] = 0` and `[h₀, ∂] = h₁/2` at expression level, so the translate of a relation is
  respected.
-/

noncomputable section

namespace KhanSL2.Source

open SourcePresentation

attribute [local instance] FreeAlgebra.Pre.hasCoeGenerator
  FreeAlgebra.Pre.hasCoeSemiring FreeAlgebra.Pre.hasMul
  FreeAlgebra.Pre.hasAdd FreeAlgebra.Pre.hasZero FreeAlgebra.Pre.hasOne
  FreeAlgebra.Pre.hasSMul

theorem X0_X1 : X 0 * X 1 = 0 := by
  have h := SourceGeneratorChecks.differentiated_X0_sq
  rw [X_mul_X 1 0, ← two_smul ℂ] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-- Generator values of `h₁`. -/
def contractionGenOne : Generator → Source
  | .X _ => 0
  | .Y i => -X i

/-- Generator values of `h₀`. -/
def contractionGenZero : Generator → Source
  | .X _ => 0
  | .Y i => (-((i : ℂ) / 2)) • X (i - 1)

/-- Evaluation of an odd derivation with generator values `g` on finite expressions. -/
def hEval (g : Generator → Source) : Expression → Source
  | .of a => g a
  | .ofScalar _ => 0
  | .add a b => hEval g a + hEval g b
  | .mul a b => hEval g a * mk b + parity (mk a) * hEval g b

variable (g : Generator → Source)

@[simp] theorem hEval_of (a : Generator) : hEval g (.of a) = g a := rfl
@[simp] theorem hEval_x (i : ℕ) : hEval g (x i) = g (.X i) := rfl
@[simp] theorem hEval_y (i : ℕ) : hEval g (y i) = g (.Y i) := rfl
@[simp] theorem hEval_scalar (r : ℂ) : hEval g (.ofScalar r) = 0 := rfl
@[simp] theorem hEval_zero : hEval g 0 = 0 := rfl
@[simp] theorem hEval_one : hEval g 1 = 0 := rfl
@[simp] theorem hEval_add (a b : Expression) : hEval g (a + b) = hEval g a + hEval g b := rfl
@[simp] theorem hEval_mul (a b : Expression) :
    hEval g (a * b) = hEval g a * mk b + parity (mk a) * hEval g b := rfl

theorem hEval_smul (r : ℂ) (a : Expression) : hEval g (r • a) = r • hEval g a := by
  change 0 * mk a + parity (algebraMap ℂ Source r) * hEval g a = r • hEval g a
  rw [zero_mul, zero_add, AlgHom.commutes, Algebra.smul_def]

theorem hEval_algebra {a b : Expression} (h : FreeAlgebra.Rel ℂ Generator a b) :
    hEval g a = hEval g b := by
  induction h with
  | add_scalar => simp
  | mul_scalar => simp
  | central_scalar =>
    rename_i r a
    change 0 * mk a + parity (algebraMap ℂ Source r) * hEval g a =
      hEval g a * algebraMap ℂ Source r + parity (mk a) * 0
    rw [zero_mul, zero_add, mul_zero, add_zero, AlgHom.commutes, Algebra.commutes]
  | add_assoc => simp [add_assoc]
  | add_comm => simp [add_comm]
  | zero_add => simp
  | mul_assoc =>
    simp only [hEval_mul, mk_mul, map_mul, add_mul, mul_add, mul_assoc]
    abel
  | one_mul =>
    simp only [hEval_mul, hEval_one, zero_mul, zero_add, mk_one, map_one, one_mul]
  | mul_one =>
    simp only [hEval_mul, hEval_one, mul_zero, add_zero, mk_one, mul_one]
  | left_distrib =>
    simp only [hEval_mul, hEval_add, mk_add, mul_add, add_mul]
    abel
  | right_distrib =>
    simp only [hEval_mul, hEval_add, mk_add, map_add, mul_add, add_mul]
    abel
  | zero_mul => simp
  | mul_zero => simp
  | add_compat_left _ ih => simp [ih]
  | add_compat_right _ ih => simp [ih]
  | mul_compat_left hr ih =>
    simp only [hEval_mul, ih]
    rw [show mk _ = mk _ from Quot.sound (Relation.algebra hr)]
  | mul_compat_right hr ih =>
    simp only [hEval_mul, ih]
    rw [show mk _ = mk _ from Quot.sound (Relation.algebra hr)]

/-- Descent through the defining relation, given the relation checks and translation. -/
theorem hEval_relation
    (hxx : ∀ i j, hEval g (x i * x j) = hEval g (x j * x i))
    (hxy : ∀ i j, hEval g (x i * y j) = hEval g (y j * x i))
    (hyy : ∀ i j, hEval g (y i * y j) = hEval g ((-1 : ℂ) • (y j * y i)))
    (hyy0 : ∀ i, hEval g (y i * y i) = 0)
    (h00 : hEval g (x 0 * x 0) = 0) (h01 : hEval g (x 0 * y 0) = 0)
    (h02 : hEval g (x 0 * y 1) = 0) (h03 : hEval g (y 0 * y 1) = 0)
    (htr : ∀ a b, Relation a b → hEval g a = hEval g b →
      hEval g (SourcePresentation.translate a) = hEval g (SourcePresentation.translate b))
    {a b : Expression} (h : Relation a b) : hEval g a = hEval g b := by
  induction h with
  | algebra h => exact hEval_algebra g h
  | xx i j => exact hxx i j
  | xy i j => exact hxy i j
  | yy i j => exact hyy i j
  | yy_self i => exact hyy0 i
  | x0_sq => exact h00
  | x0_y0 => exact h01
  | x0_y1 => exact h02
  | y0_y1 => exact h03
  | translate hr ih => exact htr _ _ hr ih
  | add_left _ ih => simp [ih]
  | add_right _ ih => simp [ih]
  | mul_left hr ih =>
    simp only [hEval_mul, ih]
    rw [show mk _ = mk _ from Quot.sound hr]
  | mul_right hr ih =>
    simp only [hEval_mul, ih]
    rw [show mk _ = mk _ from Quot.sound hr]

/-- The source parity commutes with translation, at the level of `mk`. -/
theorem parity_mk_translate (a : Expression) :
    parity (mk (SourcePresentation.translate a)) = translation (parity (mk a)) := by
  change parity (translation (mk a)) = _
  exact parity_translation _

theorem mk_translate' (a : Expression) :
    mk (SourcePresentation.translate a) = translation (mk a) := rfl

variable {g} in
theorem hEval_add' (a b : Expression) :
    hEval g (FreeAlgebra.Pre.add a b) = hEval g a + hEval g b := rfl

variable {g} in
theorem hEval_mul' (a b : Expression) :
    hEval g (FreeAlgebra.Pre.mul a b) = hEval g a * mk b + parity (mk a) * hEval g b := rfl

/-! ## `h₁` -/

theorem hEval_one_translate (e : Expression) :
    hEval contractionGenOne (SourcePresentation.translate e) =
      translation (hEval contractionGenOne e) := by
  induction e with
  | of a =>
    cases a with
    | X i => simp [SourcePresentation.translate, contractionGenOne]
    | Y i => simp [SourcePresentation.translate, contractionGenOne]
  | ofScalar r => simp [SourcePresentation.translate]
  | add a b ha hb =>
    show hEval contractionGenOne (SourcePresentation.translate a + SourcePresentation.translate b)
      = translation (hEval contractionGenOne (a + b))
    rw [hEval_add, hEval_add, ha, hb, map_add]
  | mul a b ha hb =>
    show hEval contractionGenOne (SourcePresentation.translate a * b +
      a * SourcePresentation.translate b) = translation (hEval contractionGenOne (a * b))
    rw [hEval_add, hEval_mul, hEval_mul, hEval_mul, ha, hb, parity_mk_translate, mk_translate',
      map_add, translation_mul, translation_mul]
    abel

theorem contractionOne_relation {a b : Expression} (h : Relation a b) :
    hEval contractionGenOne a = hEval contractionGenOne b := by
  apply hEval_relation contractionGenOne _ _ _ _ _ _ _ _ _ h
  · intro i j; simp [contractionGenOne]
  · intro i j
    simp only [hEval_mul, hEval_x, hEval_y, contractionGenOne, zero_mul, zero_add, mul_zero,
      add_zero]
    change parity (X i) * -X j = -X j * X i
    rw [parity_X, mul_neg, neg_mul, X_mul_X]
  · intro i j
    rw [hEval_smul]
    simp only [hEval_mul, hEval_y, contractionGenOne]
    change -X i * Y j + parity (Y i) * -X j = (-1 : ℂ) • (-X j * Y i + parity (Y j) * -X i)
    rw [parity_Y, parity_Y, neg_one_smul]
    simp only [neg_mul, mul_neg, neg_neg, X_mul_Y]
    abel
  · intro i
    simp only [hEval_mul, hEval_y, contractionGenOne]
    change -X i * Y i + parity (Y i) * -X i = 0
    rw [parity_Y, neg_mul_neg, neg_mul, X_mul_Y, neg_add_cancel]
  · simp [contractionGenOne]
  · simp only [hEval_mul, hEval_x, hEval_y, contractionGenOne, zero_mul, zero_add]
    change parity (X 0) * -X 0 = 0
    rw [parity_X, mul_neg, X0_sq, neg_zero]
  · simp only [hEval_mul, hEval_x, hEval_y, contractionGenOne, zero_mul, zero_add]
    change parity (X 0) * -X 1 = 0
    rw [parity_X, mul_neg, X0_X1, neg_zero]
  · simp only [hEval_mul, hEval_y, contractionGenOne]
    change -X 0 * Y 1 + parity (Y 0) * -X 1 = 0
    rw [parity_Y, neg_mul, X0_Y1, neg_zero, zero_add, neg_mul_neg, ← X_mul_Y,
      SourceGeneratorChecks.X1_Y0]
  · intro a b _ hab
    rw [hEval_one_translate, hEval_one_translate, hab]

/-! ## `h₀` -/

theorem hEval_zero_translate (e : Expression) :
    hEval contractionGenZero (SourcePresentation.translate e) =
      translation (hEval contractionGenZero e) + (1 / 2 : ℂ) • hEval contractionGenOne e := by
  induction e with
  | of a =>
    cases a with
    | X i => simp [SourcePresentation.translate, contractionGenZero, contractionGenOne]
    | Y i =>
      cases i with
      | zero =>
        simp [SourcePresentation.translate, contractionGenZero, contractionGenOne]
      | succ i =>
        show hEval contractionGenZero (y (i + 1 + 1)) =
          translation (hEval contractionGenZero (y (i + 1))) +
            (1 / 2 : ℂ) • hEval contractionGenOne (y (i + 1))
        simp only [hEval_y, contractionGenZero, contractionGenOne, map_smul, Nat.add_sub_cancel,
          translation_X]
        push_cast
        module
  | ofScalar r => simp [SourcePresentation.translate]
  | add a b ha hb =>
    show hEval contractionGenZero (SourcePresentation.translate a + SourcePresentation.translate b)
      = translation (hEval contractionGenZero (a + b)) + (1 / 2 : ℂ) • hEval contractionGenOne (a + b)
    rw [hEval_add, hEval_add, hEval_add, ha, hb, map_add]
    module
  | mul a b ha hb =>
    show hEval contractionGenZero (SourcePresentation.translate a * b +
      a * SourcePresentation.translate b) = translation (hEval contractionGenZero (a * b)) +
        (1 / 2 : ℂ) • hEval contractionGenOne (a * b)
    rw [hEval_add, hEval_mul, hEval_mul, hEval_mul, hEval_mul, ha, hb, parity_mk_translate,
      mk_translate', map_add, translation_mul, translation_mul]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add]
    abel

theorem contractionZero_relation {a b : Expression} (h : Relation a b) :
    hEval contractionGenZero a = hEval contractionGenZero b := by
  apply hEval_relation contractionGenZero _ _ _ _ _ _ _ _ _ h
  · intro i j; simp [contractionGenZero]
  · intro i j
    simp only [hEval_mul, hEval_x, hEval_y, contractionGenZero, zero_mul, zero_add, mul_zero,
      add_zero]
    change parity (X i) * ((-((j : ℂ) / 2)) • X (j - 1)) = ((-((j : ℂ) / 2)) • X (j - 1)) * X i
    rw [parity_X, mul_smul_comm, smul_mul_assoc, X_mul_X]
  · intro i j
    rw [hEval_smul]
    simp only [hEval_mul, hEval_y, contractionGenZero]
    change ((-((i : ℂ) / 2)) • X (i - 1)) * Y j + parity (Y i) * ((-((j : ℂ) / 2)) • X (j - 1)) =
      (-1 : ℂ) • (((-((j : ℂ) / 2)) • X (j - 1)) * Y i +
        parity (Y j) * ((-((i : ℂ) / 2)) • X (i - 1)))
    rw [parity_Y, parity_Y]
    simp only [smul_mul_assoc, mul_smul_comm, neg_mul, X_mul_Y]
    module
  · intro i
    simp only [hEval_mul, hEval_y, contractionGenZero]
    change ((-((i : ℂ) / 2)) • X (i - 1)) * Y i + parity (Y i) * ((-((i : ℂ) / 2)) • X (i - 1))
      = 0
    rw [parity_Y]
    simp only [smul_mul_assoc, mul_smul_comm, neg_mul, X_mul_Y]
    module
  · simp [contractionGenZero]
  · simp [contractionGenZero]
  · simp only [hEval_mul, hEval_x, hEval_y, contractionGenZero, zero_mul, zero_add]
    change parity (X 0) * ((-(((1 : ℕ) : ℂ) / 2)) • X (1 - 1)) = 0
    rw [parity_X, Nat.sub_self, mul_smul_comm, X0_sq, smul_zero]
  · simp only [hEval_mul, hEval_y, contractionGenZero]
    change ((-(((0 : ℕ) : ℂ) / 2)) • X (0 - 1)) * Y 1 +
      parity (Y 0) * ((-(((1 : ℕ) : ℂ) / 2)) • X (1 - 1)) = 0
    rw [parity_Y, Nat.sub_self]
    simp only [Nat.cast_zero, zero_div, neg_zero, zero_smul, zero_mul, zero_add, neg_mul,
      mul_smul_comm, ← X_mul_Y, X0_Y0, smul_zero, neg_zero]
  · intro a b hr hab
    rw [hEval_zero_translate, hEval_zero_translate, hab, contractionOne_relation hr]

/-! ## The contractions as linear maps -/

/-- Descend an expression evaluation to a linear map on the source. -/
def contractionOfEval (h : ∀ a b, Relation a b → hEval g a = hEval g b) :
    Source →ₗ[ℂ] Source where
  toFun := Quot.lift (hEval g) h
  map_add' := by rintro ⟨a⟩ ⟨b⟩; rfl
  map_smul' := by rintro r ⟨a⟩; exact hEval_smul g r a

/-- **`h₁`**. -/
def contractionOne : Source →ₗ[ℂ] Source :=
  contractionOfEval contractionGenOne (fun _ _ h => contractionOne_relation h)

/-- **`h₀`**. -/
def contractionZero : Source →ₗ[ℂ] Source :=
  contractionOfEval contractionGenZero (fun _ _ h => contractionZero_relation h)

/-- `h_ℓ` for `ℓ = 0, 1`. -/
def contraction : ℕ → Source →ₗ[ℂ] Source
  | 0 => contractionZero
  | _ + 1 => contractionOne

theorem contraction_mk (ℓ : ℕ) (e : Expression) :
    contraction ℓ (mk e) =
      hEval (if ℓ = 0 then contractionGenZero else contractionGenOne) e := by
  cases ℓ <;> rfl

theorem contraction_mul (ℓ : ℕ) (a b : Source) :
    contraction ℓ (a * b) = contraction ℓ a * b + parity a * contraction ℓ b := by
  induction a using Quot.inductionOn
  induction b using Quot.inductionOn
  cases ℓ <;> rfl

theorem contraction_algebraMap (ℓ : ℕ) (r : ℂ) : contraction ℓ (algebraMap ℂ Source r) = 0 := by
  cases ℓ <;> rfl

@[simp] theorem contraction_X (ℓ i : ℕ) : contraction ℓ (X i) = 0 := by
  cases ℓ <;> rfl

theorem contractionOne_Y (i : ℕ) : contraction 1 (Y i) = -X i := rfl

theorem contractionZero_Y (i : ℕ) : contraction 0 (Y i) = (-((i : ℂ) / 2)) • X (i - 1) := rfl

theorem contraction_parity {ℓ : ℕ} (hℓ : ℓ ≤ 1) (a : Source) :
    contraction ℓ (parity a) = -parity (contraction ℓ a) := by
  induction a using Source.inductionOn with
  | scalar r => rw [AlgHom.commutes, contraction_algebraMap, map_zero, neg_zero]
  | hx i => simp
  | hy i =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
    · rw [parity_Y, map_neg, contractionZero_Y, map_smul, parity_X]
    · rw [parity_Y, map_neg, contractionOne_Y, map_neg, parity_X]
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]
  | mul a b ha hb =>
    rw [map_mul, contraction_mul, contraction_mul, ha, hb, parity_parity, map_add, map_mul,
      map_mul, parity_parity]
    noncomm_ring

end KhanSL2.Source
