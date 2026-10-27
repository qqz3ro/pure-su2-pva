module

public import KhanSL2.SourceSupercomm

@[expose] public section

/-! # The parity involution on the source differential algebra -/

namespace KhanSL2.Source

open SourcePresentation

attribute [local instance] FreeAlgebra.Pre.hasCoeGenerator
  FreeAlgebra.Pre.hasCoeSemiring FreeAlgebra.Pre.hasMul
  FreeAlgebra.Pre.hasAdd FreeAlgebra.Pre.hasZero FreeAlgebra.Pre.hasOne
  FreeAlgebra.Pre.hasSMul

def parityEval : Expression → Source
  | .of (.X i) => X i
  | .of (.Y i) => -Y i
  | .ofScalar r => algebraMap ℂ Source r
  | .add a b => parityEval a + parityEval b
  | .mul a b => parityEval a * parityEval b

@[simp] theorem parityEval_zero : parityEval 0 = 0 := map_zero (algebraMap ℂ Source)
@[simp] theorem parityEval_one : parityEval 1 = 1 := map_one (algebraMap ℂ Source)
@[simp] theorem parityEval_add (a b : Expression) :
    parityEval (a + b) = parityEval a + parityEval b := rfl
@[simp] theorem parityEval_mul (a b : Expression) :
    parityEval (a * b) = parityEval a * parityEval b := rfl
@[simp] theorem parityEval_x (i : ℕ) : parityEval (x i) = X i := rfl
@[simp] theorem parityEval_y (i : ℕ) : parityEval (y i) = -Y i := rfl
@[simp] theorem parityEval_scalar (r : ℂ) :
    parityEval (.ofScalar r) = algebraMap ℂ Source r := rfl
@[simp] theorem parityEval_smul (r : ℂ) (a : Expression) :
    parityEval (r • a) = r • parityEval a := by
  exact (Algebra.smul_def r (parityEval a)).symm

theorem parityEval_translate (a : Expression) :
    parityEval (SourcePresentation.translate a) = translation (parityEval a) := by
  induction a with
  | of g =>
    cases g with
    | X i => rfl
    | Y i => simp [SourcePresentation.translate, parityEval, x, y]
  | ofScalar r =>
    change parityEval 0 = translation (algebraMap ℂ Source r)
    rw [Algebra.algebraMap_eq_smul_one, parityEval_zero, map_smul]
    change 0 = r • (0 : Source)
    rw [smul_zero]
  | add a b ha hb =>
    simpa only [SourcePresentation.translate, parityEval, map_add] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb =>
    simp only [SourcePresentation.translate, parityEval, ha, hb,
      translation_mul]

theorem parityEval_algebra {a b : Expression} (h : FreeAlgebra.Rel ℂ Generator a b) :
    parityEval a = parityEval b := by
  induction h with
  | central_scalar =>
    exact Algebra.commutes _ _
  | _ =>
    simp_all [parityEval, add_assoc, add_comm, mul_assoc, mul_add, add_mul]

theorem parityEval_relation {a b : Expression} (h : Relation a b) :
    parityEval a = parityEval b := by
  induction h with
  | algebra h => exact parityEval_algebra h
  | xx i j => simpa using X_mul_X i j
  | xy i j => simpa using congrArg Neg.neg (X_mul_Y i j)
  | yy i j => simpa using Y_mul_Y i j
  | yy_self i => simp
  | x0_sq => simp
  | x0_y0 => simp
  | x0_y1 => simp
  | y0_y1 => simp
  | translate h ih => simpa only [parityEval_translate] using congrArg translation ih
  | add_left _ ih => simp only [parityEval_add, ih]
  | add_right _ ih => simp only [parityEval_add, ih]
  | mul_left _ ih => simp only [parityEval_mul, ih]
  | mul_right _ ih => simp only [parityEval_mul, ih]

/-- The even generators are fixed and the odd generators change sign. -/
def parity : Source →ₐ[ℂ] Source where
  toFun := Quot.lift parityEval (fun _ _ h => parityEval_relation h)
  map_one' := parityEval_one
  map_mul' := by rintro ⟨a⟩ ⟨b⟩; rfl
  map_zero' := parityEval_zero
  map_add' := by rintro ⟨a⟩ ⟨b⟩; rfl
  commutes' _ := rfl

@[simp] theorem parity_mk (a : Expression) : parity (mk a) = parityEval a := rfl
@[simp] theorem parity_X (i : ℕ) : parity (X i) = X i := rfl
@[simp] theorem parity_Y (i : ℕ) : parity (Y i) = -Y i := rfl

theorem parity_translation (a : Source) :
    parity (translation a) = translation (parity a) := by
  induction a using Quot.inductionOn with
  | _ a => exact parityEval_translate a

@[simp] theorem parity_parity (a : Source) : parity (parity a) = a := by
  induction a using inductionOn with
  | scalar r => simp
  | hx i => simp
  | hy i => simp
  | add a b ha hb => simp [ha, hb]
  | mul a b ha hb => simp [ha, hb]

theorem parity_homogeneous {d : Degree} {a : Expression} (ha : Homogeneous d a) :
    parity (mk a) = koszulSign (1, 0, 0) d • mk a := by
  induction ha with
  | zero d => simp
  | scalar r =>
    change parity (algebraMap ℂ Source r) = koszulSign (1, 0, 0) 0 • algebraMap ℂ Source r
    simpa only [koszulSign_zero_right, one_smul] using parity.commutes r
  | x i =>
    change parity (X i) = koszulSign (1, 0, 0) (2, 1, (i : ℤ) + 2) • X i
    simp [koszulSign]
  | y i =>
    change parity (Y i) = koszulSign (1, 0, 0) (3, 3, (i : ℤ) + 3) • Y i
    simp [koszulSign]
  | add ha hb ia ib => simpa only [mk_add, map_add, smul_add] using congrArg₂ (· + ·) ia ib
  | mul ha hb ia ib =>
    rw [mk_mul, map_mul, ia, ib, koszulSign_add_right, smul_mul_smul_comm]

/-- Parity acts on a homogeneous element by its CE-degree sign. -/
theorem parity_of_mem {d : Degree} {a : Source} (ha : a ∈ piece d) :
    parity a = koszulSign (1, 0, 0) d • a := by
  obtain ⟨a, ha, rfl⟩ := ha
  exact parity_homogeneous ha

end KhanSL2.Source
