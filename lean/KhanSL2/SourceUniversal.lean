module

public import KhanSL2.Source
public import KhanSL2.PVA

@[expose] public section

/-!
# Evaluation of the source presentation

The map below is constructed by evaluation of finite expressions and descent
through the defining relation. Its construction uses the four actual equations
on the images of `X 0` and `Y 0`, rather than an assumed isomorphism.
-/

noncomputable section

namespace KhanSL2

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

/-- The data needed to evaluate the source's differential presentation. -/
structure SourceGeneratorImages (D : DifferentialData A) where
  x : A
  y : A
  x_mem : x ∈ D.piece (2, 1, 2)
  y_mem : y ∈ D.piece (3, 3, 3)
  x_sq : D.mul x x = 0
  xy : D.mul x y = 0
  x_ty : D.mul x (D.translation y) = 0
  y_ty : D.mul y (D.translation y) = 0

namespace SourceGeneratorImages

open SourcePresentation

attribute [local instance] FreeAlgebra.Pre.hasCoeGenerator
  FreeAlgebra.Pre.hasCoeSemiring FreeAlgebra.Pre.hasMul
  FreeAlgebra.Pre.hasAdd FreeAlgebra.Pre.hasZero FreeAlgebra.Pre.hasOne
  FreeAlgebra.Pre.hasSMul

variable {D : DifferentialData A} (s : SourceGeneratorImages D)

/-- Evaluate each generator as the corresponding iterate of translation. -/
def eval (s : SourceGeneratorImages D) : Expression → A
  | .of (.X i) => (D.translation ^ i) s.x
  | .of (.Y i) => (D.translation ^ i) s.y
  | .ofScalar r => r • D.one
  | .add a b => eval s a + eval s b
  | .mul a b => D.mul (eval s a) (eval s b)

@[simp] theorem eval_x (i : ℕ) : s.eval (SourcePresentation.x i) = (D.translation ^ i) s.x := rfl
@[simp] theorem eval_y (i : ℕ) : s.eval (SourcePresentation.y i) = (D.translation ^ i) s.y := rfl
@[simp] theorem eval_scalar (r : ℂ) : s.eval (.ofScalar r) = r • D.one := rfl
@[simp] theorem eval_zero : s.eval 0 = 0 := zero_smul _ _
@[simp] theorem eval_one : s.eval 1 = D.one := one_smul _ _
@[simp] theorem eval_add (a b : Expression) :
    s.eval (a + b) = s.eval a + s.eval b := rfl
@[simp] theorem eval_mul (a b : Expression) :
    s.eval (a * b) = D.mul (s.eval a) (s.eval b) := rfl

variable (hD : IsGradedDifferentialSuperalgebra A D)
include hD

@[simp] theorem eval_smul (r : ℂ) (a : Expression) :
    s.eval (r • a) = r • s.eval a := by
  change D.mul (r • D.one) (s.eval a) = _
  rw [map_smul, LinearMap.smul_apply, hD.one_mul]

theorem eval_algebra {a b : Expression} (h : FreeAlgebra.Rel ℂ Generator a b) :
    s.eval a = s.eval b := by
  induction h with
  | add_scalar => simp [add_smul]
  | mul_scalar => simp [smul_smul, hD.one_mul, mul_comm]
  | central_scalar => simp [hD.one_mul, hD.mul_one]
  | add_assoc => exact add_assoc _ _ _
  | add_comm => exact add_comm _ _
  | zero_add => simp
  | mul_assoc => exact hD.mul_assoc _ _ _
  | one_mul => simp [hD.one_mul]
  | mul_one => simp [hD.mul_one]
  | left_distrib => simp
  | right_distrib => simp
  | zero_mul => simp
  | mul_zero => simp
  | add_compat_left _ ih => simp [ih]
  | add_compat_right _ ih => simp [ih]
  | mul_compat_left _ ih => simp [ih]
  | mul_compat_right _ ih => simp [ih]

theorem eval_translate (a : Expression) :
    s.eval (translate a) = D.translation (s.eval a) := by
  induction a with
  | of g =>
    cases g <;> simp [translate, eval, pow_succ', Module.End.mul_apply, SourcePresentation.x, SourcePresentation.y]
  | ofScalar r => simp [translate, eval, hD.translation_one]
  | add a b ha hb => simp [translate, eval, ha, hb]
  | mul a b ha hb => simpa [translate, eval, ha, hb] using
      (hD.translation_mul (s.eval a) (s.eval b)).symm

theorem iterate_x_mem (i : ℕ) :
    (D.translation ^ i) s.x ∈ D.piece (2, 1, (i : ℤ) + 2) := by
  induction i with
  | zero => simpa using s.x_mem
  | succ i ih =>
    simpa [pow_succ', Module.End.mul_apply, Degree.translate,
      Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      using hD.translation_degree _ _ ih

theorem iterate_y_mem (i : ℕ) :
    (D.translation ^ i) s.y ∈ D.piece (3, 3, (i : ℤ) + 3) := by
  induction i with
  | zero => simpa using s.y_mem
  | succ i ih =>
    simpa [pow_succ', Module.End.mul_apply, Degree.translate,
      Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      using hD.translation_degree _ _ ih

/-- Evaluation respects every generator and closure rule of the relation. -/
theorem eval_relation {a b : Expression} (h : Relation a b) :
    s.eval a = s.eval b := by
  induction h with
  | algebra h => exact s.eval_algebra hD h
  | xx i j =>
    simpa [koszulSign] using hD.supercomm _ _ _ _
      (s.iterate_x_mem hD i) (s.iterate_x_mem hD j)
  | xy i j =>
    simpa [koszulSign] using hD.supercomm _ _ _ _
      (s.iterate_x_mem hD i) (s.iterate_y_mem hD j)
  | yy i j =>
    simpa [koszulSign, s.eval_smul hD] using hD.supercomm _ _ _ _
      (s.iterate_y_mem hD i) (s.iterate_y_mem hD j)
  | yy_self i =>
    have h := hD.supercomm _ _ _ _ (s.iterate_y_mem hD i) (s.iterate_y_mem hD i)
    have hn : D.mul ((D.translation ^ i) s.y) ((D.translation ^ i) s.y) =
        -D.mul ((D.translation ^ i) s.y) ((D.translation ^ i) s.y) := by
      simpa [koszulSign] using h
    have hz : (2 : ℂ) • D.mul ((D.translation ^ i) s.y) ((D.translation ^ i) s.y) = 0 := by
      rw [two_smul]
      exact (congrArg
        (fun z => z + D.mul ((D.translation ^ i) s.y) ((D.translation ^ i) s.y)) hn).trans
        (neg_add_cancel _)
    simpa using (smul_eq_zero.mp hz).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  | x0_sq => simpa using s.x_sq
  | x0_y0 => simpa using s.xy
  | x0_y1 => simpa using s.x_ty
  | y0_y1 => simpa using s.y_ty
  | translate _ ih => rw [s.eval_translate hD, s.eval_translate hD, ih]
  | add_left _ ih => simp [ih]
  | add_right _ ih => simp [ih]
  | mul_left _ ih => simp [ih]
  | mul_right _ ih => simp [ih]

/-- The explicit evaluation map on the presented source quotient. -/
def lift : Source →ₗ[ℂ] A where
  toFun := Quot.lift s.eval (fun _ _ h => s.eval_relation hD h)
  map_add' := by rintro ⟨a⟩ ⟨b⟩; rfl
  map_smul' := by rintro r ⟨a⟩; exact s.eval_smul hD r a

@[simp] theorem lift_mk (a : Expression) : s.lift hD (Source.mk a) = s.eval a := rfl

@[simp] theorem lift_X (i : ℕ) :
    s.lift hD (Source.X i) = (D.translation ^ i) s.x := rfl

@[simp] theorem lift_Y (i : ℕ) :
    s.lift hD (Source.Y i) = (D.translation ^ i) s.y := rfl

@[simp] theorem lift_one : s.lift hD 1 = D.one := one_smul _ _

theorem lift_mul (a b : Source) :
    s.lift hD (a * b) = D.mul (s.lift hD a) (s.lift hD b) := by
  induction a using Quot.inductionOn with | _ a =>
    induction b using Quot.inductionOn with | _ b => rfl

theorem lift_translation (a : Source) :
    s.lift hD (Source.translation a) = D.translation (s.lift hD a) := by
  induction a using Quot.inductionOn with | _ a => exact s.eval_translate hD a

theorem eval_homogeneous {d : Degree} {a : Expression} (h : Homogeneous d a) :
    s.eval a ∈ D.piece d := by
  induction h with
  | zero d => simp
  | scalar r => exact (D.piece 0).smul_mem r hD.one_degree
  | x i => exact s.iterate_x_mem hD i
  | y i => exact s.iterate_y_mem hD i
  | add _ _ ha hb => exact (D.piece _).add_mem ha hb
  | mul _ _ ha hb => exact hD.mul_degree _ _ _ _ ha hb

theorem lift_degree {d : Degree} {a : Source} (ha : a ∈ Source.piece d) :
    s.lift hD a ∈ D.piece d := by
  obtain ⟨e, he, rfl⟩ := ha
  exact s.eval_homogeneous hD he

/-- The constructed evaluation is uniquely determined by the two generator
images and preservation of multiplication, the unit, and translation. -/
theorem lift_unique (f : Source →ₗ[ℂ] A)
    (h1 : f 1 = D.one)
    (hmul : ∀ a b, f (a * b) = D.mul (f a) (f b))
    (hT : ∀ a, f (Source.translation a) = D.translation (f a))
    (hx : f (Source.X 0) = s.x) (hy : f (Source.Y 0) = s.y) :
    f = s.lift hD := by
  have hx' (i : ℕ) : f (Source.X i) = (D.translation ^ i) s.x := by
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      rw [← Source.translation_X i, hT, ih, pow_succ', Module.End.mul_apply]
  have hy' (i : ℕ) : f (Source.Y i) = (D.translation ^ i) s.y := by
    induction i with
    | zero => simpa using hy
    | succ i ih =>
      rw [← Source.translation_Y i, hT, ih, pow_succ', Module.End.mul_apply]
  ext a
  induction a using Source.inductionOn with
  | scalar r => simp [Algebra.algebraMap_eq_smul_one, h1]
  | hx i => exact hx' i
  | hy i => exact hy' i
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => rw [hmul, s.lift_mul hD, ha, hb]

end SourceGeneratorImages
end KhanSL2
