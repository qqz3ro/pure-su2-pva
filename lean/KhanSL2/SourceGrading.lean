module

public import KhanSL2.Source
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.MonoidAlgebra.Module

@[expose] public section

/-!
# The internal grading of the presented source

The grading is proved using a coaction into the group algebra of the degree
group. Each generator is sent to itself placed in its declared degree. The
defining relations, including their differential closure, respect this map.
-/

namespace KhanSL2.Source

open SourcePresentation

attribute [local instance] FreeAlgebra.Pre.hasCoeGenerator
  FreeAlgebra.Pre.hasCoeSemiring FreeAlgebra.Pre.hasMul
  FreeAlgebra.Pre.hasAdd FreeAlgebra.Pre.hasZero FreeAlgebra.Pre.hasOne
  FreeAlgebra.Pre.hasSMul

noncomputable section

abbrev GradedEnvelope := AddMonoidAlgebra Source Degree

def envelopeTranslation : GradedEnvelope →ₗ[ℂ] GradedEnvelope :=
  (Finsupp.lsum ℂ fun d =>
    (AddMonoidAlgebra.lsingle (d + (0, 0, 1))).comp translation).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem envelopeTranslation_single (d : Degree) (a : Source) :
    envelopeTranslation (AddMonoidAlgebra.single d a) =
      AddMonoidAlgebra.single (d + (0, 0, 1)) (translation a) := by
  change (Finsupp.single d a).sum (fun e b =>
    AddMonoidAlgebra.single (e + (0, 0, 1)) (translation b)) = _
  exact Finsupp.sum_single_index (by simp)

theorem envelopeTranslation_mul (a b : GradedEnvelope) :
    envelopeTranslation (a * b) =
      envelopeTranslation a * b + a * envelopeTranslation b := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, ha, hb]; abel
  | single d a =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]; abel
    | single e b =>
      simp only [AddMonoidAlgebra.single_mul_single, envelopeTranslation_single,
        translation_mul]
      rw [AddMonoidAlgebra.single_add]
      congr 1
      · congr 1
        abel
      · congr 1
        abel

def generatorDegree : Generator → Degree
  | .X i => (2, 1, (i : ℤ) + 2)
  | .Y i => (3, 3, (i : ℤ) + 3)

def generatorValue : Generator → Source
  | .X i => X i
  | .Y i => Y i

def gradedEval : Expression → GradedEnvelope :=
  FreeAlgebra.liftFun ℂ Generator fun g =>
    AddMonoidAlgebra.single (generatorDegree g) (generatorValue g)

@[simp] theorem gradedEval_scalar (r : ℂ) :
    gradedEval (.ofScalar r) = AddMonoidAlgebra.single 0 (algebraMap ℂ Source r) := rfl

@[simp] theorem gradedEval_add (a b : Expression) :
    gradedEval (a + b) = gradedEval a + gradedEval b := rfl

@[simp] theorem gradedEval_mul (a b : Expression) :
    gradedEval (a * b) = gradedEval a * gradedEval b := rfl

@[simp] theorem gradedEval_zero : gradedEval 0 = 0 := by
  change AddMonoidAlgebra.single 0 (algebraMap ℂ Source 0) = 0
  simp

@[simp] theorem gradedEval_x (i : ℕ) :
    gradedEval (x i) = AddMonoidAlgebra.single (2, 1, (i : ℤ) + 2) (X i) := rfl

@[simp] theorem gradedEval_y (i : ℕ) :
    gradedEval (y i) = AddMonoidAlgebra.single (3, 3, (i : ℤ) + 3) (Y i) := rfl

theorem gradedEval_translate (a : Expression) :
    gradedEval (SourcePresentation.translate a) = envelopeTranslation (gradedEval a) := by
  induction a with
  | of g =>
    cases g <;>
      simp [SourcePresentation.translate, gradedEval, FreeAlgebra.liftFun,
        generatorDegree, generatorValue, envelopeTranslation_single, x, y,
        Nat.cast_add, Nat.cast_one, add_assoc]
  | ofScalar r =>
    simp only [SourcePresentation.translate, gradedEval_scalar, envelopeTranslation_single]
    have h : translation (algebraMap ℂ Source r) = 0 := rfl
    simp [h]
  | add a b ha hb =>
    change gradedEval (SourcePresentation.translate a + SourcePresentation.translate b) =
      envelopeTranslation (gradedEval a + gradedEval b)
    simp only [gradedEval_add, map_add, ha, hb]
  | mul a b ha hb =>
    change gradedEval (SourcePresentation.translate a * b + a * SourcePresentation.translate b) =
      envelopeTranslation (gradedEval a * gradedEval b)
    simp only [gradedEval_add, gradedEval_mul,
      envelopeTranslation_mul, ha, hb]

theorem gradedEval_algebra {a b : Expression} (h : FreeAlgebra.Rel ℂ Generator a b) :
    gradedEval a = gradedEval b := by
  let f : Generator → GradedEnvelope := fun g =>
    AddMonoidAlgebra.single (generatorDegree g) (generatorValue g)
  have hh := congrArg (FreeAlgebra.lift ℂ f) (Quot.sound h)
  unfold FreeAlgebra.lift at hh
  exact hh

theorem gradedEval_relation {a b : Expression} (h : Relation a b) :
    gradedEval a = gradedEval b := by
  induction h with
  | algebra h => exact gradedEval_algebra h
  | xx i j =>
    simp only [gradedEval_mul, gradedEval_x, AddMonoidAlgebra.single_mul_single]
    rw [X_mul_X, add_comm]
  | xy i j =>
    simp only [gradedEval_mul, gradedEval_x, gradedEval_y,
      AddMonoidAlgebra.single_mul_single]
    rw [X_mul_Y, add_comm]
  | yy i j =>
    change gradedEval (y i * y j) =
      gradedEval ((.ofScalar (-1)) * (y j * y i))
    simp only [gradedEval_mul, gradedEval_y, gradedEval_scalar,
      AddMonoidAlgebra.single_mul_single, zero_add, map_neg, map_one, neg_one_mul]
    rw [Y_mul_Y, add_comm]
  | yy_self i =>
    simp [gradedEval, FreeAlgebra.liftFun, y, generatorDegree, generatorValue,
      AddMonoidAlgebra.single_mul_single]
  | x0_sq =>
    simp [gradedEval, FreeAlgebra.liftFun, x, generatorDegree, generatorValue,
      AddMonoidAlgebra.single_mul_single]
  | x0_y0 =>
    simp [gradedEval, FreeAlgebra.liftFun, x, y, generatorDegree, generatorValue,
      AddMonoidAlgebra.single_mul_single]
  | x0_y1 =>
    simp [gradedEval, FreeAlgebra.liftFun, x, y, generatorDegree, generatorValue,
      AddMonoidAlgebra.single_mul_single]
  | y0_y1 =>
    simp [gradedEval, FreeAlgebra.liftFun, y, generatorDegree, generatorValue,
      AddMonoidAlgebra.single_mul_single]
  | translate _ ih => simp only [gradedEval_translate, ih]
  | add_left _ ih => simp only [gradedEval_add, ih]
  | add_right _ ih => simp only [gradedEval_add, ih]
  | mul_left _ ih => simp only [gradedEval_mul, ih]
  | mul_right _ ih => simp only [gradedEval_mul, ih]

/-- The degree coaction, recording the homogeneous components of a source element. -/
def coaction : Source →ₐ[ℂ] GradedEnvelope where
  toFun := Quot.lift gradedEval fun _ _ h => gradedEval_relation h
  map_one' := rfl
  map_zero' := by change AddMonoidAlgebra.single 0 (algebraMap ℂ Source 0) = 0; simp
  map_add' a b := by induction a using Quot.inductionOn; induction b using Quot.inductionOn; rfl
  map_mul' a b := by induction a using Quot.inductionOn; induction b using Quot.inductionOn; rfl
  commutes' _ := rfl

@[simp] theorem coaction_mk (a : Expression) : coaction (mk a) = gradedEval a := rfl

theorem gradedEval_homogeneous {d : Degree} {a : Expression} (h : Homogeneous d a) :
    gradedEval a = AddMonoidAlgebra.single d (mk a) := by
  induction h with
  | zero d => simp [gradedEval, FreeAlgebra.liftFun]
  | scalar r => rfl
  | x i => rfl
  | y i => rfl
  | add _ _ ha hb => simp only [gradedEval_add, ha, hb, mk_add, AddMonoidAlgebra.single_add]
  | mul _ _ ha hb =>
    simp only [gradedEval_mul, ha, hb, mk_mul, AddMonoidAlgebra.single_mul_single]

theorem coaction_of_mem {d : Degree} {a : Source} (h : a ∈ piece d) :
    coaction a = AddMonoidAlgebra.single d a := by
  obtain ⟨e, he, rfl⟩ := h
  exact gradedEval_homogeneous he

theorem coaction_directSum_coe (a : DirectSum Degree fun d => piece d) (d : Degree) :
    (coaction (DirectSum.coeLinearMap piece a)).coeff d = (a d : Source) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of e a =>
    rw [DirectSum.coeLinearMap_of, coaction_of_mem a.property]
    by_cases h : e = d
    · subst e
      simp
    · simp [Finsupp.single_eq_of_ne (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add a b ha hb =>
    simp only [map_add]
    change (coaction (DirectSum.coeLinearMap piece a)).coeff d +
      (coaction (DirectSum.coeLinearMap piece b)).coeff d = (a d : Source) + (b d : Source)
    rw [ha, hb]

theorem piece_iSup_mul_mem {a b : Source}
    (ha : a ∈ ⨆ d, piece d) (hb : b ∈ ⨆ d, piece d) :
    a * b ∈ ⨆ d, piece d := by
  refine Submodule.iSup_induction piece (motive := fun a => a * b ∈ ⨆ d, piece d) ha ?_ ?_ ?_
  · intro d a ha
    refine Submodule.iSup_induction piece (motive := fun b => a * b ∈ ⨆ d, piece d) hb ?_ ?_ ?_
    · intro e b hb
      exact Submodule.mem_iSup_of_mem (d + e) (mul_mem ha hb)
    · simp
    · intro b c hb hc
      simpa only [mul_add] using (⨆ d, piece d).add_mem hb hc
  · simp
  · intro a c ha hc
    simpa only [add_mul] using (⨆ d, piece d).add_mem ha hc

theorem piece_iSup_eq_top : (⨆ d, piece d) = ⊤ := by
  suffices h : ∀ a : Source, a ∈ ⨆ d, piece d from top_unique (fun a _ => h a)
  intro a
  induction a using inductionOn with
  | scalar r =>
    exact Submodule.mem_iSup_of_mem 0 ⟨.ofScalar r, .scalar r, rfl⟩
  | hx i => exact Submodule.mem_iSup_of_mem _ (X_mem i)
  | hy i => exact Submodule.mem_iSup_of_mem _ (Y_mem i)
  | add a b ha hb => exact (⨆ d, piece d).add_mem ha hb
  | mul a b ha hb => exact piece_iSup_mul_mem ha hb

/-- The declared homogeneous components form an actual internal direct sum. -/
theorem grading_internal : DirectSum.IsInternal piece := by
  change Function.Bijective (DirectSum.coeLinearMap piece)
  constructor
  · intro a b hab
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    rw [← coaction_directSum_coe a d, ← coaction_directSum_coe b d, hab]
  · apply LinearMap.range_eq_top.mp
    rw [DirectSum.range_coeLinearMap, piece_iSup_eq_top]

end
end KhanSL2.Source
