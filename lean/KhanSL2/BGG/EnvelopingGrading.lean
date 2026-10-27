module

public import KhanSL2.BGG.CurrentScaling
public import KhanSL2.BGG.WordGrading
public import KhanSL2.BGG.UEGeneration
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

/-!
# The connected positive energy grading of the positive-current enveloping algebra

This grading is constructed from weighted words and the dilation of currents.
It is independent of PBW and does not assume a decomposition or a grading axiom.
-/

noncomputable section

namespace KhanSL2.BGG

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev PositiveEnveloping := UniversalEnvelopingAlgebra ℂ positive

/-- Homogeneous Lie generators, indexed by positive mode and coefficient. -/
def positiveLieGenerator (i : ℕ × G) : positive := positiveMode i.1 i.2

/-- The corresponding generators of the positive-current enveloping algebra. -/
def positiveUEGenerator (i : ℕ × G) : PositiveEnveloping :=
  UniversalEnvelopingAlgebra.ι ℂ (positiveLieGenerator i)

/-- Each mode has its actual positive polynomial degree. -/
def positiveEnergy (i : ℕ × G) : ℤ := (i.1 : ℤ) + 1

/-- The enveloping-algebra dilation induced by substituting `2X` for `X`. -/
def positiveUEScale : PositiveEnveloping →ₐ[ℂ] PositiveEnveloping :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((UniversalEnvelopingAlgebra.ι ℂ).comp (positiveScale 2))

@[simp] theorem positiveUEScale_generator (i : ℕ × G) :
    positiveUEScale (positiveUEGenerator i) =
      ((2 : ℂ) ^ positiveEnergy i) • positiveUEGenerator i := by
  simp only [positiveUEScale, positiveUEGenerator,
    UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    positiveLieGenerator, positiveScale_mode, map_smul]
  rw [show positiveEnergy i = ((i.1 + 1 : ℕ) : ℤ) by simp [positiveEnergy], zpow_natCast]

theorem energyEigenvalue_injective : Function.Injective (fun n : ℤ => (2 : ℂ) ^ n) := by
  intro i j h
  have hr : (2 : ℝ) ^ i = (2 : ℝ) ^ j := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zpow, Complex.ofReal_ofNat] using h
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hr

/-- The energy-`n` piece consists of linear combinations of ordered mode words of total energy `n`. -/
def positiveUEPiece : ℤ → Submodule ℂ PositiveEnveloping :=
  WordGrading.piece positiveUEGenerator positiveEnergy

/-- The positive-mode family generates the enveloping algebra. -/
theorem positiveUE_generates :
    Algebra.adjoin ℂ (Set.range positiveUEGenerator) = ⊤ := by
  have hLie : LieSubalgebra.lieSpan ℂ positive (Set.range positiveLieGenerator) = ⊤ := by
    apply top_unique
    rw [← lieSpan_positiveMode_zero_eq_top]
    apply LieSubalgebra.lieSpan_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨(0, x), rfl⟩
  have h := UE.adjoin_eq_top_of_lieSpan_eq_top ℂ positive (Set.range positiveLieGenerator) hLie
  have hset : (UniversalEnvelopingAlgebra.ι ℂ) '' Set.range positiveLieGenerator =
      Set.range positiveUEGenerator := by
    ext a
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨positiveLieGenerator i, ⟨i, rfl⟩, rfl⟩
  rw [hset] at h
  exact h

/-- The actual connected energy grading on `U(z sl₂[z])`. -/
instance positiveUEGradedAlgebra : GradedAlgebra positiveUEPiece :=
  WordGrading.grading positiveUEGenerator positiveEnergy positiveUEScale
    (fun n : ℤ => (2 : ℂ) ^ n) (by simp)
    (fun i j => zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0) i j)
    positiveUEScale_generator energyEigenvalue_injective positiveUE_generates

/-- No element has negative energy. -/
theorem positiveUEPiece_negative (n : ℤ) (hn : n < 0) : positiveUEPiece n = ⊥ :=
  WordGrading.piece_eq_bot_of_neg positiveUEGenerator positiveEnergy
    (fun i => by dsimp [positiveEnergy]; omega) n hn

/-- The energy-zero subspace is exactly the scalar line. -/
theorem positiveUEPiece_zero :
    positiveUEPiece 0 = Submodule.span ℂ {(1 : PositiveEnveloping)} :=
  WordGrading.piece_zero_eq_span_one positiveUEGenerator positiveEnergy
    (fun i => by dsimp [positiveEnergy]; omega)

/-- A mode generator lies in the piece of its stated energy. -/
theorem positiveUEGenerator_mem (i : ℕ × G) :
    positiveUEGenerator i ∈ positiveUEPiece (positiveEnergy i) :=
  WordGrading.generator_mem_piece positiveUEGenerator positiveEnergy i

@[simp] theorem augmentation_positiveUEGenerator (i : ℕ × G) :
    UE.augmentation ℂ positive (positiveUEGenerator i) = 0 :=
  UE.augmentation_ι ℂ positive (positiveLieGenerator i)

/-- Augmentation vanishes in every nonzero energy, as required for the graded trivial module. -/
theorem positiveUEPiece_le_augmentation_kernel (n : ℤ) (hn : n ≠ 0) :
    positiveUEPiece n ≤ LinearMap.ker (UE.augmentation ℂ positive).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  change UE.augmentation ℂ positive (WordGrading.word positiveUEGenerator l) = 0
  cases l with
  | nil => exact (hn (by simpa using hl.symm)).elim
  | cons i l =>
    rw [WordGrading.word_cons, map_mul, augmentation_positiveUEGenerator, zero_mul]
/-- The scalar field identifies with the degree-zero algebra, not just its underlying subspace. -/
def positiveUEZeroEquiv :
    ℂ ≃ₐ[ℂ] (SetLike.GradeZero.subalgebra positiveUEPiece) := by
  let f : ℂ →ₐ[ℂ] (SetLike.GradeZero.subalgebra positiveUEPiece) := Algebra.ofId _ _
  apply AlgEquiv.ofBijective f
  constructor
  · intro a b h
    have hval := congrArg
      (fun q : SetLike.GradeZero.subalgebra positiveUEPiece => (q : PositiveEnveloping)) h
    have haug := congrArg (UE.augmentation ℂ positive) hval
    simpa only [f, Algebra.ofId_apply, Subalgebra.coe_algebraMap,
      UE.augmentation_algebraMap] using haug
  · intro q
    have hq : (q : PositiveEnveloping) ∈ positiveUEPiece 0 := q.property
    rw [positiveUEPiece_zero] at hq
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hq
    refine ⟨r, Subtype.ext ?_⟩
    change algebraMap ℂ PositiveEnveloping r = (q : PositiveEnveloping)
    simpa only [Algebra.smul_def, mul_one] using hr

/-- The semisimple degree-zero hypothesis required by minimal graded resolutions. -/
instance positiveUEZeroSemisimple : IsSemisimpleRing (positiveUEPiece 0) :=
  positiveUEZeroEquiv.toRingEquiv.isSemisimpleRing
end KhanSL2.BGG
