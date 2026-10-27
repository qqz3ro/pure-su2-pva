module

public import KhanSL2.BGG.FirstMaps
public import KhanSL2.BGG.EnvelopingGrading

@[expose] public section

/-! The nonnegative polynomial-energy grading of the full current enveloping algebra. -/

noncomputable section

namespace KhanSL2.BGG

attribute [local instance 100] LieRing.ofAssociativeRing

def currentLieGenerator (i : ℕ × G) : Current := mode i.1 i.2

def currentUEGenerator (i : ℕ × G) : Enveloping :=
  UniversalEnvelopingAlgebra.ι ℂ (currentLieGenerator i)

def currentEnergy (i : ℕ × G) : ℤ := i.1

/-- Polynomial dilation extends to the actual full enveloping algebra. -/
def currentUEScale : Enveloping →ₐ[ℂ] Enveloping :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((UniversalEnvelopingAlgebra.ι ℂ).comp (currentScale 2))

@[simp] theorem currentUEScale_generator (i : ℕ × G) :
    currentUEScale (currentUEGenerator i) =
      ((2 : ℂ) ^ currentEnergy i) • currentUEGenerator i := by
  simp only [currentUEScale, currentUEGenerator,
    UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    currentLieGenerator, currentScale_mode, map_smul, currentEnergy, zpow_natCast]

@[simp] theorem currentUEScale_const (x : G) :
    currentUEScale (constGenerator x) = constGenerator x := by
  have h := currentUEScale_generator (0, x)
  simpa only [currentEnergy, Nat.cast_zero, zpow_zero, one_smul, currentUEGenerator,
    currentLieGenerator, constGenerator, constant_apply] using h

/-- Ordered homogeneous current words span the enveloping algebra. -/
theorem currentUE_generates : Algebra.adjoin ℂ (Set.range currentUEGenerator) = ⊤ := by
  have hLie : LieSubalgebra.lieSpan ℂ Current (Set.range currentLieGenerator) = ⊤ := by
    apply eq_top_of_all_modes
    intro n x
    exact LieSubalgebra.subset_lieSpan ⟨(n, x), rfl⟩
  have h := UE.adjoin_eq_top_of_lieSpan_eq_top ℂ Current (Set.range currentLieGenerator) hLie
  have hset : (UniversalEnvelopingAlgebra.ι ℂ) '' Set.range currentLieGenerator =
      Set.range currentUEGenerator := by
    ext a
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨currentLieGenerator i, ⟨i, rfl⟩, rfl⟩
  rw [hset] at h
  exact h

def currentUEPiece : ℤ → Submodule ℂ Enveloping :=
  WordGrading.piece currentUEGenerator currentEnergy

instance currentUEGradedAlgebra : GradedAlgebra currentUEPiece :=
  WordGrading.grading currentUEGenerator currentEnergy currentUEScale
    (fun n : ℤ => (2 : ℂ) ^ n) (by simp)
    (fun i j => zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0) i j)
    currentUEScale_generator energyEigenvalue_injective currentUE_generates

theorem currentWord_degree_nonneg (l : List (ℕ × G)) :
    0 ≤ WordGrading.degree currentEnergy l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
    exact add_nonneg (Int.natCast_nonneg i.1) ih

theorem currentUEPiece_negative (n : ℤ) (hn : n < 0) : currentUEPiece n = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  have h := currentWord_degree_nonneg l
  omega

theorem currentUEGenerator_mem (i : ℕ × G) :
    currentUEGenerator i ∈ currentUEPiece (currentEnergy i) :=
  WordGrading.generator_mem_piece currentUEGenerator currentEnergy i

theorem currentUEScale_word (l : List (ℕ × G)) :
    currentUEScale (WordGrading.word currentUEGenerator l) =
      ((2 : ℂ) ^ WordGrading.degree currentEnergy l) •
        WordGrading.word currentUEGenerator l :=
  WordGrading.scale_word currentUEGenerator currentEnergy currentUEScale
    (fun n : ℤ => (2 : ℂ) ^ n) (by simp)
    (fun i j => zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0) i j)
    currentUEScale_generator l

theorem currentUE_words_span :
    Submodule.span ℂ (Set.range (WordGrading.word currentUEGenerator)) = ⊤ := by
  apply top_unique
  rw [← WordGrading.iSup_piece_eq_top currentUEGenerator currentEnergy currentUE_generates]
  refine iSup_le fun n => Submodule.span_le.mpr ?_
  rintro a ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨l, rfl⟩

end KhanSL2.BGG
