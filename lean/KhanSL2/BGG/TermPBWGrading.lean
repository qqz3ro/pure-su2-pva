module

public import KhanSL2.BGG.TermPBWAction

@[expose] public section

/-! Relative PBW preserves and reflects the actual shifted energy grading. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG

@[simp] theorem positiveFactor_generator (i : ℕ × G) :
    positiveFactor (positiveUEGenerator i) = currentUEGenerator (i.1 + 1, i.2) := by
  exact positiveFactor_iota (positiveLieGenerator i)

theorem positiveFactor_word (l : List (ℕ × G)) :
    positiveFactor (WordGrading.word positiveUEGenerator l) =
      WordGrading.word currentUEGenerator (l.map fun i => (i.1 + 1, i.2)) := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [WordGrading.word_cons, map_mul, positiveFactor_generator,
      List.map_cons, ih]

theorem positiveWord_degree (l : List (ℕ × G)) :
    WordGrading.degree currentEnergy (l.map fun i => (i.1 + 1, i.2)) =
      WordGrading.degree positiveEnergy l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [WordGrading.degree_cons, currentEnergy, positiveEnergy, ih]

/-- The actual positive-subalgebra inclusion preserves polynomial energy. -/
theorem positiveFactor_degree {n : ℤ} {u : PositiveEnveloping}
    (hu : u ∈ positiveUEPiece n) : positiveFactor u ∈ currentUEPiece n := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    rw [positiveFactor_word]
    exact Submodule.subset_span ⟨l.map (fun i => (i.1 + 1, i.2)),
      (positiveWord_degree l).trans hl, rfl⟩
  | zero => simp
  | add u v hu hv iu iv => simpa only [map_add] using (currentUEPiece n).add_mem iu iv
  | smul r u hu ih => simpa only [map_smul] using (currentUEPiece n).smul_mem r ih

/-- Intrinsic positive-word energy on the tensor module, with the BGG generator shift. -/
def positiveTensorPiece (p : ℕ) (n : ℤ) :
    Submodule ℂ (PositiveEnveloping ⊗[ℂ] Coefficient p) :=
  Submodule.span ℂ {t | ∃ (l : List (ℕ × G)) (v : Coefficient p),
    WordGrading.degree positiveEnergy l + generatorEnergy p = n ∧
      WordGrading.word positiveUEGenerator l ⊗ₜ[ℂ] v = t}

theorem positiveTensorWord_mem (p : ℕ) (l : List (ℕ × G)) (v : Coefficient p) :
    WordGrading.word positiveUEGenerator l ⊗ₜ[ℂ] v ∈
      positiveTensorPiece p (WordGrading.degree positiveEnergy l + generatorEnergy p) :=
  Submodule.subset_span ⟨l, v, rfl, rfl⟩

/-- Relative PBW sends each intrinsic tensor degree to the previously constructed quotient degree. -/
theorem positiveTensorEquivTerm_degree (p : ℕ) {n : ℤ}
    {t : PositiveEnveloping ⊗[ℂ] Coefficient p} (ht : t ∈ positiveTensorPiece p n) :
    positiveTensorEquivTerm p t ∈ termPiece p n := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨l, v, rfl, rfl⟩ := ht
    rw [positiveTensorEquivTerm_tmul]
    exact smul_mem_termPiece p
      (positiveFactor_degree (WordGrading.word_mem_piece positiveUEGenerator positiveEnergy l))
      (termGenerator_mem p v)
  | zero => simp
  | add t s ht hs it is => simpa only [map_add] using (termPiece p n).add_mem it is
  | smul r t ht ih => simpa only [map_smul] using (termPiece p n).smul_mem r ih

/-- Dilation on PBW coordinates is the standard enveloping dilation and coefficient shift. -/
def positiveTensorDilation (p : ℕ) :
    Module.End ℂ (PositiveEnveloping ⊗[ℂ] Coefficient p) :=
  ((2 : ℂ) ^ (generatorEnergy p : ℤ)) •
    TensorProduct.map positiveUEScale.toLinearMap (LinearMap.id : Coefficient p →ₗ[ℂ] Coefficient p)

theorem positiveTensorDilation_word (p : ℕ) (l : List (ℕ × G)) (v : Coefficient p) :
    positiveTensorDilation p (WordGrading.word positiveUEGenerator l ⊗ₜ[ℂ] v) =
      ((2 : ℂ) ^ (WordGrading.degree positiveEnergy l + generatorEnergy p)) •
        (WordGrading.word positiveUEGenerator l ⊗ₜ[ℂ] v) := by
  have hs := WordGrading.scale_word positiveUEGenerator positiveEnergy positiveUEScale
    (fun n : ℤ => (2 : ℂ) ^ n) (by simp)
    (fun i j => zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0) i j)
    positiveUEScale_generator l
  simp only [positiveTensorDilation, LinearMap.smul_apply, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, LinearMap.id_apply, hs, TensorProduct.smul_tmul', smul_smul]
  rw [mul_comm ((2 : ℂ) ^ (generatorEnergy p : ℤ)) ((2 : ℂ) ^ WordGrading.degree positiveEnergy l),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]

theorem positiveTensorPiece_le_eigenspace (p : ℕ) (n : ℤ) :
    positiveTensorPiece p n ≤ Module.End.eigenspace (positiveTensorDilation p) ((2 : ℂ) ^ n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, v, rfl, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (positiveTensorDilation_word p l v)

theorem positiveTensorPiece_independent (p : ℕ) : iSupIndep (positiveTensorPiece p) :=
  ((Module.End.eigenspaces_iSupIndep (positiveTensorDilation p)).comp
    energyEigenvalue_injective).mono (positiveTensorPiece_le_eigenspace p)

theorem positiveUE_words_span :
    Submodule.span ℂ (Set.range (WordGrading.word positiveUEGenerator)) = ⊤ := by
  apply top_unique
  rw [← WordGrading.iSup_piece_eq_top positiveUEGenerator positiveEnergy positiveUE_generates]
  refine iSup_le fun n => Submodule.span_le.mpr ?_
  rintro a ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨l, rfl⟩

theorem iSup_positiveTensorPiece_eq_top (p : ℕ) : (⨆ n, positiveTensorPiece p n) = ⊤ := by
  apply top_unique
  intro t ht
  clear ht
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    have hu : u ∈ Submodule.span ℂ (Set.range (WordGrading.word positiveUEGenerator)) := by
      rw [positiveUE_words_span]
      trivial
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨l, rfl⟩ := hu
      exact le_iSup (positiveTensorPiece p) _ (positiveTensorWord_mem p l v)
    | zero => simp
    | add u w hu hw iu iw =>
      simpa only [TensorProduct.add_tmul] using (⨆ n, positiveTensorPiece p n).add_mem iu iw
    | smul r u hu ih =>
      simpa only [TensorProduct.smul_tmul'] using (⨆ n, positiveTensorPiece p n).smul_mem r ih
  | add t s ht hs => exact (⨆ n, positiveTensorPiece p n).add_mem ht hs

/-- Intrinsic tensor energies form a direct-sum decomposition. -/
theorem positiveTensorPiece_isInternal (p : ℕ) : DirectSum.IsInternal (positiveTensorPiece p) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (positiveTensorPiece_independent p) (iSup_positiveTensorPiece_eq_top p)

instance positiveTensorDecomposition (p : ℕ) : DirectSum.Decomposition (positiveTensorPiece p) :=
  (positiveTensorPiece_isInternal p).chooseDecomposition

set_option backward.isDefEq.respectTransparency false in
/-- Relative PBW also reflects homogeneous energy, hence identifies the actual graded pieces. -/
theorem positiveTensorEquivTerm_mem_iff (p : ℕ) (n : ℤ)
    (t : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    positiveTensorEquivTerm p t ∈ termPiece p n ↔ t ∈ positiveTensorPiece p n := by
  classical
  let eA := LinearEquiv.ofBijective (DirectSum.coeLinearMap (positiveTensorPiece p))
    (positiveTensorPiece_isInternal p)
  let eB := LinearEquiv.ofBijective (DirectSum.coeLinearMap (termPiece p)) (termPiece_isInternal p)
  have hcomp (s : DirectSum ℤ fun i => positiveTensorPiece p i) :
      ((eB.symm (positiveTensorEquivTerm p (eA s))) n : Term p) =
        positiveTensorEquivTerm p (s n : PositiveEnveloping ⊗[ℂ] Coefficient p) := by
    induction s using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      by_cases hi : i = n
      · subst i
        simpa [eA, eB, LinearEquiv.ofBijective_apply] using congrArg (fun z : termPiece p n => (z : Term p))
          ((termPiece_isInternal p).ofBijective_coeLinearMap_of_mem
            (positiveTensorEquivTerm_degree p x.property))
      · simpa [eA, eB, LinearEquiv.ofBijective_apply,
          DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi)] using
          congrArg (fun z : termPiece p n => (z : Term p))
            ((termPiece_isInternal p).ofBijective_coeLinearMap_of_mem_ne hi
              (positiveTensorEquivTerm_degree p x.property))
    | add u v hu hv => simpa using congrArg₂ (· + ·) hu hv
  constructor
  · intro ht
    have heq : positiveTensorEquivTerm p ((eA.symm t n : positiveTensorPiece p n) :
        PositiveEnveloping ⊗[ℂ] Coefficient p) = positiveTensorEquivTerm p t := by
      rw [← hcomp (eA.symm t), eA.apply_symm_apply]
      exact congrArg (fun z : termPiece p n => (z : Term p))
        ((termPiece_isInternal p).ofBijective_coeLinearMap_of_mem ht)
    rw [← (positiveTensorEquivTerm p).injective heq]
    exact (eA.symm t n).property
  · exact positiveTensorEquivTerm_degree p

/-- A pure tensor has the energy of its positive enveloping factor plus the coefficient shift. -/
theorem positiveTensor_tmul_mem (p : ℕ) {i : ℤ} {u : PositiveEnveloping}
    (hu : u ∈ positiveUEPiece i) (v : Coefficient p) :
    u ⊗ₜ[ℂ] v ∈ positiveTensorPiece p (i + generatorEnergy p) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    exact Submodule.subset_span ⟨l, v, by rw [hl], rfl⟩
  | zero => simp
  | add u w hu hw iu iw =>
    simpa only [TensorProduct.add_tmul] using (positiveTensorPiece p _).add_mem iu iw
  | smul r u hu ih =>
    simpa only [TensorProduct.smul_tmul'] using (positiveTensorPiece p _).smul_mem r ih

/-- The positive enveloping action adds its energy to the intrinsic tensor energy. -/
theorem smul_mem_positiveTensorPiece (p : ℕ) {i j : ℤ} {u : PositiveEnveloping}
    {t : PositiveEnveloping ⊗[ℂ] Coefficient p} (hu : u ∈ positiveUEPiece i)
    (ht : t ∈ positiveTensorPiece p j) : u • t ∈ positiveTensorPiece p (i + j) := by
  apply (positiveTensorEquivTerm_mem_iff p (i + j) (u • t)).mp
  rw [positiveTensorEquivTerm_smul]
  exact smul_mem_termPiece p (positiveFactor_degree hu) (positiveTensorEquivTerm_degree p ht)

instance positiveTensorGradedSMul (p : ℕ) :
    SetLike.GradedSMul positiveUEPiece (positiveTensorPiece p) where
  smul_mem := fun {_i _j} {_u _t} hu ht => smul_mem_positiveTensorPiece p hu ht
end KhanSL2.BGG
