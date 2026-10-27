module

public import KhanSL2.BGG.Terms
public import KhanSL2.BGG.InducedBaseMap
public import KhanSL2.BGG.CurrentUEGrading
public import Mathlib.Algebra.GradedMulAction

@[expose] public section

/-! The actual energy grading on each induced BGG term.
The quotient dilation is constructed from the balancing relations. Its distinct
energy eigenvalues prove the independence of the homogeneous word pieces. -/

noncomputable section

namespace KhanSL2.BGG

/-- Dilation by two on the induced quotient, including its prescribed energy shift. -/
def termDilation (p : ℕ) : Module.End ℂ (Term p) :=
  ((2 : ℂ) ^ (generatorEnergy p : ℤ)) •
    Induced.baseMap constGenerator (coefficientAction p) currentUEScale currentUEScale_const

theorem termDilation_smul (p : ℕ) (a : Enveloping) (q : Term p) :
    termDilation p (a • q) = currentUEScale a • termDilation p q := by
  change ((2 : ℂ) ^ (generatorEnergy p : ℤ)) •
    Induced.baseMap _ _ _ _ (a • q) = _
  rw [Induced.baseMap_smul]
  exact smul_comm _ _ _

@[simp] theorem termDilation_generator (p : ℕ) (v : Coefficient p) :
    termDilation p (termGenerator p v) =
      ((2 : ℂ) ^ (generatorEnergy p : ℤ)) • termGenerator p v := by
  simp only [termDilation, LinearMap.smul_apply, termGenerator, Induced.baseMap_of]

theorem termDilation_word (p : ℕ) (l : List (ℕ × G)) (v : Coefficient p) :
    termDilation p (WordGrading.word currentUEGenerator l • termGenerator p v) =
      ((2 : ℂ) ^ (WordGrading.degree currentEnergy l + generatorEnergy p)) •
        (WordGrading.word currentUEGenerator l • termGenerator p v) := by
  rw [termDilation_smul, currentUEScale_word, termDilation_generator]
  rw [smul_assoc, smul_comm (WordGrading.word currentUEGenerator l)
    ((2 : ℂ) ^ (generatorEnergy p : ℤ)), smul_smul]
  rw [zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]

/-- Energy `n` consists of sums of quotient words whose energy plus the generator shift is `n`. -/
def termPiece (p : ℕ) (n : ℤ) : Submodule ℂ (Term p) :=
  Submodule.span ℂ {q | ∃ (l : List (ℕ × G)) (v : Coefficient p),
    WordGrading.degree currentEnergy l + generatorEnergy p = n ∧
      WordGrading.word currentUEGenerator l • termGenerator p v = q}

theorem termWord_mem (p : ℕ) (l : List (ℕ × G)) (v : Coefficient p) :
    WordGrading.word currentUEGenerator l • termGenerator p v ∈
      termPiece p (WordGrading.degree currentEnergy l + generatorEnergy p) :=
  Submodule.subset_span ⟨l, v, rfl, rfl⟩

theorem termGenerator_mem (p : ℕ) (v : Coefficient p) :
    termGenerator p v ∈ termPiece p (generatorEnergy p) := by
  simpa only [WordGrading.word_nil, WordGrading.degree_nil, zero_add, one_smul] using
    termWord_mem p [] v

theorem termPiece_le_eigenspace (p : ℕ) (n : ℤ) :
    termPiece p n ≤ Module.End.eigenspace (termDilation p) ((2 : ℂ) ^ n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, v, rfl, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (termDilation_word p l v)

theorem termPiece_independent (p : ℕ) : iSupIndep (termPiece p) :=
  ((Module.End.eigenspaces_iSupIndep (termDilation p)).comp energyEigenvalue_injective).mono
    (termPiece_le_eigenspace p)

theorem iSup_termPiece_eq_top (p : ℕ) : (⨆ n, termPiece p n) = ⊤ := by
  apply top_unique
  intro q _
  refine Induced.induction_on constGenerator (coefficientAction p) q ?_ ?_
  · intro a v
    have ha : a ∈ Submodule.span ℂ (Set.range (WordGrading.word currentUEGenerator)) := by
      rw [currentUE_words_span]
      trivial
    change a • termGenerator p v ∈ ⨆ n, termPiece p n
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨l, rfl⟩ := hb
      exact le_iSup (termPiece p) _ (termWord_mem p l v)
    | zero => simp
    | add a b ha hb iha ihb =>
      simpa only [add_smul] using (⨆ n, termPiece p n).add_mem iha ihb
    | smul r a ha ih =>
      simpa only [smul_assoc] using (⨆ n, termPiece p n).smul_mem r ih
  · intro x y hx hy
    exact (⨆ n, termPiece p n).add_mem hx hy

/-- Every vector has a unique finite homogeneous decomposition. -/
theorem termPiece_isInternal (p : ℕ) : DirectSum.IsInternal (termPiece p) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (termPiece_independent p) (iSup_termPiece_eq_top p)

instance termDecomposition (p : ℕ) : DirectSum.Decomposition (termPiece p) :=
  (termPiece_isInternal p).chooseDecomposition

/-- The enveloping-algebra and module energies add under the actual action. -/
theorem smul_mem_termPiece (p : ℕ) {i j : ℤ} {a : Enveloping} {q : Term p}
    (ha : a ∈ currentUEPiece i) (hq : q ∈ termPiece p j) :
    a • q ∈ termPiece p (i + j) := by
  induction ha, hq using Submodule.span_induction₂ with
  | mem_mem a q ha hq =>
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨k, v, hk, rfl⟩ := hq
    exact Submodule.subset_span ⟨l ++ k, v,
      by rw [WordGrading.degree_append, add_assoc, hl, hk],
      by rw [WordGrading.word_append, mul_smul]⟩
  | zero_left q hq => simp
  | zero_right a ha => simp
  | add_left a b q ha hb hq ia ib =>
    simpa only [add_smul] using (termPiece p (i + j)).add_mem ia ib
  | add_right a q r ha hq hr iq ir =>
    simpa only [smul_add] using (termPiece p (i + j)).add_mem iq ir
  | smul_left r a q ha hq ih =>
    simpa only [smul_assoc] using (termPiece p (i + j)).smul_mem r ih
  | smul_right r a q ha hq ih =>
    simpa only [smul_comm a r q] using (termPiece p (i + j)).smul_mem r ih

instance termGradedSMul (p : ℕ) : SetLike.GradedSMul currentUEPiece (termPiece p) where
  smul_mem := fun {_i _j} {_a _q} ha hq => smul_mem_termPiece p ha hq

/-- Nothing lies below the prescribed generator energy. -/
theorem termPiece_below (p : ℕ) (n : ℤ) (hn : n < generatorEnergy p) :
    termPiece p n = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨l, v, hl, rfl⟩
  have h := currentWord_degree_nonneg l
  omega

/-- A current of polynomial degree `n` raises term energy by exactly `n`. -/
theorem mode_lie_mem_termPiece (p n : ℕ) (x : G) {j : ℤ} {q : Term p}
    (hq : q ∈ termPiece p j) : ⁅mode n x, q⁆ ∈ termPiece p ((n : ℤ) + j) := by
  rw [term_lie]
  exact smul_mem_termPiece p (currentUEGenerator_mem (n, x)) hq

theorem termHighest_mem (p : ℕ) : termHighest p ∈ termPiece p (generatorEnergy p) :=
  termGenerator_mem p _

/-- The balancing quotient sends a homogeneous tensor to its prescribed shifted degree. -/
theorem term_mk_tmul_mem (p : ℕ) {i : ℤ} {a : Enveloping}
    (ha : a ∈ currentUEPiece i) (v : Coefficient p) :
    Induced.mk constGenerator (coefficientAction p) (TensorProduct.tmul ℂ a v) ∈
      termPiece p (i + generatorEnergy p) := by
  rw [Induced.mk_tmul]
  exact smul_mem_termPiece p ha (termGenerator_mem p v)

/-- Every energy piece is stable under the actual constant sl₂ action. -/
theorem constant_lie_mem_termPiece (p : ℕ) (x : G) {j : ℤ} {q : Term p}
    (hq : q ∈ termPiece p j) : ⁅constant x, q⁆ ∈ termPiece p j := by
  simpa only [constant_apply, Nat.cast_zero, zero_add] using mode_lie_mem_termPiece p 0 x hq

end KhanSL2.BGG
