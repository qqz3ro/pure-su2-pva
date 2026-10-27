module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Positive energy gradings from homogeneous algebra generators and a scaling map. -/

noncomputable section

namespace KhanSL2.BGG.WordGrading

variable {R A I : Type*} [Field R] [Ring A] [Algebra R A]
  (x : I → A) (w : I → ℤ)

/-- An ordered word in the chosen algebra generators. -/
def word (l : List I) : A := (l.map x).prod

/-- Total energy of an ordered word. -/
def degree (l : List I) : ℤ := (l.map w).sum

@[simp] theorem word_nil : word x [] = 1 := rfl
@[simp] theorem word_cons (i : I) (l : List I) : word x (i :: l) = x i * word x l := rfl
@[simp] theorem word_append (l m : List I) : word x (l ++ m) = word x l * word x m := by
  simp [word]
@[simp] theorem degree_nil : degree w [] = 0 := rfl
@[simp] theorem degree_cons (i : I) (l : List I) : degree w (i :: l) = w i + degree w l := rfl
@[simp] theorem degree_append (l m : List I) : degree w (l ++ m) = degree w l + degree w m := by
  simp [degree]

/-- The homogeneous piece is the span of all words of the given energy. -/
def piece (n : ℤ) : Submodule R A :=
  Submodule.span R {a | ∃ l : List I, degree w l = n ∧ word x l = a}

theorem word_mem_piece (l : List I) : word x l ∈ piece (R := R) x w (degree w l) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

theorem generator_mem_piece (i : I) : x i ∈ piece (R := R) x w (w i) := by
  simpa using word_mem_piece (R := R) x w [i]

theorem one_mem_piece_zero : (1 : A) ∈ piece (R := R) x w 0 :=
  word_mem_piece x w []

theorem mul_mem_piece {i j : ℤ} {a b : A}
    (ha : a ∈ piece (R := R) x w i) (hb : b ∈ piece (R := R) x w j) :
    a * b ∈ piece (R := R) x w (i + j) := by
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨m, hm, rfl⟩ := hb
    exact Submodule.subset_span ⟨l ++ m, by simp [hl, hm], word_append x l m⟩
  | zero_left b hb => simp
  | zero_right a ha => simp
  | add_left a b c ha hb hc hac hbc =>
    simpa only [add_mul] using (piece (R := R) x w (i + j)).add_mem hac hbc
  | add_right a b c ha hb hc hab hac =>
    simpa only [mul_add] using (piece (R := R) x w (i + j)).add_mem hab hac
  | smul_left r a b ha hb hab =>
    simpa only [smul_mul_assoc] using (piece (R := R) x w (i + j)).smul_mem r hab
  | smul_right r a b ha hb hab =>
    simpa only [mul_smul_comm] using (piece (R := R) x w (i + j)).smul_mem r hab

instance : SetLike.GradedMonoid (piece (R := R) x w) where
  one_mem := one_mem_piece_zero x w
  mul_mem := fun {_i _j} {_a _b} ha hb => mul_mem_piece x w ha hb

private def allWords : Submodule R A := Submodule.span R (Set.range (word x))

private theorem allWords_mul {a b : A} (ha : a ∈ allWords (R := R) x)
    (hb : b ∈ allWords (R := R) x) : a * b ∈ allWords (R := R) x := by
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
    obtain ⟨l, rfl⟩ := ha
    obtain ⟨m, rfl⟩ := hb
    exact Submodule.subset_span ⟨l ++ m, word_append x l m⟩
  | zero_left b hb => simp
  | zero_right a ha => simp
  | add_left a b c ha hb hc hac hbc =>
    simpa only [add_mul] using (allWords (R := R) x).add_mem hac hbc
  | add_right a b c ha hb hc hab hac =>
    simpa only [mul_add] using (allWords (R := R) x).add_mem hab hac
  | smul_left r a b ha hb hab =>
    simpa only [smul_mul_assoc] using (allWords (R := R) x).smul_mem r hab
  | smul_right r a b ha hb hab =>
    simpa only [mul_smul_comm] using (allWords (R := R) x).smul_mem r hab

private def allWordsAlgebra : Subalgebra R A where
  carrier := allWords (R := R) x
  add_mem' := (allWords (R := R) x).add_mem
  zero_mem' := (allWords (R := R) x).zero_mem
  mul_mem' := allWords_mul x
  one_mem' := Submodule.subset_span ⟨[], rfl⟩
  algebraMap_mem' r := by
    change algebraMap R A r ∈ allWords (R := R) x
    have h : (1 : A) ∈ allWords (R := R) x := Submodule.subset_span ⟨[], rfl⟩
    simpa only [Algebra.smul_def, mul_one] using (allWords (R := R) x).smul_mem r h

/-- Algebra generation ensures that the homogeneous word pieces span the whole algebra. -/
theorem iSup_piece_eq_top (hgen : Algebra.adjoin R (Set.range x) = ⊤) :
    ⨆ n, piece (R := R) x w n = ⊤ := by
  have hA : allWordsAlgebra (R := R) x = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨[i], by simp⟩
  have hW : allWords (R := R) x = ⊤ :=
    congrArg Subalgebra.toSubmodule hA
  apply top_unique
  rw [← hW]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact le_iSup (piece (R := R) x w) (degree w l) (word_mem_piece x w l)

section Scaling

variable (scale : A →ₐ[R] A) (mu : ℤ → R)
  (mu_zero : mu 0 = 1) (mu_add : ∀ i j, mu (i + j) = mu i * mu j)
  (hscale : ∀ i, scale (x i) = mu (w i) • x i)

include mu_zero mu_add hscale in
theorem scale_word (l : List I) : scale (word x l) = mu (degree w l) • word x l := by
  induction l with
  | nil => simp [mu_zero]
  | cons i l ih =>
    simp only [word_cons, degree_cons, map_mul, hscale, ih, mu_add,
      smul_mul_smul_comm]

include mu_zero mu_add hscale in
theorem piece_le_eigenspace (n : ℤ) :
    piece (R := R) x w n ≤ Module.End.eigenspace scale.toLinearMap (mu n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (scale_word x w scale mu mu_zero mu_add hscale l)

include mu_zero mu_add hscale in
/-- A scaling map with distinct energy eigenvalues makes the word pieces independent. -/
theorem piece_independent (hmu : Function.Injective mu) :
    iSupIndep (piece (R := R) x w) :=
  ((Module.End.eigenspaces_iSupIndep scale.toLinearMap).comp hmu).mono
    (piece_le_eigenspace x w scale mu mu_zero mu_add hscale)

/-- The actual grading obtained from generation and a scaling map, rather than an assumed grading. -/
@[instance_reducible] def grading (hmu : Function.Injective mu) (hgen : Algebra.adjoin R (Set.range x) = ⊤) :
    GradedAlgebra (piece (R := R) x w) := by
  let h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (piece_independent x w scale mu mu_zero mu_add hscale hmu) (iSup_piece_eq_top x w hgen)
  exact { h.chooseDecomposition with
    one_mem := one_mem_piece_zero x w
    mul_mem := fun {_i _j} {_a _b} ha hb => mul_mem_piece x w ha hb }

end Scaling

section Positive

variable (hw : ∀ i, 0 < w i)

include hw in
theorem degree_nonneg (l : List I) : 0 ≤ degree w l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact add_nonneg (hw i).le ih

include hw in
theorem degree_eq_zero_iff (l : List I) : degree w l = 0 ↔ l = [] := by
  cases l with
  | nil => simp
  | cons i l =>
    have h := degree_nonneg w hw l
    have hi := hw i
    simp only [degree_cons, List.cons_ne_nil, iff_false]
    omega

include hw in
/-- Positive generators imply that the grading has no negative pieces. -/
theorem piece_eq_bot_of_neg (n : ℤ) (hn : n < 0) : piece (R := R) x w n = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  have h := degree_nonneg w hw l
  omega

include hw in
/-- Connectedness: the degree-zero piece consists exactly of scalar multiples of the unit. -/
theorem piece_zero_eq_span_one : piece (R := R) x w 0 = Submodule.span R {(1 : A)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    rw [(degree_eq_zero_iff w hw l).mp hl]
    exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    rintro a (rfl : a = 1)
    exact one_mem_piece_zero x w

end Positive

end KhanSL2.BGG.WordGrading
