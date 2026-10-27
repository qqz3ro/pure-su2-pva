module

public import KhanSL2.Source

@[expose] public section

/-! Homogeneous differential generation by the two undifferentiated generators. -/

namespace KhanSL2.Source

open SourcePresentation

@[simp] theorem translation_pow_X (n i : ℕ) :
    (translation ^ n) (X i) = X (i + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, translation_X]
    simp only [Nat.add_succ]

@[simp] theorem translation_pow_Y (n i : ℕ) :
    (translation ^ n) (Y i) = Y (i + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, translation_Y]
    simp only [Nat.add_succ]

/-- Induction on a homogeneous source element, using only `X 0`, `Y 0`,
scalars, addition, multiplication and translation. -/
@[elab_as_elim] theorem homogeneous_induction
    {P : Degree → Source → Prop}
    (hzero : ∀ d, P d 0)
    (hscalar : ∀ r : ℂ, P 0 (algebraMap ℂ Source r))
    (hx : P (2, 1, 2) (X 0))
    (hy : P (3, 3, 3) (Y 0))
    (hadd : ∀ d a b, P d a → P d b → P d (a + b))
    (hmul : ∀ d e a b, P d a → P e b → P (d + e) (a * b))
    (htranslate : ∀ d a, P d a → P (d + (0, 0, 1)) (translation a))
    {d : Degree} {a : Source} (ha : a ∈ piece d) : P d a := by
  have hx' : ∀ i : ℕ, P (2, 1, (i : ℤ) + 2) (X i) := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
        using htranslate _ _ ih
  have hy' : ∀ i : ℕ, P (3, 3, (i : ℤ) + 3) (Y i) := by
    intro i
    induction i with
    | zero => simpa using hy
    | succ i ih =>
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
        using htranslate _ _ ih
  obtain ⟨e, he, rfl⟩ := ha
  induction he with
  | zero d => exact hzero d
  | scalar r => exact hscalar r
  | x i => exact hx' i
  | y i => exact hy' i
  | add _ _ ha hb => exact hadd _ _ _ ha hb
  | mul _ _ ha hb => exact hmul _ _ _ _ ha hb

end KhanSL2.Source
