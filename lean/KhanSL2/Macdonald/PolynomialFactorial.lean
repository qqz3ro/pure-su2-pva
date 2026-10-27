module

public import KhanSL2.Macdonald.Pairing

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Symmetric tensor normalization under one extra polynomial variable. -/
noncomputable section
namespace KhanSL2.Macdonald

theorem exponentFactorial_add_single (d : Exponent) (i : Mode) :
    exponentFactorial (d + Finsupp.single i 1) = (d i + 1) * exponentFactorial d := by
  classical
  have hd := Finsupp.mul_prod_erase' d i (fun (_ : Mode) (n : ℕ) => n.factorial) (by intros; rfl)
  have he := Finsupp.mul_prod_erase' (d + Finsupp.single i 1) i
    (fun (_ : Mode) (n : ℕ) => n.factorial) (by intros; rfl)
  have herase : (d + Finsupp.single i 1).erase i = d.erase i := by
    ext j
    by_cases h : j = i
    · subst j; simp
    · simp [Finsupp.erase_ne h, Finsupp.single_eq_of_ne h]
  unfold exponentFactorial
  rw [← he, herase]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  rw [mul_assoc, hd]

end KhanSL2.Macdonald
