module

public import KhanSL2.SourceAlgebra
public import KhanSL2.SourceParityProjections
public import Mathlib.Tactic.Module
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Supercommutation written without homogeneity hypotheses. -/

namespace KhanSL2.Source

private theorem mul_parity_split_homogeneous
    {d e : Degree} {a b : Source} (ha : a ∈ piece d) (hb : b ∈ piece e) :
    a * b = evenPart b * a + oddPart b * parity a := by
  rw [evenPart_apply, oddPart_apply, parity_of_mem ha, parity_of_mem hb,
    supercomm ha hb]
  have hd : d.1 % 2 = 0 ∨ d.1 % 2 = 1 := by omega
  have he : e.1 % 2 = 0 ∨ e.1 % 2 = 1 := by omega
  rcases hd with hd | hd <;> rcases he with he | he <;>
    norm_num [koszulSign, Int.mul_emod, hd, he, smul_mul_assoc, mul_smul_comm,
      add_mul, mul_add] <;>
    module

/-- The supercommutation law for arbitrary, possibly inhomogeneous elements. -/
theorem mul_parity_split (a b : Source) :
    a * b = evenPart b * a + oddPart b * parity a := by
  have ha : a ∈ ⨆ d, piece d := by rw [piece_iSup_eq_top]; trivial
  refine Submodule.iSup_induction piece
    (motive := fun a => a * b = evenPart b * a + oddPart b * parity a)
    ha ?_ ?_ ?_
  · intro d a ha
    have hb : b ∈ ⨆ e, piece e := by rw [piece_iSup_eq_top]; trivial
    refine Submodule.iSup_induction piece
      (motive := fun b => a * b = evenPart b * a + oddPart b * parity a)
      hb ?_ ?_ ?_
    · intro e b hb
      exact mul_parity_split_homogeneous ha hb
    · simp
    · intro b c hb hc
      simp only [map_add, mul_add, add_mul, hb, hc]
      abel
  · simp
  · intro a c ha hc
    simp only [map_add, mul_add, add_mul, ha, hc]
    abel

theorem mul_evenPart (a b : Source) : a * evenPart b = evenPart b * a := by
  simpa using mul_parity_split a (evenPart b)

theorem mul_oddPart (a b : Source) :
    a * oddPart b = oddPart b * parity a := by
  simpa using mul_parity_split a (oddPart b)

theorem parity_split_mul (a b : Source) :
    b * a = a * evenPart b + parity a * oddPart b := by
  rw [mul_evenPart, mul_oddPart, parity_parity, ← add_mul, evenPart_add_oddPart]

end KhanSL2.Source
