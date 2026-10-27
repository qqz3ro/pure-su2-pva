module

public import KhanSL2.StrongMacdonald.Operators
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc

@[expose] public section

/-!
# Jets of `𝔰𝔩₂` and the two unipotent moves

A jet is a triple of power series `P = (P₀, P₁, P₂)`, standing for `Σ_b P_b(z) ξ_b`. The
operator `jcross Γ P = Σ_{a,c} ε_abc Γ_a P_c` is the action of the loop element `Γ` on points
dual to the coordinate action `σ^b(-k) ↦ Σ_c ε_abc σ^c(-(k-m))`.

In the basis `e = ξ₀ + iξ₁`, `f = -ξ₀ + iξ₁`, `h = 2iξ₂` the `e`-coordinate of `P` is
`(P₀ - i P₁)/2` and the `f`-coordinate is `(-P₀ - i P₁)/2`.

* Move 1 (`f`-direction): `jcross (fDir γ)` is nilpotent of order 3, it moves the third
  component by `2iγ·a(P)` and keeps the `e`-coordinate.
* Move 2 (`ξ₂`-direction): `jcross (hDir δ)` kills the third component and multiplies the
  `e`-coordinate by `iδ`.
-/

noncomputable section
open scoped BigOperators
open Complex PowerSeries

namespace KhanSL2.StrongMacdonald

/-- A jet in `𝔰𝔩₂[[z]]`, by components in the basis `ξ`. -/
abbrev Jet := Fin 3 → PowerSeries ℂ

/-- The (dual) adjoint action of the loop element `Γ` on points. -/
def jcross (Γ P : Jet) : Jet := fun b => ∑ a, ∑ c, epsilon a b c • (Γ a * P c)

/-- Twice the `e`-coordinate: `P₀ - iP₁`. -/
def eTw (P : Jet) : PowerSeries ℂ := P 0 - C I * P 1

/-- Twice the `f`-coordinate: `-P₀ - iP₁`. -/
def fTw (P : Jet) : PowerSeries ℂ := -P 0 - C I * P 1

/-- The loop element `γ(z) f`, `f = -ξ₀ + iξ₁`. -/
def fDir (γ : PowerSeries ℂ) : Jet := ![-γ, C I * γ, 0]

/-- The loop element `δ(z) ξ₂`. -/
def hDir (δ : PowerSeries ℂ) : Jet := ![0, 0, δ]

theorem C_I_mul_C_I : (C I : PowerSeries ℂ) * C I = -1 := by
  rw [← map_mul, I_mul_I, map_neg, map_one]

/-! ## Linearity of the coordinates -/

theorem eTw_add (P Q : Jet) : eTw (P + Q) = eTw P + eTw Q := by
  simp only [eTw, Pi.add_apply]; ring

theorem eTw_smul (r : PowerSeries ℂ) (P : Jet) : eTw (r • P) = r * eTw P := by
  simp only [eTw, Pi.smul_apply, smul_eq_mul]; ring

theorem eTw_zero : eTw 0 = 0 := by simp [eTw]

/-- Recovering a point with vanishing third component from its coordinates. -/
theorem eq_of_two_eq_zero (P : Jet) (h : P 2 = 0) :
    C 2 * P 0 = eTw P - fTw P ∧ C 2 * P 1 = C I * (eTw P + fTw P) ∧ P 2 = 0 := by
  refine ⟨?_, ?_, h⟩
  · simp only [eTw, fTw, map_ofNat]; ring
  · simp only [eTw, fTw, map_ofNat]
    linear_combination (2 * P 1) * C_I_mul_C_I

/-! ## Move 1 -/

section Move1

variable (γ : PowerSeries ℂ) (P : Jet)

theorem jcross_fDir_zero : jcross (fDir γ) P 0 = -(C I * γ * P 2) := by
  simp [jcross, fDir, Fin.sum_univ_three, epsilon]

theorem jcross_fDir_one : jcross (fDir γ) P 1 = -(γ * P 2) := by
  simp [jcross, fDir, Fin.sum_univ_three, epsilon]

theorem jcross_fDir_two : jcross (fDir γ) P 2 = C I * γ * eTw P := by
  have h : jcross (fDir γ) P 2 = γ * P 1 + C I * γ * P 0 := by
    simp [jcross, fDir, Fin.sum_univ_three, epsilon]
  rw [h, eTw]
  linear_combination (γ * P 1) * C_I_mul_C_I

theorem eTw_jcross_fDir : eTw (jcross (fDir γ) P) = 0 := by
  rw [eTw, jcross_fDir_zero, jcross_fDir_one]; ring

theorem jcross_fDir_cube : jcross (fDir γ) (jcross (fDir γ) (jcross (fDir γ) P)) = 0 := by
  funext b
  fin_cases b
  · show jcross (fDir γ) _ 0 = 0
    rw [jcross_fDir_zero, jcross_fDir_two, eTw_jcross_fDir]; ring
  · show jcross (fDir γ) _ 1 = 0
    rw [jcross_fDir_one, jcross_fDir_two, eTw_jcross_fDir]; ring
  · show jcross (fDir γ) _ 2 = 0
    rw [jcross_fDir_two, eTw_jcross_fDir]; ring

/-- The point after move 1, `exp(jcross Γ) P` with `(jcross Γ)³ = 0`. -/
def move1 : Jet :=
  P + jcross (fDir γ) P + C (1 / 2 : ℂ) • jcross (fDir γ) (jcross (fDir γ) P)

theorem move1_two : move1 γ P 2 = P 2 + C I * γ * eTw P := by
  simp only [move1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jcross_fDir_two (P := jcross _ _),
    eTw_jcross_fDir, jcross_fDir_two]
  ring

theorem eTw_move1 : eTw (move1 γ P) = eTw P := by
  rw [move1, eTw_add, eTw_add, eTw_smul, eTw_jcross_fDir, eTw_jcross_fDir]; ring

end Move1

/-! ## Move 2 -/

section Move2

variable (δ : PowerSeries ℂ) (P : Jet)

theorem jcross_hDir_two : jcross (hDir δ) P 2 = 0 := by
  simp [jcross, hDir, Fin.sum_univ_three, epsilon]

theorem eTw_jcross_hDir : eTw (jcross (hDir δ) P) = C I * δ * eTw P := by
  have h0 : jcross (hDir δ) P 0 = δ * P 1 := by simp [jcross, hDir, Fin.sum_univ_three, epsilon]
  have h1 : jcross (hDir δ) P 1 = -(δ * P 0) := by simp [jcross, hDir, Fin.sum_univ_three, epsilon]
  rw [eTw, h0, h1, eTw]
  linear_combination (δ * P 1) * C_I_mul_C_I

theorem jcross_hDir_pow_two (n : ℕ) : ((jcross (hDir δ))^[n + 1] P) 2 = 0 := by
  rw [Function.iterate_succ_apply']
  exact jcross_hDir_two δ _

theorem eTw_jcross_hDir_pow (n : ℕ) :
    eTw ((jcross (hDir δ))^[n] P) = (C I * δ) ^ n * eTw P := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', eTw_jcross_hDir, ih]; ring

end Move2

end KhanSL2.StrongMacdonald
