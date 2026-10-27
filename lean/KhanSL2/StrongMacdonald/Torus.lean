module

public import KhanSL2.StrongMacdonald.OrbitMoves
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# The torus of `SL₂` on the slice

The `e`-direction move `exp(jcross (eDir γ))`, `e = ξ₀ + iξ₁`, together with the `f`-direction
move `move1` generates the torus: for constant loop elements the four moves

`e(-μ⁻¹) · f(μ - 1) · e(1) · f(μ⁻¹ - 1)`

act on the coordinates `(u, v, w) = (eTw P, fTw P, P₂)` by `(u, v, w) ↦ (μ²u, μ⁻²v, w)`. Each of
them is `exp(opA 1 Γ)` with `Γ` constant, i.e. a combination of the loop-degree-0 operators
`Y a`. Choosing `μ² = A⁻¹` moves the slice point `A e + B f` to `e + A B f`.
-/

noncomputable section
open scoped BigOperators
open Complex PowerSeries

namespace KhanSL2.StrongMacdonald

theorem C_half_mul_two : (C (1 / 2 : ℂ) : PowerSeries ℂ) * 2 = 1 := by
  rw [← map_ofNat C 2, ← map_mul]; norm_num

/-! ## The `f`-coordinate and equality of jets -/

theorem fTw_add (P Q : Jet) : fTw (P + Q) = fTw P + fTw Q := by
  simp only [fTw, Pi.add_apply]; ring

theorem fTw_smul (r : PowerSeries ℂ) (P : Jet) : fTw (r • P) = r * fTw P := by
  simp only [fTw, Pi.smul_apply, smul_eq_mul]; ring

/-- A jet is determined by its `e`- and `f`-coordinates and its third component. -/
theorem jet_ext {P Q : Jet} (he : eTw P = eTw Q) (hf : fTw P = fTw Q) (h2 : P 2 = Q 2) :
    P = Q := by
  simp only [eTw, fTw] at he hf
  have h0 : P 0 = Q 0 := by
    linear_combination C (1 / 2 : ℂ) * (he - hf) + (Q 0 - P 0) * C_half_mul_two
  have h1 : P 1 = Q 1 := by
    linear_combination C (1 / 2 : ℂ) * C I * (he + hf) +
      (C (1 / 2 : ℂ) * 2 * (P 1 - Q 1)) * C_I_mul_C_I + (Q 1 - P 1) * C_half_mul_two
  funext b
  fin_cases b
  · exact h0
  · exact h1
  · exact h2

/-! ## The `f`-direction move on the coordinates -/

section MoveF

variable (γ : PowerSeries ℂ) (P : Jet)

theorem fTw_jcross_fDir : fTw (jcross (fDir γ) P) = 2 * C I * γ * P 2 := by
  rw [fTw, jcross_fDir_zero, jcross_fDir_one]; ring

theorem fTw_move1 : fTw (move1 γ P) = fTw P + 2 * γ * (C I * P 2) - γ ^ 2 * eTw P := by
  rw [move1, fTw_add, fTw_add, fTw_smul, fTw_jcross_fDir, fTw_jcross_fDir, jcross_fDir_two]
  linear_combination (C (1 / 2 : ℂ) * 2 * γ ^ 2 * eTw P) * C_I_mul_C_I -
    (γ ^ 2 * eTw P) * C_half_mul_two

theorem I_mul_move1_two : C I * move1 γ P 2 = C I * P 2 - γ * eTw P := by
  rw [move1_two]
  linear_combination (γ * eTw P) * C_I_mul_C_I

end MoveF

/-! ## The `e`-direction move -/

/-- The loop element `γ(z) e`, `e = ξ₀ + iξ₁`. -/
def eDir (γ : PowerSeries ℂ) : Jet := ![γ, C I * γ, 0]

section MoveE

variable (γ : PowerSeries ℂ) (P : Jet)

theorem jcross_eDir_zero : jcross (eDir γ) P 0 = -(C I * γ * P 2) := by
  simp [jcross, eDir, Fin.sum_univ_three, epsilon]

theorem jcross_eDir_one : jcross (eDir γ) P 1 = γ * P 2 := by
  simp [jcross, eDir, Fin.sum_univ_three, epsilon]

theorem jcross_eDir_two : jcross (eDir γ) P 2 = -(C I * γ * fTw P) := by
  simp [jcross, eDir, Fin.sum_univ_three, epsilon, fTw]
  linear_combination (-(γ * P 1)) * C_I_mul_C_I

theorem fTw_jcross_eDir : fTw (jcross (eDir γ) P) = 0 := by
  rw [fTw, jcross_eDir_zero, jcross_eDir_one]; ring

theorem eTw_jcross_eDir : eTw (jcross (eDir γ) P) = -(2 * C I * γ * P 2) := by
  rw [eTw, jcross_eDir_zero, jcross_eDir_one]; ring

theorem jcross_eDir_cube : jcross (eDir γ) (jcross (eDir γ) (jcross (eDir γ) P)) = 0 := by
  funext b
  fin_cases b
  · show jcross (eDir γ) _ 0 = 0
    rw [jcross_eDir_zero, jcross_eDir_two, fTw_jcross_eDir]; ring
  · show jcross (eDir γ) _ 1 = 0
    rw [jcross_eDir_one, jcross_eDir_two, fTw_jcross_eDir]; ring
  · show jcross (eDir γ) _ 2 = 0
    rw [jcross_eDir_two, fTw_jcross_eDir]; ring

/-- The point after the `e`-direction move, `exp(jcross Γ) P` with `(jcross Γ)³ = 0`. -/
def moveE : Jet :=
  P + jcross (eDir γ) P + C (1 / 2 : ℂ) • jcross (eDir γ) (jcross (eDir γ) P)

theorem moveE_two : moveE γ P 2 = P 2 - C I * γ * fTw P := by
  simp only [moveE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jcross_eDir_two (P := jcross _ _),
    fTw_jcross_eDir, jcross_eDir_two]
  ring

theorem fTw_moveE : fTw (moveE γ P) = fTw P := by
  rw [moveE, fTw_add, fTw_add, fTw_smul, fTw_jcross_eDir, fTw_jcross_eDir]; ring

theorem eTw_moveE : eTw (moveE γ P) = eTw P - 2 * γ * (C I * P 2) - γ ^ 2 * fTw P := by
  rw [moveE, eTw_add, eTw_add, eTw_smul, eTw_jcross_eDir, eTw_jcross_eDir, jcross_eDir_two]
  linear_combination (C (1 / 2 : ℂ) * 2 * γ ^ 2 * fTw P) * C_I_mul_C_I -
    (γ ^ 2 * fTw P) * C_half_mul_two

theorem I_mul_moveE_two : C I * moveE γ P 2 = C I * P 2 + γ * fTw P := by
  rw [moveE_two]
  linear_combination (-(γ * fTw P)) * C_I_mul_C_I

end MoveE

/-! ## The torus -/

/-- The composite `e(-μ⁻¹) · f(μ - 1) · e(1) · f(μ⁻¹ - 1)` of four constant moves. -/
def torus (μ : ℂ) (P : Jet) : Jet :=
  move1 (C (μ⁻¹ - 1)) (moveE (C 1) (move1 (C (μ - 1)) (moveE (C (-μ⁻¹)) P)))

section Torus

variable {μ : ℂ} (hμ : μ ≠ 0) (P : Jet)

include hμ

theorem C_mul_C_inv : (C μ : PowerSeries ℂ) * C μ⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ hμ, map_one]

theorem eTw_torus : eTw (torus μ P) = C (μ ^ 2) * eTw P := by
  simp only [torus, eTw_move1, eTw_moveE, fTw_move1, fTw_moveE, I_mul_move1_two,
    I_mul_moveE_two, map_neg, map_sub, map_one, map_pow]
  linear_combination (-(C μ * C μ⁻¹ * fTw P) + 2 * C μ * (C I * P 2) + fTw P) * C_mul_C_inv hμ

theorem fTw_torus : fTw (torus μ P) = C (μ⁻¹ ^ 2) * fTw P := by
  simp only [torus, eTw_move1, eTw_moveE, fTw_move1, fTw_moveE, I_mul_move1_two,
    I_mul_moveE_two, map_neg, map_sub, map_one, map_pow]
  linear_combination (C μ * C μ⁻¹ ^ 3 * fTw P - 2 * C μ * C μ⁻¹ ^ 2 * (C I * P 2) -
    C μ * C μ⁻¹ * eTw P - 3 * C μ⁻¹ ^ 2 * fTw P + 4 * C μ⁻¹ * (C I * P 2) + eTw P) *
      C_mul_C_inv hμ

theorem torus_two : torus μ P 2 = P 2 := by
  have h : C I * torus μ P 2 = C I * P 2 := by
    simp only [torus, eTw_move1, eTw_moveE, fTw_move1, fTw_moveE, I_mul_move1_two,
      I_mul_moveE_two, map_neg, map_sub, map_one]
    linear_combination (C μ * C μ⁻¹ ^ 2 * fTw P - 2 * C μ * C μ⁻¹ * (C I * P 2) -
      C μ * eTw P - 2 * C μ⁻¹ * fTw P + 2 * (C I * P 2)) * C_mul_C_inv hμ
  linear_combination (-C I) * h + (torus μ P 2 - P 2) * C_I_mul_C_I

end Torus

/-! ## Constant moves are realized by the loop-degree-0 operators -/

theorem coeff_C_of_one_le {s : ℂ} {m : ℕ} (hm : 1 ≤ m) : coeff m (C s : PowerSeries ℂ) = 0 := by
  rw [coeff_C, if_neg (by omega)]

theorem trunc_fDir_C (s : ℂ) : Trunc 1 (fDir (C s)) := by
  intro a m hm
  fin_cases a <;> simp [fDir, coeff_C_mul, coeff_C_of_one_le hm]

theorem trunc_eDir_C (s : ℂ) : Trunc 1 (eDir (C s)) := by
  intro a m hm
  fin_cases a <;> simp [eDir, coeff_C_mul, coeff_C_of_one_le hm]

theorem locNil_fDir_C (s : ℂ) : LocNil (opA 1 (fDir (C s))) :=
  locNil_opA (trunc_fDir_C s) fun _ _ =>
    ⟨3, fun P => by rw [iterate_three, jcross_fDir_cube]; rfl⟩

theorem locNil_eDir_C (s : ℂ) : LocNil (opA 1 (eDir (C s))) :=
  locNil_opA (trunc_eDir_C s) fun _ _ =>
    ⟨3, fun P => by rw [iterate_three, jcross_eDir_cube]; rfl⟩

theorem toJet_movePtF (s : ℂ) (pt : SMode → ℂ) :
    toJet (movePt 1 (fDir (C s)) (locNil_fDir_C s) pt) = move1 (C s) (toJet pt) := by
  funext b
  ext k
  rw [coeff_toJet, movePt_apply (trunc_fDir_C s) _ pt k b (K := 3)
    (opA_pow_sigOf_eq_zero (trunc_fDir_C s) 3 k b fun P => by
      rw [iterate_three, jcross_fDir_cube]; rfl)]
  simp [Finset.sum_range_succ, move1, Nat.factorial, coeff_C_mul]

theorem toJet_movePtE (s : ℂ) (pt : SMode → ℂ) :
    toJet (movePt 1 (eDir (C s)) (locNil_eDir_C s) pt) = moveE (C s) (toJet pt) := by
  funext b
  ext k
  rw [coeff_toJet, movePt_apply (trunc_eDir_C s) _ pt k b (K := 3)
    (opA_pow_sigOf_eq_zero (trunc_eDir_C s) 3 k b fun P => by
      rw [iterate_three, jcross_eDir_cube]; rfl)]
  simp [Finset.sum_range_succ, moveE, Nat.factorial, coeff_C_mul]

section Reach

variable {x : W} (hY : ∀ c, Y c x = 0) (hX : ∀ i a, X i a x = 0)

include hY hX

theorem reach_moveF (s : ℂ) (P : Jet) : Reach x (ofJet P) (ofJet (move1 (C s) P)) := by
  have e : movePt 1 (fDir (C s)) (locNil_fDir_C s) (ofJet P) = ofJet (move1 (C s) P) := by
    have := congrArg ofJet (toJet_movePtF s (ofJet P))
    rwa [ofJet_toJet, toJet_ofJet] at this
  have h := evalAt_eq_move hY hX (locNil_fDir_C s) (ofJet P)
  rw [e] at h
  exact h

theorem reach_moveE (s : ℂ) (P : Jet) : Reach x (ofJet P) (ofJet (moveE (C s) P)) := by
  have e : movePt 1 (eDir (C s)) (locNil_eDir_C s) (ofJet P) = ofJet (moveE (C s) P) := by
    have := congrArg ofJet (toJet_movePtE s (ofJet P))
    rwa [ofJet_toJet, toJet_ofJet] at this
  have h := evalAt_eq_move hY hX (locNil_eDir_C s) (ofJet P)
  rw [e] at h
  exact h

theorem reach_torus (μ : ℂ) (P : Jet) : Reach x (ofJet P) (ofJet (torus μ P)) :=
  (((reach_moveE hY hX _ P).trans (reach_moveF hY hX _ _)).trans
    (reach_moveE hY hX _ _)).trans (reach_moveF hY hX _ _)

end Reach

/-! ## Normalizing the slice coefficient -/

/-- The jet of the slice point `A e + B(z) f`. -/
def sliceJet (A : ℂ) (B : PowerSeries ℂ) : Jet :=
  ![C (1 / 2 : ℂ) * (C A - B), C (1 / 2 : ℂ) * (C I * (C A + B)), 0]

theorem slicePt_eq (A : ℂ) (B : PowerSeries ℂ) : slicePt A B = ofJet (sliceJet A B) := rfl

theorem eTw_sliceJet (A : ℂ) (B : PowerSeries ℂ) : eTw (sliceJet A B) = C A := by
  simp only [eTw, sliceJet, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-(C (1 / 2 : ℂ) * (C A + B))) * C_I_mul_C_I + C A * C_half_mul_two

theorem fTw_sliceJet (A : ℂ) (B : PowerSeries ℂ) : fTw (sliceJet A B) = B := by
  simp only [fTw, sliceJet, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-(C (1 / 2 : ℂ) * (C A + B))) * C_I_mul_C_I + B * C_half_mul_two

theorem sliceJet_two (A : ℂ) (B : PowerSeries ℂ) : sliceJet A B 2 = 0 := rfl

/-- **The torus normalizes the slice.** The slice point `A e + B f`, `A ≠ 0`, is moved by the
torus of `SL₂` (four unipotent moves at loop degree 0) to `e + A B f`. -/
theorem reach_slicePt_one_mul {x : W} (hY : ∀ c, Y c x = 0) (hX : ∀ i a, X i a x = 0)
    (A : ℂ) (hA : A ≠ 0) (B : PowerSeries ℂ) :
    Reach x (slicePt A B) (slicePt 1 (C A * B)) := by
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq A⁻¹ (by norm_num : 0 < 2)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, inv_eq_zero] at hμ
    exact hA hμ
  have key : sliceJet 1 (C A * B) = torus μ (sliceJet A B) := by
    apply jet_ext
    · rw [eTw_sliceJet, eTw_torus hμ0, eTw_sliceJet, ← map_mul, hμ, inv_mul_cancel₀ hA]
    · rw [fTw_sliceJet, fTw_torus hμ0, fTw_sliceJet, inv_pow, hμ, inv_inv]
    · rw [torus_two hμ0, sliceJet_two, sliceJet_two]
  rw [slicePt_eq, slicePt_eq, key]
  exact reach_torus hY hX μ _

theorem reach_slice_one {x : W} (hY : ∀ c, Y c x = 0) (hX : ∀ i a, X i a x = 0)
    (A : ℂ) (hA : A ≠ 0) (B : PowerSeries ℂ) :
    ∃ B' : PowerSeries ℂ, Reach x (slicePt A B) (slicePt 1 B') :=
  ⟨C A * B, reach_slicePt_one_mul hY hX A hA B⟩

end KhanSL2.StrongMacdonald
