module

public import KhanSL2.StrongMacdonald.Orbit

@[expose] public section

/-!
# Moving a point to the slice

Every point whose `e`-coordinate has nonzero constant term is moved, on the modes `< N`, to the
slice `A e + B(z) f` by one `f`-direction move followed by `ξ₂`-direction moves at loop degrees
`1, …, N-1`. Hence an element killed by all loop operators and vanishing on the slice vanishes.
-/

noncomputable section
open scoped BigOperators
open Complex PowerSeries

namespace KhanSL2.StrongMacdonald

theorem coeff_coe_trunc (N m : ℕ) (f : PowerSeries ℂ) :
    coeff m (trunc N f : PowerSeries ℂ) = if m < N then coeff m f else 0 := by
  rw [Polynomial.coeff_coe, coeff_trunc]

/-! ## Move 1: kill the `ξ₂`-component -/

section Move1

variable (N : ℕ) (pt : SMode → ℂ)

/-- The loop element `γ f` with `γ = i·P₂/(P₀ - iP₁)`, truncated below `N`. -/
def gam1 : PowerSeries ℂ := (trunc N (C I * toJet pt 2 * (eTw (toJet pt))⁻¹) : PowerSeries ℂ)

theorem trunc_gam1 : Trunc N (fDir (gam1 N pt)) := by
  intro a m hm
  have h : coeff m (gam1 N pt) = 0 := by
    rw [gam1, coeff_coe_trunc, if_neg (by omega)]
  fin_cases a <;> simp [fDir, coeff_C_mul, h]

theorem iterate_three (f : Jet → Jet) (P : Jet) : f^[3] P = f (f (f P)) := rfl

theorem locNil_gam1 : LocNil (opA N (fDir (gam1 N pt))) :=
  locNil_opA (trunc_gam1 N pt) fun _ _ =>
    ⟨3, fun P => by rw [iterate_three, jcross_fDir_cube]; rfl⟩

theorem toJet_movePt1 :
    toJet (movePt N (fDir (gam1 N pt)) (locNil_gam1 N pt) pt) = move1 (gam1 N pt) (toJet pt) := by
  funext b
  ext k
  rw [coeff_toJet, movePt_apply (trunc_gam1 N pt) _ pt k b (K := 3)
    (opA_pow_sigOf_eq_zero (trunc_gam1 N pt) 3 k b fun P => by
      rw [iterate_three, jcross_fDir_cube]; rfl)]
  simp [Finset.sum_range_succ, move1, Nat.factorial, coeff_C_mul]

theorem movePt1_two (h0 : eCo pt 0 ≠ 0) {k : ℕ} (hk : k < N) :
    movePt N (fDir (gam1 N pt)) (locNil_gam1 N pt) pt ⟨k, 2⟩ = 0 := by
  have h1 := congrArg (coeff k) (congrFun (toJet_movePt1 N pt) 2)
  rw [coeff_toJet] at h1
  rw [h1, move1_two, map_add, mul_assoc, coeff_C_mul, gam1, coeff_trunc_mul hk]
  have he : constantCoeff (eTw (toJet pt)) ≠ 0 := by
    rwa [← coeff_zero_eq_constantCoeff_apply, ← eCo_eq]
  have hγ : C I * (C I * toJet pt 2 * (eTw (toJet pt))⁻¹ * eTw (toJet pt)) = -toJet pt 2 := by
    rw [mul_assoc (C I * toJet pt 2), PowerSeries.inv_mul_cancel _ he, mul_one, ← mul_assoc,
      C_I_mul_C_I, neg_one_mul]
  rw [← coeff_C_mul, hγ, map_neg, add_neg_cancel]

theorem eCo_movePt1 (j : ℕ) :
    eCo (movePt N (fDir (gam1 N pt)) (locNil_gam1 N pt) pt) j = eCo pt j := by
  rw [eCo_eq, eCo_eq, toJet_movePt1, eTw_move1]

end Move1

/-! ## Move 2: normalize one coefficient of the `e`-coordinate -/

section Move2

variable (N m : ℕ) (t : ℂ)

/-- The loop element `t z^m ξ₂`. -/
def gam2 : PowerSeries ℂ := C t * PowerSeries.X ^ m

theorem coeff_gam2 (j : ℕ) : coeff j (gam2 m t) = if j = m then t else 0 := by
  rw [gam2, coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

theorem trunc_gam2 (hm : m < N) : Trunc N (hDir (gam2 m t)) := by
  intro a j hj
  have h : coeff j (gam2 m t) = 0 := by rw [coeff_gam2, if_neg (by omega)]
  fin_cases a <;> simp [hDir, h]

theorem jcross_hDir_apply (δ : PowerSeries ℂ) (P : Jet) :
    jcross (hDir δ) P = ![δ * P 1, -(δ * P 0), 0] := by
  funext b
  fin_cases b <;> simp [jcross, hDir, Fin.sum_univ_three, epsilon]

theorem iterate_hDir_factor (δ : PowerSeries ℂ) (n : ℕ) (P : Jet) (b : Fin 3) :
    ∃ Q, (jcross (hDir δ))^[n] P b = δ ^ n * Q := by
  induction n generalizing b with
  | zero => exact ⟨P b, by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', jcross_hDir_apply]
    fin_cases b
    · obtain ⟨Q, hQ⟩ := ih 1; exact ⟨Q, by simp [hQ, pow_succ]; ring⟩
    · obtain ⟨Q, hQ⟩ := ih 0; exact ⟨-Q, by simp [hQ, pow_succ]; ring⟩
    · exact ⟨0, by simp⟩

theorem coeff_gam2_pow_mul (n j : ℕ) (Q : PowerSeries ℂ) :
    coeff j (gam2 m t ^ n * Q) = if m * n ≤ j then t ^ n * coeff (j - m * n) Q else 0 := by
  rw [gam2, mul_pow, ← map_pow, mul_assoc, coeff_C_mul, ← pow_mul, coeff_X_pow_mul']
  split_ifs <;> simp

theorem locNil_gam2 (hm1 : 1 ≤ m) (hm : m < N) : LocNil (opA N (hDir (gam2 m t))) :=
  locNil_opA (trunc_gam2 N m t hm) fun k b => ⟨k + 1, fun P => by
    obtain ⟨Q, hQ⟩ := iterate_hDir_factor (gam2 m t) (k + 1) P b
    rw [hQ, coeff_gam2_pow_mul, if_neg (by nlinarith)]⟩

theorem opA_gam2_pow_eq_zero (hm1 : 1 ≤ m) (hm : m < N) (k : ℕ) (b : Fin 3) :
    (opA N (hDir (gam2 m t)) ^ (k + 1)) (sigOf k b) = 0 :=
  opA_pow_sigOf_eq_zero (trunc_gam2 N m t hm) (k + 1) k b fun P => by
    obtain ⟨Q, hQ⟩ := iterate_hDir_factor (gam2 m t) (k + 1) P b
    rw [hQ, coeff_gam2_pow_mul, if_neg (by nlinarith)]

variable (hm1 : 1 ≤ m) (hm : m < N) (pt : SMode → ℂ)

theorem movePt2_two (k : ℕ) :
    movePt N (hDir (gam2 m t)) (locNil_gam2 N m t hm1 hm) pt ⟨k, 2⟩ = pt ⟨k, 2⟩ := by
  rw [movePt_apply (trunc_gam2 N m t hm) _ pt k 2 (opA_gam2_pow_eq_zero N m t hm1 hm k 2),
    Finset.sum_range_succ']
  simp [jcross_hDir_pow_two, coeff_toJet]

theorem eCo_movePt2_eq (j : ℕ) :
    eCo (movePt N (hDir (gam2 m t)) (locNil_gam2 N m t hm1 hm) pt) j =
      ∑ n ∈ Finset.range (j + 1), ((n.factorial : ℂ)⁻¹) *
        coeff j ((C I * gam2 m t) ^ n * eTw (toJet pt)) := by
  rw [eCo, movePt_apply (trunc_gam2 N m t hm) _ pt j 0 (opA_gam2_pow_eq_zero N m t hm1 hm j 0),
    movePt_apply (trunc_gam2 N m t hm) _ pt j 1 (opA_gam2_pow_eq_zero N m t hm1 hm j 1),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← eTw_jcross_hDir_pow, eTw, map_sub, coeff_C_mul]
  ring

theorem coeff_CI_gam2_pow_mul (n j : ℕ) (Q : PowerSeries ℂ) :
    coeff j ((C I * gam2 m t) ^ n * Q) =
      if m * n ≤ j then (I * t) ^ n * coeff (j - m * n) Q else 0 := by
  rw [mul_pow, ← map_pow, mul_assoc, coeff_C_mul, coeff_gam2_pow_mul]
  split_ifs <;> ring

theorem eCo_movePt2_lt {j : ℕ} (hj : j < m) :
    eCo (movePt N (hDir (gam2 m t)) (locNil_gam2 N m t hm1 hm) pt) j = eCo pt j := by
  rw [eCo_movePt2_eq N m t hm1 hm pt, Finset.sum_range_succ', Finset.sum_eq_zero, zero_add,
    eCo_eq]
  · simp
  · intro n _
    rw [coeff_CI_gam2_pow_mul, if_neg (by nlinarith), mul_zero]

theorem eCo_movePt2_self :
    eCo (movePt N (hDir (gam2 m t)) (locNil_gam2 N m t hm1 hm) pt) m =
      eCo pt m + I * t * eCo pt 0 := by
  rw [eCo_movePt2_eq N m t hm1 hm pt]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, zero_add, eCo_eq,
    eCo_eq]
  · simp only [coeff_CI_gam2_pow_mul]; simp; ring
  · intro n _
    rw [coeff_CI_gam2_pow_mul, if_neg (by nlinarith), mul_zero]

end Move2

/-! ## Reaching the slice -/

/-- The slice point `A e + B(z) f`. -/
def slicePt (A : ℂ) (B : PowerSeries ℂ) : SMode → ℂ :=
  ofJet ![C (1 / 2 : ℂ) * (C A - B), C (1 / 2 : ℂ) * (C I * (C A + B)), 0]

/-- Evaluation at `pt` is an odd substitution of evaluation at `pt'`. -/
def Reach (x : W) (pt pt' : SMode → ℂ) : Prop :=
  ∃ Θ : Ext →ₐ[ℂ] Ext, evalAt pt x = Θ (evalAt pt' x)

theorem Reach.trans {x : W} {p q r : SMode → ℂ} (h1 : Reach x p q) (h2 : Reach x q r) :
    Reach x p r := by
  obtain ⟨Θ₁, h1⟩ := h1
  obtain ⟨Θ₂, h2⟩ := h2
  exact ⟨Θ₁.comp Θ₂, by rw [h1, h2, AlgHom.comp_apply]⟩

/-- The normalization reached after the moves at loop degrees `< m`. -/
def Normal (N m : ℕ) (A : ℂ) (pt : SMode → ℂ) : Prop :=
  (∀ k < N, pt ⟨k, 2⟩ = 0) ∧ (∀ j, 1 ≤ j → j < m → eCo pt j = 0) ∧ eCo pt 0 = A

theorem exists_normal {x : W} (hY : ∀ c, Y c x = 0) (hX : ∀ i a, X i a x = 0) {N : ℕ}
    (pt : SMode → ℂ) (h0 : eCo pt 0 ≠ 0) :
    ∀ m, 1 ≤ m → m ≤ N → ∃ pt', Reach x pt pt' ∧ Normal N m (eCo pt 0) pt' := by
  intro m hm1 hmN
  induction m, hm1 using Nat.le_induction with
  | base =>
    refine ⟨movePt N (fDir (gam1 N pt)) (locNil_gam1 N pt) pt, evalAt_eq_move hY hX _ pt,
      fun k hk => movePt1_two N pt h0 hk, fun j hj1 hj => by omega, eCo_movePt1 N pt 0⟩
  | succ m hm1 ih =>
    obtain ⟨p, hp, h2, hlow, hA⟩ := ih (by omega)
    have hm : m < N := by omega
    set t : ℂ := I * eCo p m / eCo pt 0 with ht
    refine ⟨movePt N (hDir (gam2 m t)) (locNil_gam2 N m t hm1 hm) p,
      hp.trans (evalAt_eq_move hY hX _ p), fun k hk => ?_, fun j hj1 hj => ?_, ?_⟩
    · rw [movePt2_two N m t hm1 hm p]; exact h2 k hk
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [eCo_movePt2_lt N m t hm1 hm p hj]; exact hlow j hj1 hj
      · rw [eCo_movePt2_self N j t hm1 hm p, hA, ht]
        field_simp
        rw [I_sq]; ring
    · rw [eCo_movePt2_lt N m t hm1 hm p (by omega), hA]

theorem two_mul_pt_zero (pt : SMode → ℂ) (k : ℕ) :
    2 * pt ⟨k, 0⟩ = eCo pt k - coeff k (fTw (toJet pt)) := by
  simp [eCo, fTw, coeff_toJet, coeff_C_mul]; ring

theorem two_mul_pt_one (pt : SMode → ℂ) (k : ℕ) :
    2 * pt ⟨k, 1⟩ = I * (eCo pt k + coeff k (fTw (toJet pt))) := by
  simp [eCo, fTw, coeff_toJet, coeff_C_mul]
  ring_nf
  rw [I_sq]; ring

theorem normal_agree {N : ℕ} {A : ℂ} {pt : SMode → ℂ} (h : Normal N N A pt) :
    ∀ g : SMode, g.index < N → pt g = slicePt A (fTw (toJet pt)) g := by
  obtain ⟨h2, hlow, hA⟩ := h
  have he : ∀ k < N, eCo pt k = coeff k (C A) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [hA]
    · rw [hlow k hk0 hk, coeff_C, if_neg (by omega)]
  rintro ⟨k, b⟩ hk
  simp only at hk
  fin_cases b
  · have := two_mul_pt_zero pt k
    simp only [slicePt, ofJet, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, coeff_C_mul,
      map_sub]
    rw [← he k hk]
    linear_combination (1 / 2 : ℂ) * this
  · have := two_mul_pt_one pt k
    simp only [slicePt, ofJet, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      coeff_C_mul, map_add]
    rw [← he k hk]
    linear_combination (1 / 2 : ℂ) * this
  · simp [slicePt, ofJet, h2 k hk]

/-- **Restriction to the slice is injective on invariants.** An element killed by all loop
operators and vanishing at every slice point `A e + B f` with `A ≠ 0` is zero. -/
theorem eq_zero_of_slicePt {x : W} (hY : ∀ c, Y c x = 0) (hX : ∀ i a, X i a x = 0)
    (h : ∀ (A : ℂ) (B : PowerSeries ℂ), A ≠ 0 → evalAt (slicePt A B) x = 0) : x = 0 := by
  set L : MvPolynomial SMode ℂ :=
    MvPolynomial.X ⟨0, 0⟩ - MvPolynomial.C I * MvPolynomial.X ⟨0, 1⟩ with hL
  have hLe : ∀ pt, MvPolynomial.eval pt L = eCo pt 0 := by
    intro pt; simp [hL, eCo]
  have hL0 : L ≠ 0 := by
    intro h0
    have := hLe (fun g => if g = ⟨0, 0⟩ then 1 else 0)
    rw [h0] at this
    simp [eCo] at this
  apply eq_zero_of_evalAt hL0
  intro pt hpt
  rw [hLe] at hpt
  obtain ⟨N₀, hN₀⟩ := exists_low x
  have hx : Low (N₀ + 1) x := hN₀.mono (by omega)
  obtain ⟨pt', ⟨Θ, hΘ⟩, hnorm⟩ := exists_normal hY hX (N := N₀ + 1) pt hpt (N₀ + 1)
    (by omega) le_rfl
  rw [hΘ, evalAt_congr_of_low hx (normal_agree hnorm), h _ _ hpt, map_zero]

end KhanSL2.StrongMacdonald
