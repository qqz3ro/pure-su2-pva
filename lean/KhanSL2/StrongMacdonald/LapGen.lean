module

public import KhanSL2.StrongMacdonald.Laplacian

@[expose] public section

/-!
# FGT Lemma 3.13 on generators and on pairs of even generators

On even generators and on pairs of them only the terms `T^†L` and `X^†X` survive, and
they agree summand by summand. On an odd generator the identity reduces to a
harmonic-number identity.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

theorem Td_sigOf (i k : ℕ) (a b : Fin 3) :
    Td i a (sigOf k b) = -∑ c, epsilon a b c • sigOf (k + (i + 1)) c := by
  simp [Td]

theorem Xd_sigOf (i k : ℕ) (a b : Fin 3) :
    Xd i a (sigOf k b) = -∑ c, epsilon a b c • sigOf (k + (i + 1)) c := by
  simp [Xd]

theorem L_sigOf (i k : ℕ) (a b : Fin 3) : L i a (sigOf k b) = Rlow a (i + 1) (sigOf k b) := by
  simp [L]

theorem X_sigOf (i k : ℕ) (a b : Fin 3) : X i a (sigOf k b) = Rlow a (i + 1) (sigOf k b) := by
  simp [X]

theorem Td_Rlow_sigOf (i k : ℕ) (a b : Fin 3) :
    Td i a (Rlow a (i + 1) (sigOf k b)) = Xd i a (Rlow a (i + 1) (sigOf k b)) := by
  rw [Rlow_sigOf]
  split
  · simp only [map_sum, map_smul, Td_sigOf, Xd_sigOf]
  · simp

theorem KD_sigOf (i k : ℕ) (a a' b : Fin 3) : KD i a a' (sigOf k b) = 0 := by
  simp [KD]

theorem Fam_sigOf (i k : ℕ) (b : Fin 3) : Fam i (sigOf k b) = 0 := by
  simp only [Fam, starFam, boxFam, DFam, KFam, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, iota_sigOf, map_zero,
    zero_add, L_sigOf, X_sigOf, Td_Rlow_sigOf, KD_sigOf, smul_zero, Finset.sum_const_zero,
    add_zero, sub_self, dUd, dUpDag_sigOf, dU]

/-! ## Second-order defects of products on generators -/

theorem HomDer.cross_mul_sigOf {p q : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A)
    (hB : HomDer q B) (hpq : (p + q) % 2 = 0) (k : ℕ) (b : Fin 3) (y : W) :
    cross (A * B) (sigOf k b) y = ((-1 : ℂ) ^ (p * q)) • (B (sigOf k b) * A y) +
      A (sigOf k b) * B y := by
  have h := hA.cross_mul hB hpq (.s ⟨k, b⟩) y
  simp only [Gen.elt, Gen.par, mul_zero, pow_zero, one_smul, add_zero] at h
  exact h

theorem HomDer.cross_mul_psiOf {p q : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A)
    (hB : HomDer q B) (hpq : (p + q) % 2 = 0) (k : ℕ) (b : Fin 3) (y : W) :
    cross (A * B) (psiOf k b) y = ((-1 : ℂ) ^ (p * (q + 1))) • (B (psiOf k b) * A y) +
      ((-1 : ℂ) ^ q) • (A (psiOf k b) * B y) := by
  have h := hA.cross_mul hB hpq (.p ⟨k, b⟩) y
  simp only [Gen.elt, Gen.par, mul_one] at h
  exact h

/-- The defect of the difference family at an even generator. -/
theorem cross_Fam_sigOf (i k : ℕ) (b : Fin 3) (y : W) :
    cross (Fam i) (sigOf k b) y =
      ∑ a, lam i • (E i a (sigOf k b) * iota i a y +
          (L i a (sigOf k b) * Td i a y + Td i a (sigOf k b) * L i a y)) -
        (∑ a, lam i • (X i a (sigOf k b) * Xd i a y + Xd i a (sigOf k b) * X i a y) +
          ∑ a, dU i a (sigOf k b) * dUd i a y +
          ∑ a, ∑ b', ∑ c, (-(epsilon a b' c * lam i)) • (Y c (sigOf k b) * KD i a b' y)) := by
  have h1 : ∀ a, cross (E i a * iota i a) (sigOf k b) y = E i a (sigOf k b) * iota i a y := by
    intro a
    rw [(homDer_E i a).cross_mul_sigOf (homDer_iota i a) rfl, iota_sigOf]
    simp
  have h2 : ∀ a, cross (Td i a * L i a) (sigOf k b) y =
      L i a (sigOf k b) * Td i a y + Td i a (sigOf k b) * L i a y := by
    intro a
    rw [(homDer_Td i a).cross_mul_sigOf (homDer_L i a) rfl]
    simp
  have h3 : ∀ a, cross (Xd i a * X i a) (sigOf k b) y =
      X i a (sigOf k b) * Xd i a y + Xd i a (sigOf k b) * X i a y := by
    intro a
    rw [(homDer_Xd i a).cross_mul_sigOf (homDer_X i a) rfl]
    simp
  have h4 : ∀ a, cross (dU i a * dUd i a) (sigOf k b) y = dU i a (sigOf k b) * dUd i a y := by
    intro a
    rw [(homDer_dU i a).cross_mul_sigOf (homDer_dUd i a) rfl]
    simp [dUd]
  have h5 : ∀ a b' c, cross (Y c * KD i a b') (sigOf k b) y = Y c (sigOf k b) * KD i a b' y := by
    intro a b' c
    rw [(homDer_Y c).cross_mul_sigOf (homDer_KD i a b') rfl, KD_sigOf]
    simp
  simp only [Fam, starFam, boxFam, DFam, KFam, cross_sub, cross_add, cross_sum, cross_smul,
    h1, h2, h3, h4, h5]

/-- The defect of the difference family at an odd generator. -/
theorem cross_Fam_psiOf (i k : ℕ) (b : Fin 3) (y : W) :
    cross (Fam i) (psiOf k b) y =
      ∑ a, lam i • (iota i a (psiOf k b) * E i a y - E i a (psiOf k b) * iota i a y +
          (L i a (psiOf k b) * Td i a y + Td i a (psiOf k b) * L i a y)) -
        (∑ a, lam i • (X i a (psiOf k b) * Xd i a y + Xd i a (psiOf k b) * X i a y) +
          ∑ a, dUd i a (psiOf k b) * dU i a y +
          ∑ a, ∑ b', ∑ c, (-(epsilon a b' c * lam i)) •
            (KD i a b' (psiOf k b) * Y c y + Y c (psiOf k b) * KD i a b' y)) := by
  have h1 : ∀ a, cross (E i a * iota i a) (psiOf k b) y =
      iota i a (psiOf k b) * E i a y - E i a (psiOf k b) * iota i a y := by
    intro a
    rw [(homDer_E i a).cross_mul_psiOf (homDer_iota i a) rfl]
    simp [sub_eq_add_neg]
  have h2 : ∀ a, cross (Td i a * L i a) (psiOf k b) y =
      L i a (psiOf k b) * Td i a y + Td i a (psiOf k b) * L i a y := by
    intro a
    rw [(homDer_Td i a).cross_mul_psiOf (homDer_L i a) rfl]
    simp
  have h3 : ∀ a, cross (Xd i a * X i a) (psiOf k b) y =
      X i a (psiOf k b) * Xd i a y + Xd i a (psiOf k b) * X i a y := by
    intro a
    rw [(homDer_Xd i a).cross_mul_psiOf (homDer_X i a) rfl]
    simp
  have h4 : ∀ a, cross (dU i a * dUd i a) (psiOf k b) y = dUd i a (psiOf k b) * dU i a y := by
    intro a
    rw [(homDer_dU i a).cross_mul_psiOf (homDer_dUd i a) rfl]
    simp [dU]
  have h5 : ∀ a b' c, cross (Y c * KD i a b') (psiOf k b) y =
      KD i a b' (psiOf k b) * Y c y + Y c (psiOf k b) * KD i a b' y := by
    intro a b' c
    rw [(homDer_Y c).cross_mul_psiOf (homDer_KD i a b') rfl]
    simp
  simp only [Fam, starFam, boxFam, DFam, KFam, cross_sub, cross_add, cross_sum, cross_smul,
    h1, h2, h3, h4, h5]

/-! ## Pairs of even generators -/

theorem cross_Fam_sigOf_sigOf (i k n : ℕ) (b c : Fin 3) :
    cross (Fam i) (sigOf k b) (sigOf n c) = 0 := by
  rw [cross_Fam_sigOf]
  simp only [iota_sigOf, mul_zero, zero_add, L_sigOf, X_sigOf, Td_sigOf, Xd_sigOf, dUd,
    dUpDag_sigOf, KD_sigOf, smul_zero, Finset.sum_const_zero, add_zero, sub_self]

/-! ## Odd generators -/

theorem HomDer.map_ite_one {p : ℕ} {D : Module.End ℂ W} (h : HomDer p D) (P : Prop) [Decidable P] :
    D (if P then 1 else 0) = 0 := by
  split
  · exact h.map_one
  · exact map_zero D

theorem starFam_psiOf (i n : ℕ) (b : Fin 3) :
    starFam i (psiOf n b) =
      (if i < n then ((n : ℂ) + 1) / (((i : ℂ) + 1) * ((n : ℂ) - i)) else 0) • psiOf n b := by
  simp only [starFam, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.mul_apply, iota_psiOf, (homDer_E _ _).map_ite_one, zero_add, L, Rlow_psiOf,
    adLow_psiOf]
  by_cases h : i < n
  · obtain ⟨j, rfl⟩ : ∃ j, n = i + 1 + j := ⟨n - (i + 1), by omega⟩
    simp only [show i + 1 ≤ i + 1 + j by omega, if_true, h, Nat.add_sub_cancel_left, map_sum,
      map_smul, Td, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, Rup_psiOf,
      neg_zero, adLowDag_psiOf, zero_add]
    rw [show j + (i + 1) = i + 1 + j by omega]
    have hc : ((↑(i + 1 + j) : ℂ) + 1) / ((↑i + 1) * (↑(i + 1 + j) - ↑i)) =
        ((i : ℂ) + j + 2) * ((i : ℂ) + 1)⁻¹ * ((j : ℂ) + 1)⁻¹ := by
      have h1 := Nat.cast_add_one_ne_zero (R := ℂ) i
      have h2 := Nat.cast_add_one_ne_zero (R := ℂ) j
      push_cast
      rw [show (i : ℂ) + 1 + j - i = j + 1 by ring]
      field_simp
      ring
    rw [hc]
    fin_cases b <;> simp [Fin.sum_univ_three, epsilon, lam] <;> module
  · simp [h, show ¬ (i + 1 ≤ n) by omega]

theorem boxFam_psiOf (i n : ℕ) (b : Fin 3) :
    boxFam i (psiOf n b) =
      (if i < n then 2 * ((n : ℂ) - i) / (((i : ℂ) + 1) * ((n : ℂ) + 1)) else 0) • psiOf n b := by
  simp only [boxFam, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, X,
    LinearMap.sub_apply, Rlow_psiOf, adUpDag_psiOf, zero_sub]
  by_cases h : i < n
  · obtain ⟨j, rfl⟩ : ∃ j, n = i + 1 + j := ⟨n - (i + 1), by omega⟩
    simp only [show i + 1 ≤ i + 1 + j by omega, if_true, h, Nat.add_sub_cancel_left, map_neg,
      map_sum, map_smul, Xd, LinearMap.sub_apply, LinearMap.neg_apply, Rup_psiOf, neg_zero,
      adUp_psiOf, zero_sub]
    rw [show j + (i + 1) = i + 1 + j by omega, show i + 1 + j + 1 - (i + 1) = j + 1 by omega]
    have hc : 2 * ((↑(i + 1 + j) : ℂ) - ↑i) / ((↑i + 1) * (↑(i + 1 + j) + 1)) =
        2 * ((j : ℂ) + 1) * ((i : ℂ) + 1)⁻¹ * ((i : ℂ) + j + 2)⁻¹ := by
      have h1 := Nat.cast_add_one_ne_zero (R := ℂ) i
      have h2 : (i : ℂ) + j + 2 ≠ 0 := by
        have := Nat.cast_add_one_ne_zero (R := ℂ) (i + j + 1); push_cast at this
        rwa [show (i : ℂ) + j + 1 + 1 = i + j + 2 by ring] at this
      push_cast
      rw [show (i : ℂ) + 1 + j + 1 = i + j + 2 by ring]
      field_simp
      ring
    rw [hc]
    fin_cases b <;> simp [Fin.sum_univ_three, epsilon, lam] <;> module
  · simp [h, show ¬ (i + 1 ≤ n) by omega]

theorem DFam_psiOf (i n : ℕ) (b : Fin 3) :
    DFam i (psiOf n b) = (if i ≤ n then 2 / ((n : ℂ) + 1) else 0) • psiOf n b := by
  simp only [DFam, LinearMap.sum_apply, Module.End.mul_apply, dUd, dUpDag_psiOf]
  by_cases h : i ≤ n
  · obtain ⟨j, rfl⟩ : ∃ j, n = i + j := ⟨n - i, by omega⟩
    simp only [show i + 1 ≤ i + j + 1 by omega, if_true, h, map_sum, map_smul, dU, dUp_sigOf]
    rw [show i + j + 1 - (i + 1) + (i + 1) - 1 = i + j by omega]
    fin_cases b <;> simp [Fin.sum_univ_three, epsilon] <;> module
  · simp [h, show ¬ (i + 1 ≤ n + 1) by omega]

theorem KFam_psiOf (i n : ℕ) (b : Fin 3) :
    KFam i (psiOf n b) = (if i = n then -(2 / ((n : ℂ) + 1)) else 0) • psiOf n b := by
  simp only [KFam, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, KD,
    lmul_apply, iota_psiOf, mul_ite, mul_one, mul_zero]
  by_cases h : i = n
  · subst h
    simp only [true_and, if_true]
    simp only [apply_ite (Y _), map_zero, Y, LinearMap.add_apply, Rlow_psiOf, adLow_psiOf,
      zero_add, Nat.zero_le, if_true, Nat.sub_zero]
    fin_cases b <;> simp [Fin.sum_univ_three, epsilon, lam] <;> module
  · simp [h]

theorem sum_range_ite_lt (N n : ℕ) (hn : n ≤ N) (f : ℕ → ℂ) :
    ∑ i ∈ Finset.range N, (if i < n then f i else 0) = ∑ i ∈ Finset.range n, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem sum_inv_sub_eq (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / ((n : ℂ) - i) = ∑ i ∈ Finset.range n, 1 / ((i : ℂ) + 1) := by
  rw [← Finset.sum_range_reflect (fun i => 1 / ((i : ℂ) + 1)) n]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring_nf

theorem Fam_psiOf (i n : ℕ) (b : Fin 3) :
    Fam i (psiOf n b) =
      ((if i < n then ((n : ℂ) + 1) / (((i : ℂ) + 1) * ((n : ℂ) - i)) else 0) -
        ((if i < n then 2 * ((n : ℂ) - i) / (((i : ℂ) + 1) * ((n : ℂ) + 1)) else 0) +
          (if i ≤ n then 2 / ((n : ℂ) + 1) else 0) +
          (if i = n then -(2 / ((n : ℂ) + 1)) else 0))) • psiOf n b := by
  rw [Fam, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.add_apply, starFam_psiOf,
    boxFam_psiOf, DFam_psiOf, KFam_psiOf]
  simp only [sub_smul, add_smul]

/-- FGT Lemma 3.13 on an odd generator. -/
theorem sum_Fam_psiOf (n N : ℕ) (b : Fin 3) (hN : n < N) :
    ∑ i ∈ Finset.range N, Fam i (psiOf n b) = 0 := by
  simp only [Fam_psiOf, ← Finset.sum_smul]
  convert zero_smul ℂ (psiOf n b)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_range_ite_lt N n hN.le, sum_range_ite_lt N n hN.le, Finset.sum_ite_eq' (Finset.range N),
    if_pos (Finset.mem_range.mpr hN)]
  have hle : ∑ i ∈ Finset.range N, (if i ≤ n then 2 / ((n : ℂ) + 1) else 0) =
      ∑ i ∈ Finset.range (n + 1), 2 / ((n : ℂ) + 1) := by
    rw [← sum_range_ite_lt N (n + 1) (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.lt_succ_iff]
  rw [hle, Finset.sum_const, Finset.card_range]
  have hn1 := Nat.cast_add_one_ne_zero (R := ℂ) n
  have hterm : ∀ i ∈ Finset.range n, ((n : ℂ) + 1) / (((i : ℂ) + 1) * ((n : ℂ) - i)) -
      2 * ((n : ℂ) - i) / (((i : ℂ) + 1) * ((n : ℂ) + 1)) =
      1 / ((n : ℂ) - i) - 1 / ((i : ℂ) + 1) + 2 / ((n : ℂ) + 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h1 := Nat.cast_add_one_ne_zero (R := ℂ) i
    have h2 : (n : ℂ) - i ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (Nat.ne_of_gt hi')
    field_simp
    ring
  rw [show ∀ (A B C D : ℂ), A - (B + C + D) = (A - B) - C - D by intros; ring,
    ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_inv_sub_eq, sub_self, zero_add, Finset.sum_const,
    Finset.card_range]
  simp only [nsmul_eq_mul]
  push_cast
  field_simp
  ring

end KhanSL2.StrongMacdonald
