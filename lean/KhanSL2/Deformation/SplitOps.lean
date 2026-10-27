module

public import KhanSL2.Deformation.RestrictedActions

@[expose] public section

/-!
# The contraction `ι` of the split complex (blueprint `lem:D0split`)

In split coordinates (see `SplitMap.lean`) Lean's `c j` stands for `c⁺_{j+1}` (the factor `𝔩₊`)
and `b j` for `c⁻_j` (the factor `𝔩 = 𝔤[z]`). This file defines the contraction `ι_e` with
`b₀ᵉ`, an odd derivation, computes it on the contracted pairs `bbPair`, `bbConv` and on `Q`,
and proves `[L^P_j, ι_a] = Σ_d ε_{jad} ι_d` when `P` contains the `b₀` modes
(`colorActionOn_iota`). The split differential `D''` and the Cartan formula
`[D'', ι_e] = L^B_e` are in `SplitDifferential.lean`.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## The contraction `ι` -/

/-- Generator values of the contraction with `b₀ᵉ`. -/
def iotaGen (e : Fin 3) (m : Mode) : Cochain := if m = .b 0 e then cochainOne else 0

/-- **The contraction `ι_e`** with `b₀ᵉ`. -/
def iota (e : Fin 3) : Cochain →ₗ[ℂ] Cochain := extendDerivation (iotaGen e)

theorem iota_generator (e : Fin 3) (m : Mode) :
    iota e (generator m) = if m = .b 0 e then cochainOne else 0 :=
  extendDerivation_generator _ m

theorem isOddDer_iota (e : Fin 3) : IsOddDer (iota e) :=
  isOddDer_of_even _ (fun m => by
    unfold iotaGen
    split_ifs
    · exact cochainParity_one
    · simp)

theorem iota_generator_mul_generator (e : Fin 3) (m m' : Mode) :
    iota e (generator m * generator m') =
      (if m = .b 0 e then generator m' else 0) - (if m' = .b 0 e then generator m else 0) := by
  rw [(isOddDer_iota e).mul, iota_generator, iota_generator, cochainParity_generator]
  split_ifs <;> simp [← cochain_one_eq, sub_eq_add_neg]

theorem iota_bbPair (e : Fin 3) (i k : ℕ) (a : Fin 3) :
    iota e (bbPair i k a) =
      (if i = 0 then ∑ c : Fin 3, epsilon a e c • generator (.b k c) else 0) -
        (if k = 0 then ∑ c : Fin 3, epsilon a c e • generator (.b i c) else 0) := by
  simp only [bbPair, map_sum, map_smul, iota_generator_mul_generator, Mode.b.injEq, smul_sub,
    Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    split_ifs with hi
    · subst hi
      simp only [true_and, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp [hi]
  · split_ifs with hk
    · subst hk
      simp only [true_and, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp [hk]

/-- `ι_e (Σ_{i+k=j} ε b_i b_k) = 2 Σ_c ε_{aec} b_j^c`. -/
theorem iota_bbConv (e : Fin 3) (j : ℕ) (a : Fin 3) :
    iota e (bbConv j a) = (2 : ℂ) • ∑ c : Fin 3, epsilon a e c • generator (.b j c) := by
  have hswap : (∑ c : Fin 3, epsilon a c e • generator (.b j c)) =
      -∑ c : Fin 3, epsilon a e c • generator (.b j c) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro c _
    rw [epsilon_swap_right, neg_smul]
  rw [bbConv, map_sum]
  cases j with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_self, iota_bbPair,
      if_true, hswap, sub_neg_eq_add, two_smul]
  | succ j =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hmid : ∀ i ∈ Finset.range j, iota e (bbPair (i + 1) (j + 1 - (i + 1)) a) = 0 := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [iota_bbPair, if_neg (by omega), if_neg (by omega), sub_zero]
    rw [Finset.sum_eq_zero hmid, iota_bbPair, iota_bbPair]
    simp only [Nat.sub_zero, Nat.sub_self, if_true, add_eq_zero, one_ne_zero, and_false,
      if_false, Nat.add_one_ne_zero, sub_zero, zero_sub, hswap, neg_neg, zero_add, two_smul]

/-- `ι` anticommutes with left multiplication by a non-`b₀` generator. -/
theorem iota_qGenerator (e : Fin 3) (j : ℕ) (a : Fin 3) : iota e (qGenerator (.c j a)) = 0 := by
  simp only [qGenerator, map_smul, map_sum, ← cochain_mul_eq_wedge, iota_generator_mul_generator]
  simp

/-! ## Commutation of restricted colour actions with `ι` -/

theorem iota_colorGenerator (a j : Fin 3) (m : Mode) :
    iota a (colorGenerator j m) = if m.isB0 then epsilon j m.color a • cochainOne else 0 := by
  cases m with
  | c k x => simp [colorGenerator, iota_generator, Mode.recolor, Mode.isB0, map_sum, map_smul]
  | b k x =>
    cases k with
    | succ k => simp [colorGenerator, iota_generator, Mode.recolor, Mode.isB0, map_sum, map_smul]
    | zero =>
      simp [colorGenerator, iota_generator, Mode.recolor, Mode.isB0, Mode.color, map_sum,
        map_smul]

theorem colorActionOn_iota {P : Mode → Bool}
    (hP0 : ∀ x, P (.b 0 x) = true) (j a : Fin 3) (u : Cochain) :
    colorActionOn P j (iota a u) - iota a (colorActionOn P j u) =
      ∑ d : Fin 3, epsilon j a d • iota d u := by
  have h := (isOddDer_iota a).commutator (isEvenDer_colorActionOn P j)
  have hR : IsOddDer (∑ d : Fin 3, epsilon j a d • iota d) := by
    simp only [Fin.sum_univ_three]
    exact (((isOddDer_iota 0).smul _).add ((isOddDer_iota 1).smul _)).add
      ((isOddDer_iota 2).smul _)
  have hneg : IsOddDer (-(∑ d : Fin 3, epsilon j a d • iota d)) := by
    rw [← neg_one_smul ℂ (∑ d : Fin 3, epsilon j a d • iota d)]
    exact hR.smul (-1)
  have := h.ext hneg (fun m => by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, colorActionOn_generator,
      iota_generator, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    have hL1 : colorActionOn P j cochainOne = 0 := (isEvenDer_colorActionOn P j).map_one
    by_cases hm : m.isB0
    · obtain ⟨x, rfl⟩ : ∃ x, m = .b 0 x := by
        cases m with
        | c k x => simp [Mode.isB0] at hm
        | b k x => cases k with
          | zero => exact ⟨x, rfl⟩
          | succ k => simp [Mode.isB0] at hm
      simp only [hP0, if_true, iota_colorGenerator, Mode.isB0, Mode.color, Mode.b.injEq,
        true_and]
      split_ifs with hxa
      · subst hxa
        rw [hL1, sub_zero, ← Finset.sum_neg_distrib,
          Finset.sum_eq_single x (fun d _ hd => by rw [if_neg (Ne.symm hd), smul_zero, neg_zero])
            (by simp)]
        simp
      · rw [map_zero, sub_zero, ← Finset.sum_neg_distrib,
          Finset.sum_eq_single x (fun d _ hd => by rw [if_neg (Ne.symm hd), smul_zero, neg_zero])
            (by simp), if_pos rfl, epsilon_swap_right, neg_smul]
    · have hne : ∀ d, m ≠ .b 0 d := by
        intro d hd; subst hd; simp [Mode.isB0] at hm
      split_ifs <;> simp_all [iota_colorGenerator])
  have h2 := LinearMap.congr_fun this u
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at h2
  rw [← neg_sub, h2, neg_neg]

end KhanSL2
