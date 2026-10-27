module

public import KhanSL2.Deformation.Kunneth

@[expose] public section

/-!
# Exactness of the split differential on invariants (blueprint `lem:Hlpos`)

Two Casimir null-homotopies reduce an invariant `D''`-cocycle to the fully invariant part:

1. `[D'', ι_e] = L^B_e` (the `𝔩`-factor action is homotopically trivial), so every cocycle is
   cohomologous to an `L^B`-invariant one; there `D'' = D̂ = d_c + d_Z - d_g`;
2. `[D̂, -ι_e] = L^{B₀}_e`, so it is cohomologous to an `L^{B₀}`-invariant one, in `V00`, where
   `D'' = d_c + d_Z`;
3. Künneth (`kunneth`) finishes in positive `T`.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-- Casimir pieces of fixed cochain degree and `T`. -/
def coarseSplit (P : Mode → Bool) (hP : ColorStable P) (T : ℤ) : CasimirSplit Cochain where
  W k := gPiece coarse (k, T)
  fin _ := finiteDimensional_coarse _
  L := colorActionOn P
  L_mem a _ _ hv := colorActionOn_mem_coarse P a hv
  action := isColorAction_colorActionOn hP

theorem coarse_shift_up {n T : ℤ} {v : Cochain} (hv : v ∈ gPiece coarse ((n, T) + (1, 0))) :
    v ∈ gPiece coarse (n + 1, T) := by
  convert hv using 2; simp

theorem coarse_shift_down {n T : ℤ} {v : Cochain} (hv : v ∈ gPiece coarse ((n, T) + (-1, 0))) :
    v ∈ gPiece coarse (n - 1, T) := by
  convert hv using 2; simp [sub_eq_add_neg]

/-- **Step 1**: the null-homotopy of the `L^B` Casimir. -/
def homotopyB (T : ℤ) : CasimirHomotopy Cochain where
  toCasimirSplit := coarseSplit Mode.isB colorStable_isB T
  D := dpp
  ι := iota
  D_mem hv := coarse_shift_up (dpp_mem_coarse hv)
  ι_mem a _ _ hv := coarse_shift_down (iota_mem_coarse a hv)
  cartan a v := dpp_iota a v
  D_L a v := dpp_LB a v

/-- `D̂ = d_c + d_Z - d_g`. -/
def Dhat : Cochain →ₗ[ℂ] Cochain := dC + dZ - dG

theorem Dhat_apply (v : Cochain) : Dhat v = dC v + dZ v - dG v := rfl

/-- **Step 2**: the null-homotopy of the `L^{B₀}` Casimir. -/
def homotopyB0 (T : ℤ) : CasimirHomotopy Cochain where
  toCasimirSplit := coarseSplit Mode.isB0 colorStable_isB0 T
  D := Dhat
  ι a := -iota a
  D_mem hv := by
    rw [Dhat_apply]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (coarse_shift_up (dC_mem_coarse hv))
      (coarse_shift_up (dZ_mem_coarse hv))) (coarse_shift_up (dG_mem_coarse hv))
  ι_mem a _ _ hv := by
    rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (coarse_shift_down (iota_mem_coarse a hv))
  cartan a v := by
    change Dhat (-iota a v) + -iota a (Dhat v) = LB0 a v
    have h1 := dC_iota a v
    have h2 := dZ_iota a v
    have h3 := dG_iota a v
    simp only [Dhat_apply, map_neg, map_sub, map_add] at h1 h2 h3 ⊢
    linear_combination (norm := module) -h1 - h2 + h3
  D_L a v := by
    change Dhat (LB0 a v) = LB0 a (Dhat v)
    simp only [Dhat_apply, map_sub, map_add, dC_LB0, dZ_LB0, dG_LB0]

/-! ## Vector transformation rules -/

theorem colorAction_colorActionOn_comm {Q : Mode → Bool} (hQ : ColorStable Q) (j a : Fin 3)
    (v : Cochain) :
    colorAction j (colorActionOn Q a v) - colorActionOn Q a (colorAction j v) =
      ∑ d : Fin 3, epsilon j a d • colorActionOn Q d v := by
  have h := colorActionOn_comm colorStable_true hQ j a v
  simp only [Bool.true_and, colorActionOn_true] at h
  exact h

theorem LB_LB0_comm (j a : Fin 3) (v : Cochain) :
    LB j (LB0 a v) - LB0 a (LB j v) = ∑ d : Fin 3, epsilon j a d • LB0 d v := by
  have h := colorActionOn_comm colorStable_isB colorStable_isB0 j a v
  have hfun : (fun m => Mode.isB m && Mode.isB0 m) = Mode.isB0 := by
    funext m; cases m with
    | c k x => rfl
    | b k x => cases k <;> rfl
  rw [hfun] at h
  exact h

theorem colorAction_iota_comm (j a : Fin 3) (v : Cochain) :
    colorAction j (iota a v) - iota a (colorAction j v) = ∑ d : Fin 3, epsilon j a d • iota d v :=
  colorActionOn_iota (P := fun _ => true) (fun _ => rfl) j a v

theorem LB_iota_comm (j a : Fin 3) (v : Cochain) :
    LB j (iota a v) - iota a (LB j v) = ∑ d : Fin 3, epsilon j a d • iota d v :=
  colorActionOn_iota (P := Mode.isB) (fun _ => rfl) j a v

theorem neg_vector {X : Fin 3 → Cochain →ₗ[ℂ] Cochain} {M : Cochain →ₗ[ℂ] Cochain} {j : Fin 3}
    (h : ∀ a v, M (X a v) - X a (M v) = ∑ d : Fin 3, epsilon j a d • X d v) (a : Fin 3)
    (v : Cochain) :
    M ((-X a) v) - (-X a) (M v) = ∑ d : Fin 3, epsilon j a d • (-X d) v := by
  simp only [LinearMap.neg_apply, map_neg, smul_neg, Finset.sum_neg_distrib, ← h a v]
  abel

/-! ## Exactness of `D''` -/

/-- **`D''` is exact on invariants in positive `T`.** -/
theorem dpp_exact {n T : ℤ} (hT : T ≠ 0) {u : Cochain} (hu : u ∈ gPiece coarse (n, T))
    (hinv : ∀ e, colorAction e u = 0) (hD : dpp u = 0) :
    ∃ w ∈ gPiece coarse (n - 1, T), (∀ e, colorAction e w = 0) ∧ u = dpp w := by
  -- step 1
  let H₁ := homotopyB T
  obtain ⟨u₁, hu₁, hM₁, hL₁, hD₁, w₁, hw₁, hMw₁, rfl⟩ := H₁.casimir_reduction
    (fun j => colorAction j) (fun j _ _ hv => colorAction_mem_coarse j hv)
    (fun j v => by
      simp only [CasimirSplit.Ω_apply]
      exact pair_sum_comm (colorAction j) j H₁.L H₁.L (colorAction_colorActionOn_comm
        colorStable_isB j) (colorAction_colorActionOn_comm colorStable_isB j) v)
    (fun j v => by
      simp only [CasimirHomotopy.h, LinearMap.sum_apply, LinearMap.comp_apply]
      exact pair_sum_comm (colorAction j) j H₁.ι H₁.L (colorAction_iota_comm j)
        (colorAction_colorActionOn_comm colorStable_isB j) v)
    hu hinv hD
  change ∀ a, LB a u₁ = 0 at hL₁
  change dpp u₁ = 0 at hD₁
  -- step 2
  have hDhat₁ : Dhat u₁ = 0 := by rw [Dhat_apply, ← dpp_eq_of_LB hL₁]; exact hD₁
  let H₂ := homotopyB0 T
  let M₂ : Fin 3 ⊕ Fin 3 → Cochain →ₗ[ℂ] Cochain := Sum.elim (fun j => colorAction j) LB
  obtain ⟨u₂, hu₂, hM₂, hL₂, hD₂, w₂, hw₂, hMw₂, hu₁eq⟩ := H₂.casimir_reduction M₂
    (fun j _ _ hv => by
      cases j with
      | inl j => exact colorAction_mem_coarse j hv
      | inr j => exact colorActionOn_mem_coarse _ j hv)
    (fun j v => by
      simp only [CasimirSplit.Ω_apply]
      cases j with
      | inl j =>
        exact pair_sum_comm (colorAction j) j H₂.L H₂.L
          (colorAction_colorActionOn_comm colorStable_isB0 j)
          (colorAction_colorActionOn_comm colorStable_isB0 j) v
      | inr j => exact pair_sum_comm (LB j) j H₂.L H₂.L (LB_LB0_comm j) (LB_LB0_comm j) v)
    (fun j v => by
      simp only [CasimirHomotopy.h, LinearMap.sum_apply, LinearMap.comp_apply]
      cases j with
      | inl j =>
        exact pair_sum_comm (colorAction j) j H₂.ι H₂.L (neg_vector (colorAction_iota_comm j))
          (colorAction_colorActionOn_comm colorStable_isB0 j) v
      | inr j =>
        exact pair_sum_comm (LB j) j H₂.ι H₂.L (neg_vector (LB_iota_comm j)) (LB_LB0_comm j) v)
    hu₁ (fun j => by
      cases j with
      | inl j => exact hM₁ j
      | inr j => exact hL₁ j) hDhat₁
  change ∀ a, LB0 a u₂ = 0 at hL₂
  change Dhat u₂ = 0 at hD₂
  change u₁ = u₂ + Dhat w₂ at hu₁eq
  -- step 3
  have hV : u₂ ∈ V00 := by
    rw [mem_V00]
    intro e
    have hc := hM₂ (.inl e)
    have hb := hM₂ (.inr e)
    simp only [M₂, Sum.elim_inl, Sum.elim_inr] at hc hb
    rw [colorAction_eq_LC_LB, LinearMap.add_apply, hb, add_zero] at hc
    rw [LB_eq, LinearMap.add_apply, hL₂, zero_add] at hb
    exact ⟨hc, hb, hL₂ e⟩
  have hCZ : dC u₂ + dZ u₂ = 0 := by
    rw [Dhat_apply, dG_eq_zero_of_LB0 hL₂, sub_zero] at hD₂
    exact hD₂
  obtain ⟨w₃, hw₃V, hw₃, hu₂eq⟩ := kunneth hT hV hu₂ hCZ
  -- assemble
  have hw₂B : ∀ e, LB e w₂ = 0 := fun e => hMw₂ (.inr e)
  have hw₂inv : ∀ e, colorAction e w₂ = 0 := fun e => hMw₂ (.inl e)
  have hw₃inv : ∀ e, colorAction e w₃ = 0 := by
    intro e
    obtain ⟨h1, h2, h3⟩ := mem_V00.mp hw₃V e
    rw [colorAction_eq_LC_LB, LinearMap.add_apply, LB_eq, LinearMap.add_apply, h1, h2, h3]
    simp
  have hdpp₃ : dpp w₃ = dC w₃ + dZ w₃ := by
    have hB0 : ∀ e, LB0 e w₃ = 0 := fun e => (mem_V00.mp hw₃V e).2.2
    have hZ : ∀ e, LZ e w₃ = 0 := fun e => (mem_V00.mp hw₃V e).2.1
    rw [dpp_eq]
    simp only [LinearMap.add_apply, dG_eq_zero_of_LB0 hB0, coupling_eq_zero_of_LZ hZ, add_zero]
  have hdpp₂ : dpp w₂ = Dhat w₂ := by rw [Dhat_apply, dpp_eq_of_LB hw₂B]
  refine ⟨w₁ + w₂ + w₃, Submodule.add_mem _ (Submodule.add_mem _ hw₁ hw₂) hw₃, fun e => ?_, ?_⟩
  · rw [map_add, map_add, hMw₁ e, hw₂inv e, hw₃inv e, add_zero, add_zero]
  · change u₁ + dpp w₁ = dpp (w₁ + w₂ + w₃)
    rw [map_add, map_add, hu₁eq, hu₂eq, hdpp₂, hdpp₃]
    abel

end KhanSL2
