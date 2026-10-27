module

public import KhanSL2.Deformation.SplitDifferential
public import KhanSL2.Deformation.PureModes
public import KhanSL2.Injectivity.ExteriorSubstitution

@[expose] public section

/-!
# Identities for the split differential (blueprint `lem:D0split`, `lem:Hlpos`)

* the swap `σ : c_j ↔ b_{j+1}`, `b₀ ↦ b₀`, an algebra involution exchanging `d_c ↔ d_Z` and
  `L^C ↔ L^Z`;
* `d_c² = d_Z² = d_c d_Z + d_Z d_c = 0`;
* the equivariances of `d_c, d_Z, d_g, D''` under the restricted colour actions;
* on `L^B`-invariants `D'' = d_c + d_Z - d_g`; on `L^{B₀}`-invariants `d_g = 0`; on
  `L^Z`-invariants the coupling vanishes.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## Mode classes and the pieces of the generator images -/

theorem bbPair_mem_pureIn {P : Mode → Bool} {i k : ℕ} (hi : ∀ x, P (.b i x) = true)
    (hk : ∀ x, P (.b k x) = true) (a : Fin 3) : bbPair i k a ∈ pureIn P := by
  apply (pureIn P).sum_mem; intro b _
  apply (pureIn P).sum_mem; intro c _
  exact (pureIn P).smul_mem _ (mul_mem_pureIn (generator_mem_pureIn (hi b))
    (generator_mem_pureIn (hk c)))

theorem zzConv_mem_pureIn (j : ℕ) (a : Fin 3) : zzConv j a ∈ pureIn Mode.isZ := by
  apply (pureIn _).sum_mem
  intro i hi
  have hi' := Finset.mem_range.mp hi
  obtain ⟨k, hk⟩ : ∃ k, j - i = k + 1 := ⟨j - i - 1, by omega⟩
  rw [hk]
  exact bbPair_mem_pureIn (fun _ => rfl) (fun _ => rfl) a

theorem bbConv_mem_pureIn (j : ℕ) (a : Fin 3) : bbConv j a ∈ pureIn Mode.isB := by
  apply (pureIn _).sum_mem
  intro i _
  exact bbPair_mem_pureIn (fun _ => rfl) (fun _ => rfl) a

theorem qGenerator_c_mem_pureIn (j : ℕ) (a : Fin 3) : qGenerator (.c j a) ∈ pureIn Mode.isC := by
  apply (pureIn _).smul_mem
  apply (pureIn _).sum_mem; intro i _
  apply (pureIn _).sum_mem; intro b _
  apply (pureIn _).sum_mem; intro c _
  apply (pureIn _).smul_mem
  rw [← cochain_mul_eq_wedge]
  exact mul_mem_pureIn (generator_mem_pureIn rfl) (generator_mem_pureIn rfl)

theorem dCGen_mem_pureIn (m : Mode) : dCGen m ∈ pureIn Mode.isC := by
  cases m with
  | c j a => exact qGenerator_c_mem_pureIn j a
  | b j a => exact (pureIn _).zero_mem

theorem dZGen_mem_pureIn (m : Mode) : dZGen m ∈ pureIn Mode.isZ := by
  cases m with
  | c j a => exact (pureIn _).zero_mem
  | b j a =>
    cases j with
    | zero => exact (pureIn _).zero_mem
    | succ j => exact (pureIn _).smul_mem _ (zzConv_mem_pureIn j a)

theorem dGGen_mem_pureIn (m : Mode) : dGGen m ∈ pureIn Mode.isB0 := by
  cases m with
  | c j a => exact (pureIn _).zero_mem
  | b j a =>
    cases j with
    | zero => exact (pureIn _).smul_mem _ (bbPair_mem_pureIn (fun _ => rfl) (fun _ => rfl) a)
    | succ j => exact (pureIn _).zero_mem

theorem dCGen_of_not (m : Mode) (h : m.isC = false) : dCGen m = 0 := by
  cases m with
  | c j a => simp [Mode.isC] at h
  | b j a => rfl

theorem dZGen_of_not (m : Mode) (h : m.isZ = false) : dZGen m = 0 := by
  cases m with
  | c j a => rfl
  | b j a => cases j with
    | zero => rfl
    | succ j => simp [Mode.isZ] at h

theorem dGGen_of_not (m : Mode) (h : m.isB0 = false) : dGGen m = 0 := by
  cases m with
  | c j a => rfl
  | b j a => cases j with
    | zero => simp [Mode.isB0] at h
    | succ j => rfl

theorem colorActionOn_gen_of_not {P : Mode → Bool} (e : Fin 3) (m : Mode) (h : P m = false) :
    (fun m => if P m then colorGenerator e m else 0) m = 0 := by simp [h]

theorem colorActionOn_gen_mem {P : Mode → Bool} (hP : ColorStable P) (e : Fin 3) (m : Mode)
    (h : P m = true) : (fun m => if P m then colorGenerator e m else 0) m ∈ pureIn P := by
  simp only [h, if_true]
  exact colorGenerator_mem_pureIn hP e h

/-! ## Agreement on pure classes -/

theorem dC_eq_q_of_pureC {u : Cochain} (hu : u ∈ pureIn Mode.isC) : dC u = q u :=
  extendDerivation_congr_pureIn dCGen qGenerator (fun m hm => by
    cases m with
    | c j a => rfl
    | b j a => simp [Mode.isC] at hm) hu

theorem colorActionOn_eq_of_pure {P Q : Mode → Bool} (hPQ : ∀ m, Q m = true → P m = true)
    (e : Fin 3) {u : Cochain} (hu : u ∈ pureIn Q) : colorActionOn P e u = colorAction e u := by
  rw [← colorActionOn_true]
  exact extendDerivation_congr_pureIn _ _ (fun m hm => by simp [hPQ m hm]) hu

theorem colorActionOn_pure_zero {P Q : Mode → Bool} (hPQ : ∀ m, Q m = true → P m = false)
    (e : Fin 3) {u : Cochain} (hu : u ∈ pureIn Q) : colorActionOn P e u = 0 :=
  extendDerivation_pureIn_zero _ (fun m hm => by simp [hPQ m hm]) hu

/-! ## Squares -/

theorem dC_dC (u : Cochain) : dC (dC u) = 0 := by
  have h := anticomm_odd_odd isOddDer_dC isOddDer_dC (fun m => by
    rw [dC_generator]
    cases m with
    | c j a =>
      have : dC (dCGen (.c j a)) = 0 := by
        rw [dC_eq_q_of_pureC (dCGen_mem_pureIn _)]
        exact q_qGenerator _
      rw [this, add_zero]
    | b j a => simp [dCGen]) u
  have h2 : (2 : ℂ) • dC (dC u) = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem dC_dZ_anticomm (u : Cochain) : dC (dZ u) + dZ (dC u) = 0 :=
  anticomm_odd_odd isOddDer_dC isOddDer_dZ (fun m => by
    rw [dC_generator, dZ_generator]
    have h1 : dC (dZGen m) = 0 := extendDerivation_pureIn_zero dCGen
      (fun m' hm' => dCGen_of_not m' (by cases m' with
        | c j a => cases j <;> simp [Mode.isZ] at hm'
        | b j a => rfl)) (dZGen_mem_pureIn m)
    have h2 : dZ (dCGen m) = 0 := extendDerivation_pureIn_zero dZGen
      (fun m' hm' => dZGen_of_not m' (by cases m' with
        | c j a => rfl
        | b j a => simp [Mode.isC] at hm')) (dCGen_mem_pureIn m)
    rw [h1, h2, add_zero]) u

/-! ## The swap `σ` -/

/-- Generator images of the swap `c_j ↔ b_{j+1}`, `b₀ ↦ b₀`. -/
def swapGen : Mode → Cochain
  | .c j a => generator (.b (j + 1) a)
  | .b 0 a => generator (.b 0 a)
  | .b (j + 1) a => generator (.c j a)

theorem swapGen_parity (m : Mode) : FiniteExterior.parityLinear (swapGen m) = -swapGen m := by
  rw [← cochainParity_apply]
  cases m with
  | c j a => simp [swapGen]
  | b j a => cases j <;> simp [swapGen]

/-- **The swap** `σ`. -/
def swap : Cochain →ₐ[ℂ] Cochain := FiniteExterior.substituteOdd swapGen swapGen_parity

@[simp] theorem swap_generator (m : Mode) : swap (generator m) = swapGen m :=
  FiniteExterior.substituteOdd_generator _ _ m

theorem swap_generator_parity (m : Mode) :
    cochainParity (swap (generator m)) = -swap (generator m) := by
  rw [swap_generator, cochainParity_apply, swapGen_parity]

theorem swap_swap (u : Cochain) : swap (swap u) = u := by
  have : swap.comp swap = AlgHom.id ℂ Cochain := by
    apply FiniteExterior.algHom_ext
    intro m
    change swap (swap (generator m)) = generator m
    cases m with
    | c j a => simp [swapGen]
    | b j a => cases j <;> simp [swapGen]
  exact congrArg (fun F : Cochain →ₐ[ℂ] Cochain => F u) this

theorem swap_injective : Function.Injective swap :=
  fun u v h => by rw [← swap_swap u, h, swap_swap]

theorem swap_dC (u : Cochain) : swap (dC u) = dZ (swap u) :=
  twisted_odd swap swap_generator_parity isOddDer_dC isOddDer_dZ (fun m => by
    rw [dC_generator, swap_generator]
    cases m with
    | c j a =>
      simp only [dCGen, swapGen, dZ_generator, dZGen, zzConv, qGenerator, map_smul, map_sum,
        ← cochain_mul_eq_wedge, map_mul, swap_generator, bbPair, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h : j - 1 - i + 1 = j - i := by omega
      simp only [h]
    | b j a =>
      cases j with
      | zero => simp [dCGen, swapGen, dZGen]
      | succ j => simp [dCGen, swapGen, dZGen]) u

theorem dZ_swap (u : Cochain) : dZ (swap u) = swap (dC u) := (swap_dC u).symm

theorem swap_dZ (u : Cochain) : swap (dZ u) = dC (swap u) := by
  rw [← swap_swap (dC (swap u)), swap_dC, swap_swap]

theorem dZ_dZ (u : Cochain) : dZ (dZ u) = 0 := by
  rw [← swap_swap u, dZ_swap, dZ_swap, dC_dC, map_zero]

theorem swap_LC (e : Fin 3) (u : Cochain) : swap (LC e u) = LZ e (swap u) :=
  twisted_even swap (isEvenDer_colorActionOn _ e) (isEvenDer_colorActionOn _ e) (fun m => by
    rw [colorActionOn_generator, swap_generator]
    cases m with
    | c j a =>
      simp [swapGen, Mode.isC, Mode.isZ, colorActionOn_generator, colorGenerator, Mode.color,
        Mode.recolor, map_sum, map_smul]
    | b j a =>
      cases j with
      | zero => simp [swapGen, Mode.isC, Mode.isZ, colorActionOn_generator]
      | succ j => simp [swapGen, Mode.isC, Mode.isZ, colorActionOn_generator]) u

theorem swap_LZ (e : Fin 3) (u : Cochain) : swap (LZ e u) = LC e (swap u) := by
  rw [← swap_swap (LC e (swap u)), swap_LC, swap_swap]

theorem swap_LB0 (e : Fin 3) (u : Cochain) : swap (LB0 e u) = LB0 e (swap u) :=
  twisted_even swap (isEvenDer_colorActionOn _ e) (isEvenDer_colorActionOn _ e) (fun m => by
    rw [colorActionOn_generator, swap_generator]
    cases m with
    | c j a => simp [swapGen, Mode.isB0, colorActionOn_generator]
    | b j a =>
      cases j with
      | zero =>
        simp [swapGen, Mode.isB0, colorActionOn_generator, colorGenerator, Mode.color,
          Mode.recolor, map_sum, map_smul]
      | succ j => simp [swapGen, Mode.isB0, colorActionOn_generator]) u

/-! ## Equivariance -/

theorem disjoint_isC_isZ : ∀ m, Mode.isC m = true → Mode.isZ m = false := by
  intro m h; cases m with
  | c j a => rfl
  | b j a => simp [Mode.isC] at h

theorem disjoint_isC_isB0 : ∀ m, Mode.isC m = true → Mode.isB0 m = false := by
  intro m h; cases m with
  | c j a => rfl
  | b j a => simp [Mode.isC] at h

theorem disjoint_isC_isB : ∀ m, Mode.isC m = true → Mode.isB m = false := by
  intro m h; cases m with
  | c j a => rfl
  | b j a => simp [Mode.isC] at h

theorem disjoint_isZ_isB0 : ∀ m, Mode.isZ m = true → Mode.isB0 m = false := by
  intro m h; cases m with
  | c j a => rfl
  | b j a => cases j with
    | zero => simp [Mode.isZ] at h
    | succ j => rfl

theorem disjoint_isZ_isC : ∀ m, Mode.isZ m = true → Mode.isC m = false := by
  intro m h; cases m with
  | c j a => simp [Mode.isZ] at h
  | b j a => rfl

theorem disjoint_isB0_isC : ∀ m, Mode.isB0 m = true → Mode.isC m = false := by
  intro m h; cases m with
  | c j a => simp [Mode.isB0] at h
  | b j a => rfl

theorem disjoint_isB0_isZ : ∀ m, Mode.isB0 m = true → Mode.isZ m = false := by
  intro m h; cases m with
  | c j a => simp [Mode.isB0] at h
  | b j a => cases j with
    | zero => rfl
    | succ j => simp [Mode.isB0] at h

/-- Derivations on disjoint classes commute: the generic instance used below. -/
theorem comm_disjoint_odd {P Q : Mode → Bool} (hQ : ColorStable Q)
    (hPQ : ∀ m, P m = true → Q m = false) (f : Mode → Cochain) (hD : IsOddDer (extendDerivation f))
    (hf : ∀ m, P m = false → f m = 0) (hfP : ∀ m, f m ∈ pureIn P) (e : Fin 3) (v : Cochain) :
    extendDerivation f (colorActionOn Q e v) = colorActionOn Q e (extendDerivation f v) :=
  comm_odd_even hD (isEvenDer_colorActionOn Q e) (fun m =>
    generator_comm_of_disjoint hPQ f _ hf (fun m _ => hfP m) (colorActionOn_gen_of_not e)
      (colorActionOn_gen_mem hQ e) m) v

theorem dC_LZ (e : Fin 3) (v : Cochain) : dC (LZ e v) = LZ e (dC v) :=
  comm_disjoint_odd colorStable_isZ disjoint_isC_isZ dCGen isOddDer_dC dCGen_of_not
    dCGen_mem_pureIn e v

theorem dC_LB0 (e : Fin 3) (v : Cochain) : dC (LB0 e v) = LB0 e (dC v) :=
  comm_disjoint_odd colorStable_isB0 disjoint_isC_isB0 dCGen isOddDer_dC dCGen_of_not
    dCGen_mem_pureIn e v

theorem dZ_LC (e : Fin 3) (v : Cochain) : dZ (LC e v) = LC e (dZ v) :=
  comm_disjoint_odd colorStable_isC disjoint_isZ_isC dZGen isOddDer_dZ dZGen_of_not
    dZGen_mem_pureIn e v

theorem dZ_LB0 (e : Fin 3) (v : Cochain) : dZ (LB0 e v) = LB0 e (dZ v) :=
  comm_disjoint_odd colorStable_isB0 disjoint_isZ_isB0 dZGen isOddDer_dZ dZGen_of_not
    dZGen_mem_pureIn e v

theorem dG_LC (e : Fin 3) (v : Cochain) : dG (LC e v) = LC e (dG v) :=
  comm_disjoint_odd colorStable_isC disjoint_isB0_isC dGGen isOddDer_dG dGGen_of_not
    dGGen_mem_pureIn e v

theorem dG_LZ (e : Fin 3) (v : Cochain) : dG (LZ e v) = LZ e (dG v) :=
  comm_disjoint_odd colorStable_isZ disjoint_isB0_isZ dGGen isOddDer_dG dGGen_of_not
    dGGen_mem_pureIn e v

theorem dC_LC (e : Fin 3) (v : Cochain) : dC (LC e v) = LC e (dC v) :=
  comm_odd_even isOddDer_dC (isEvenDer_colorActionOn _ e) (fun m => by
    rw [colorActionOn_generator, dC_generator]
    cases m with
    | c j a =>
      simp only [Mode.isC, if_true]
      have hcg : colorGenerator e (.c j a) ∈ pureIn Mode.isC :=
        colorGenerator_mem_pureIn colorStable_isC e rfl
      rw [dC_eq_q_of_pureC hcg, colorActionOn_eq_of_pure (fun _ h => h) e
        (dCGen_mem_pureIn _), dCGen, ← q_generator, ← colorAction_generator, q_colorAction]
    | b j a => simp [Mode.isC, dCGen]) v

theorem dZ_LZ (e : Fin 3) (v : Cochain) : dZ (LZ e v) = LZ e (dZ v) := by
  rw [← swap_swap v, ← swap_LC, ← swap_dC, dZ_swap, dC_LC, swap_LC, swap_dC]

theorem dG_LB0 (e : Fin 3) (v : Cochain) : dG (LB0 e v) = LB0 e (dG v) :=
  comm_odd_even isOddDer_dG (isEvenDer_colorActionOn _ e) (fun m => by
    rw [colorActionOn_generator, dG_generator]
    cases m with
    | c j a => simp [Mode.isB0, dGGen]
    | b j a =>
      cases j with
      | succ j => simp [Mode.isB0, dGGen]
      | zero =>
        simp only [Mode.isB0, if_true, dGGen, map_smul,
          colorActionOn_bbPair e (P := Mode.isB0) (i := 0) (k := 0) (fun _ => rfl) (fun _ => rfl),
          colorGenerator, Mode.color, Mode.recolor, map_sum, dG_generator, Finset.smul_sum,
          smul_smul]
        apply Finset.sum_congr rfl; intro f _
        ring_nf) v

theorem dpp_LB (e : Fin 3) (v : Cochain) : dpp (LB e v) = LB e (dpp v) :=
  comm_odd_even isOddDer_dpp (isEvenDer_colorActionOn _ e) (fun m => by
    rw [colorActionOn_generator, dpp_generator]
    cases m with
    | c j a =>
      simp only [Mode.isB, map_zero, dppGen]
      exact (colorActionOn_pure_zero disjoint_isC_isB e (qGenerator_c_mem_pureIn j a)).symm
    | b j a =>
      simp only [Mode.isB, if_true, dppGen, map_smul, bbConv, map_sum,
        colorActionOn_bbPair e (P := Mode.isB) (fun _ => rfl) (fun _ => rfl),
        colorGenerator, Mode.color, Mode.recolor, dpp_generator, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro f _
      apply Finset.sum_congr rfl; intro i _
      ring_nf) v

/-! ## Relations on invariants -/

theorem dG_eq_half_sum (v : Cochain) :
    dG v = (1 / 2 : ℂ) • ∑ e : Fin 3, generator (.b 0 e) * LB0 e v := by
  have h := LinearMap.congr_fun b0_LB0_eq v
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply] at h
  rw [h, smul_smul]; norm_num

theorem dG_eq_zero_of_LB0 {v : Cochain} (hv : ∀ e, LB0 e v = 0) : dG v = 0 := by
  rw [dG_eq_half_sum]; simp [hv]

theorem coupling_eq_zero_of_LZ {v : Cochain} (hv : ∀ e, LZ e v = 0) : coupling v = 0 := by
  simp [coupling, LinearMap.sum_apply, hv]

/-- On `L^B`-invariants, `D'' = d_c + d_Z - d_g`. -/
theorem dpp_eq_of_LB {v : Cochain} (hv : ∀ e, LB e v = 0) : dpp v = dC v + dZ v - dG v := by
  have hZ (e : Fin 3) : LZ e v = -LB0 e v := by
    have := hv e
    rw [LB_eq, LinearMap.add_apply] at this
    exact eq_neg_of_add_eq_zero_right this
  have hc : coupling v = -((2 : ℂ) • dG v) := by
    have h := LinearMap.congr_fun b0_LB0_eq v
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.smul_apply] at h
    simp only [coupling, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, hZ,
      mul_neg, Finset.sum_neg_distrib, h]
  rw [dpp_eq]
  simp only [LinearMap.add_apply, hc, two_smul]
  abel

end KhanSL2
