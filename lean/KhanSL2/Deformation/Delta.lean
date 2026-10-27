module

public import KhanSL2.Deformation.Derivations
public import KhanSL2.CETranslation

@[expose] public section

/-!
# The deformation operators `δ₀`, `δ₁` (paper (5.1), blueprint `def:delta`, `lem:deltalaws`)

`δ_ℓ` is the odd derivation with `δ_ℓ b_j = 0` and
`δ_ℓ c^a_n = -½ Σ_{i+k=n-ℓ} ε_{abc} b^b_i b^c_k`. Lean's `Mode.c j a` is the paper's `c^a_{j+1}`.

Proved here, on all cochains:
* `δ_ℓ` is an odd derivation of degree `(1, 2, 2 - ℓ)` (`delta_degree`);
* `δ_ℓ² = 0` (`delta_delta`);
* `δ_ℓ` commutes with the colour action, hence preserves invariants (`delta_colorAction`);
* `[δ₁, ∂] = δ₀` and `[δ₀, ∂] = 0` (`delta_one_translation`, `delta_zero_translation`).
-/

noncomputable section

namespace KhanSL2

/-- The colour-contracted pair `Σ_{b,c} ε_{abc} b^b_i b^c_k`. -/
def bbPair (i k : ℕ) (a : Fin 3) : Cochain :=
  ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c • (generator (.b i b) * generator (.b k c))

/-- The convolution `Σ_{i+k=n} ε_{abc} b^b_i b^c_k`. -/
def bbConv (n : ℕ) (a : Fin 3) : Cochain :=
  ∑ i ∈ Finset.range (n + 1), bbPair i (n - i) a

/-- Generator values of `δ_ℓ`. -/
def deltaGenerator (ℓ : ℕ) : Mode → Cochain
  | .b _ _ => 0
  | .c j a => (-(1 / 2 : ℂ)) • bbConv (j + 1 - ℓ) a

/-- **The deformation `δ_ℓ`** (paper (5.1)). -/
def delta (ℓ : ℕ) : Cochain →ₗ[ℂ] Cochain := extendDerivation (deltaGenerator ℓ)

@[simp] theorem delta_generator (ℓ : ℕ) (m : Mode) :
    delta ℓ (generator m) = deltaGenerator ℓ m :=
  extendDerivation_generator _ m

@[simp] theorem delta_cochainOne (ℓ : ℕ) : delta ℓ cochainOne = 0 :=
  extendDerivation_one _

@[simp] theorem deltaGenerator_b (ℓ j : ℕ) (a : Fin 3) : deltaGenerator ℓ (.b j a) = 0 := rfl

theorem deltaGenerator_c (ℓ j : ℕ) (a : Fin 3) :
    deltaGenerator ℓ (.c j a) = (-(1 / 2 : ℂ)) • bbConv (j + 1 - ℓ) a := rfl

/-- `δ₀ c_n = δ₁ c_{n+1}` on generators. -/
theorem deltaGenerator_zero_c (j : ℕ) (a : Fin 3) :
    deltaGenerator 0 (.c j a) = deltaGenerator 1 (.c (j + 1) a) := by
  simp only [deltaGenerator_c, Nat.sub_zero, Nat.add_sub_cancel]

/-! ## Degrees and parity -/

theorem bbPair_mem (i k : ℕ) (a : Fin 3) :
    bbPair i k a ∈ cochainPiece (2, 2, (i : ℤ) + k + 2) := by
  apply (cochainPiece _).sum_mem
  intro b _
  apply (cochainPiece _).sum_mem
  intro c _
  apply (cochainPiece _).smul_mem
  have hdeg : ((1, ((Mode.b i b).bCount : ℤ), ((Mode.b i b).weight : ℤ)) : Degree) +
      (1, ((Mode.b k c).bCount : ℤ), ((Mode.b k c).weight : ℤ)) =
      (2, 2, (i : ℤ) + k + 2) := by
    simp only [Mode.bCount, Mode.weight, Nat.cast_one, Prod.mk_add_mk, Nat.cast_add]
    refine Prod.ext (by norm_num) (Prod.ext (by norm_num) (by simp only; ring))
  rw [← hdeg]
  exact cochain_wedge_mem (cochain_generator_mem _) (cochain_generator_mem _)

theorem bbConv_mem (n : ℕ) (a : Fin 3) : bbConv n a ∈ cochainPiece (2, 2, (n : ℤ) + 2) := by
  apply (cochainPiece _).sum_mem
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have h := bbPair_mem i (n - i) a
  rwa [show (i : ℤ) + ((n - i : ℕ) : ℤ) = n by push_cast [Nat.cast_sub (by omega : i ≤ n)]; ring]
    at h

/-- The degree shift of `δ_ℓ`: total degree `+1`, `b`-count `+2`, spin `+(2-ℓ)`. -/
def deltaShift (ℓ : ℕ) : Degree := (1, 2, 2 - (ℓ : ℤ))

theorem deltaGenerator_degree {ℓ : ℕ} (hℓ : ℓ ≤ 1) (m : Mode) :
    deltaGenerator ℓ m ∈ cochainPiece ((1, (m.bCount : ℤ), (m.weight : ℤ)) + deltaShift ℓ) := by
  cases m with
  | b j a => exact Submodule.zero_mem _
  | c j a =>
    rw [deltaGenerator_c]
    apply Submodule.smul_mem
    have h := bbConv_mem (j + 1 - ℓ) a
    convert h using 2
    simp only [Mode.bCount, Mode.weight, deltaShift, Prod.mk_add_mk, Nat.cast_zero,
      Nat.cast_sub (by omega : ℓ ≤ j + 1)]
    refine Prod.ext (by norm_num) (Prod.ext (by norm_num) (by simp only; push_cast; ring))

theorem delta_degree {ℓ : ℕ} (hℓ : ℓ ≤ 1) {d : Degree} {u : Cochain}
    (hu : u ∈ cochainPiece d) : delta ℓ u ∈ cochainPiece (d + deltaShift ℓ) :=
  extendDerivation_degree (deltaGenerator ℓ) (deltaShift ℓ) (deltaGenerator_degree hℓ) hu

theorem bbConv_parity (n : ℕ) (a : Fin 3) : cochainParity (bbConv n a) = bbConv n a := by
  simpa [koszulSign] using cochainParity_of_mem (bbConv_mem n a)

theorem deltaGenerator_parity (ℓ : ℕ) (m : Mode) :
    cochainParity (deltaGenerator ℓ m) = deltaGenerator ℓ m := by
  cases m with
  | b j a => simp
  | c j a => rw [deltaGenerator_c, map_smul, bbConv_parity]

theorem delta_wedge (ℓ : ℕ) (u v : Cochain) :
    delta ℓ (wedge u v) = wedge (delta ℓ u) v + wedge (cochainParity u) (delta ℓ v) := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
    (deltaGenerator ℓ) u v (cochainParity u)
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_even Mode.code Mode.code_injective
    (deltaGenerator ℓ m) (deltaGenerator_parity ℓ m) (cochainParity u)).symm

theorem delta_mul (ℓ : ℕ) (u v : Cochain) :
    delta ℓ (u * v) = delta ℓ u * v + cochainParity u * delta ℓ v := delta_wedge ℓ u v

theorem delta_parity {ℓ : ℕ} (hℓ : ℓ ≤ 1) (u : Cochain) :
    delta ℓ (cochainParity u) = -cochainParity (delta ℓ u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv, neg_add]
  | single s r =>
    have hpar := cochainParity_of_mem (delta_degree hℓ (cochain_single_mem s r))
    have hsign : koszulSign (1, 0, 0) (monomialDegree s + deltaShift ℓ) =
        (-1 : ℂ) ^ (s.card + 1) := by
      rw [nat_parity_sign]
      simp only [koszulSign, monomialDegree, deltaShift, Prod.fst_add, Nat.cast_add,
        Nat.cast_one, one_mul]
    rw [hpar, hsign]
    change delta ℓ (FiniteExterior.parityLinear (Finsupp.single s r)) = _
    rw [FiniteExterior.parity_single, map_smul, pow_succ, mul_neg_one, neg_smul, neg_neg]

theorem isOddDer_delta {ℓ : ℕ} (hℓ : ℓ ≤ 1) : IsOddDer (delta ℓ) :=
  ⟨delta_mul ℓ, delta_parity hℓ⟩

/-! ## `δ² = 0` -/

theorem delta_bbPair (ℓ i k : ℕ) (a : Fin 3) : delta ℓ (bbPair i k a) = 0 := by
  simp [bbPair, map_sum, map_smul, delta_mul]

theorem delta_bbConv (ℓ n : ℕ) (a : Fin 3) : delta ℓ (bbConv n a) = 0 := by
  simp [bbConv, map_sum, delta_bbPair]

/-- **`δ_ℓ² = 0`** on all cochains. -/
theorem delta_delta {ℓ : ℕ} (hℓ : ℓ ≤ 1) (u : Cochain) : delta ℓ (delta ℓ u) = 0 := by
  have h := (isOddDer_delta hℓ).anticommutator (isOddDer_delta hℓ)
  have h0 : (delta ℓ ∘ₗ delta ℓ + delta ℓ ∘ₗ delta ℓ) = 0 := by
    have hz : IsEvenDer (0 : Cochain →ₗ[ℂ] Cochain) := ⟨fun _ _ => by simp, fun _ => by simp⟩
    apply h.ext hz
    intro m
    cases m with
    | b j a => simp
    | c j a => simp [deltaGenerator_c, delta_bbConv]
  have h2 : (2 : ℂ) • delta ℓ (delta ℓ u) = 0 := by
    rw [two_smul]
    exact LinearMap.congr_fun h0 u
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-! ## Colour equivariance -/

theorem colorAction_bbPair (e a : Fin 3) (i k : ℕ) :
    colorAction e (bbPair i k a) = ∑ f : Fin 3, epsilon e a f • bbPair i k f := by
  simp only [bbPair, map_sum, map_smul, colorAction_mul, colorAction_generator,
    colorGenerator, Mode.color, Mode.recolor, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_smul]
  fin_cases e <;> fin_cases a <;>
    simp [Fin.sum_univ_three, epsilon] <;> module

theorem colorAction_bbConv (e : Fin 3) (n : ℕ) (a : Fin 3) :
    colorAction e (bbConv n a) = ∑ f : Fin 3, epsilon e a f • bbConv n f := by
  simp only [bbConv, map_sum, colorAction_bbPair, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem delta_colorAction_generator (ℓ : ℕ) (e : Fin 3) (m : Mode) :
    delta ℓ (colorAction e (generator m)) = colorAction e (delta ℓ (generator m)) := by
  cases m with
  | b j a =>
    simp [colorGenerator, Mode.color, Mode.recolor]
  | c j a =>
    simp only [colorAction_generator, colorGenerator, Mode.color, Mode.recolor, map_sum,
      map_smul, delta_generator, deltaGenerator_c, colorAction_bbConv, Finset.smul_sum,
      smul_smul]
    apply Finset.sum_congr rfl
    intro f _
    rw [mul_comm]

/-- **`δ_ℓ` commutes with the colour action.** -/
theorem delta_colorAction {ℓ : ℕ} (hℓ : ℓ ≤ 1) (e : Fin 3) (u : Cochain) :
    delta ℓ (colorAction e u) = colorAction e (delta ℓ u) := by
  have h := (isOddDer_delta hℓ).commutator (isEvenDer_colorAction e)
  have hz : IsOddDer (0 : Cochain →ₗ[ℂ] Cochain) := ⟨fun _ _ => by simp, fun _ => by simp⟩
  have h0 := h.ext hz (fun m => by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      delta_colorAction_generator, sub_self])
  have := LinearMap.congr_fun h0 u
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    sub_eq_zero] at this
  exact this

theorem invariant_delta {ℓ : ℕ} (hℓ : ℓ ≤ 1) {u : Cochain} (hu : u ∈ relativeInvariants) :
    delta ℓ u ∈ relativeInvariants := by
  rw [mem_relativeInvariants_iff] at hu ⊢
  intro a
  rw [← delta_colorAction hℓ, hu a, map_zero]

/-! ## Translation -/

theorem isEvenDer_translation : IsEvenDer translation :=
  ⟨translation_mul, translation_parity⟩

theorem translation_bbPair (i k : ℕ) (a : Fin 3) :
    translation (bbPair i k a) =
      ((i + 1 : ℕ) : ℂ) • bbPair (i + 1) k a + ((k + 1 : ℕ) : ℂ) • bbPair i (k + 1) a := by
  simp only [bbPair, map_sum, map_smul, translation_mul, translation_generator,
    translationGenerator, Mode.translationCoefficient, Mode.next, smul_mul_assoc,
    mul_smul_comm, smul_add, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  congr 1 <;> congr 1 <;> push_cast <;> ring

theorem translation_bbConv (n : ℕ) (a : Fin 3) :
    translation (bbConv n a) = ((n + 1 : ℕ) : ℂ) • bbConv (n + 1) a := by
  set A : ℕ → Cochain := fun i => bbPair i (n + 1 - i) a with hA
  have h1 : ∀ i ∈ Finset.range (n + 1), translation (bbPair i (n - i) a) =
      ((i + 1 : ℕ) : ℂ) • A (i + 1) + ((n + 1 - i : ℕ) : ℂ) • A i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [translation_bbPair]
    simp only [hA, show n + 1 - (i + 1) = n - i by omega, show n - i + 1 = n + 1 - i by omega]
  rw [bbConv, map_sum, Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have hs1 : (∑ i ∈ Finset.range (n + 1), ((i + 1 : ℕ) : ℂ) • A (i + 1)) =
      ∑ i ∈ Finset.range (n + 1 + 1), ((i : ℕ) : ℂ) • A i := by
    rw [Finset.sum_range_succ' (fun i => ((i : ℕ) : ℂ) • A i) (n + 1)]
    simp
  have hs2 : (∑ i ∈ Finset.range (n + 1), ((n + 1 - i : ℕ) : ℂ) • A i) =
      ∑ i ∈ Finset.range (n + 1 + 1), ((n + 1 - i : ℕ) : ℂ) • A i := by
    rw [Finset.sum_range_succ (fun i => ((n + 1 - i : ℕ) : ℂ) • A i) (n + 1)]
    simp
  rw [hs1, hs2, ← Finset.sum_add_distrib, bbConv, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [← add_smul, ← Nat.cast_add, show i + (n + 1 - i) = n + 1 by omega]

theorem delta_translation_generator (ℓ : ℕ) (j : ℕ) (a : Fin 3) :
    delta ℓ (translation (generator (.c j a))) - translation (delta ℓ (generator (.c j a))) =
      (-(1 / 2 : ℂ)) • (((j + 2 : ℕ) : ℂ) • bbConv (j + 2 - ℓ) a -
        ((j + 1 - ℓ + 1 : ℕ) : ℂ) • bbConv (j + 1 - ℓ + 1) a) := by
  simp only [translation_generator, translationGenerator, Mode.translationCoefficient,
    Mode.next, map_smul, delta_generator, deltaGenerator_c, translation_bbConv]
  rw [show j + 1 + 1 - ℓ = j + 2 - ℓ by omega]
  module

/-- **`[δ₁, ∂] = δ₀`** on all cochains. -/
theorem delta_one_translation (u : Cochain) :
    delta 1 (translation u) - translation (delta 1 u) = delta 0 u := by
  have h := (isOddDer_delta (le_refl 1)).commutator isEvenDer_translation
  have h' := h.ext (isOddDer_delta (zero_le_one)) (fun m => by
    cases m with
    | b j a => simp [translationGenerator, Mode.next]
    | c j a =>
      simp only [LinearMap.sub_apply, LinearMap.comp_apply]
      rw [delta_translation_generator, delta_generator, deltaGenerator_c]
      rw [show j + 2 - 1 = j + 1 by omega, show j + 1 - 1 + 1 = j + 1 by omega,
        show j + 1 - 0 = j + 1 by omega]
      rw [show ((j + 2 : ℕ) : ℂ) = ((j + 1 : ℕ) : ℂ) + 1 by push_cast; ring, add_smul,
        one_smul, add_sub_cancel_left])
  exact LinearMap.congr_fun h' u

/-- **`[δ₀, ∂] = 0`** on all cochains. -/
theorem delta_zero_translation (u : Cochain) :
    delta 0 (translation u) = translation (delta 0 u) := by
  have h := (isOddDer_delta (zero_le_one)).commutator isEvenDer_translation
  have hz : IsOddDer (0 : Cochain →ₗ[ℂ] Cochain) := ⟨fun _ _ => by simp, fun _ => by simp⟩
  have h' := h.ext hz (fun m => by
    cases m with
    | b j a => simp [translationGenerator, Mode.next]
    | c j a =>
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply]
      rw [delta_translation_generator]
      rw [show j + 2 - 0 = j + 2 by omega, show j + 1 - 0 + 1 = j + 2 by omega, sub_self,
        smul_zero])
  have := LinearMap.congr_fun h' u
  simpa [sub_eq_zero] using this

end KhanSL2
