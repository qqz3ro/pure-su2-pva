module

public import KhanSL2.Deformation.SourceContraction

@[expose] public section

/-!
# The source contraction identities (paper (5.3), blueprint `lem:contractions`, `cor:Aacyclic`)

On `A`, `δᴬ₁ h₁ + h₁ δᴬ₁ = E = 2S - B` and `δᴬ₀ h₀ + h₀ δᴬ₀ = T = S - B`; in general
`δᴬ_ℓ h_ℓ + h_ℓ δᴬ_ℓ = (1 + ℓ) S - B` on the piece of degree `(_, B, S)` (`anticomm_energy`).
Hence `(φ(A), δ̄_ℓ)` is exact in nonzero energy (`phi_deltaBar_exact`).
-/

noncomputable section

namespace KhanSL2.Source

open SourcePresentation

/-- The energy `(1 + ℓ) S - B` of a degree: `E = 2S - B` for `ℓ = 1`, `T = S - B` for `ℓ = 0`. -/
def energyOf (ℓ : ℕ) (d : Degree) : ℤ := (1 + ℓ) * d.2.2 - d.2.1

theorem energyOf_add (ℓ : ℕ) (d e : Degree) : energyOf ℓ (d + e) = energyOf ℓ d + energyOf ℓ e := by
  simp only [energyOf, Prod.snd_add, Prod.fst_add]
  ring

theorem energyOf_zero (ℓ : ℕ) : energyOf ℓ 0 = 0 := by simp [energyOf]

/-- `h_ℓ` lowers the degree by `(1, 2, 2 - ℓ)`. -/
theorem contraction_degree {ℓ : ℕ} (hℓ : ℓ ≤ 1) {d : Degree} {a : Source} (ha : a ∈ piece d) :
    contraction ℓ a ∈ piece (d - deltaShift ℓ) := by
  obtain ⟨e, he, rfl⟩ := ha
  induction he with
  | zero d => rw [mk_zero, map_zero]; exact Submodule.zero_mem _
  | scalar r =>
    change contraction ℓ (algebraMap ℂ Source r) ∈ _
    rw [contraction_algebraMap]; exact Submodule.zero_mem _
  | x i => change contraction ℓ (X i) ∈ _; rw [contraction_X]; exact Submodule.zero_mem _
  | y i =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
    · change contraction 0 (Y i) ∈ _
      rw [contractionZero_Y]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      · apply Submodule.smul_mem
        have h := X_mem (i - 1)
        convert h using 2
        simp only [deltaShift, Prod.mk_sub_mk]
        refine Prod.ext (by norm_num) (Prod.ext (by norm_num) ?_)
        simp only [Nat.cast_sub (by omega : 1 ≤ i)]
        push_cast; ring
    · change contraction 1 (Y i) ∈ _
      rw [contractionOne_Y]
      apply Submodule.neg_mem
      convert X_mem i using 2
      simp only [deltaShift, Prod.mk_sub_mk]
      refine Prod.ext (by norm_num) (Prod.ext (by norm_num) ?_)
      push_cast; ring
  | add _ _ ha hb =>
    rw [mk_add, map_add]
    exact Submodule.add_mem _ ha hb
  | @mul d e a b ha' hb' ha hb =>
    rw [mk_mul, contraction_mul]
    refine Submodule.add_mem _ ?_ ?_
    · have := mul_mem ha ⟨b, hb', rfl⟩
      convert this using 2
      abel
    · have hpa : parity (mk a) ∈ piece d := by
        rw [parity_of_mem ⟨a, ha', rfl⟩]
        exact Submodule.smul_mem _ _ ⟨a, ha', rfl⟩
      have := mul_mem hpa hb
      convert this using 2
      abel

/-- The anticommutator `δᴬ h + h δᴬ` is an even derivation. -/
theorem anticomm_mul {ℓ : ℕ} (hℓ : ℓ ≤ 1) (a b : Source) :
    deltaA ℓ hℓ (contraction ℓ (a * b)) + contraction ℓ (deltaA ℓ hℓ (a * b)) =
      (deltaA ℓ hℓ (contraction ℓ a) + contraction ℓ (deltaA ℓ hℓ a)) * b +
        a * (deltaA ℓ hℓ (contraction ℓ b) + contraction ℓ (deltaA ℓ hℓ b)) := by
  rw [contraction_mul, deltaA_mul, map_add, map_add, deltaA_mul, deltaA_mul, contraction_mul,
    contraction_mul, deltaA_parity, contraction_parity hℓ, parity_parity]
  noncomm_ring

/-- **The contraction identity**: `δᴬ_ℓ h_ℓ + h_ℓ δᴬ_ℓ = (1 + ℓ) S - B` on the piece of degree
`(_, B, S)`. -/
theorem anticomm_energy {ℓ : ℕ} (hℓ : ℓ ≤ 1) {d : Degree} {a : Source} (ha : a ∈ piece d) :
    deltaA ℓ hℓ (contraction ℓ a) + contraction ℓ (deltaA ℓ hℓ a) = (energyOf ℓ d : ℂ) • a := by
  obtain ⟨e, he, rfl⟩ := ha
  induction he with
  | zero d => simp
  | scalar r =>
    change deltaA ℓ hℓ (contraction ℓ (algebraMap ℂ Source r)) +
      contraction ℓ (deltaA ℓ hℓ (algebraMap ℂ Source r)) = _
    rw [contraction_algebraMap, deltaA_algebraMap, map_zero, map_zero, add_zero, energyOf_zero,
      Int.cast_zero, zero_smul]
  | x i =>
    change deltaA ℓ hℓ (contraction ℓ (X i)) + contraction ℓ (deltaA ℓ hℓ (X i)) = _
    rw [contraction_X, map_zero, zero_add]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
    · rw [deltaA_zero_X, map_smul, contractionZero_Y, Nat.add_sub_cancel, smul_smul]
      congr 1
      simp only [energyOf]
      push_cast; ring
    · rw [deltaA_one_X, map_smul, contractionOne_Y, smul_neg, ← neg_smul]
      congr 1
      simp only [energyOf]
      push_cast; ring
  | y i =>
    change deltaA ℓ hℓ (contraction ℓ (Y i)) + contraction ℓ (deltaA ℓ hℓ (Y i)) = _
    rw [deltaA_Y, map_zero, add_zero]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
    · rw [contractionZero_Y, map_smul]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [energyOf]
      · rw [deltaA_zero_X, Nat.sub_add_cancel hi, smul_smul]
        congr 1
        simp only [energyOf]
        push_cast; ring
    · rw [contractionOne_Y, map_neg, deltaA_one_X, ← neg_smul]
      congr 1
      simp only [energyOf]
      push_cast; ring
  | add _ _ ha hb =>
    rw [mk_add]
    simp only [map_add]
    rw [smul_add, ← ha, ← hb]
    abel
  | @mul d e a b _ _ ha hb =>
    rw [mk_mul, anticomm_mul, ha, hb, smul_mul_assoc, mul_smul_comm, ← add_smul, energyOf_add,
      Int.cast_add]

/-- **Exactness of the source image** (blueprint `cor:Aacyclic`): in nonzero energy, a
`δ̄_ℓ`-closed element of `φ(A_d)` is `δ̄_ℓ` of an element of `φ(A_{d - (1, 2, 2 - ℓ)})`. -/
theorem phi_deltaBar_exact {ℓ : ℕ} (hℓ : ℓ ≤ 1) {d : Degree} (hE : energyOf ℓ d ≠ 0)
    {a : Source} (ha : a ∈ piece d) (hδ : deltaBar ℓ hℓ (phi a) = 0) :
    ∃ a' ∈ piece (d - deltaShift ℓ), phi a = deltaBar ℓ hℓ (phi a') := by
  have hδA : deltaA ℓ hℓ a = 0 := phi_injective (by rw [phi_deltaA, hδ, map_zero])
  have h := anticomm_energy hℓ ha
  rw [hδA, map_zero, add_zero] at h
  have hE' : (energyOf ℓ d : ℂ) ≠ 0 := by exact_mod_cast hE
  refine ⟨(energyOf ℓ d : ℂ)⁻¹ • contraction ℓ a,
    Submodule.smul_mem _ _ (contraction_degree hℓ ha), ?_⟩
  rw [← phi_deltaA, map_smul, h, smul_smul, inv_mul_cancel₀ hE', one_smul]

end KhanSL2.Source
