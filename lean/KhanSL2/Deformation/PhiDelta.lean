module

public import KhanSL2.Deformation.GeneratorImages
public import KhanSL2.Injectivity

@[expose] public section

/-!
# The source operators `δᴬ_ℓ` (blueprint `lem:deltasource`)

`δ̄_ℓ` preserves `φ(A)` (`deltaBar_phi_mem_range`). Since `φ` is injective (`phi_injective`),
there is a unique linear `δᴬ_ℓ : A → A` with `φ ∘ δᴬ_ℓ = δ̄_ℓ ∘ φ` (`phi_deltaA`). It is an odd
derivation of `A` (`deltaA_mul`, `deltaA_parity`) with
`δᴬ₁ X_j = -(2j+3) Y_j`, `δᴬ₀ X_j = -2 Y_{j+1}`, `δᴬ_ℓ Y_j = 0` (paper (5.2)).
-/

noncomputable section

namespace KhanSL2

open Source

theorem xRepresentative_parity : cochainParity xRepresentative = xRepresentative := by
  simpa [koszulSign] using cochainParity_of_mem xRepresentative_degree

theorem yRepresentative_parity : cochainParity yRepresentative = -yRepresentative := by
  simpa [koszulSign] using cochainParity_of_mem yRepresentative_degree

/-! ## On the classes `x₀`, `y₀` -/

abbrev T : Module.End ℂ Cohomology := targetData.translation

theorem deltaBar_one_xClass : deltaBar 1 (le_refl 1) xClass = (-3 : ℂ) • yClass := by
  rw [xClass, yClass, deltaBar_classOf, ← classOf_smul' _ _ _ (Submodule.smul_mem _ _
    yRepresentative_mem_cycles)]
  exact classOf_congr delta_one_xRepresentative _ _

theorem deltaBar_zero_xClass : deltaBar 0 zero_le_one xClass = (-2 : ℂ) • T yClass := by
  rw [xClass, yClass, deltaBar_classOf, target_translation_classOf,
    ← classOf_smul' _ _ _ (Submodule.smul_mem _ _ (CohomologyDescent.cycle_translation
      relativeComplex_laws.translation_commutes yRepresentative_mem_cycles))]
  exact classOf_congr delta_zero_xRepresentative _ _

theorem deltaBar_yClass (ℓ : ℕ) (hℓ : ℓ ≤ 1) : deltaBar ℓ hℓ yClass = 0 := by
  rw [yClass, deltaBar_classOf]
  rw [classOf_congr (delta_yRepresentative ℓ) _ (Submodule.zero_mem _)]
  rfl

theorem parityBar_xClass : parityBar xClass = xClass := by
  rw [xClass, parityBar_classOf]
  exact classOf_congr xRepresentative_parity _ _

theorem parityBar_yClass : parityBar yClass = -yClass := by
  rw [yClass, parityBar_classOf, ← classOf_neg' _ _ (Submodule.neg_mem _
    yRepresentative_mem_cycles)]
  exact classOf_congr yRepresentative_parity _ _

/-! ## Iterated translates -/

theorem deltaBar_zero_T_pow (j : ℕ) (x : Cohomology) :
    deltaBar 0 zero_le_one ((T ^ j) x) = (T ^ j) (deltaBar 0 zero_le_one x) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      deltaBar_zero_translation, ih]

theorem parityBar_T_pow (j : ℕ) (x : Cohomology) :
    parityBar ((T ^ j) x) = (T ^ j) (parityBar x) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      parityBar_translation, ih]

theorem deltaBar_one_T_pow_xClass (j : ℕ) :
    deltaBar 1 (le_refl 1) ((T ^ j) xClass) = (-(2 * j + 3 : ℂ)) • (T ^ j) yClass := by
  induction j with
  | zero => simp [deltaBar_one_xClass]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, deltaBar_one_translation, ih, map_smul,
      deltaBar_zero_T_pow, deltaBar_zero_xClass, map_smul, ← Module.End.mul_apply (T ^ j),
      ← pow_succ, ← Module.End.mul_apply T, ← pow_succ', ← add_smul]
    push_cast
    ring_nf

theorem deltaBar_T_pow_yClass (ℓ : ℕ) (hℓ : ℓ ≤ 1) (j : ℕ) :
    deltaBar ℓ hℓ ((T ^ j) yClass) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
  · rw [deltaBar_zero_T_pow, deltaBar_yClass, map_zero]
  · induction j with
    | zero => exact deltaBar_yClass 1 _
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, deltaBar_one_translation, ih, map_zero, zero_add,
        deltaBar_zero_T_pow, deltaBar_yClass, map_zero]

/-! ## On `φ` of the generators -/

theorem deltaBar_one_phi_X (j : ℕ) :
    deltaBar 1 (le_refl 1) (phi (X j)) = phi ((-(2 * j + 3 : ℂ)) • Y j) := by
  rw [phi_X, deltaBar_one_T_pow_xClass, map_smul, phi_Y]

theorem deltaBar_zero_phi_X (j : ℕ) :
    deltaBar 0 zero_le_one (phi (X j)) = phi ((-2 : ℂ) • Y (j + 1)) := by
  rw [phi_X, deltaBar_zero_T_pow, deltaBar_zero_xClass, map_smul, map_smul, phi_Y,
    pow_succ, Module.End.mul_apply]

theorem deltaBar_phi_Y (ℓ : ℕ) (hℓ : ℓ ≤ 1) (j : ℕ) : deltaBar ℓ hℓ (phi (Y j)) = 0 := by
  rw [phi_Y, deltaBar_T_pow_yClass]

theorem phi_algebraMap (r : ℂ) : phi (algebraMap ℂ Source r) = r • targetData.one := rfl

theorem phi_parity (a : Source) : phi (parity a) = parityBar (phi a) := by
  induction a using Source.inductionOn with
  | scalar r => rw [AlgHom.commutes, phi_algebraMap, map_smul, parityBar_one]
  | hx i => rw [parity_X, phi_X, parityBar_T_pow, parityBar_xClass]
  | hy i => rw [parity_Y, map_neg, phi_Y, parityBar_T_pow, parityBar_yClass, map_neg]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => rw [map_mul, phi_mul, phi_mul, ha, hb, parityBar_mul]

theorem deltaBar_phi_algebraMap (ℓ : ℕ) (hℓ : ℓ ≤ 1) (r : ℂ) :
    deltaBar ℓ hℓ (phi (algebraMap ℂ Source r)) = 0 := by
  rw [phi_algebraMap, map_smul, deltaBar_one, smul_zero]

/-- **`δ̄_ℓ` preserves the source image.** -/
theorem deltaBar_phi_mem_range (ℓ : ℕ) (hℓ : ℓ ≤ 1) (a : Source) :
    deltaBar ℓ hℓ (phi a) ∈ LinearMap.range phi := by
  induction a using Source.inductionOn with
  | scalar r => rw [deltaBar_phi_algebraMap]; exact Submodule.zero_mem _
  | hx i =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
    · exact ⟨_, (deltaBar_zero_phi_X i).symm⟩
    · exact ⟨_, (deltaBar_one_phi_X i).symm⟩
  | hy i => rw [deltaBar_phi_Y]; exact Submodule.zero_mem _
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  | mul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    rw [phi_mul, deltaBar_mul, ← ha', ← hb', ← phi_parity, ← phi_mul, ← phi_mul, ← map_add]
    exact ⟨_, rfl⟩

/-! ## The source operator -/

/-- **`δᴬ_ℓ`**: the source operator with `φ ∘ δᴬ_ℓ = δ̄_ℓ ∘ φ`. -/
def deltaA (ℓ : ℕ) (hℓ : ℓ ≤ 1) : Source →ₗ[ℂ] Source :=
  (LinearEquiv.ofInjective phi phi_injective).symm.toLinearMap ∘ₗ
    (deltaBar ℓ hℓ ∘ₗ phi).codRestrict (LinearMap.range phi)
      (fun a => deltaBar_phi_mem_range ℓ hℓ a)

theorem phi_deltaA (ℓ : ℕ) (hℓ : ℓ ≤ 1) (a : Source) :
    phi (deltaA ℓ hℓ a) = deltaBar ℓ hℓ (phi a) := by
  change ((LinearEquiv.ofInjective phi phi_injective)
    ((LinearEquiv.ofInjective phi phi_injective).symm
      ⟨deltaBar ℓ hℓ (phi a), deltaBar_phi_mem_range ℓ hℓ a⟩) : Cohomology) = _
  rw [LinearEquiv.apply_symm_apply]

theorem deltaA_mul (ℓ : ℕ) (hℓ : ℓ ≤ 1) (a b : Source) :
    deltaA ℓ hℓ (a * b) = deltaA ℓ hℓ a * b + parity a * deltaA ℓ hℓ b := by
  apply phi_injective
  rw [phi_deltaA, phi_mul, deltaBar_mul, map_add, phi_mul, phi_mul, phi_deltaA, phi_deltaA,
    phi_parity]

theorem deltaA_parity (ℓ : ℕ) (hℓ : ℓ ≤ 1) (a : Source) :
    deltaA ℓ hℓ (parity a) = -parity (deltaA ℓ hℓ a) := by
  apply phi_injective
  rw [phi_deltaA, phi_parity, deltaBar_parityBar, map_neg, phi_parity, phi_deltaA]

theorem deltaA_one_X (j : ℕ) : deltaA 1 (le_refl 1) (X j) = (-(2 * j + 3 : ℂ)) • Y j := by
  apply phi_injective
  rw [phi_deltaA, deltaBar_one_phi_X]

theorem deltaA_zero_X (j : ℕ) : deltaA 0 zero_le_one (X j) = (-2 : ℂ) • Y (j + 1) := by
  apply phi_injective
  rw [phi_deltaA, deltaBar_zero_phi_X]

theorem deltaA_Y (ℓ : ℕ) (hℓ : ℓ ≤ 1) (j : ℕ) : deltaA ℓ hℓ (Y j) = 0 := by
  apply phi_injective
  rw [phi_deltaA, deltaBar_phi_Y, map_zero]

theorem deltaA_algebraMap (ℓ : ℕ) (hℓ : ℓ ≤ 1) (r : ℂ) :
    deltaA ℓ hℓ (algebraMap ℂ Source r) = 0 := by
  apply phi_injective
  rw [phi_deltaA, deltaBar_phi_algebraMap, map_zero]

end KhanSL2
