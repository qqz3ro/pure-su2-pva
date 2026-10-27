module

public import KhanSL2.Deformation.RelabelOne
public import KhanSL2.CanonicalMap

@[expose] public section

/-!
# `δ_ℓ` on cohomology (blueprint `lem:deltasource`)

* `q_delta_anticomm`: `Qδ_ℓ + δ_ℓQ = 0` on invariant cochains. For `ℓ = 1` this holds on all
  cochains (`q_delta_one_anticomm`); for `ℓ = 0` it follows from `[δ₁, ∂] = δ₀`, `[Q, δ₁] = 0`
  and `[Q, ∂] = Σ c₁ᵃ Lₐ`, which vanishes on invariants.
* `deltaBar ℓ`: the induced operator on `Cohomology`; `parityBar`: the induced parity.
* `deltaBar_mul`: `δ̄` is an odd derivation of the cohomology ring.
* `deltaBar_phi_X`, `deltaBar_phi_Y`: paper (5.2),
  `δ₁ X_j = -(2j+3) Y_j`, `δ₀ X_j = -2 Y_{j+1}`, `δ_ℓ Y_j = 0`, on the images under `φ`.
-/

noncomputable section

namespace KhanSL2

/-! ## `Q` and `δ_ℓ` anticommute on invariants -/

/-- **`Qδ₀ + δ₀Q = 0` on invariant cochains.** -/
theorem q_delta_zero_anticomm {u : Cochain} (hu : u ∈ relativeInvariants) :
    q (delta 0 u) + delta 0 (q u) = 0 := by
  have hT (x : Cochain) (hx : x ∈ relativeInvariants) :
      q (translation x) = translation (q x) := q_translation_commutes hx
  have hδ1 : delta 1 u ∈ relativeInvariants := invariant_delta (le_refl 1) hu
  have e1 : delta 0 u = delta 1 (translation u) - translation (delta 1 u) :=
    (delta_one_translation u).symm
  have e2 : delta 0 (q u) = delta 1 (translation (q u)) - translation (delta 1 (q u)) :=
    (delta_one_translation (q u)).symm
  have e3 : q (delta 1 (translation u)) = -delta 1 (q (translation u)) :=
    eq_neg_of_add_eq_zero_left (q_delta_one_anticomm _)
  have e6 : q (delta 1 u) = -delta 1 (q u) := eq_neg_of_add_eq_zero_left (q_delta_one_anticomm _)
  rw [e1, e2, map_sub, e3, hT u hu, hT _ hδ1, e6, map_neg]
  abel

theorem q_delta_anticomm {ℓ : ℕ} (hℓ : ℓ ≤ 1) {u : Cochain} (hu : u ∈ relativeInvariants) :
    q (delta ℓ u) = -delta ℓ (q u) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
  · exact eq_neg_of_add_eq_zero_left (q_delta_zero_anticomm hu)
  · exact eq_neg_of_add_eq_zero_left (q_delta_one_anticomm u)

theorem delta_mem_cycles {ℓ : ℕ} (hℓ : ℓ ≤ 1) {u : Cochain} (hu : u ∈ relativeCycles) :
    delta ℓ u ∈ relativeCycles := by
  refine ⟨invariant_delta hℓ hu.1, ?_⟩
  change q (delta ℓ u) = 0
  rw [q_delta_anticomm hℓ hu.1, LinearMap.mem_ker.mp hu.2, map_zero, neg_zero]

/-! ## Induced operators on cohomology -/

/-- `δ_ℓ` on the cycle space. -/
def deltaCycles (ℓ : ℕ) (hℓ : ℓ ≤ 1) : CycleSpace →ₗ[ℂ] CycleSpace :=
  (delta ℓ).restrict (fun _ hu => delta_mem_cycles hℓ hu)

theorem deltaCycles_boundaries (ℓ : ℕ) (hℓ : ℓ ≤ 1) :
    relativeBoundaries ≤ relativeBoundaries.comap (deltaCycles ℓ hℓ) := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := hv
  refine ⟨-delta ℓ w, Submodule.neg_mem _ (invariant_delta hℓ hw), ?_⟩
  change q (-delta ℓ w) = delta ℓ (v : Cochain)
  rw [map_neg, q_delta_anticomm hℓ hw, neg_neg, hwv]
  rfl

/-- **`δ̄_ℓ`**, the operator induced on cohomology. -/
def deltaBar (ℓ : ℕ) (hℓ : ℓ ≤ 1) : Cohomology →ₗ[ℂ] Cohomology :=
  relativeBoundaries.mapQ relativeBoundaries (deltaCycles ℓ hℓ) (deltaCycles_boundaries ℓ hℓ)

theorem deltaBar_classOf (ℓ : ℕ) (hℓ : ℓ ≤ 1) (u : Cochain) (hu : u ∈ relativeCycles) :
    deltaBar ℓ hℓ (classOf u hu) = classOf (delta ℓ u) (delta_mem_cycles hℓ hu) := rfl

/-- Parity on the cycle space. -/
def parityCycles : CycleSpace →ₗ[ℂ] CycleSpace :=
  (cochainParity.toLinearMap).restrict (fun _ hu => cycle_parity hu)

theorem parityCycles_boundaries :
    relativeBoundaries ≤ relativeBoundaries.comap parityCycles := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := hv
  refine ⟨-cochainParity w, Submodule.neg_mem _ (invariant_parity hw), ?_⟩
  change q (-cochainParity w) = cochainParity (v : Cochain)
  rw [map_neg, q_parity, neg_neg, hwv]
  rfl

/-- The parity involution of the cohomology ring. -/
def parityBar : Cohomology →ₗ[ℂ] Cohomology :=
  relativeBoundaries.mapQ relativeBoundaries parityCycles parityCycles_boundaries

theorem parityBar_classOf (u : Cochain) (hu : u ∈ relativeCycles) :
    parityBar (classOf u hu) = classOf (cochainParity u) (cycle_parity hu) := rfl

theorem classOf_congr {u v : Cochain} (huv : u = v) (hu : u ∈ relativeCycles)
    (hv : v ∈ relativeCycles) : classOf u hu = classOf v hv := by
  subst huv
  rfl

theorem classOf_add' (u v : Cochain) (hu : u ∈ relativeCycles) (hv : v ∈ relativeCycles)
    (huv : u + v ∈ relativeCycles) : classOf (u + v) huv = classOf u hu + classOf v hv := rfl

theorem classOf_smul' (r : ℂ) (u : Cochain) (hu : u ∈ relativeCycles)
    (hru : r • u ∈ relativeCycles) : classOf (r • u) hru = r • classOf u hu := rfl

theorem classOf_neg' (u : Cochain) (hu : u ∈ relativeCycles) (hnu : -u ∈ relativeCycles) :
    classOf (-u) hnu = -classOf u hu := rfl

/-- Every cohomology class is the class of a cycle. -/
theorem exists_classOf (x : Cohomology) : ∃ u, ∃ hu : u ∈ relativeCycles, classOf u hu = x := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨u, hu, rfl⟩

/-- **`δ̄_ℓ` is an odd derivation** of the cohomology ring. -/
theorem deltaBar_mul (ℓ : ℕ) (hℓ : ℓ ≤ 1) (x y : Cohomology) :
    deltaBar ℓ hℓ (targetData.mul x y) =
      targetData.mul (deltaBar ℓ hℓ x) y + targetData.mul (parityBar x) (deltaBar ℓ hℓ y) := by
  obtain ⟨u, hu, rfl⟩ := exists_classOf x
  obtain ⟨v, hv, rfl⟩ := exists_classOf y
  rw [target_mul_classOf, deltaBar_classOf, deltaBar_classOf, deltaBar_classOf,
    parityBar_classOf, target_mul_classOf, target_mul_classOf, ← classOf_add' _ _ _ _
      (Submodule.add_mem _ (cycle_wedge (delta_mem_cycles hℓ hu) hv)
        (cycle_wedge (cycle_parity hu) (delta_mem_cycles hℓ hv)))]
  exact classOf_congr (delta_wedge ℓ u v) _ _

theorem parityBar_mul (x y : Cohomology) :
    parityBar (targetData.mul x y) = targetData.mul (parityBar x) (parityBar y) := by
  obtain ⟨u, hu, rfl⟩ := exists_classOf x
  obtain ⟨v, hv, rfl⟩ := exists_classOf y
  rw [target_mul_classOf, parityBar_classOf, parityBar_classOf, parityBar_classOf,
    target_mul_classOf]
  exact classOf_congr (by rw [← cochain_mul_eq_wedge, map_mul, cochain_mul_eq_wedge]) _ _

theorem deltaBar_parityBar (ℓ : ℕ) (hℓ : ℓ ≤ 1) (x : Cohomology) :
    deltaBar ℓ hℓ (parityBar x) = -parityBar (deltaBar ℓ hℓ x) := by
  obtain ⟨u, hu, rfl⟩ := exists_classOf x
  rw [parityBar_classOf, deltaBar_classOf, deltaBar_classOf, parityBar_classOf,
    ← classOf_neg' _ _ (Submodule.neg_mem _ (cycle_parity (delta_mem_cycles hℓ hu)))]
  exact classOf_congr (delta_parity hℓ u) _ _

theorem parityBar_parityBar (x : Cohomology) : parityBar (parityBar x) = x := by
  obtain ⟨u, hu, rfl⟩ := exists_classOf x
  rw [parityBar_classOf, parityBar_classOf]
  exact classOf_congr (cochainParity_involutive u) _ _

theorem deltaBar_one (ℓ : ℕ) (hℓ : ℓ ≤ 1) : deltaBar ℓ hℓ targetData.one = 0 := by
  rw [target_one_classOf, deltaBar_classOf]
  rw [classOf_congr (delta_cochainOne ℓ) _ (Submodule.zero_mem _)]
  rfl

theorem parityBar_one : parityBar targetData.one = targetData.one := by
  rw [target_one_classOf, parityBar_classOf]
  exact classOf_congr cochainParity_one _ _

/-! ## Translation -/

theorem deltaBar_one_translation (x : Cohomology) :
    deltaBar 1 (le_refl 1) (targetData.translation x) =
      targetData.translation (deltaBar 1 (le_refl 1) x) + deltaBar 0 zero_le_one x := by
  obtain ⟨u, hu, rfl⟩ := exists_classOf x
  simp only [target_translation_classOf, deltaBar_classOf]
  rw [← classOf_add' _ _ _ _ (Submodule.add_mem _
    (CohomologyDescent.cycle_translation relativeComplex_laws.translation_commutes
      (delta_mem_cycles (le_refl 1) hu)) (delta_mem_cycles zero_le_one hu))]
  exact classOf_congr (by rw [← delta_one_translation u]; abel) _ _

theorem deltaBar_zero_translation (x : Cohomology) :
    deltaBar 0 zero_le_one (targetData.translation x) =
      targetData.translation (deltaBar 0 zero_le_one x) := by
  obtain ⟨u, hu, rfl⟩ := exists_classOf x
  simp only [target_translation_classOf, deltaBar_classOf]
  exact classOf_congr (delta_zero_translation u) _ _

theorem parityBar_translation (x : Cohomology) :
    parityBar (targetData.translation x) = targetData.translation (parityBar x) := by
  obtain ⟨u, hu, rfl⟩ := exists_classOf x
  simp only [target_translation_classOf, parityBar_classOf]
  exact classOf_congr (translation_parity u).symm _ _

end KhanSL2
