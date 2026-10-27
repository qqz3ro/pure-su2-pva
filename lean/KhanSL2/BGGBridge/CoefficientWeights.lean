module

public import KhanSL2.BGG.CurrentBasis
public import KhanSL2.Chains.Grading

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # Cartan weights in the fixed coefficient degree

Each root-current generator has Cartan half-weight in `{-1,0,1}`. Thus a
coefficient exterior monomial of degree B has half-weight between -B and B.
The same bound holds for every simultaneous degree/Cartan eigenvector.
-/

noncomputable section
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- Root-current basis with the lexicographic order needed by the exterior basis. -/
def coefficientRootBasis : Module.Basis Idx ℂ Cur := currentBasis.reindex toLex

@[simp] theorem coefficientRootBasis_apply (q : Idx) :
    coefficientRootBasis q = currentBasis (ofLex q) := by
  rw [coefficientRootBasis, Module.Basis.reindex_apply]
  rfl

/-- Cartan half-weights of the root colors `e,h,f`. -/
def coefficientHalfWeight (a : Fin 3) : ℤ := ![1, 0, -1] a

theorem coefficientHalfWeight_bounds (a : Fin 3) :
    -1 ≤ coefficientHalfWeight a ∧ coefficientHalfWeight a ≤ 1 := by
  fin_cases a <;> norm_num [coefficientHalfWeight]

theorem rootWeight_eq_twice (a : Fin 3) :
    rootWeight a = (2 : ℂ) * (coefficientHalfWeight a : ℂ) := by
  fin_cases a <;> norm_num [rootWeight, coefficientHalfWeight]

/-- Integer half-weight of an exterior root monomial. -/
def coefficientMonomialWeight (s : Finset Idx) : ℤ :=
  ∑ q ∈ s, coefficientHalfWeight (ofLex q).2

theorem coefficientMonomialWeight_bounds (s : Finset Idx) :
    -(s.card : ℤ) ≤ coefficientMonomialWeight s ∧
      coefficientMonomialWeight s ≤ (s.card : ℤ) := by
  constructor
  · calc
      -(s.card : ℤ) = ∑ _q ∈ s, (-1 : ℤ) := by simp
      _ ≤ coefficientMonomialWeight s :=
        Finset.sum_le_sum fun q _ => (coefficientHalfWeight_bounds (ofLex q).2).1
  · calc
      coefficientMonomialWeight s ≤ ∑ _q ∈ s, (1 : ℤ) :=
        Finset.sum_le_sum fun q _ => (coefficientHalfWeight_bounds (ofLex q).2).2
      _ = (s.card : ℤ) := by simp

/-- Cartan action is diagonal in the root exterior basis. -/
theorem coefficientCartan_basis (s : Finset Idx) :
    ⁅constant MatrixSL2.h, coefficientRootBasis.ExteriorAlgebra s⁆ =
      ((2 : ℂ) * (coefficientMonomialWeight s : ℂ)) •
        coefficientRootBasis.ExteriorAlgebra s := by
  change LieChains.derivExt (adCur (constant MatrixSL2.h)) _ = _
  rw [LieChains.derivExt_basis coefficientRootBasis (adCur (constant MatrixSL2.h))
    (fun q => rootWeight (ofLex q).2) (fun q => ?_)]
  · congr 1
    simp only [rootWeight_eq_twice, ← Finset.mul_sum, coefficientMonomialWeight,
      Int.cast_sum]
  · rw [coefficientRootBasis_apply]
    exact constant_h_lie_currentBasis (ofLex q).1 (ofLex q).2

/-- The fixed coefficient degree bounds every nonzero Cartan eigenvector. -/
theorem coefficient_weight_bounds (B : ℕ) (j : ℤ) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν)
    (hj : ⁅constant MatrixSL2.h, ν⁆ = (2 * (j : ℂ)) • ν)
    (hν : ν ≠ 0) : -(B : ℤ) ≤ j ∧ j ≤ (B : ℤ) := by
  classical
  let b := coefficientRootBasis.ExteriorAlgebra
  have he : ∃ s, b.repr ν s ≠ 0 := by
    by_contra h
    apply hν
    apply b.repr.injective
    ext s
    simpa using not_exists_not.mp h s
  obtain ⟨s, hs⟩ := he
  have hc : (s.card : ℂ) = (B : ℂ) :=
    (b.apply_eq_smul_iff_of_diagonal (LieChains.derivExt (1 : Module.End ℂ Cur))
      (fun s => (s.card : ℂ)) (LieChains.derivExt_one_basis coefficientRootBasis)
      (B : ℂ) ν).mp hB s hs
  have hw : (2 : ℂ) * (coefficientMonomialWeight s : ℂ) = 2 * (j : ℂ) :=
    (b.apply_eq_smul_iff_of_diagonal (LieModule.toEnd ℂ Cur NB (constant MatrixSL2.h))
      (fun s => (2 : ℂ) * (coefficientMonomialWeight s : ℂ)) coefficientCartan_basis
      (2 * (j : ℂ)) ν).mp hj s hs
  have hc' : s.card = B := by exact_mod_cast hc
  have hw' : coefficientMonomialWeight s = j := by
    have hh := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hw
    exact_mod_cast hh
  simpa only [hc', hw'] using coefficientMonomialWeight_bounds s

/-- There are no coefficient-degree-B vectors of Cartan half-weight greater than B. -/
theorem coefficient_eq_zero_of_weight_gt (B : ℕ) (j : ℤ) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν)
    (hj : ⁅constant MatrixSL2.h, ν⁆ = (2 * (j : ℂ)) • ν)
    (hgt : (B : ℤ) < j) : ν = 0 := by
  by_contra hν
  have h := (coefficient_weight_bounds B j ν hB hj hν).2
  omega

/-- There are no coefficient-degree-B vectors of Cartan half-weight less than -B. -/
theorem coefficient_eq_zero_of_weight_lt (B : ℕ) (j : ℤ) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν)
    (hj : ⁅constant MatrixSL2.h, ν⁆ = (2 * (j : ℂ)) • ν)
    (hlt : j < -(B : ℤ)) : ν = 0 := by
  by_contra hν
  have h := (coefficient_weight_bounds B j ν hB hj hν).1
  omega

/-- Diagonal inverse to the shifted Cartan operator away from its eigenvalue. -/
def coefficientCartanInverse (p : ℕ) : Module.End ℂ NB :=
  coefficientRootBasis.ExteriorAlgebra.constr ℂ fun s =>
    ((2 * (coefficientMonomialWeight s : ℂ) - 2 * (p : ℂ))⁻¹) •
      coefficientRootBasis.ExteriorAlgebra s

@[simp] theorem coefficientCartanInverse_basis (p : ℕ) (s : Finset Idx) :
    coefficientCartanInverse p (coefficientRootBasis.ExteriorAlgebra s) =
      ((2 * (coefficientMonomialWeight s : ℂ) - 2 * (p : ℂ))⁻¹) •
        coefficientRootBasis.ExteriorAlgebra s :=
  Module.Basis.constr_basis _ _ _ _

/-- The diagonal inverse preserves coefficient degree. -/
theorem coefficientCartanInverse_degree (B p : ℕ) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν) :
    LieChains.derivExt (1 : Module.End ℂ Cur) (coefficientCartanInverse p ν) =
      (B : ℂ) • coefficientCartanInverse p ν := by
  have hc : LieChains.derivExt (1 : Module.End ℂ Cur) ∘ₗ coefficientCartanInverse p =
      coefficientCartanInverse p ∘ₗ LieChains.derivExt (1 : Module.End ℂ Cur) := by
    apply coefficientRootBasis.ExteriorAlgebra.ext
    intro s
    simp only [LinearMap.comp_apply, coefficientCartanInverse_basis, map_smul,
      LieChains.derivExt_one_basis, smul_smul]
    rw [mul_comm]
  calc
    LieChains.derivExt (1 : Module.End ℂ Cur) (coefficientCartanInverse p ν) =
        coefficientCartanInverse p (LieChains.derivExt (1 : Module.End ℂ Cur) ν) :=
      LinearMap.congr_fun hc ν
    _ = (B : ℂ) • coefficientCartanInverse p ν := by rw [hB, map_smul]

/-- Above coefficient degree B, the shifted Cartan operator has the stated inverse. -/
theorem coefficientCartanInverse_spec (B p : ℕ) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν)
    (hp : B < p) :
    ⁅constant MatrixSL2.h, coefficientCartanInverse p ν⁆ -
      (2 * (p : ℂ)) • coefficientCartanInverse p ν = ν := by
  classical
  let b := coefficientRootBasis.ExteriorAlgebra
  have hI (s : Finset Idx) : b.repr (coefficientCartanInverse p ν) s =
      (2 * (coefficientMonomialWeight s : ℂ) - 2 * (p : ℂ))⁻¹ * b.repr ν s :=
    b.repr_apply_of_diagonal (coefficientCartanInverse p) _
      (coefficientCartanInverse_basis p) ν s
  have hH (s : Finset Idx) : b.repr ⁅constant MatrixSL2.h, coefficientCartanInverse p ν⁆ s =
      (2 * (coefficientMonomialWeight s : ℂ)) * b.repr (coefficientCartanInverse p ν) s :=
    b.repr_apply_of_diagonal (LieModule.toEnd ℂ Cur NB (constant MatrixSL2.h)) _
      coefficientCartan_basis (coefficientCartanInverse p ν) s
  apply b.repr.injective
  ext s
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [hH, hI]
  by_cases hs : b.repr ν s = 0
  · simp only [hs, mul_zero, sub_zero]
  · have hc : (s.card : ℂ) = (B : ℂ) :=
      (b.apply_eq_smul_iff_of_diagonal (LieChains.derivExt (1 : Module.End ℂ Cur))
        (fun s => (s.card : ℂ)) (LieChains.derivExt_one_basis coefficientRootBasis)
        (B : ℂ) ν).mp hB s hs
    have hc' : s.card = B := by exact_mod_cast hc
    have hw : coefficientMonomialWeight s < (p : ℤ) := by
      have hle := (coefficientMonomialWeight_bounds s).2
      rw [hc'] at hle
      exact lt_of_le_of_lt hle (by exact_mod_cast hp)
    have hδ : (2 : ℂ) * (coefficientMonomialWeight s : ℂ) - 2 * (p : ℂ) ≠ 0 := by
      intro hh
      have heq := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (sub_eq_zero.mp hh)
      have heq' : coefficientMonomialWeight s = (p : ℤ) := by exact_mod_cast heq
      exact (ne_of_lt hw) heq'
    rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ hδ, one_mul]

/-- The shifted Cartan map is surjective on coefficient degree B when B<p. -/
theorem coefficient_cartan_sub_surjective (B p : ℕ) (hp : B < p) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν) :
    ∃ μ : NB, LieChains.derivExt (1 : Module.End ℂ Cur) μ = (B : ℂ) • μ ∧
      ⁅constant MatrixSL2.h, μ⁆ - (2 * (p : ℂ)) • μ = ν :=
  ⟨coefficientCartanInverse p ν, coefficientCartanInverse_degree B p ν hB,
    coefficientCartanInverse_spec B p ν hB hp⟩

end KhanSL2.BGGBridge
