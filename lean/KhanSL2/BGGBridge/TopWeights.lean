module

public import KhanSL2.BGGBridge.CoefficientWeights
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # The extremal coefficient space

In coefficient degree B, the Cartan eigenvalue 2B occurs precisely on wedges
whose root-current factors all have color e. The complementary weights admit
an explicit inverse for the shifted Cartan operator.
-/

noncomputable section
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

theorem coefficientHalfWeight_eq_one_iff (a : Fin 3) :
    coefficientHalfWeight a = 1 ↔ a = 0 := by
  fin_cases a <;> norm_num [coefficientHalfWeight]

/-- Maximal half-weight forces every exterior factor to have color e. -/
theorem coefficientMonomialWeight_eq_card_iff (s : Finset Idx) :
    coefficientMonomialWeight s = (s.card : ℤ) ↔
      ∀ q ∈ s, (ofLex q).2 = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coefficientMonomialWeight]
  | @insert a s ha ih =>
    have hsum : coefficientMonomialWeight (insert a s) =
        coefficientHalfWeight (ofLex a).2 + coefficientMonomialWeight s := by
      simp [coefficientMonomialWeight, ha]
    rw [hsum, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    constructor
    · intro he
      have hwa := (coefficientHalfWeight_bounds (ofLex a).2).2
      have hws := (coefficientMonomialWeight_bounds s).2
      have heqa : coefficientHalfWeight (ofLex a).2 = 1 := by omega
      have heqs : coefficientMonomialWeight s = (s.card : ℤ) := by omega
      simpa only [Finset.mem_insert, forall_eq_or_imp] using
        And.intro (coefficientHalfWeight_eq_one_iff _ |>.mp heqa) (ih.mp heqs)
    · intro he
      have heqa := (coefficientHalfWeight_eq_one_iff (ofLex a).2).mpr
        (he a (Finset.mem_insert_self _ _))
      have heqs := ih.mpr (fun q hq => he q (Finset.mem_insert_of_mem hq))
      rw [heqa, heqs]
      omega

/-- The span of degree-B root exterior monomials whose factors all have color e. -/
def coefficientTopSubspace (B : ℕ) : Submodule ℂ NB :=
  Submodule.span ℂ {ν | ∃ s : Finset Idx, s.card = B ∧
    (∀ q ∈ s, (ofLex q).2 = 0) ∧ ν = coefficientRootBasis.ExteriorAlgebra s}

theorem coefficient_basis_mem_top (B : ℕ) (s : Finset Idx) (hs : s.card = B)
    (he : ∀ q ∈ s, (ofLex q).2 = 0) :
    coefficientRootBasis.ExteriorAlgebra s ∈ coefficientTopSubspace B :=
  Submodule.subset_span ⟨s, hs, he, rfl⟩

theorem coefficientTopSubspace_degree (B : ℕ) {ν : NB}
    (hν : ν ∈ coefficientTopSubspace B) :
    LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν := by
  have hle : coefficientTopSubspace B ≤
      Module.End.eigenspace (LieChains.derivExt (1 : Module.End ℂ Cur)) (B : ℂ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, _, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    rw [LieChains.derivExt_one_basis, hs]
  exact Module.End.mem_eigenspace_iff.mp (hle hν)

theorem coefficientTopSubspace_weight (B : ℕ) {ν : NB}
    (hν : ν ∈ coefficientTopSubspace B) :
    ⁅constant MatrixSL2.h, ν⁆ = (2 * (B : ℂ)) • ν := by
  have hle : coefficientTopSubspace B ≤ Module.End.eigenspace
      (LieModule.toEnd ℂ Cur NB (constant MatrixSL2.h)) (2 * (B : ℂ)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, he, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change ⁅constant MatrixSL2.h, coefficientRootBasis.ExteriorAlgebra s⁆ = _
    rw [coefficientCartan_basis, (coefficientMonomialWeight_eq_card_iff s).mpr he, hs]
    simp
  exact Module.End.mem_eigenspace_iff.mp (hle hν)

/-- Projection to the extremal weight in coefficient degree B. -/
def coefficientTopProjection (B : ℕ) : Module.End ℂ NB :=
  coefficientRootBasis.ExteriorAlgebra.constr ℂ fun s =>
    if s.card = B ∧ coefficientMonomialWeight s = (B : ℤ) then
      coefficientRootBasis.ExteriorAlgebra s else 0

@[simp] theorem coefficientTopProjection_basis (B : ℕ) (s : Finset Idx) :
    coefficientTopProjection B (coefficientRootBasis.ExteriorAlgebra s) =
      (if s.card = B ∧ coefficientMonomialWeight s = (B : ℤ) then (1 : ℂ) else 0) •
        coefficientRootBasis.ExteriorAlgebra s := by
  simp only [coefficientTopProjection, Module.Basis.constr_basis]
  split <;> simp

/-- Every projected coefficient lies in the span of all-e monomials. -/
theorem coefficientTopProjection_mem (B : ℕ) (ν : NB) :
    coefficientTopProjection B ν ∈ coefficientTopSubspace B := by
  have hle : LinearMap.range (coefficientTopProjection B) ≤ coefficientTopSubspace B := by
    rw [coefficientTopProjection, Module.Basis.constr_range]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    dsimp only
    split_ifs with hs
    · exact coefficient_basis_mem_top B s hs.1
        ((coefficientMonomialWeight_eq_card_iff s).mp (by simpa [hs.1] using hs.2))
    · exact (coefficientTopSubspace B).zero_mem
  exact hle ⟨ν, rfl⟩

theorem coefficientTopProjection_degree (B : ℕ) (ν : NB) :
    LieChains.derivExt (1 : Module.End ℂ Cur) (coefficientTopProjection B ν) =
      (B : ℂ) • coefficientTopProjection B ν :=
  coefficientTopSubspace_degree B (coefficientTopProjection_mem B ν)

theorem coefficientTopProjection_weight (B : ℕ) (ν : NB) :
    ⁅constant MatrixSL2.h, coefficientTopProjection B ν⁆ =
      (2 * (B : ℂ)) • coefficientTopProjection B ν :=
  coefficientTopSubspace_weight B (coefficientTopProjection_mem B ν)

/-- The shifted Cartan inverse is an inverse on the complement of extremal weight. -/
theorem coefficientCartanInverse_top_spec (B : ℕ) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν) :
    ⁅constant MatrixSL2.h, coefficientCartanInverse B ν⁆ -
      (2 * (B : ℂ)) • coefficientCartanInverse B ν = ν - coefficientTopProjection B ν := by
  classical
  let b := coefficientRootBasis.ExteriorAlgebra
  have hI (s : Finset Idx) : b.repr (coefficientCartanInverse B ν) s =
      (2 * (coefficientMonomialWeight s : ℂ) - 2 * (B : ℂ))⁻¹ * b.repr ν s :=
    b.repr_apply_of_diagonal (coefficientCartanInverse B) _
      (coefficientCartanInverse_basis B) ν s
  have hH (s : Finset Idx) : b.repr ⁅constant MatrixSL2.h, coefficientCartanInverse B ν⁆ s =
      (2 * (coefficientMonomialWeight s : ℂ)) * b.repr (coefficientCartanInverse B ν) s :=
    b.repr_apply_of_diagonal (LieModule.toEnd ℂ Cur NB (constant MatrixSL2.h)) _
      coefficientCartan_basis (coefficientCartanInverse B ν) s
  have hP (s : Finset Idx) : b.repr (coefficientTopProjection B ν) s =
      (if s.card = B ∧ coefficientMonomialWeight s = (B : ℤ) then (1 : ℂ) else 0) *
        b.repr ν s :=
    b.repr_apply_of_diagonal (coefficientTopProjection B) _
      (coefficientTopProjection_basis B) ν s
  apply b.repr.injective
  ext s
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [hH, hI, hP]
  by_cases hs : b.repr ν s = 0
  · simp only [hs, mul_zero, sub_zero]
  · have hc : (s.card : ℂ) = (B : ℂ) :=
      (b.apply_eq_smul_iff_of_diagonal (LieChains.derivExt (1 : Module.End ℂ Cur))
        (fun s => (s.card : ℂ)) (LieChains.derivExt_one_basis coefficientRootBasis)
        (B : ℂ) ν).mp hB s hs
    have hc' : s.card = B := by exact_mod_cast hc
    by_cases hw : coefficientMonomialWeight s = (B : ℤ)
    · simp [hw, hc']
    · have hδ : (2 : ℂ) * (coefficientMonomialWeight s : ℂ) - 2 * (B : ℂ) ≠ 0 := by
        intro hh
        have heq := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (sub_eq_zero.mp hh)
        apply hw
        exact_mod_cast heq
      rw [if_neg (by simp [hw]), zero_mul, sub_zero,
        ← sub_mul, ← mul_assoc, mul_inv_cancel₀ hδ, one_mul]

/-- Every coefficient vector is a shifted-Cartan image plus an all-e extremal vector. -/
theorem coefficient_top_cartan_decomposition (B : ℕ) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν) :
    ∃ y, LieChains.derivExt (1 : Module.End ℂ Cur) y = (B : ℂ) • y ∧
      ∃ q ∈ coefficientTopSubspace B,
        ⁅constant MatrixSL2.h, y⁆ - (2 * (B : ℂ)) • y + q = ν := by
  refine ⟨coefficientCartanInverse B ν, coefficientCartanInverse_degree B B ν hB,
    coefficientTopProjection B ν, coefficientTopProjection_mem B ν, ?_⟩
  rw [coefficientCartanInverse_top_spec B ν hB, sub_add_cancel]

end KhanSL2.BGGBridge
