module

public import KhanSL2.BGGBridge.TopWeights

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # Ordered tuples for the extremal coefficient space -/

noncomputable section
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- Each all-e root exterior basis monomial is an ordered wedge of B current modes. -/
theorem coefficientTop_basis_eq_ιMulti (B : ℕ) (s : Finset Idx) (hs : s.card = B)
    (he : ∀ q ∈ s, (ofLex q).2 = 0) :
    ∃ d : Fin B → ℕ, coefficientRootBasis.ExteriorAlgebra s =
      ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (d i, 0)) := by
  let e : Fin B ↪o Idx := s.orderEmbOfFin hs
  refine ⟨fun i => (ofLex (e i)).1, ?_⟩
  rw [ExteriorAlgebra.basis_apply_ofCard coefficientRootBasis hs]
  change ExteriorAlgebra.ιMulti ℂ B (fun i => coefficientRootBasis (e i)) = _
  congr 1
  funext i
  rw [coefficientRootBasis_apply]
  congr 1
  apply Prod.ext
  · rfl
  · exact he (e i) (Finset.orderEmbOfFin_mem s hs i)

/-- To bound the extremal coefficient subspace, it is enough to check ordered all-e wedges. -/
theorem coefficientTopSubspace_le_of_ιMulti (B : ℕ) (W : Submodule ℂ NB)
    (hW : ∀ d : Fin B → ℕ,
      ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (d i, 0)) ∈ W) :
    coefficientTopSubspace B ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, he, rfl⟩
  obtain ⟨d, hd⟩ := coefficientTop_basis_eq_ιMulti B s hs he
  rw [hd]
  exact hW d

/-- The extremal projection fixes a vector satisfying its two eigenvalue equations. -/
theorem coefficientTopProjection_eq_self (B : ℕ) (ν : NB)
    (hB : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν)
    (hH : ⁅constant MatrixSL2.h, ν⁆ = (2 * (B : ℂ)) • ν) :
    coefficientTopProjection B ν = ν := by
  classical
  let b := coefficientRootBasis.ExteriorAlgebra
  apply b.repr.injective
  ext s
  rw [b.repr_apply_of_diagonal (coefficientTopProjection B) _
    (coefficientTopProjection_basis B) ν s]
  by_cases hs : b.repr ν s = 0
  · simp only [hs, mul_zero]
  · have hc : (s.card : ℂ) = (B : ℂ) :=
      (b.apply_eq_smul_iff_of_diagonal (LieChains.derivExt (1 : Module.End ℂ Cur))
        (fun s => (s.card : ℂ)) (LieChains.derivExt_one_basis coefficientRootBasis)
        (B : ℂ) ν).mp hB s hs
    have hw : (2 : ℂ) * (coefficientMonomialWeight s : ℂ) = 2 * (B : ℂ) :=
      (b.apply_eq_smul_iff_of_diagonal (LieModule.toEnd ℂ Cur NB (constant MatrixSL2.h))
        (fun s => (2 : ℂ) * (coefficientMonomialWeight s : ℂ)) coefficientCartan_basis
        (2 * (B : ℂ)) ν).mp hH s hs
    have hc' : s.card = B := by exact_mod_cast hc
    have hw' : coefficientMonomialWeight s = (B : ℤ) := by
      have hh := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hw
      exact_mod_cast hh
    rw [if_pos ⟨hc', hw'⟩, one_mul]

/-- The all-e span is exactly the simultaneous degree-B and Cartan-weight-2B space. -/
theorem mem_coefficientTopSubspace_iff (B : ℕ) (ν : NB) :
    ν ∈ coefficientTopSubspace B ↔
      LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν ∧
      ⁅constant MatrixSL2.h, ν⁆ = (2 * (B : ℂ)) • ν := by
  constructor
  · intro hν
    exact ⟨coefficientTopSubspace_degree B hν, coefficientTopSubspace_weight B hν⟩
  · rintro ⟨hB, hH⟩
    rw [← coefficientTopProjection_eq_self B ν hB hH]
    exact coefficientTopProjection_mem B ν

end KhanSL2.BGGBridge
