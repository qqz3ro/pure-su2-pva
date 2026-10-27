module

public import KhanSL2.Factorization.RelativeChainsWeightHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The finite weight/symmetric-degree quotients form the actual algebraic direct
sum of relative chains. This is a finite-support decomposition, not a completion. -/

noncomputable section
open scoped BigOperators DirectSum
namespace KhanSL2.Factorization
open Macdonald BGGBridge

theorem weightComponent_inclusion_ne {w s w' s' : ℕ}
    (hne : (w,s) ≠ (w',s')) (z : WeightChains w' s') :
    weightComponent w s (weightInclusion w' s' z) = 0 := by
  induction z using Submodule.Quotient.induction_on with
  | H u =>
    rw [weightInclusion_mk, weightComponent_mk]
    have hz : rawWeightComponent w s (chainModel.symm u.val) = 0 := by
      apply Subtype.ext
      rw [rawWeightComponent_val, chainModel.apply_symm_apply]
      exact weightProjection_of_mem_ne hne u.property
    rw [hz, Submodule.Quotient.mk_zero]

/-- Sum the actual finite block classes by their specified quotient inclusions. -/
def weightSumMap : (⨁ d : ℕ × ℕ, WeightChains d.1 d.2) →ₗ[ℂ]
    RelativeChains SymmetricCoefficients :=
  DirectSum.toModule ℂ (ℕ × ℕ) (RelativeChains SymmetricCoefficients)
    (fun d => weightInclusion d.1 d.2)

@[simp] theorem weightSumMap_of (d : ℕ × ℕ) (u : WeightChains d.1 d.2) :
    weightSumMap (DirectSum.of (fun d : ℕ × ℕ => WeightChains d.1 d.2) d u) =
      weightInclusion d.1 d.2 u :=
  DirectSum.toModule_lof ℂ (φ := fun d : ℕ × ℕ => weightInclusion d.1 d.2) d u

theorem weightComponent_sumMap (u : ⨁ d : ℕ × ℕ, WeightChains d.1 d.2) (d : ℕ × ℕ) :
    weightComponent d.1 d.2 (weightSumMap u) = u d := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | of e u =>
    rw [weightSumMap_of]
    by_cases h : e = d
    · subst e
      rw [weightComponent_inclusion]
      simp
    · rw [weightComponent_inclusion_ne (by simpa only [Prod.mk.eta] using Ne.symm h)]
      simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add u v hu hv =>
    simp only [map_add, hu, hv]
    rfl

theorem weightSumMap_injective : Function.Injective weightSumMap := by
  intro u v h
  apply DFinsupp.ext
  intro d
  rw [← weightComponent_sumMap u d, ← weightComponent_sumMap v d, h]

theorem weightSumMap_surjective : Function.Surjective weightSumMap := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective (relC SymmetricCoefficients) z
  have hu : u = chainModel.symm
      (∑ b ∈ (basis.repr (chainModel u)).support,
        basis.repr (chainModel u) b • basis b) := by
    rw [← eq_sum_basis, chainModel.symm_apply_apply]
  rw [hu, map_sum, map_sum]
  apply Submodule.sum_mem
  intro b hb
  rw [map_smul, map_smul]
  apply Submodule.smul_mem
  let v : WeightChains (weight b) (symmetricDegree b) :=
    Submodule.Quotient.mk (⟨basis b,basis_mem_weightDegreePiece b⟩ :
      weightDegreePiece (weight b) (symmetricDegree b))
  refine ⟨DirectSum.of (fun d : ℕ × ℕ => WeightChains d.1 d.2)
    (weight b,symmetricDegree b) v, ?_⟩
  rw [weightSumMap_of]
  rfl

/-- Algebraic direct-sum decomposition of the actual relative CE chain quotient. -/
def weightSumEquiv : (⨁ d : ℕ × ℕ, WeightChains d.1 d.2) ≃ₗ[ℂ]
    RelativeChains SymmetricCoefficients :=
  LinearEquiv.ofBijective weightSumMap ⟨weightSumMap_injective,weightSumMap_surjective⟩

@[simp] theorem weightSumEquiv_of (d : ℕ × ℕ) (u : WeightChains d.1 d.2) :
    weightSumEquiv (DirectSum.of (fun d : ℕ × ℕ => WeightChains d.1 d.2) d u) =
      weightInclusion d.1 d.2 u := weightSumMap_of d u

@[simp] theorem weightSumEquiv_symm_apply (z : RelativeChains SymmetricCoefficients)
    (d : ℕ × ℕ) : weightSumEquiv.symm z d = weightComponent d.1 d.2 z := by
  have h := weightComponent_sumMap (weightSumEquiv.symm z) d
  change weightComponent d.1 d.2 (weightSumEquiv (weightSumEquiv.symm z)) = _ at h
  rw [weightSumEquiv.apply_symm_apply] at h
  exact h.symm

end KhanSL2.Factorization
