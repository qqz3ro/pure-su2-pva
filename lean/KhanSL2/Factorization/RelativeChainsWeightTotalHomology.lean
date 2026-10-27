module

public import KhanSL2.Factorization.RelativeChainsWeightDecomposition
public import KhanSL2.Factorization.RelativeChainsTotalHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual total relative CE homology is the finite-support direct sum of
its finite weight/symmetric-degree homologies. All maps are the original inclusions. -/

noncomputable section
open scoped BigOperators DirectSum
namespace KhanSL2.Factorization
open Macdonald

def weightChainInclusionPair (w s : ℕ) :
    PerfectDuality.PairMap (weightBoundary w s) (weightBoundary w s)
      (differential SymmetricCoefficients) (differential SymmetricCoefficients) where
  left := weightInclusion w s
  middle := weightInclusion w s
  right := weightInclusion w s
  comm_in := LinearMap.ext (weightInclusion_boundary w s)
  comm_out := LinearMap.ext (weightInclusion_boundary w s)

def weightChainComponentPair (w s : ℕ) :
    PerfectDuality.PairMap (differential SymmetricCoefficients) (differential SymmetricCoefficients)
      (weightBoundary w s) (weightBoundary w s) where
  left := weightComponent w s
  middle := weightComponent w s
  right := weightComponent w s
  comm_in := LinearMap.ext (weightComponent_differential w s)
  comm_out := LinearMap.ext (weightComponent_differential w s)

/-- The actual homogeneous-block inclusion on total relative homology. -/
def weightHomologyInclusion (w s : ℕ) :
    WeightHomology w s →ₗ[ℂ] TotalHomology SymmetricCoefficients :=
  (weightChainInclusionPair w s).homologyMap
    (weightBoundary_comp_self w s) (differential_comp_self SymmetricCoefficients)

/-- The actual finite-block projection on total relative homology. -/
def weightHomologyComponent (w s : ℕ) :
    TotalHomology SymmetricCoefficients →ₗ[ℂ] WeightHomology w s :=
  (weightChainComponentPair w s).homologyMap
    (differential_comp_self SymmetricCoefficients) (weightBoundary_comp_self w s)

@[simp] theorem weightHomologyComponent_inclusion (w s : ℕ) (u : WeightHomology w s) :
    weightHomologyComponent w s (weightHomologyInclusion w s u) = u := by
  obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (weightBoundary w s) (weightBoundary w s)) u
  change Submodule.Quotient.mk
    ((weightChainComponentPair w s).cyclesMap ((weightChainInclusionPair w s).cyclesMap v)) =
      Submodule.Quotient.mk v
  congr 1
  apply Subtype.ext
  exact weightComponent_inclusion w s v.val

theorem weightHomologyComponent_inclusion_ne {w s w' s' : ℕ}
    (hne : (w,s) ≠ (w',s')) (u : WeightHomology w' s') :
    weightHomologyComponent w s (weightHomologyInclusion w' s' u) = 0 := by
  obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (weightBoundary w' s') (weightBoundary w' s')) u
  change Submodule.Quotient.mk
    ((weightChainComponentPair w s).cyclesMap ((weightChainInclusionPair w' s').cyclesMap v)) = 0
  have hzero : (weightChainComponentPair w s).cyclesMap
      ((weightChainInclusionPair w' s').cyclesMap v) = 0 := by
    apply Subtype.ext
    exact weightComponent_inclusion_ne hne v.val
  rw [hzero,Submodule.Quotient.mk_zero]

/-- Sum homogeneous homology classes by the canonical block inclusions. -/
def weightHomologySumMap : (⨁ d : ℕ × ℕ, WeightHomology d.1 d.2) →ₗ[ℂ]
    TotalHomology SymmetricCoefficients :=
  DirectSum.toModule ℂ (ℕ × ℕ) (TotalHomology SymmetricCoefficients)
    (fun d => weightHomologyInclusion d.1 d.2)

@[simp] theorem weightHomologySumMap_of (d : ℕ × ℕ) (u : WeightHomology d.1 d.2) :
    weightHomologySumMap (DirectSum.of (fun d : ℕ × ℕ => WeightHomology d.1 d.2) d u) =
      weightHomologyInclusion d.1 d.2 u := DirectSum.toModule_lof ℂ (φ := fun d : ℕ × ℕ => weightHomologyInclusion d.1 d.2) d u

theorem weightHomologyComponent_sumMap (u : ⨁ d : ℕ × ℕ, WeightHomology d.1 d.2)
    (d : ℕ × ℕ) : weightHomologyComponent d.1 d.2 (weightHomologySumMap u) = u d := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | of e u =>
    rw [weightHomologySumMap_of]
    by_cases h : e = d
    · subst e
      rw [weightHomologyComponent_inclusion]
      simp
    · rw [weightHomologyComponent_inclusion_ne (by simpa only [Prod.mk.eta] using Ne.symm h)]
      simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add u v hu hv =>
    simp only [map_add, hu, hv]
    rfl

theorem weightHomologySumMap_injective : Function.Injective weightHomologySumMap := by
  intro u v h
  apply DFinsupp.ext
  intro d
  rw [← weightHomologyComponent_sumMap u d, ← weightHomologyComponent_sumMap v d, h]

theorem weightHomologySumMap_surjective : Function.Surjective weightHomologySumMap := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential SymmetricCoefficients)
      (differential SymmetricCoefficients)) z
  let v := weightSumEquiv.symm u.val
  let c (d : ℕ × ℕ) : LinearMap.ker (weightBoundary d.1 d.2) :=
    (weightChainComponentPair d.1 d.2).cyclesMap u
  have hsum : ∑ d ∈ v.support, (weightChainInclusionPair d.1 d.2).cyclesMap (c d) = u := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change (∑ d ∈ v.support, weightInclusion d.1 d.2 (weightComponent d.1 d.2 u.val)) = u.val
    have h := congrArg weightSumEquiv (DirectSum.sum_support_of v)
    simp only [map_sum, weightSumEquiv_of] at h
    simpa only [v, weightSumEquiv_symm_apply, weightSumEquiv.apply_symm_apply] using h
  rw [← hsum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  refine ⟨DirectSum.of (fun d : ℕ × ℕ => WeightHomology d.1 d.2) d
    (Submodule.Quotient.mk (c d)), ?_⟩
  rw [weightHomologySumMap_of]
  rfl

/-- Actual total relative homology is an algebraic direct sum of finite blocks. -/
def weightHomologySumEquiv : (⨁ d : ℕ × ℕ, WeightHomology d.1 d.2) ≃ₗ[ℂ]
    TotalHomology SymmetricCoefficients :=
  LinearEquiv.ofBijective weightHomologySumMap
    ⟨weightHomologySumMap_injective,weightHomologySumMap_surjective⟩

end KhanSL2.Factorization
