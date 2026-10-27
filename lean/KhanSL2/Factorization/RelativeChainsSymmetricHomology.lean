module

public import KhanSL2.Factorization.RelativeChainsSymmetricDegree
public import KhanSL2.Factorization.RelativeChainsSlice
public import KhanSL2.Factorization.RelativeChainsHomologyWindow

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Fixed symmetric coefficient degree in actual relative homology, extracted
by the genuine coefficient inclusion/projection and finite-support weight decomposition. -/

noncomputable section
open scoped DirectSum
namespace KhanSL2.Factorization
open Macdonald

def symmetricHomologyInclusion (s : ℕ) :
    TotalHomology (symmetricPower s) →ₗ[ℂ] TotalHomology SymmetricCoefficients :=
  (totalPairMap (symmetricChainInclusion s)
    (LinearMap.ext (symmetricChainInclusion_differential s))).homologyMap
      (differential_comp_self (symmetricPower s)) (differential_comp_self SymmetricCoefficients)

def symmetricHomologyProjection (s : ℕ) :
    TotalHomology SymmetricCoefficients →ₗ[ℂ] TotalHomology (symmetricPower s) :=
  (totalPairMap (symmetricChainProjection s)
    (LinearMap.ext (symmetricChainProjection_differential s))).homologyMap
      (differential_comp_self SymmetricCoefficients) (differential_comp_self (symmetricPower s))

@[simp] theorem symmetricHomologyProjection_inclusion (s : ℕ)
    (z : TotalHomology (symmetricPower s)) :
    symmetricHomologyProjection s (symmetricHomologyInclusion s z) = z := by
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential (symmetricPower s))
      (differential (symmetricPower s))) z
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk u
  congr 1
  apply Subtype.ext
  exact symmetricChainProjection_inclusion s u.val

theorem symmetricHomologyProjection_weightInclusion (s w t : ℕ) (z : WeightHomology w t) :
    symmetricHomologyInclusion s (symmetricHomologyProjection s (weightHomologyInclusion w t z)) =
      if t=s then weightHomologyInclusion w t z else 0 := by
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (weightBoundary w t) (weightBoundary w t)) z
  let v : LinearMap.ker (differential SymmetricCoefficients) :=
    (totalPairMap (symmetricChainInclusion s)
      (LinearMap.ext (symmetricChainInclusion_differential s))).cyclesMap
        ((totalPairMap (symmetricChainProjection s)
          (LinearMap.ext (symmetricChainProjection_differential s))).cyclesMap
            ((weightChainInclusionPair w t).cyclesMap u))
  change Submodule.Quotient.mk v =
    if t=s then Submodule.Quotient.mk ((weightChainInclusionPair w t).cyclesMap u) else 0
  have hv := symmetricChainProjection_weightInclusion s w t u.val
  by_cases h : t=s
  · rw [if_pos h]
    congr 1
    apply Subtype.ext
    change symmetricChainInclusion s (symmetricChainProjection s (weightInclusion w t u.val)) =
      weightInclusion w t u.val
    simpa only [if_pos h] using hv
  · rw [if_neg h]
    have hvzero : v=0 := by
      apply Subtype.ext
      change symmetricChainInclusion s (symmetricChainProjection s (weightInclusion w t u.val)) = 0
      simpa only [if_neg h] using hv
    rw [hvzero,Submodule.Quotient.mk_zero]

@[simp] theorem weightHomologySumEquiv_of (d : ℕ × ℕ) (u : WeightHomology d.1 d.2) :
    weightHomologySumEquiv (DirectSum.of (fun d : ℕ × ℕ => WeightHomology d.1 d.2) d u) =
      weightHomologyInclusion d.1 d.2 u := weightHomologySumMap_of d u

@[simp] theorem weightHomologySumEquiv_symm_apply (z : TotalHomology SymmetricCoefficients)
    (d : ℕ × ℕ) : weightHomologySumEquiv.symm z d = weightHomologyComponent d.1 d.2 z := by
  have h := weightHomologyComponent_sumMap (weightHomologySumEquiv.symm z) d
  change weightHomologyComponent d.1 d.2
    (weightHomologySumEquiv (weightHomologySumEquiv.symm z)) = _ at h
  rw [weightHomologySumEquiv.apply_symm_apply] at h
  exact h.symm

theorem symmetricHomologyProjection_weightSum (s w t : ℕ) (u : WeightHomology w t) :
    symmetricHomologyInclusion s (symmetricHomologyProjection s
      (weightHomologySumEquiv (DirectSum.of (fun d : ℕ × ℕ => WeightHomology d.1 d.2) (w,t) u))) =
        if t=s then weightHomologySumEquiv
          (DirectSum.of (fun d : ℕ × ℕ => WeightHomology d.1 d.2) (w,t) u) else 0 := by
  rw [weightHomologySumEquiv_of]
  exact symmetricHomologyProjection_weightInclusion s w t u

/-- Sum finite loop-weight homology classes into the actual degree-s symmetric coefficients. -/
def weightSymmetricHomologyEquiv (s : ℕ) : (⨁ w, WeightHomology w s) ≃ₗ[ℂ]
    TotalHomology (symmetricPower s) :=
  DirectSumSlice.equiv (fun d : ℕ × ℕ => WeightHomology d.1 d.2)
    weightHomologySumEquiv (symmetricHomologyInclusion s) (symmetricHomologyProjection s) s
    (symmetricHomologyProjection_inclusion s) (symmetricHomologyProjection_weightSum s)

/-- Actual symmetric-power relative homology has exactly its finite-support loop-weight blocks. -/
def symmetricPowerHomologyEquiv (s : ℕ) : TotalHomology (symmetricPower s) ≃ₗ[ℂ]
    (⨁ w, WeightHomology w s) := (weightSymmetricHomologyEquiv s).symm

@[simp] theorem weightSymmetricHomologyEquiv_of (s w : ℕ) (u : WeightHomology w s) :
    weightSymmetricHomologyEquiv s (DirectSum.of (fun w => WeightHomology w s) w u) =
      symmetricHomologyProjection s (weightHomologyInclusion w s u) := by
  rw [weightSymmetricHomologyEquiv,DirectSumSlice.equiv_of,weightHomologySumEquiv_of]

@[simp] theorem symmetricPowerHomologyEquiv_apply (s : ℕ)
    (u : TotalHomology (symmetricPower s)) (w : ℕ) :
    symmetricPowerHomologyEquiv s u w =
      weightHomologyComponent w s (symmetricHomologyInclusion s u) := by
  rw [symmetricPowerHomologyEquiv,weightSymmetricHomologyEquiv,
    DirectSumSlice.equiv_symm_apply,weightHomologySumEquiv_symm_apply]

end KhanSL2.Factorization
