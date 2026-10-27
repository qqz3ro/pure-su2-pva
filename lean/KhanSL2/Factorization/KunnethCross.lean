module

public import KhanSL2.Factorization.KunnethCoefficientMaps
public import KhanSL2.Factorization.KunnethQuotient
public import KhanSL2.Factorization.ShuffleParityDegree
public import Mathlib.LinearAlgebra.Quotient.Bilinear

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual total homology cross product: tensor two cycle representatives.
Both boundary relations are checked using the actual signed tensor boundary. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

theorem relativeParity_involutive (u : RelativeChains M) :
    relativeParity M (relativeParity M u) = u := by
  obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective (BGGBridge.relC M) u
  obtain ⟨z,rfl⟩ := (CEModel.J (N := M)).surjective v
  rw [relativeParity_mk,rawParity_J,relativeParity_mk,rawParity_J,CEParity.parity_parity]

theorem differential_relativeParity (u : RelativeChains M) :
    differential M (relativeParity M u) = -relativeParity M (differential M u) := by
  obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective (BGGBridge.relC M) u
  obtain ⟨z,rfl⟩ := (CEModel.J (N := M)).surjective v
  change (BGGBridge.relC M).mkQ (rawDifferential M (rawParity M (CEModel.J z))) =
    - (BGGBridge.relC M).mkQ (rawParity M (rawDifferential M (CEModel.J z)))
  rw [rawParity_J,← CEModel.J_boundary,← CEModel.J_boundary,
    CEParity.boundary_parity,map_neg,rawParity_J,map_neg]

/-- Bilinear tensor product of two actual cycles. -/
def tensorCycles : LinearMap.ker (differential M) →ₗ[ℂ]
    LinearMap.ker (differential N) →ₗ[ℂ]
      LinearMap.ker (relativeTensorDifferential M N) where
  toFun u :=
    (((TensorProduct.mk ℂ (RelativeChains M) (RelativeChains N)) u.val).comp
      (LinearMap.ker (differential N)).subtype).codRestrict _ (by
        intro v
        change relativeTensorDifferential M N (u.val ⊗ₜ[ℂ] v.val) = 0
        rw [relativeTensorDifferential_tmul,u.property,v.property]
        simp)
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact TensorProduct.add_tmul _ _ _
  map_smul' c u := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact (TensorProduct.smul_tmul' _ _ _).symm

@[simp] theorem tensorCycles_val (u : LinearMap.ker (differential M))
    (v : LinearMap.ker (differential N)) : (tensorCycles M N u v).val = u.val ⊗ₜ[ℂ] v.val := rfl

def tensorHomologyClass : LinearMap.ker (relativeTensorDifferential M N) →ₗ[ℂ]
    TensorTotalHomology M N := squareZeroClass (relativeTensorDifferential M N)

def tensorCycleClass : LinearMap.ker (differential M) →ₗ[ℂ]
    LinearMap.ker (differential N) →ₗ[ℂ] TensorTotalHomology M N :=
  (tensorCycles M N).compr₂ (tensorHomologyClass M N)

theorem tensorCycleClass_left_boundary : PerfectDuality.pairBoundaries (differential M)
    (differential M) ≤ (tensorCycleClass M N).ker := by
  rintro u ⟨z,hz⟩
  apply LinearMap.ext
  intro v
  change Submodule.Quotient.mk (tensorCycles M N u v) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨z ⊗ₜ[ℂ] v.val,?_⟩
  change relativeTensorDifferential M N (z ⊗ₜ[ℂ] v.val) = u.val ⊗ₜ[ℂ] v.val
  rw [relativeTensorDifferential_tmul,hz,v.property]
  simp

theorem tensorCycleClass_right_boundary : PerfectDuality.pairBoundaries (differential N)
    (differential N) ≤ (tensorCycleClass M N).flip.ker := by
  rintro v ⟨z,hz⟩
  apply LinearMap.ext
  intro u
  change Submodule.Quotient.mk (tensorCycles M N u v) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨relativeParity M u.val ⊗ₜ[ℂ] z,?_⟩
  change relativeTensorDifferential M N (relativeParity M u.val ⊗ₜ[ℂ] z) = u.val ⊗ₜ[ℂ] v.val
  rw [relativeTensorDifferential_tmul,differential_relativeParity,u.property,
    map_zero,neg_zero,relativeParity_involutive,hz]
  simp

/-- The canonical total cross product, defined by actual cycle tensors. -/
def totalHomologyCross : TotalHomology M ⊗[ℂ] TotalHomology N →ₗ[ℂ]
    TensorTotalHomology M N :=
  TensorProduct.lift ((tensorCycleClass M N).liftQ₂
    (PerfectDuality.pairBoundaries (differential M) (differential M))
    (PerfectDuality.pairBoundaries (differential N) (differential N))
    (tensorCycleClass_left_boundary M N) (tensorCycleClass_right_boundary M N))

@[simp] theorem totalHomologyCross_mk_tmul_mk (u : LinearMap.ker (differential M))
    (v : LinearMap.ker (differential N)) :
    totalHomologyCross M N (Submodule.Quotient.mk u ⊗ₜ[ℂ] Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (tensorCycles M N u v) := rfl

end KhanSL2.Factorization
