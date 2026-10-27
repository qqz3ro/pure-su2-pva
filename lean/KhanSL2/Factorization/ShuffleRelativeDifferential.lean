module

public import KhanSL2.Factorization.ShuffleModel
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual relative shuffle is a chain map for the signed relative tensor boundary. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge KhanSL2.Current

variable (M N : Type*)
  [AddCommGroup M] [Module ℂ M] [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]

/-- Exterior parity transported through the actual CE comparison. -/
def rawParity : Module.End ℂ (RawChains M) :=
  (CEModel.J (N := M)).toLinearMap.comp
    ((CEParity.parity plus M).comp (CEModel.J (N := M)).symm.toLinearMap)

omit [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M] in
@[simp] theorem rawParity_J (u : LieChains.Chains ℂ plus M) :
    rawParity M (CEModel.J u) = CEModel.J (CEParity.parity plus M u) := by
  simp only [rawParity, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

private theorem abstractParity_constantAction (a : Fin 3) (u : LieChains.Chains ℂ plus M) :
    CEParity.parity plus M (CEModel.constantAction a u) =
      CEModel.constantAction a (CEParity.parity plus M u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul ω m =>
    simp only [CEModel.constantAction, LieChains.lieDeriv_tmul, map_add,
      CEParity.parity_tmul, ExteriorShuffle.parity_derivExt]
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem rawParity_actC_color (a : Fin 3) (z : RawChains M) :
    rawParity M (actC M (MatrixSL2.color a) z) = actC M (MatrixSL2.color a) (rawParity M z) := by
  obtain ⟨u, rfl⟩ := (CEModel.J (N := M)).surjective z
  rw [← CEModel.J_constantAction, rawParity_J, rawParity_J,
    abstractParity_constantAction, CEModel.J_constantAction]

theorem rawParity_actC (x : G) (z : RawChains M) :
    rawParity M (actC M x z) = actC M x (rawParity M z) := by
  rw [CEModel.actC_sum, CEModel.actC_sum, map_sum]
  simp_rw [map_smul, rawParity_actC_color]

theorem rawParity_relations : relC M ≤ (relC M).comap (rawParity M) :=
  le_comap_of_commute (actC M) (actC M) (rawParity M) (rawParity_actC M)

/-- Exterior parity on the actual constant-coinvariant quotient. -/
def relativeParity : Module.End ℂ (RelativeChains M) :=
  (relC M).mapQ (relC M) (rawParity M) (rawParity_relations M)

@[simp] theorem relativeParity_mk (z : RawChains M) :
    relativeParity M ((relC M).mkQ z) = (relC M).mkQ (rawParity M z) := rfl

/-- The transported raw tensor boundary is the usual signed sum on its two factors. -/
theorem rawTensorDifferential_tmul (u : RawChains M) (v : RawChains N) :
    rawTensorDifferential M N (u ⊗ₜ[ℂ] v) =
      rawDifferential M u ⊗ₜ[ℂ] v + rawParity M u ⊗ₜ[ℂ] rawDifferential N v := by
  obtain ⟨x, rfl⟩ := (CEModel.J (N := M)).surjective u
  obtain ⟨y, rfl⟩ := (CEModel.J (N := N)).surjective v
  change rawTensorDifferential M N (tensorModelEquiv M N (x ⊗ₜ[ℂ] y)) = _
  rw [rawTensorDifferential_model, CETensor.differential_tmul, map_add,
    tensorModelEquiv_tmul, tensorModelEquiv_tmul, rawParity_J]
  rw [CEModel.J_boundary, CEModel.J_boundary]

/-- The actual signed boundary on the tensor product of the two relative complexes. -/
def relativeTensorDifferential : Module.End ℂ (RelativeChains M ⊗[ℂ] RelativeChains N) :=
  LinearMap.rTensor (RelativeChains N) (differential M) +
    TensorProduct.map (relativeParity M) (differential N)

@[simp] theorem relativeTensorDifferential_tmul (u : RelativeChains M) (v : RelativeChains N) :
    relativeTensorDifferential M N (u ⊗ₜ[ℂ] v) =
      differential M u ⊗ₜ[ℂ] v + relativeParity M u ⊗ₜ[ℂ] differential N v := rfl

/-- Projection to the two relative factors intertwines the actual signed boundaries. -/
theorem projectRelativeTensor_differential (z : RawChains M ⊗[ℂ] RawChains N) :
    projectRelativeTensor M N (rawTensorDifferential M N z) =
      relativeTensorDifferential M N (projectRelativeTensor M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [rawTensorDifferential_tmul, map_add, projectRelativeTensor_tmul,
      projectRelativeTensor_tmul, projectRelativeTensor_tmul, relativeTensorDifferential_tmul,
      relativeParity_mk]
    rfl
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The specified relative shuffle is a chain map, with no factorization assumption. -/
theorem relativeShuffle_differential (z : RelativeChains (M ⊗[ℂ] N)) :
    relativeShuffle M N (differential (M ⊗[ℂ] N) z) =
      relativeTensorDifferential M N (relativeShuffle M N z) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (relC (M ⊗[ℂ] N)) z
  change projectRelativeTensor M N (rawShuffle M N (rawDifferential (M ⊗[ℂ] N) u)) =
    relativeTensorDifferential M N (projectRelativeTensor M N (rawShuffle M N u))
  rw [rawShuffle_differential, projectRelativeTensor_differential]

theorem projectRelativeTensor_surjective : Function.Surjective (projectRelativeTensor M N) :=
  TensorProduct.map_surjective (Submodule.mkQ_surjective (relC M))
    (Submodule.mkQ_surjective (relC N))

private theorem rawTensorDifferential_square (z : RawChains M ⊗[ℂ] RawChains N) :
    rawTensorDifferential M N (rawTensorDifferential M N z) = 0 := by
  obtain ⟨u, rfl⟩ := (tensorModelEquiv M N).surjective z
  rw [rawTensorDifferential_model, rawTensorDifferential_model]
  have h := LinearMap.congr_fun (CETensor.differential_comp_self plus M N) u
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [h, map_zero]

/-- Square-zero of the actual relative tensor differential. -/
theorem relativeTensorDifferential_comp_self :
    (relativeTensorDifferential M N).comp (relativeTensorDifferential M N) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨u, rfl⟩ := projectRelativeTensor_surjective M N z
  change relativeTensorDifferential M N
    (relativeTensorDifferential M N (projectRelativeTensor M N u)) = 0
  rw [← projectRelativeTensor_differential, ← projectRelativeTensor_differential,
    rawTensorDifferential_square, map_zero]

end KhanSL2.Factorization
