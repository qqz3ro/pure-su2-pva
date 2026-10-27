module

public import KhanSL2.Factorization.RelativeChainsAction
public import KhanSL2.Factorization.ShuffleEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Transport of the canonical CE shuffle to the existing positive exterior model,
followed by its actual descent to constant-coinvariant relative chains. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge KhanSL2.Current

variable (M N : Type*)
  [AddCommGroup M] [Module ℂ M] [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]

/-- The canonical comparison on the two target chain factors. -/
def tensorModelEquiv : CETensor.TensorChains plus M N ≃ₗ[ℂ]
    (RawChains M ⊗[ℂ] RawChains N) :=
  TensorProduct.congr (CEModel.J (N := M)) (CEModel.J (N := N))

omit [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
  [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N] in
@[simp] theorem tensorModelEquiv_tmul (u : LieChains.Chains ℂ plus M)
    (v : LieChains.Chains ℂ plus N) :
    tensorModelEquiv M N (u ⊗ₜ[ℂ] v) = CEModel.J u ⊗ₜ[ℂ] CEModel.J v := rfl

/-- The canonical CE shuffle in the project's existing exterior chain model. -/
def rawShuffle : RawChains (M ⊗[ℂ] N) →ₗ[ℂ] (RawChains M ⊗[ℂ] RawChains N) :=
  (tensorModelEquiv M N).toLinearMap.comp
    ((CEShuffle.shuffle plus M N).comp (CEModel.J (N := M ⊗[ℂ] N)).symm.toLinearMap)

omit [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
  [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N] in
@[simp] theorem rawShuffle_J (z : LieChains.Chains ℂ plus (M ⊗[ℂ] N)) :
    rawShuffle M N (CEModel.J z) = tensorModelEquiv M N (CEShuffle.shuffle plus M N z) := by
  simp only [rawShuffle, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- The signed tensor boundary transported by the actual exterior comparison. -/
def rawTensorDifferential : Module.End ℂ (RawChains M ⊗[ℂ] RawChains N) :=
  (tensorModelEquiv M N).toLinearMap.comp
    ((CETensor.differential plus M N).comp (tensorModelEquiv M N).symm.toLinearMap)

@[simp] theorem rawTensorDifferential_model (z : CETensor.TensorChains plus M N) :
    rawTensorDifferential M N (tensorModelEquiv M N z) =
      tensorModelEquiv M N (CETensor.differential plus M N z) := by
  simp only [rawTensorDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- The transported shuffle intertwines the actual coefficient CE differential. -/
theorem rawShuffle_differential (z : RawChains (M ⊗[ℂ] N)) :
    rawShuffle M N (rawDifferential (M ⊗[ℂ] N) z) =
      rawTensorDifferential M N (rawShuffle M N z) := by
  obtain ⟨u, rfl⟩ := (CEModel.J (N := M ⊗[ℂ] N)).surjective z
  rw [show rawDifferential (M ⊗[ℂ] N) (CEModel.J u) =
      CEModel.J (LieChains.boundary (M ⊗[ℂ] N) u) from (CEModel.J_boundary u).symm,
    rawShuffle_J, rawShuffle_J, rawTensorDifferential_model, CEShuffle.shuffle_boundary]

private theorem tensorModelEquiv_action (a : Fin 3) (z : CETensor.TensorChains plus M N) :
    tensorModelEquiv M N
      (CEShuffle.tensorAction plus M N (relD a)
        (LieModule.toEnd ℂ BGG.Current M (constant (MatrixSL2.color a)))
        (LieModule.toEnd ℂ BGG.Current N (constant (MatrixSL2.color a))) z) =
      diag (actC M (MatrixSL2.color a)) (actC N (MatrixSL2.color a)) (tensorModelEquiv M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [CEShuffle.tensorAction_tmul, map_add, tensorModelEquiv_tmul,
      tensorModelEquiv_tmul, tensorModelEquiv_tmul, diag_tmul]
    change CEModel.J (CEModel.constantAction a u) ⊗ₜ[ℂ] CEModel.J v +
      CEModel.J u ⊗ₜ[ℂ] CEModel.J (CEModel.constantAction a v) = _
    rw [CEModel.J_constantAction, CEModel.J_constantAction]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem rawShuffle_actC_color (a : Fin 3) (z : RawChains (M ⊗[ℂ] N)) :
    rawShuffle M N (actC (M ⊗[ℂ] N) (MatrixSL2.color a) z) =
      diag (actC M (MatrixSL2.color a)) (actC N (MatrixSL2.color a)) (rawShuffle M N z) := by
  obtain ⟨u, rfl⟩ := (CEModel.J (N := M ⊗[ℂ] N)).surjective z
  rw [← CEModel.J_constantAction, rawShuffle_J, rawShuffle_J]
  change tensorModelEquiv M N
      (CEShuffle.shuffle plus M N (LieChains.lieDeriv (relD a)
        (CEShuffle.coefficientAction M N
          (LieModule.toEnd ℂ BGG.Current M (constant (MatrixSL2.color a)))
          (LieModule.toEnd ℂ BGG.Current N (constant (MatrixSL2.color a)))) u)) = _
  rw [CEShuffle.shuffle_lieDeriv, tensorModelEquiv_action]

private theorem tensorAction_sum (x : G) (z : RawChains M ⊗[ℂ] RawChains N) :
    diag (actC M x) (actC N x) z =
      ∑ a : Fin 3, FreeCE.colorBasis.repr x a •
        diag (actC M (MatrixSL2.color a)) (actC N (MatrixSL2.color a)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [diag_tmul, CEModel.actC_sum, CEModel.actC_sum]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, diag_tmul,
      smul_add, Finset.sum_add_distrib]
  | add z w hz hw => simp only [map_add, hz, hw, smul_add, Finset.sum_add_distrib]

/-- The canonical shuffle is equivariant for the actual outer constant action. -/
theorem rawShuffle_actC (x : G) (z : RawChains (M ⊗[ℂ] N)) :
    rawShuffle M N (actC (M ⊗[ℂ] N) x z) =
      diag (actC M x) (actC N x) (rawShuffle M N z) := by
  rw [CEModel.actC_sum, map_sum]
  simp_rw [map_smul, rawShuffle_actC_color]
  exact (tensorAction_sum M N x (rawShuffle M N z)).symm

/-- Pass both output factors to their actual relative quotients. -/
def projectRelativeTensor : RawChains M ⊗[ℂ] RawChains N →ₗ[ℂ]
    RelativeChains M ⊗[ℂ] RelativeChains N :=
  TensorProduct.map (relC M).mkQ (relC N).mkQ

@[simp] theorem projectRelativeTensor_tmul (u : RawChains M) (v : RawChains N) :
    projectRelativeTensor M N (u ⊗ₜ[ℂ] v) =
      (relC M).mkQ u ⊗ₜ[ℂ] (relC N).mkQ v := rfl

private theorem mkQ_actC (x : G) (z : RawChains M) : (relC M).mkQ (actC M x z) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_iSup_of_mem x ⟨z, rfl⟩

/-- Every diagonal constant relation vanishes after taking the two relative quotients. -/
theorem projectRelativeTensor_action (x : G) (z : RawChains M ⊗[ℂ] RawChains N) :
    projectRelativeTensor M N (diag (actC M x) (actC N x) z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [diag_tmul, map_add, projectRelativeTensor_tmul, projectRelativeTensor_tmul,
      mkQ_actC, mkQ_actC]
    simp
  | add z w hz hw => simp only [map_add, hz, hw, add_zero]

/-- Well-definedness of the canonical shuffle on actual constant coinvariants. -/
theorem rawShuffle_relations : relC (M ⊗[ℂ] N) ≤
    LinearMap.ker ((projectRelativeTensor M N).comp (rawShuffle M N)) := by
  apply iSup_le
  rintro x _ ⟨z, rfl⟩
  change projectRelativeTensor M N (rawShuffle M N (actC (M ⊗[ℂ] N) x z)) = 0
  rw [rawShuffle_actC, projectRelativeTensor_action]

/-- The specified relative CE shuffle; its relation-preservation proof is unconditional. -/
def relativeShuffle : RelativeChains (M ⊗[ℂ] N) →ₗ[ℂ]
    RelativeChains M ⊗[ℂ] RelativeChains N :=
  (relC (M ⊗[ℂ] N)).liftQ
    ((projectRelativeTensor M N).comp (rawShuffle M N)) (rawShuffle_relations M N)

@[simp] theorem relativeShuffle_mk (z : RawChains (M ⊗[ℂ] N)) :
    relativeShuffle M N ((relC (M ⊗[ℂ] N)).mkQ z) =
      projectRelativeTensor M N (rawShuffle M N z) := rfl

end KhanSL2.Factorization

