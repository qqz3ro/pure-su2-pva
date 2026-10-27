module

public import KhanSL2.Factorization.RelativeChainsGrading
public import KhanSL2.Factorization.ShuffleRelativeDifferential
public import KhanSL2.BGGBridge.GradingOps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Exterior Euler degree and the actual CE shuffle. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge KhanSL2.Current

private theorem exteriorEuler_action (x : G) (u : PositiveCE.Cochain) :
    FiniteExterior.euler (fun _ => (1 : ℂ)) (ColorRoot.positiveAction x u) =
      ColorRoot.positiveAction x (FiniteExterior.euler (fun _ => (1 : ℂ)) u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s c =>
    have hs : Finsupp.single s c ∈ degC s.card :=
      Finsupp.single_mem_supported ℂ c rfl
    rw [(FiniteExterior.euler_degree_eq_smul_iff _ _).mpr
      (positiveAction_mem_degC x hs),
      (FiniteExterior.euler_degree_eq_smul_iff _ _).mpr hs, map_smul]

variable (N : Type*) [AddCommGroup N] [Module ℂ N]

/-- Exterior degree before taking constant coinvariants. -/
def rawEuler : Module.End ℂ (RawChains N) :=
  LinearMap.rTensor N (FiniteExterior.euler (fun _ => (1 : ℂ)))

@[simp] theorem rawEuler_tmul (u : PositiveCE.Cochain) (n : N) :
    rawEuler N (u ⊗ₜ[ℂ] n) =
      FiniteExterior.euler (fun _ => (1 : ℂ)) u ⊗ₜ[ℂ] n := rfl

/-- The Euler operator is the usual exterior derivation under the actual comparison. -/
theorem rawEuler_J (z : LieChains.Chains ℂ plus N) :
    rawEuler N (CEModel.J z) =
      CEModel.J (LieChains.lieDeriv (1 : Module.End ℂ plus) (0 : Module.End ℂ N) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    rw [CEModel.J_tmul, rawEuler_tmul, LieChains.lieDeriv_tmul,
      LinearMap.zero_apply, TensorProduct.tmul_zero, add_zero, CEModel.J_tmul,
      exteriorEquiv_derivExt 1 formW one_plusModeBasis]
    rfl
  | add z w hz hw => simp only [map_add, hz, hw]

theorem rawEuler_of_mem_degree {j : ℕ} {z : RawChains N} (hz : z ∈ rawDegree N j) :
    rawEuler N z = (j : ℂ) • z := by
  obtain ⟨u, rfl⟩ := hz
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, rawEuler_tmul,
      (FiniteExterior.euler_degree_eq_smul_iff _ _).mpr u.property,
      TensorProduct.smul_tmul']
  | add u v hu hv => simp only [map_add, hu, hv, smul_add]

variable [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]

theorem rawEuler_actC (x : G) (z : RawChains N) :
    rawEuler N (actC N x z) = actC N x (rawEuler N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    simp only [actC, diag_tmul, map_add, rawEuler_tmul, exteriorEuler_action]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The actual exterior Euler operator on constant coinvariants. -/
def relativeEuler : Module.End ℂ (RelativeChains N) :=
  (relC N).mapQ (relC N) (rawEuler N)
    (le_comap_of_commute (actC N) (actC N) (rawEuler N) (rawEuler_actC N))

@[simp] theorem relativeEuler_mk (z : RawChains N) :
    relativeEuler N ((relC N).mkQ z) = (relC N).mkQ (rawEuler N z) := rfl

theorem relativeEuler_of_mem_degree {j : ℕ} {z : RelativeChains N}
    (hz : z ∈ degree N j) : relativeEuler N z = (j : ℂ) • z := by
  obtain ⟨u, hu, rfl⟩ := hz
  rw [relativeEuler_mk, rawEuler_of_mem_degree N hu, map_smul]

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]

/-- Total exterior Euler degree on the tensor of actual relative chains. -/
def relativeTensorEuler : Module.End ℂ (RelativeChains M ⊗[ℂ] RelativeChains N) :=
  LinearMap.rTensor (RelativeChains N) (relativeEuler M) +
    LinearMap.lTensor (RelativeChains M) (relativeEuler N)

@[simp] theorem relativeTensorEuler_tmul (u : RelativeChains M) (v : RelativeChains N) :
    relativeTensorEuler (N := N) (M := M) (u ⊗ₜ[ℂ] v) =
      relativeEuler M u ⊗ₜ[ℂ] v + u ⊗ₜ[ℂ] relativeEuler N v := rfl

omit [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
  [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M] in
private theorem tensorModelEquiv_euler (z : CETensor.TensorChains plus M N) :
    tensorModelEquiv M N (CEShuffle.tensorAction plus M N 1 0 0 z) =
      diag (rawEuler M) (rawEuler N) (tensorModelEquiv M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [CEShuffle.tensorAction_tmul, map_add, tensorModelEquiv_tmul,
      tensorModelEquiv_tmul, tensorModelEquiv_tmul, diag_tmul,
      rawEuler_J, rawEuler_J]
  | add z w hz hw => simp only [map_add, hz, hw]

omit [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
  [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M] in
/-- The canonical shuffle preserves total exterior Euler degree before quotienting. -/
theorem rawShuffle_euler (z : RawChains (M ⊗[ℂ] N)) :
    rawShuffle M N (rawEuler (M ⊗[ℂ] N) z) =
      diag (rawEuler M) (rawEuler N) (rawShuffle M N z) := by
  obtain ⟨u, rfl⟩ := (CEModel.J (N := M ⊗[ℂ] N)).surjective z
  rw [rawEuler_J, rawShuffle_J, rawShuffle_J]
  rw [← tensorModelEquiv_euler]
  apply congrArg (tensorModelEquiv M N)
  simpa only [CEShuffle.coefficientAction, LinearMap.rTensor_zero,
    LinearMap.lTensor_zero, add_zero] using
      CEShuffle.shuffle_lieDeriv plus M N (1 : Module.End ℂ plus)
        (0 : Module.End ℂ M) (0 : Module.End ℂ N) u

private theorem projectRelativeTensor_euler (z : RawChains M ⊗[ℂ] RawChains N) :
    projectRelativeTensor M N (diag (rawEuler M) (rawEuler N) z) =
      relativeTensorEuler (M := M) (N := N) (projectRelativeTensor M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [diag_tmul, map_add, projectRelativeTensor_tmul, projectRelativeTensor_tmul,
      projectRelativeTensor_tmul, relativeTensorEuler_tmul,
      relativeEuler_mk, relativeEuler_mk]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The actual quotient shuffle preserves total exterior Euler degree. -/
theorem relativeShuffle_euler (z : RelativeChains (M ⊗[ℂ] N)) :
    relativeShuffle M N (relativeEuler (M ⊗[ℂ] N) z) =
      relativeTensorEuler (M := M) (N := N) (relativeShuffle M N z) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (relC (M ⊗[ℂ] N)) z
  rw [relativeEuler_mk, relativeShuffle_mk, relativeShuffle_mk,
    rawShuffle_euler, projectRelativeTensor_euler]

end KhanSL2.Factorization
