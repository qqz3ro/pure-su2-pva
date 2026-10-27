module

public import KhanSL2.Factorization.RelativeChains
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Coefficient functoriality of the actual relative CE complex.
Constant-equivariant maps suffice to descend to coinvariants; current-equivariant
maps are additionally proved to commute with the actual CE differential. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge

variable {N M P : Type*}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]

/-- Only constant equivariance is required for maps of the underlying relative chain spaces. -/
def ConstantEquivariant (f : N →ₗ[ℂ] M) : Prop :=
  ∀ (x : G) (n : N), f ⁅constant x, n⁆ = ⁅constant x, f n⁆

omit [LieModule ℂ Current N] in
theorem ConstantEquivariant.id : ConstantEquivariant (LinearMap.id : N →ₗ[ℂ] N) :=
  fun _ _ => rfl

omit [LieModule ℂ Current N] [LieModule ℂ Current M] in
theorem ConstantEquivariant.zero : ConstantEquivariant (0 : N →ₗ[ℂ] M) := by
  intro x n
  simp

omit [LieModule ℂ Current N] [LieModule ℂ Current M] [LieModule ℂ Current P] in
theorem ConstantEquivariant.comp {f : N →ₗ[ℂ] M} {g : M →ₗ[ℂ] P}
    (hg : ConstantEquivariant g) (hf : ConstantEquivariant f) :
    ConstantEquivariant (g.comp f) := by
  intro x n
  simp only [LinearMap.comp_apply, hf x n, hg x (f n)]

omit [LieModule ℂ Current N] [LieModule ℂ Current M] in
theorem ConstantEquivariant.add {f g : N →ₗ[ℂ] M}
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) :
    ConstantEquivariant (f + g) := by
  intro x n
  simp only [LinearMap.add_apply, hf x n, hg x n, lie_add]

omit [LieModule ℂ Current N] [LieModule ℂ Current M] in
theorem constantEquivariant_of_lieHom (f : N →ₗ⁅ℂ,Current⁆ M) :
    ConstantEquivariant f.toLinearMap := fun x n => f.map_lie (constant x) n

/-- Tensor a coefficient map with the identity on the positive exterior factor. -/
def rawMap (f : N →ₗ[ℂ] M) : RawChains N →ₗ[ℂ] RawChains M :=
  LinearMap.lTensor PositiveCE.Cochain f

omit [LieRingModule Current N] [LieModule ℂ Current N]
  [LieRingModule Current M] [LieModule ℂ Current M] in
@[simp] theorem rawMap_tmul (f : N →ₗ[ℂ] M) (ω : PositiveCE.Cochain) (n : N) :
    rawMap f (ω ⊗ₜ[ℂ] n) = ω ⊗ₜ[ℂ] f n := rfl

theorem rawMap_actC (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (x : G) (z : RawChains N) : rawMap f (actC N x z) = actC M x (rawMap f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω n =>
    simp only [actC, diag_tmul, map_add, rawMap_tmul]
    exact congrArg (fun t => ColorRoot.positiveAction x ω ⊗ₜ[ℂ] f n + ω ⊗ₜ[ℂ] t)
      (hf x n)
  | add z w hz hw => simp only [map_add, hz, hw]

theorem rawMap_relations (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f) :
    relC N ≤ (relC M).comap (rawMap f) :=
  le_comap_of_commute (actC N) (actC M) (rawMap f) (rawMap_actC f hf)

/-- The actual induced map on the constant-coinvariant chain spaces. -/
def coefficientMap (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f) :
    RelativeChains N →ₗ[ℂ] RelativeChains M :=
  (relC N).mapQ (relC M) (rawMap f) (rawMap_relations f hf)

@[simp] theorem coefficientMap_mk (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (z : RawChains N) :
    coefficientMap f hf (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (rawMap f z) := rfl

@[simp] theorem coefficientMap_id :
    coefficientMap (LinearMap.id : N →ₗ[ℂ] N) ConstantEquivariant.id = LinearMap.id := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro ω n
  rfl

@[simp] theorem coefficientMap_zero :
    coefficientMap (0 : N →ₗ[ℂ] M) ConstantEquivariant.zero = 0 := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro ω n
  change Submodule.Quotient.mk (ω ⊗ₜ[ℂ] (0 : M)) = 0
  simp

theorem coefficientMap_comp (f : N →ₗ[ℂ] M) (g : M →ₗ[ℂ] P)
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) :
    coefficientMap (g.comp f) (hg.comp hf) = (coefficientMap g hg).comp (coefficientMap f hf) := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro ω n
  rfl

theorem coefficientMap_add (f g : N →ₗ[ℂ] M)
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) :
    coefficientMap (f + g) (hf.add hg) = coefficientMap f hf + coefficientMap g hg := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro ω n
  change (relC M).mkQ (ω ⊗ₜ[ℂ] (f n + g n)) =
    (relC M).mkQ (ω ⊗ₜ[ℂ] f n) + (relC M).mkQ (ω ⊗ₜ[ℂ] g n)
  rw [TensorProduct.tmul_add, map_add]

/-- Relative chains preserve coefficient surjections without a splitting assumption. -/
theorem coefficientMap_surjective (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (hs : Function.Surjective f) : Function.Surjective (coefficientMap f hf) := by
  intro z
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (relC M) z
  obtain ⟨v, rfl⟩ := LinearMap.lTensor_surjective PositiveCE.Cochain hs w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

omit [LieRingModule Current N] [LieModule ℂ Current N]
  [LieRingModule Current M] [LieModule ℂ Current M] in
/-- Coefficient maps preserve actual exterior degree before coinvariants. -/
theorem rawMap_mem_degree (f : N →ₗ[ℂ] M) {j : ℕ} {z : RawChains N}
    (hz : z ∈ rawDegree N j) : rawMap f z ∈ rawDegree M j := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨LinearMap.lTensor (degC j) f w, ?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul ω n => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

theorem coefficientMap_mem_degree (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    {j : ℕ} {z : RelativeChains N} (hz : z ∈ degree N j) :
    coefficientMap f hf z ∈ degree M j := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨rawMap f w, rawMap_mem_degree f hw, rfl⟩

/-- The coefficient map on the actual degree-j chain group. -/
def coefficientDegreeMap (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f) (j : ℕ) :
    degree N j →ₗ[ℂ] degree M j :=
  (coefficientMap f hf).restrict (fun _ h => coefficientMap_mem_degree f hf h)

@[simp] theorem coefficientDegreeMap_apply (f : N →ₗ[ℂ] M)
    (hf : ConstantEquivariant f) (j : ℕ) (z : degree N j) :
    (coefficientDegreeMap f hf j z : RelativeChains M) = coefficientMap f hf z := rfl

/-- Actual current-equivariant maps intertwine the right enveloping action. -/
theorem rightAction_natural (f : N →ₗ⁅ℂ,Current⁆ M)
    (u : PositiveEnveloping) (n : N) :
    f (ract (rightAction N) u n) = ract (rightAction M) u (f n) := by
  revert n
  refine positiveUE_induction (P := fun u => ∀ n : N,
    f (ract (rightAction N) u n) = ract (rightAction M) u (f n)) ?_ ?_ ?_ ?_ u
  · intro y n
    rw [ract_ι, ract_ι, map_neg, f.map_lie]
  · intro r n
    rw [ract_algebraMap, ract_algebraMap, map_smul]
  · intro a b ha hb n
    rw [ract_add, LinearMap.add_apply, map_add, ract_add, LinearMap.add_apply, ha, hb]
  · intro a b ha hb n
    rw [ract_mul_apply, ract_mul_apply, hb, ha]

private theorem coefficient_ev_natural (f : N →ₗ⁅ℂ,Current⁆ M)
    (t : PositiveEnveloping ⊗[ℂ] PositiveCE.Cochain) (n : N) :
    rawMap f.toLinearMap (ev (rightAction N) PositiveCE.Cochain (t ⊗ₜ[ℂ] n)) =
      ev (rightAction M) PositiveCE.Cochain (t ⊗ₜ[ℂ] f n) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u ω =>
    rw [ev_tmul_tmul, rawMap_tmul, ev_tmul_tmul]
    exact congrArg (fun v : M => ω ⊗ₜ[ℂ] v) (rightAction_natural f u n)
  | add t s ht hs => simp only [TensorProduct.add_tmul, map_add, ht, hs]

/-- Naturality holds for the genuine differential, not just for an abstract chain model. -/
theorem rawMap_differential (f : N →ₗ⁅ℂ,Current⁆ M) (z : RawChains N) :
    rawMap f.toLinearMap (rawDifferential N z) =
      rawDifferential M (rawMap f.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ω n =>
    change rawMap f.toLinearMap (base (rightAction N) FreeCE.differential (ω ⊗ₜ[ℂ] n)) =
      base (rightAction M) FreeCE.differential (ω ⊗ₜ[ℂ] f n)
    rw [base_tmul, base_tmul]
    exact coefficient_ev_natural f _ n
  | add z w hz hw => simp only [map_add, hz, hw]

theorem coefficientMap_differential (f : N →ₗ⁅ℂ,Current⁆ M) (z : RelativeChains N) :
    coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f) (differential N z) =
      differential M (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f) z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.Quotient.mk (rawMap f.toLinearMap (rawDifferential N z)) =
      Submodule.Quotient.mk (rawDifferential M (rawMap f.toLinearMap z))
    rw [rawMap_differential]

/-- Functoriality on the genuine cycle/boundary quotient in each exterior degree. -/
def homologyMap (f : N →ₗ⁅ℂ,Current⁆ M) (j : ℕ) : Homology N j →ₗ[ℂ] Homology M j :=
  (window N j).homologyMap (window M j)
    (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
    (differential_comp_self N) (differential_comp_self M)
    (LinearMap.ext (coefficientMap_differential f))
    (fun _ h => coefficientMap_mem_degree _ _ h)
    (fun _ h => coefficientMap_mem_degree _ _ h)

end KhanSL2.Factorization


