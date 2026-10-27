module

public import KhanSL2.Factorization.FiniteBGGTransferHomotopy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.BGGTransfer
open BGG BGGBridge

variable {N M P : Type}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]

/-- The unchanged harmonic tensor factor makes BGG coefficient maps functorial. -/
def harmonicRawMap (f : N →ₗ[ℂ] M) : HarmN N →ₗ[ℂ] HarmN M :=
  LinearMap.lTensor PositiveCE.Harmonic f

theorem harmonicRawMap_act (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (x : G) (z : HarmN N) : harmonicRawMap f (actH N x z) =
      actH M x (harmonicRawMap f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul h n =>
    simp only [harmonicRawMap,actH,diag_tmul,map_add,LinearMap.lTensor_tmul,
      LieModule.toEnd_apply_apply]
    rw [hf]

def harmonicMap (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f) :
    HarmonicQuotient N →ₗ[ℂ] HarmonicQuotient M :=
  (relH N).mapQ (relH M) (harmonicRawMap f)
    (le_comap_of_commute (actH N) (actH M) (harmonicRawMap f)
      (harmonicRawMap_act f hf))

@[simp] theorem harmonicMap_mk (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (z : HarmN N) : harmonicMap f hf ((relH N).mkQ z) =
      (relH M).mkQ (harmonicRawMap f z) := rfl

@[simp] theorem harmonicMap_id :
    harmonicMap (LinearMap.id : N →ₗ[ℂ] N) ConstantEquivariant.id = LinearMap.id := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro h n
  rfl

theorem harmonicMap_comp (f : N →ₗ[ℂ] M) (g : M →ₗ[ℂ] P)
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) :
    harmonicMap (g.comp f) (hg.comp hf) = (harmonicMap g hg).comp (harmonicMap f hf) := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro h n
  rfl

/-- Arbitrary current coefficient maps commute with base change of every
universal free-chain map, including the BGG differential and contraction. -/
theorem base_coefficient_natural {U V : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] (f : N →ₗ⁅ℂ,Current⁆ M)
    (F : PositiveEnveloping ⊗[ℂ] U →ₗ[PositiveEnveloping] PositiveEnveloping ⊗[ℂ] V)
    (z : U ⊗[ℂ] N) :
    LinearMap.lTensor V f.toLinearMap (base (rightAction N) F z) =
      base (rightAction M) F (LinearMap.lTensor U f.toLinearMap z) := by
  have hev (t : PositiveEnveloping ⊗[ℂ] V) (n : N) :
      LinearMap.lTensor V f.toLinearMap (ev (rightAction N) V (t ⊗ₜ[ℂ] n)) =
        ev (rightAction M) V (t ⊗ₜ[ℂ] f n) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t u ht hu => simp only [TensorProduct.add_tmul,map_add,ht,hu]
    | tmul u v =>
      rw [ev_tmul_tmul,LinearMap.lTensor_tmul,ev_tmul_tmul]
      exact congrArg (fun m : M => v ⊗ₜ[ℂ] m) (rightAction_natural f u n)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul u n =>
    rw [base_tmul,LinearMap.lTensor_tmul,base_tmul]
    exact hev _ n

theorem harmonicMap_differential (f : N →ₗ⁅ℂ,Current⁆ M) (z : HarmonicQuotient N) :
    harmonicMap f.toLinearMap (constantEquivariant_of_lieHom f) (dHq N z) =
      dHq M (harmonicMap f.toLinearMap (constantEquivariant_of_lieHom f) z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (relH M).mkQ (harmonicRawMap f.toLinearMap (dH N z)) =
      (relH M).mkQ (dH M (harmonicRawMap f.toLinearMap z))
    exact congrArg (relH M).mkQ (base_coefficient_natural f PositiveTransfer.differential z)

end KhanSL2.Factorization.BGGTransfer

