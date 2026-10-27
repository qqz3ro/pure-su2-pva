module

public import KhanSL2.Factorization.CoefficientTotalScalars
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Tensor products over ℂ with the genuine joint action of two independent
coefficient rings. On pure tensors the action is (r⊗s)(m⊗n)=rm⊗sn. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization

/-- A separate scalar interpretation of the ordinary vector-space tensor product. -/
def ExternalTensor (_R _S M N : Type) [AddCommGroup M] [AddCommGroup N]
    [Module ℂ M] [Module ℂ N] : Type := M ⊗[ℂ] N

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]

/-- The prescribed independent coefficient actions, before any homology is taken. -/
def externalTensorAction : R ⊗[ℂ] S →ₐ[ℂ] Module.End ℂ (M ⊗[ℂ] N) :=
  (Module.endTensorEndAlgHom (R:=ℂ) (S:=ℂ) (A:=ℂ) (M:=M) (N:=N)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ M : R →ₐ[ℂ] Module.End ℂ M)
      (Algebra.lsmul ℂ ℂ N : S →ₐ[ℂ] Module.End ℂ N))

instance : AddCommGroup (ExternalTensor R S M N) := inferInstanceAs (AddCommGroup (M ⊗[ℂ] N))
instance : Module ℂ (ExternalTensor R S M N) := inferInstanceAs (Module ℂ (M ⊗[ℂ] N))
instance : Module (R ⊗[ℂ] S) (ExternalTensor R S M N) :=
  Module.compHom (M ⊗[ℂ] N) (externalTensorAction R S M N).toRingHom

/-- Forgetting the joint scalar structure changes no vector. -/
def externalTensorEquiv : ExternalTensor R S M N ≃ₗ[ℂ] M ⊗[ℂ] N := LinearEquiv.refl ℂ _

@[simp] theorem externalTensor_smul_tmul (r : R) (s : S) (m : M) (n : N) :
    (r ⊗ₜ[ℂ] s) • ((externalTensorEquiv R S M N).symm (m ⊗ₜ[ℂ] n)) =
      (externalTensorEquiv R S M N).symm ((r • m) ⊗ₜ[ℂ] (s • n)) := rfl

/-- Compatibility with the original complex scalar multiplication. -/
instance externalTensor_isScalarTower : IsScalarTower ℂ (R ⊗[ℂ] S) (ExternalTensor R S M N) where
  smul_assoc c r x :=
    LinearMap.congr_fun ((externalTensorAction R S M N).toLinearMap.map_smul c r) x

instance externalTensor_smulCommClass : SMulCommClass ℂ (R ⊗[ℂ] S) (ExternalTensor R S M N) where
  smul_comm c r x := (map_smul (externalTensorAction R S M N r) c x).symm

variable {M N}
variable {P Q : Type} [AddCommGroup P] [AddCommGroup Q]
  [Module ℂ P] [Module R P] [IsScalarTower ℂ R P]
  [Module ℂ Q] [Module S Q] [IsScalarTower ℂ S Q]

/-- The tensor of the two original coefficient-linear maps is jointly coefficient-linear. -/
def externalTensorMap (f : M →ₗ[R] P) (g : N →ₗ[S] Q) :
    ExternalTensor R S M N →ₗ[R ⊗[ℂ] S] ExternalTensor R S P Q where
  toFun z := TensorProduct.map (f.restrictScalars ℂ) (g.restrictScalars ℂ) z
  map_add' := map_add _
  map_smul' c z := by
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [add_smul,map_add,hc,hd]
    | tmul r s =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [smul_add,map_add,hz,hw]
      | tmul m n =>
        change f (r • m) ⊗ₜ[ℂ] g (s • n) = (r • f m) ⊗ₜ[ℂ] (s • g n)
        rw [map_smul,map_smul]

end KhanSL2.Factorization
