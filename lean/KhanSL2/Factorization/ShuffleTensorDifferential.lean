module

public import KhanSL2.Factorization.ShuffleChainParity

@[expose] public section

/-! The genuine signed tensor differential and its Cartan identity. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.CETensor
open KhanSL2.LieChains

variable (L M N : Type*) [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule L N] [LieModule ℂ L N]

abbrev TensorChains := Chains ℂ L M ⊗[ℂ] Chains ℂ L N

/-- The ordinary tensor-complex boundary, with the sign from the left exterior degree. -/
def differential : Module.End ℂ (TensorChains L M N) :=
  LinearMap.rTensor (Chains ℂ L N) (boundary M) +
    TensorProduct.map (CEParity.parity L M) (boundary N)

/-- Creation acts diagonally, with the same Koszul sign. -/
def create (y : L) : Module.End ℂ (TensorChains L M N) :=
  LinearMap.rTensor (Chains ℂ L N) (wedgeLeft M y) +
    TensorProduct.map (CEParity.parity L M) (wedgeLeft N y)

/-- The even diagonal Lie derivative on the two CE factors. -/
def action (y : L) : Module.End ℂ (TensorChains L M N) :=
  LinearMap.rTensor (Chains ℂ L N) (theta M y) +
    LinearMap.lTensor (Chains ℂ L M) (theta N y)

@[simp] theorem differential_tmul (u : Chains ℂ L M) (v : Chains ℂ L N) :
    differential L M N (u ⊗ₜ[ℂ] v) =
      boundary M u ⊗ₜ[ℂ] v + CEParity.parity L M u ⊗ₜ[ℂ] boundary N v := rfl

omit [LieRingModule L M] [LieModule ℂ L M] [LieRingModule L N] [LieModule ℂ L N] in
@[simp] theorem create_tmul (y : L) (u : Chains ℂ L M) (v : Chains ℂ L N) :
    create L M N y (u ⊗ₜ[ℂ] v) =
      wedgeLeft M y u ⊗ₜ[ℂ] v + CEParity.parity L M u ⊗ₜ[ℂ] wedgeLeft N y v := rfl

@[simp] theorem action_tmul (y : L) (u : Chains ℂ L M) (v : Chains ℂ L N) :
    action L M N y (u ⊗ₜ[ℂ] v) = theta M y u ⊗ₜ[ℂ] v + u ⊗ₜ[ℂ] theta N y v := rfl

/-- Square-zero is proved using the actual boundary and its odd parity. -/
theorem differential_comp_self : (differential L M N).comp (differential L M N) = 0 := by
  apply TensorProduct.ext'
  intro u v
  simp only [LinearMap.comp_apply, differential_tmul, map_add, boundary_boundary,
    CEParity.boundary_parity, CEParity.parity_parity, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, TensorProduct.neg_tmul, LinearMap.zero_apply]
  abel

/-- Cartan's identity on the tensor complex. -/
theorem differential_create (y : L) (z : TensorChains L M N) :
    differential L M N (create L M N y z) =
      -action L M N y z - create L M N y (differential L M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; abel
  | tmul u v =>
    simp only [create_tmul, differential_tmul, action_tmul, map_add,
      boundary_wedgeLeft, CEParity.parity_wedge, CEParity.boundary_parity,
      CEParity.parity_parity, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
      TensorProduct.neg_tmul, TensorProduct.tmul_neg]
    abel
  | add z w hz hw => simp only [map_add, hz, hw]; abel

end KhanSL2.Factorization.CETensor


