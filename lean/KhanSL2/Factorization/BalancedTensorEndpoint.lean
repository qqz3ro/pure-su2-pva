module

public import KhanSL2.Factorization.BalancedTensorDifferential

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

/-- The actual balanced boundary agrees with the categorical degree-lowering map. -/
theorem balancedTensorDegreeForget_boundary (j : ℕ)
    (z : (balancedTensorComplex A M N).X (j+1)) :
    balancedTensorDegreeForget A M N j ((balancedTensorComplex A M N).d (j+1) j z) =
      balancedTensorDifferential A M N (balancedTensorDegreeForget A M N (j+1) z) := by
  exact congrArg (fun f => f.hom z) (balancedTensorDegreeForget_differential A M N j)

/-- The genuine signed balanced boundary vanishes in total degree zero. -/
theorem balancedTensorDegreeForget_zero_boundary (z : (balancedTensorComplex A M N).X 0) :
    balancedTensorDifferential A M N (balancedTensorDegreeForget A M N 0 z) = 0 := by
  have h : ModuleCat.ofHom ((balancedTensorDifferential A M N).comp
      (balancedTensorDegreeForget A M N 0)) = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p+q=0 at hpq
    have hp : p=0 := by omega
    have hq : q=0 := by omega
    subst p
    subst q
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change degree M 0 at u
    change degree N 0 at v
    change balancedTensorDifferential A M N (balancedTensorDegreeForget A M N 0
      (balancedTensorDegreeInclusion A M N 0 0 0 hpq (u ⊗ₜ[A] v))) = 0
    rw [balancedTensorDegreeForget_inclusion,TensorProduct.map_tmul]
    change balancedTensorDifferential A M N (u.val ⊗ₜ[A] v.val) = 0
    rw [balancedTensorDifferential_tmul,
      differential_eq_zero_of_degree_zero M u.property,
      differential_eq_zero_of_degree_zero N v.property]
    simp
  exact congrArg (fun f => f.hom z) h

/-- The outgoing boundary identity includes the endpoint of the nonnegative complex. -/
theorem balancedTensorComplex_d_out_apply (j : ℕ) (z : (balancedTensorComplex A M N).X j) :
    balancedTensorDegreeForget A M N (j-1) ((balancedTensorComplex A M N).d j (j-1) z) =
      balancedTensorDifferential A M N (balancedTensorDegreeForget A M N j z) := by
  cases j with
  | zero =>
    rw [(balancedTensorComplex A M N).shape 0 0 (show ¬ (ComplexShape.down ℕ).Rel 0 0 by simp)]
    change balancedTensorDegreeForget A M N 0 0 = _
    rw [map_zero]
    exact (balancedTensorDegreeForget_zero_boundary A M N z).symm
  | succ j =>
    simp only [Nat.add_one_sub_one]
    exact balancedTensorDegreeForget_boundary A M N j z

end KhanSL2.Factorization
