module

public import KhanSL2.Factorization.BalancedTensorProjection
public import KhanSL2.Factorization.RelativeChainsTotalHomology

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass

/-- The actual degree component intertwines the boundary with its successor component. -/
theorem balancedTensorDegreeComponent_differential (j : ℕ)
    (z : RelativeChains M ⊗[A] RelativeChains N) :
    balancedTensorDegreeComponent A M N j (balancedTensorDifferential A M N z) =
      (balancedTensorComplex A M N).d (j+1) j (balancedTensorDegreeComponent A M N (j+1) z) := by
  apply balancedTensorDegreeForget_injective A M N j
  have hd := congrArg (fun f => f.hom (balancedTensorDegreeComponent A M N (j+1) z))
    (balancedTensorDegreeForget_differential A M N j)
  change balancedTensorDegreeProjection A M N j (balancedTensorDifferential A M N z) = _
  rw [balancedTensorDegreeProjection_differential]
  exact hd.symm

/-- The actual total boundary vanishes on exterior degree zero of the balanced tensor. -/
theorem balancedTensorDegreeForget_zero_differential (z : (balancedTensorComplex A M N).X 0) :
    balancedTensorDifferential A M N (balancedTensorDegreeForget A M N 0 z) = 0 := by
  have he : ModuleCat.ofHom ((balancedTensorDifferential A M N).comp
      (balancedTensorDegreeForget A M N 0)) = 0 := by
    apply mapBifunctor.hom_ext
    intro p q h
    change p+q=0 at h
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero.mp h
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro u v
    change balancedTensorDifferential A M N
      (balancedTensorDegreeForget A M N 0 (balancedTensorDegreeInclusion A M N 0 0 0 rfl (u ⊗ₜ[A] v))) = 0
    rw [balancedTensorDegreeForget_inclusion,TensorProduct.map_tmul]
    change balancedTensorDifferential A M N (u.val ⊗ₜ[A] v.val) = 0
    rw [balancedTensorDifferential_tmul,
      differential_eq_zero_of_degree_zero M u.property,
      differential_eq_zero_of_degree_zero N v.property]
    simp
  exact congrArg (fun f => f.hom z) he

/-- Categorical tensor cycles are exactly the homogeneous total cycles, including degree zero. -/
theorem balancedTensorDegree_cycle_iff (j : ℕ) (z : (balancedTensorComplex A M N).X j) :
    (balancedTensorComplex A M N).d j (j-1) z = 0 ↔
      balancedTensorDifferential A M N (balancedTensorDegreeForget A M N j z) = 0 := by
  cases j with
  | zero =>
    have hd : (balancedTensorComplex A M N).d 0 0 = 0 :=
      (balancedTensorComplex A M N).shape 0 0 (by simp)
    simp only [Nat.zero_sub,hd,balancedTensorDegreeForget_zero_differential]
    exact iff_of_true rfl trivial
  | succ j =>
    rw [Nat.succ_sub_one]
    have hd := congrArg (fun f => f.hom z) (balancedTensorDegreeForget_differential A M N j)
    change balancedTensorDegreeForget A M N j ((balancedTensorComplex A M N).d (j+1) j z) =
      balancedTensorDifferential A M N (balancedTensorDegreeForget A M N (j+1) z) at hd
    rw [← hd]
    exact (map_eq_zero_iff (balancedTensorDegreeForget A M N j)
      (balancedTensorDegreeForget_injective A M N j)).symm

variable (L : Type) [AddCommGroup L] [Module ℂ L] [Module A L] [IsScalarTower ℂ A L]
  [LieRingModule Current L] [LieModule ℂ Current L] [CoefficientLinearCurrent A L]

/-- The same cycle identification for the original coefficient CE source. -/
theorem coefficientDegree_cycle_iff (j : ℕ) (z : (coefficientRelativeComplex A L).X j) :
    (coefficientRelativeComplex A L).d j (j-1) z = 0 ↔ differential L z.val = 0 := by
  cases j with
  | zero =>
    have hd : (coefficientRelativeComplex A L).d 0 0 = 0 :=
      (coefficientRelativeComplex A L).shape 0 0 (by simp)
    simp only [Nat.zero_sub,hd,differential_eq_zero_of_degree_zero L z.property]
    exact iff_of_true rfl trivial
  | succ j =>
    rw [Nat.succ_sub_one,coefficientRelativeComplex_d]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h

end KhanSL2.Factorization

