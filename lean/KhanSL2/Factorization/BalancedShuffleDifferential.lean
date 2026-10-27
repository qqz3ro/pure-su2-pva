module

public import KhanSL2.Factorization.BalancedShuffleRelative
public import KhanSL2.Factorization.ShuffleParityDegree

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass

theorem relativeParity_coefficient_smul (a : A) (z : RelativeChains M) :
    relativeParity M (a • z) = a • relativeParity M z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (relC M).mkQ (rawParity M (rawMap (coefficientScalarLieHom A M a).toLinearMap z)) =
      (relC M).mkQ (rawMap (coefficientScalarLieHom A M a).toLinearMap (rawParity M z))
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,hz,hw]
    | tmul ω m => simp only [rawMap_tmul,rawParity_tmul]

def coefficientParityLinear : Module.End A (RelativeChains M) where
  __ := (relativeParity M).toAddMonoidHom
  map_smul' := relativeParity_coefficient_smul A M

/-- The signed tensor boundary over the coefficient algebra. -/
def balancedTensorDifferential : Module.End A (RelativeChains M ⊗[A] RelativeChains N) :=
  TensorProduct.map (coefficientDifferentialLinear A M) LinearMap.id +
    TensorProduct.map (coefficientParityLinear A M) (coefficientDifferentialLinear A N)

@[simp] theorem balancedTensorDifferential_tmul (u : RelativeChains M) (v : RelativeChains N) :
    balancedTensorDifferential A M N (u ⊗ₜ[A] v) =
      differential M u ⊗ₜ[A] v + relativeParity M u ⊗ₜ[A] differential N v := rfl

theorem relativeTensorBalance_differential (z : RelativeChains M ⊗[ℂ] RelativeChains N) :
    relativeTensorBalance A M N (relativeTensorDifferential M N z) =
      balancedTensorDifferential A M N (relativeTensorBalance A M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul u v =>
    rw [relativeTensorDifferential_tmul,map_add,relativeTensorBalance_tmul,
      relativeTensorBalance_tmul,relativeTensorBalance_tmul,balancedTensorDifferential_tmul]

/-- Balancing retains the original square-zero signed tensor differential. -/
theorem balancedTensorDifferential_square :
    (balancedTensorDifferential A M N).comp (balancedTensorDifferential A M N) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨u,rfl⟩ := balancedCoefficientMap_surjective A (RelativeChains M) (RelativeChains N) z
  change balancedTensorDifferential A M N
    (balancedTensorDifferential A M N (relativeTensorBalance A M N u)) = 0
  rw [← relativeTensorBalance_differential,← relativeTensorBalance_differential]
  have h := LinearMap.congr_fun (relativeTensorDifferential_comp_self M N) u
  change relativeTensorDifferential M N (relativeTensorDifferential M N u) = 0 at h
  rw [h,map_zero]

/-- The balanced shuffle intertwines the actual CE and signed tensor boundaries. -/
theorem balancedRelativeShuffle_differential (z : RelativeChains (BalancedCoefficients A M N)) :
    balancedRelativeShuffle A M N (differential (BalancedCoefficients A M N) z) =
      balancedTensorDifferential A M N (balancedRelativeShuffle A M N z) := by
  obtain ⟨u,rfl⟩ := coefficientMap_surjective (balancedCoefficientLieHom A M N).toLinearMap
    (constantEquivariant_of_lieHom (balancedCoefficientLieHom A M N))
    (balancedCoefficientMap_surjective A M N) z
  rw [← coefficientMap_differential (balancedCoefficientLieHom A M N),
    balancedRelativeShuffle_balance,balancedRelativeShuffle_balance,relativeShuffle_differential,
    relativeTensorBalance_differential]

end KhanSL2.Factorization
