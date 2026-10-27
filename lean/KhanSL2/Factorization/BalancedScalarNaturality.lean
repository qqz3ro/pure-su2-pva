module

public import KhanSL2.Factorization.BalancedScalarComplex

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
variable (K : Type) [CommRing K] [Algebra A K] [Algebra ℂ K] [IsScalarTower ℂ A K]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass

/-- The canonical scalar-extension map on the balanced tensor of actual chains. -/
def balancedChainScalarTensorMap :
    K ⊗[A] (RelativeChains M ⊗[A] RelativeChains N) →ₗ[K]
      RelativeChains (CoefficientBaseChange A M K) ⊗[K] RelativeChains (CoefficientBaseChange A N K) :=
  (TensorProduct.map (relativeChainsScalarMap A M K) (relativeChainsScalarMap A N K)).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange A K (RelativeChains M) (RelativeChains N)).toLinearMap

@[simp] theorem balancedChainScalarTensorMap_tmul (k : K) (u : RelativeChains M) (v : RelativeChains N) :
    balancedChainScalarTensorMap A M N K (k ⊗ₜ[A] (u ⊗ₜ[A] v)) =
      relativeChainsScalarMap A M K (k ⊗ₜ[A] u) ⊗ₜ[K]
        relativeChainsScalarMap A N K (1 ⊗ₜ[A] v) := rfl

/-- The actual current-module scalar unit for balanced coefficients. -/
def balancedScalarCoefficientUnit : BalancedCoefficients A M N →ₗ⁅ℂ,Current⁆
    BalancedCoefficients K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) :=
  (balancedBaseChangeEquiv A M N K).toLieModuleHom.comp
    (coefficientBaseChangeUnit A (BalancedCoefficients A M N) K)

omit [LieModule ℂ Current M] [LieModule ℂ Current N] in
/-- Its square with the original unbalanced coefficient units commutes literally. -/
theorem balancedScalarCoefficientUnit_balance :
    (balancedScalarCoefficientUnit A M N K).toLinearMap.comp (balancedCoefficientMap A M N) =
      (balancedCoefficientMap K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)).comp
        (TensorProduct.map (coefficientBaseChangeUnit A M K).toLinearMap
          (coefficientBaseChangeUnit A N K).toLinearMap) := by
  apply TensorProduct.ext'
  intro m n
  rfl

/-- The original tensor-chain units commute with coefficient balancing. -/
theorem balancedChainScalarTensorMap_unit_balance (z : RelativeChains M ⊗[ℂ] RelativeChains N) :
    balancedChainScalarTensorMap A M N K (1 ⊗ₜ[A] relativeTensorBalance A M N z) =
      relativeTensorBalance K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)
        (TensorProduct.map
          (coefficientMap (coefficientBaseChangeUnit A M K).toLinearMap
            (constantEquivariant_of_lieHom (coefficientBaseChangeUnit A M K)))
          (coefficientMap (coefficientBaseChangeUnit A N K).toLinearMap
            (constantEquivariant_of_lieHom (coefficientBaseChangeUnit A N K))) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,TensorProduct.tmul_add,hu,hv]
  | tmul u v =>
    rw [relativeTensorBalance_tmul,balancedChainScalarTensorMap_tmul,
      TensorProduct.map_tmul,relativeTensorBalance_tmul]
    change (1:K) • coefficientMap (coefficientBaseChangeUnit A M K).toLinearMap
      (constantEquivariant_of_lieHom (coefficientBaseChangeUnit A M K)) u ⊗ₜ[K]
        ((1:K) • coefficientMap (coefficientBaseChangeUnit A N K).toLinearMap
          (constantEquivariant_of_lieHom (coefficientBaseChangeUnit A N K)) v) = _
    rw [one_smul,one_smul]

/-- The true balanced shuffle commutes with the scalar unit on actual chains. -/
theorem balancedRelativeShuffle_scalarUnit (z : RelativeChains (BalancedCoefficients A M N)) :
    balancedRelativeShuffle K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)
      (coefficientMap (balancedScalarCoefficientUnit A M N K).toLinearMap
        (constantEquivariant_of_lieHom (balancedScalarCoefficientUnit A M N K)) z) =
      balancedChainScalarTensorMap A M N K (1 ⊗ₜ[A] balancedRelativeShuffle A M N z) := by
  obtain ⟨u,rfl⟩ := coefficientMap_surjective (balancedCoefficientLieHom A M N).toLinearMap
    (constantEquivariant_of_lieHom (balancedCoefficientLieHom A M N))
    (balancedCoefficientMap_surjective A M N) z
  have hc : coefficientMap (balancedScalarCoefficientUnit A M N K).toLinearMap
      (constantEquivariant_of_lieHom (balancedScalarCoefficientUnit A M N K))
      (coefficientMap (balancedCoefficientLieHom A M N).toLinearMap
        (constantEquivariant_of_lieHom (balancedCoefficientLieHom A M N)) u) =
    coefficientMap (balancedCoefficientLieHom K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)).toLinearMap
      (constantEquivariant_of_lieHom (balancedCoefficientLieHom K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)))
      (coefficientMap (TensorProduct.map (coefficientBaseChangeUnit A M K).toLinearMap
        (coefficientBaseChangeUnit A N K).toLinearMap)
        ((constantEquivariant_of_lieHom (coefficientBaseChangeUnit A M K)).tensorMap
          (constantEquivariant_of_lieHom (coefficientBaseChangeUnit A N K))) u) := by
    induction u using Submodule.Quotient.induction_on with
    | _ u =>
      change (relC _).mkQ (rawMap _ (rawMap _ u)) = (relC _).mkQ (rawMap _ (rawMap _ u))
      congr 1
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => simp only [map_add,hu,hv]
      | tmul ω t =>
        apply congrArg (fun z => ω ⊗ₜ[ℂ] z)
        exact LinearMap.congr_fun (balancedScalarCoefficientUnit_balance A M N K) t
  rw [hc,balancedRelativeShuffle_balance,relativeShuffle_coeffMap,
    balancedRelativeShuffle_balance,balancedChainScalarTensorMap_unit_balance]
/-- The canonical scalar-extension map on the actual balanced-coefficient chains. -/
def balancedChainScalarSourceMap : K ⊗[A] RelativeChains (BalancedCoefficients A M N) →ₗ[K]
    RelativeChains (BalancedCoefficients K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)) :=
  (coefficientMapLinear K (balancedBaseChangeEquiv A M N K).toLieModuleHom
    (balancedBaseChangeLinearEquiv A M N K).map_smul).comp
      (relativeChainsScalarMap A (BalancedCoefficients A M N) K)

@[simp] theorem balancedChainScalarSourceMap_tmul (k : K)
    (z : RelativeChains (BalancedCoefficients A M N)) :
    balancedChainScalarSourceMap A M N K (k ⊗ₜ[A] z) =
      k • coefficientMap (balancedScalarCoefficientUnit A M N K).toLinearMap
        (constantEquivariant_of_lieHom (balancedScalarCoefficientUnit A M N K)) z := by
  change coefficientMapLinear K (balancedBaseChangeEquiv A M N K).toLieModuleHom
    (balancedBaseChangeLinearEquiv A M N K).map_smul
    (k • coefficientMap (coefficientBaseChangeUnit A (BalancedCoefficients A M N) K).toLinearMap
      (constantEquivariant_of_lieHom (coefficientBaseChangeUnit A (BalancedCoefficients A M N) K)) z) = _
  rw [map_smul]
  congr 1
  exact (LinearMap.congr_fun (coefficientMap_comp
    (coefficientBaseChangeUnit A (BalancedCoefficients A M N) K).toLinearMap
    (balancedBaseChangeEquiv A M N K).toLieModuleHom.toLinearMap
    (constantEquivariant_of_lieHom (coefficientBaseChangeUnit A (BalancedCoefficients A M N) K))
    (constantEquivariant_of_lieHom (balancedBaseChangeEquiv A M N K).toLieModuleHom)) z).symm

/-- Arbitrary scalar extension preserves the specified total balanced shuffle map. -/
theorem balancedRelativeShuffle_scalar (z : K ⊗[A] RelativeChains (BalancedCoefficients A M N)) :
    balancedRelativeShuffleLinear K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)
      (balancedChainScalarSourceMap A M N K z) =
      balancedChainScalarTensorMap A M N K ((balancedRelativeShuffleLinear A M N).baseChange K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul k z =>
    rw [balancedChainScalarSourceMap_tmul,map_smul,LinearMap.baseChange_tmul]
    change k • balancedRelativeShuffle K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)
      (coefficientMap (balancedScalarCoefficientUnit A M N K).toLinearMap
        (constantEquivariant_of_lieHom (balancedScalarCoefficientUnit A M N K)) z) =
        balancedChainScalarTensorMap A M N K (k ⊗ₜ[A] balancedRelativeShuffle A M N z)
    rw [balancedRelativeShuffle_scalarUnit]
    rw [← map_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]

end KhanSL2.Factorization






