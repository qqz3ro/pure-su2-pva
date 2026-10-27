module

public import KhanSL2.Factorization.BalancedScalarNaturality

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily NonnegativeCone

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
variable (K : Type) [CommRing K] [Algebra A K] [Algebra ℂ K] [IsScalarTower ℂ A K]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass

/-- The actual scalar tensor comparison on each homogeneous pure tensor. -/
theorem balancedScalarTargetIso_tmul_inclusion (p q j : ℕ) (h : p+q=j)
    (k : K) (u : degree M p) (v : degree N q) :
    (balancedScalarTargetIso A M N K).hom.f j
      (k ⊗ₜ[A] balancedTensorDegreeInclusion A M N p q j h (u ⊗ₜ[A] v)) =
      balancedTensorDegreeInclusion K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)
        p q j h (relativeChainsScalarDegreeMap A M K p (k ⊗ₜ[A] u) ⊗ₜ[K]
          relativeChainsScalarDegreeMap A N K q (1 ⊗ₜ[A] v)) := by
  change (HomologicalComplex.tensorHom (relativeChainsScalarComplexIso A M K).hom
    (relativeChainsScalarComplexIso A N K).hom).f j
      (scalarTensorDegreeMap K (coefficientRelativeComplex A M) (coefficientRelativeComplex A N) j
        (k ⊗ₜ[A] balancedTensorDegreeInclusion A M N p q j h (u ⊗ₜ[A] v))) = _
  have hs := scalarTensorDegreeMap_tmul_inclusion K (coefficientRelativeComplex A M)
    (coefficientRelativeComplex A N) p q j h k (u ⊗ₜ[A] v)
  change scalarTensorDegreeMap K (coefficientRelativeComplex A M) (coefficientRelativeComplex A N) j
    (k ⊗ₜ[A] balancedTensorDegreeInclusion A M N p q j h (u ⊗ₜ[A] v)) = _ at hs
  rw [hs,TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  have hi := congrArg (fun f => f.hom ((k ⊗ₜ[A] u) ⊗ₜ[K] (1 ⊗ₜ[A] v)))
    (HomologicalComplex.ι_tensorHom (relativeChainsScalarComplexIso A M K).hom
      (relativeChainsScalarComplexIso A N K).hom p q j h)
  exact hi

/-- Forgetting tensor degree gives precisely the actual total scalar comparison. -/
theorem balancedScalarTargetIso_forget (j : ℕ)
    (z : (scalarComplex K (balancedTensorComplex A M N)).X j) :
    balancedTensorDegreeForget K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) j
      ((balancedScalarTargetIso A M N K).hom.f j z) =
      balancedChainScalarTensorMap A M N K ((balancedTensorDegreeForget A M N j).baseChange K z) := by
  let f : K ⊗[A] (balancedTensorComplex A M N).X j →ₗ[K]
      RelativeChains (CoefficientBaseChange A M K) ⊗[K] RelativeChains (CoefficientBaseChange A N K) :=
    (balancedTensorDegreeForget K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) j).comp
    ((balancedScalarTargetIso A M N K).hom.f j).hom
  let g := (balancedChainScalarTensorMap A M N K).comp ((balancedTensorDegreeForget A M N j).baseChange K)
  change f z = g z
  change K ⊗[A] (balancedTensorComplex A M N).X j at z
  induction z using TensorProduct.induction_on with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul k z =>
    have he : ModuleCat.ofHom ((f.restrictScalars A).comp
        (TensorProduct.mk A K ((balancedTensorComplex A M N).X j) k)) =
      ModuleCat.ofHom ((g.restrictScalars A).comp
        (TensorProduct.mk A K ((balancedTensorComplex A M N).X j) k)) := by
      apply mapBifunctor.hom_ext
      intro p q h
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro u v
      change balancedTensorDegreeForget K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) j
        ((balancedScalarTargetIso A M N K).hom.f j
          (k ⊗ₜ[A] balancedTensorDegreeInclusion A M N p q j h (u ⊗ₜ[A] v))) =
        balancedChainScalarTensorMap A M N K
          (k ⊗ₜ[A] balancedTensorDegreeForget A M N j
            (balancedTensorDegreeInclusion A M N p q j h (u ⊗ₜ[A] v)))
      rw [balancedScalarTargetIso_tmul_inclusion,balancedTensorDegreeForget_inclusion,
        balancedTensorDegreeForget_inclusion,TensorProduct.map_tmul,TensorProduct.map_tmul,
        balancedChainScalarTensorMap_tmul]
      rfl
    exact congrArg (fun φ => φ.hom z) he

/-- Forgetting source degree gives the original scalar-extension coefficient map. -/
theorem balancedScalarSourceIso_forget (j : ℕ)
    (z : (scalarComplex K (coefficientRelativeComplex A (BalancedCoefficients A M N))).X j) :
    ((balancedScalarSourceIso A M N K).hom.f j z).val =
      balancedChainScalarSourceMap A M N K
        ((coefficientDegreeInclusionLinear A (BalancedCoefficients A M N) j).baseChange K z) := rfl

/-- The specified balanced shuffle commutes with arbitrary base change as a
morphism of genuine complexes, including all signs and degree components. -/
theorem balancedShuffleComplex_scalar :
    scalarMap K (balancedShuffleComplex A M N) ≫ (balancedScalarTargetIso A M N K).hom =
      (balancedScalarSourceIso A M N K).hom ≫
        balancedShuffleComplex K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply balancedTensorDegreeForget_injective K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) j
  change balancedTensorDegreeForget K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) j
    ((balancedScalarTargetIso A M N K).hom.f j ((balancedDegreeShuffle A M N j).baseChange K z)) =
    balancedTensorDegreeForget K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) j
      (balancedDegreeShuffle K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K) j
        ((balancedScalarSourceIso A M N K).hom.f j z))
  rw [balancedScalarTargetIso_forget,balancedTensorDegreeForget_degreeShuffle,balancedScalarSourceIso_forget]
  have h : (balancedTensorDegreeForget A M N j).comp (balancedDegreeShuffle A M N j) =
      (balancedRelativeShuffleLinear A M N).comp (coefficientDegreeInclusionLinear A (BalancedCoefficients A M N) j) := by
    apply LinearMap.ext
    exact balancedTensorDegreeForget_degreeShuffle A M N j
  have hk := congrArg (fun f => f.baseChange K) h
  simp only [LinearMap.baseChange_comp] at hk
  have he := LinearMap.congr_fun hk z
  change (balancedTensorDegreeForget A M N j).baseChange K
    ((balancedDegreeShuffle A M N j).baseChange K z) =
      (balancedRelativeShuffleLinear A M N).baseChange K
        ((coefficientDegreeInclusionLinear A (BalancedCoefficients A M N) j).baseChange K z) at he
  rw [he]
  exact (balancedRelativeShuffle_scalar A M N K _).symm

/-- Scalar quasi-isomorphism is the quasi-isomorphism of the actual specialized shuffle. -/
theorem balancedShuffleComplex_quasiIso_of_scalar
    [QuasiIso (scalarMap K (balancedShuffleComplex A M N))] :
    QuasiIso (balancedShuffleComplex K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)) := by
  have h : QuasiIso ((balancedScalarSourceIso A M N K).hom ≫
      balancedShuffleComplex K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K)) := by
    rw [← balancedShuffleComplex_scalar]
    infer_instance
  let := h
  exact quasiIso_of_comp_left (balancedScalarSourceIso A M N K).hom _

end KhanSL2.Factorization

