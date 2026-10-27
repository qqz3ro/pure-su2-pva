module

public import KhanSL2.Factorization.BalancedTensorModel
public import KhanSL2.Factorization.ShuffleComplex

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

section CoefficientDegreeSurjection
variable {M N : Type} [AddCommGroup M] [Module ℂ M]
  [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

theorem coefficientMap_degreeProjection (f : M →ₗ[ℂ] N) (hf : ConstantEquivariant f)
    (j : ℕ) (z : RelativeChains M) :
    coefficientMap f hf (degreeProjection M j z) = degreeProjection N j (coefficientMap f hf z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (relC N).mkQ (rawMap f (rawDegreeProjection M j z)) =
      (relC N).mkQ (rawDegreeProjection N j (rawMap f z))
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,hz,hw]
    | tmul ω m => rfl

theorem coefficientDegreeMap_surjective (f : M →ₗ[ℂ] N) (hf : ConstantEquivariant f)
    (hs : Function.Surjective f) (j : ℕ) : Function.Surjective (coefficientDegreeMap f hf j) := by
  intro z
  obtain ⟨u,hu⟩ := coefficientMap_surjective f hf hs z.val
  refine ⟨degreeComponent M j u,?_⟩
  apply Subtype.ext
  change coefficientMap f hf (degreeProjection M j u) = z.val
  rw [coefficientMap_degreeProjection,hu,degreeProjection_of_mem N z.property]
end CoefficientDegreeSurjection

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass

/-- Balancing a homogeneous tensor term preserves exactly its total degree. -/
theorem balancedTensorDegreeForget_component_balance (j : ℕ) (u : (tensorComplex M N).X j) :
    balancedTensorDegreeForget A M N j (balancedTensorDegreeComponent A M N j
      (relativeTensorBalance A M N (tensorDegreeForget M N j u))) =
        relativeTensorBalance A M N (tensorDegreeForget M N j u) := by
  let P := ((balancedTensorDegreeForget A M N j).comp
    (balancedTensorDegreeComponent A M N j)).restrictScalars ℂ
  have h : ModuleCat.ofHom (P.comp ((relativeTensorBalance A M N).comp (tensorDegreeForget M N j))) =
      ModuleCat.ofHom ((relativeTensorBalance A M N).comp (tensorDegreeForget M N j)) := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro v w
    change degree M p at v
    change degree N q at w
    change balancedTensorDegreeForget A M N j (balancedTensorDegreeComponent A M N j
      (relativeTensorBalance A M N (tensorDegreeForget M N j
        (tensorDegreeInclusion M N p q j hpq (v ⊗ₜ[ℂ] w))))) =
      relativeTensorBalance A M N (tensorDegreeForget M N j
        (tensorDegreeInclusion M N p q j hpq (v ⊗ₜ[ℂ] w)))
    rw [tensorDegreeForget_inclusion,TensorProduct.map_tmul,relativeTensorBalance_tmul]
    change balancedTensorDegreeForget A M N j
      (balancedTensorDegreeComponent A M N j (v.val ⊗ₜ[A] w.val)) = v.val ⊗ₜ[A] w.val
    rw [balancedTensorDegreeComponent_subtype_tmul A M N p q j hpq,balancedTensorDegreeForget_inclusion]
    rfl
  exact congrArg (fun f => f.hom u) h

/-- The balanced shuffle retains the original homogeneous total-degree constraint. -/
theorem balancedTensorDegreeForget_component_shuffle (j : ℕ)
    (z : degree (BalancedCoefficients A M N) j) :
    balancedTensorDegreeForget A M N j
      (balancedTensorDegreeComponent A M N j (balancedRelativeShuffle A M N z.val)) =
        balancedRelativeShuffle A M N z.val := by
  obtain ⟨u,hu⟩ := coefficientDegreeMap_surjective (balancedCoefficientLieHom A M N).toLinearMap
    (constantEquivariant_of_lieHom (balancedCoefficientLieHom A M N))
    (balancedCoefficientMap_surjective A M N) j z
  have huv := congrArg Subtype.val hu
  change coefficientMap (balancedCoefficientLieHom A M N).toLinearMap
    (constantEquivariant_of_lieHom (balancedCoefficientLieHom A M N)) u.val = z.val at huv
  rw [← huv,balancedRelativeShuffle_balance,← tensorDegreeForget_degreeShuffle M N j u]
  exact balancedTensorDegreeForget_component_balance A M N j (degreeShuffle M N j u)

end KhanSL2.Factorization

