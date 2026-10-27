module

public import KhanSL2.Factorization.BalancedShuffleRaw

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
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass

theorem balancedRawShuffle_relations : relC (BalancedCoefficients A M N) ≤
    LinearMap.ker (balancedRawShuffle A M N) := by
  refine iSup_le fun x => ?_
  rintro _ ⟨z,rfl⟩
  obtain ⟨u,rfl⟩ := LinearMap.lTensor_surjective PositiveCE.Cochain
    (balancedCoefficientMap_surjective A M N) z
  change balancedRawShuffle A M N
    (actC (BalancedCoefficients A M N) x (rawMap (balancedCoefficientMap A M N) u)) = 0
  rw [← rawMap_actC (balancedCoefficientMap A M N)
    (constantEquivariant_of_lieHom (balancedCoefficientLieHom A M N)),
    balancedRawShuffle_balance,rawShuffle_actC,projectRelativeTensor_action,map_zero]

/-- The actual relative shuffle over the coefficient algebra, descending through
the genuine constant Lie relations and coefficient balancing relations. -/
def balancedRelativeShuffle : RelativeChains (BalancedCoefficients A M N) →ₗ[ℂ]
    RelativeChains M ⊗[A] RelativeChains N :=
  (relC (BalancedCoefficients A M N)).liftQ (balancedRawShuffle A M N)
    (balancedRawShuffle_relations A M N)

@[simp] theorem balancedRelativeShuffle_mk (z : RawChains (BalancedCoefficients A M N)) :
    balancedRelativeShuffle A M N ((relC (BalancedCoefficients A M N)).mkQ z) =
      balancedRawShuffle A M N z := rfl

/-- The new map is exactly the old shuffle after the canonical balancing quotients. -/
theorem balancedRelativeShuffle_balance (z : RelativeChains (M ⊗[ℂ] N)) :
    balancedRelativeShuffle A M N
      (coefficientMap (balancedCoefficientLieHom A M N).toLinearMap
        (constantEquivariant_of_lieHom (balancedCoefficientLieHom A M N)) z) =
      relativeTensorBalance A M N (relativeShuffle M N z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z => exact balancedRawShuffle_balance A M N z

theorem balancedExteriorReorder_smul (t : ExteriorShuffle.Tensor KhanSL2.Current.plus)
    (a : A) (z : BalancedCoefficients A M N) :
    balancedExteriorReorder A M N t (a • z) = a • balancedExteriorReorder A M N t z := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t s ht hs => simp only [map_add,LinearMap.add_apply,smul_add,ht,hs]
  | tmul u v => exact (TensorProduct.map (exteriorChainInsertion A M u)
      (exteriorChainInsertion A N v)).map_smul a z

theorem balancedRawShuffle_smul (a : A) (z : RawChains (BalancedCoefficients A M N)) :
    balancedRawShuffle A M N
      (rawMap (coefficientScalarLieHom A (BalancedCoefficients A M N) a).toLinearMap z) =
      a • balancedRawShuffle A M N z := by
  obtain ⟨u,rfl⟩ := (CEModel.J (N:=BalancedCoefficients A M N)).surjective z
  rw [rawMap_J,balancedRawShuffle_J,balancedRawShuffle_J]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,smul_add,hu,hv]
  | tmul u n => exact balancedExteriorReorder_smul A M N (ExteriorShuffle.shuffle KhanSL2.Current.plus u) a n

theorem balancedRelativeShuffle_smul (a : A) (z : RelativeChains (BalancedCoefficients A M N)) :
    balancedRelativeShuffle A M N (a • z) = a • balancedRelativeShuffle A M N z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z => exact balancedRawShuffle_smul A M N a z

/-- The specified balanced shuffle is linear over the original coefficient algebra. -/
def balancedRelativeShuffleLinear : RelativeChains (BalancedCoefficients A M N) →ₗ[A]
    RelativeChains M ⊗[A] RelativeChains N where
  __ := (balancedRelativeShuffle A M N).toAddMonoidHom
  map_smul' := balancedRelativeShuffle_smul A M N

end KhanSL2.Factorization

