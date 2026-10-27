module

public import KhanSL2.Factorization.BalancedCoefficients
public import KhanSL2.Factorization.ShuffleRelativeNaturality

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

/-- The canonical balancing quotient on the two relative-chain factors. -/
def relativeTensorBalance : RelativeChains M ⊗[ℂ] RelativeChains N →ₗ[ℂ]
    RelativeChains M ⊗[A] RelativeChains N :=
  balancedCoefficientMap A (RelativeChains M) (RelativeChains N)

@[simp] theorem relativeTensorBalance_tmul (u : RelativeChains M) (v : RelativeChains N) :
    relativeTensorBalance A M N (u ⊗ₜ[ℂ] v) = u ⊗ₜ[A] v := rfl

/-- Insert one genuine exterior chain, preserving all coefficient scalars. -/
def exteriorChainInsertion (u : ExteriorAlgebra ℂ KhanSL2.Current.plus) : M →ₗ[A] RelativeChains M :=
  coefficientChainInsertion A M (exteriorEquiv u)

/-- Regroup the two exterior outputs with balanced coefficient factors. -/
def balancedExteriorReorder :
    (ExteriorAlgebra ℂ KhanSL2.Current.plus ⊗[ℂ] ExteriorAlgebra ℂ KhanSL2.Current.plus) →ₗ[ℂ]
      (BalancedCoefficients A M N →ₗ[ℂ] RelativeChains M ⊗[A] RelativeChains N) :=
  TensorProduct.lift
    { toFun u :=
        { toFun v := (TensorProduct.map (exteriorChainInsertion A M u)
              (exteriorChainInsertion A N v)).restrictScalars ℂ
          map_add' v w := by
            apply LinearMap.ext
            intro z
            induction z using TensorProduct.induction_on with
            | zero => simp
            | add z t hz ht => simp only [map_add,LinearMap.add_apply,hz,ht]
            | tmul m n =>
              change (relC M).mkQ (exteriorEquiv u ⊗ₜ[ℂ] m) ⊗ₜ[A]
                (relC N).mkQ (exteriorEquiv (v+w) ⊗ₜ[ℂ] n) = _
              simp only [map_add,TensorProduct.add_tmul,TensorProduct.tmul_add,LinearMap.add_apply]
              rfl
          map_smul' c v := by
            apply LinearMap.ext
            intro z
            induction z using TensorProduct.induction_on with
            | zero => simp
            | add z t hz ht => simp only [map_add,LinearMap.smul_apply,smul_add,hz,ht]
            | tmul m n =>
              change (relC M).mkQ (exteriorEquiv u ⊗ₜ[ℂ] m) ⊗ₜ[A]
                (relC N).mkQ (exteriorEquiv (c • v) ⊗ₜ[ℂ] n) = _
              rw [map_smul,← TensorProduct.smul_tmul' c (exteriorEquiv v) n,map_smul,
                TensorProduct.tmul_smul]
              rfl }
      map_add' u v := by
        apply LinearMap.ext
        intro w
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z t hz ht => simp only [map_add,LinearMap.add_apply,hz,ht]
        | tmul m n =>
          change (relC M).mkQ (exteriorEquiv (u+v) ⊗ₜ[ℂ] m) ⊗ₜ[A]
            (relC N).mkQ (exteriorEquiv w ⊗ₜ[ℂ] n) = _
          simp only [map_add,TensorProduct.add_tmul,LinearMap.add_apply]
          rfl
      map_smul' c u := by
        apply LinearMap.ext
        intro w
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z t hz ht => simp only [map_add,LinearMap.smul_apply,smul_add,hz,ht]
        | tmul m n =>
          change (relC M).mkQ (exteriorEquiv (c • u) ⊗ₜ[ℂ] m) ⊗ₜ[A]
            (relC N).mkQ (exteriorEquiv w ⊗ₜ[ℂ] n) = _
          rw [map_smul,← TensorProduct.smul_tmul' c (exteriorEquiv u) m,map_smul,
            ← TensorProduct.smul_tmul']
          rfl }

@[simp] theorem balancedExteriorReorder_tmul (u v : ExteriorAlgebra ℂ KhanSL2.Current.plus)
    (m : M) (n : N) :
    balancedExteriorReorder A M N (u ⊗ₜ[ℂ] v)
      (show BalancedCoefficients A M N from m ⊗ₜ[A] n) =
        (relC M).mkQ (exteriorEquiv u ⊗ₜ[ℂ] m) ⊗ₜ[A]
          (relC N).mkQ (exteriorEquiv v ⊗ₜ[ℂ] n) := rfl

def balancedExteriorShuffle : LieChains.Chains ℂ KhanSL2.Current.plus (BalancedCoefficients A M N) →ₗ[ℂ]
    RelativeChains M ⊗[A] RelativeChains N :=
  TensorProduct.lift ((balancedExteriorReorder A M N).comp (ExteriorShuffle.shuffle KhanSL2.Current.plus))

/-- The canonical raw shuffle, now balanced over the coefficient algebra. -/
def balancedRawShuffle : RawChains (BalancedCoefficients A M N) →ₗ[ℂ]
    RelativeChains M ⊗[A] RelativeChains N :=
  (balancedExteriorShuffle A M N).comp (CEModel.J (N:=BalancedCoefficients A M N)).symm.toLinearMap

@[simp] theorem balancedRawShuffle_J (z : LieChains.Chains ℂ KhanSL2.Current.plus (BalancedCoefficients A M N)) :
    balancedRawShuffle A M N (CEModel.J z) = balancedExteriorShuffle A M N z := by
  simp only [balancedRawShuffle,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

/-- Balancing the coefficients and outputs preserves the specified original shuffle. -/
theorem balancedRawShuffle_balance (z : RawChains (M ⊗[ℂ] N)) :
    balancedRawShuffle A M N (rawMap (balancedCoefficientMap A M N) z) =
      relativeTensorBalance A M N (projectRelativeTensor M N (rawShuffle M N z)) := by
  have hr (t : ExteriorShuffle.Tensor KhanSL2.Current.plus) (m : M) (n : N) :
      balancedExteriorReorder A M N t (show BalancedCoefficients A M N from m ⊗ₜ[A] n) =
        relativeTensorBalance A M N (projectRelativeTensor M N
          (tensorModelEquiv M N (CEShuffle.reorder KhanSL2.Current.plus M N (t ⊗ₜ[ℂ] (m ⊗ₜ[ℂ] n))))) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t s ht hs => simp only [map_add,LinearMap.add_apply,TensorProduct.add_tmul,ht,hs]
    | tmul u v => rfl
  obtain ⟨u,rfl⟩ := (CEModel.J (N:=M ⊗[ℂ] N)).surjective z
  rw [rawMap_J,balancedRawShuffle_J,rawShuffle_J]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul u t =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t s ht hs => simp only [TensorProduct.tmul_add,map_add,ht,hs]
    | tmul m n => exact hr (ExteriorShuffle.shuffle KhanSL2.Current.plus u) m n

end KhanSL2.Factorization


