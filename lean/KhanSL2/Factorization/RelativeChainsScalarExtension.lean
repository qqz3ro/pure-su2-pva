module

public import KhanSL2.Factorization.CoefficientChainMaps

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]
variable (A : Type) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]

instance coefficientBaseChange_originalTower :
    IsScalarTower R A (CoefficientBaseChange R M A) :=
  inferInstanceAs (IsScalarTower R A (A ⊗[R] M))

/-- The scalar-extended coefficient module is still linear over the original ring. -/
instance coefficientBaseChange_originalLinear :
    CoefficientLinearCurrent R (CoefficientBaseChange R M A) where
  lie_smul x r m := (currentBaseChangeEnd R M A x).map_smul_of_tower r m

attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass

/-- The original and extended scalar actions on chains use the same coefficient factor. -/
instance coefficientBaseChange_chainTower :
    IsScalarTower R A (RelativeChains (CoefficientBaseChange R M A)) where
  smul_assoc r a z := by
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      change (relC (CoefficientBaseChange R M A)).mkQ
        (rawMap (coefficientScalarLieHom A (CoefficientBaseChange R M A) (r • a)).toLinearMap z) =
        (relC (CoefficientBaseChange R M A)).mkQ
          (rawMap (coefficientScalarLieHom R (CoefficientBaseChange R M A) r).toLinearMap
            (rawMap (coefficientScalarLieHom A (CoefficientBaseChange R M A) a).toLinearMap z))
      congr 1
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add,hz,hw]
      | tmul ω m =>
        change ω ⊗ₜ[ℂ] ((r • a) • m) = ω ⊗ₜ[ℂ] (r • (a • m))
        rw [smul_assoc]

/-- The canonical coefficient unit map is an actual current-module map. -/
def coefficientBaseChangeUnit : M →ₗ⁅ℂ,Current⁆ CoefficientBaseChange R M A where
  toFun m := (1:A) ⊗ₜ[R] m
  map_add' m n := TensorProduct.tmul_add _ _ _
  map_smul' c m := by
    change (1:A) ⊗ₜ[R] (c • m) = c • ((1:A) ⊗ₜ[R] m)
    rw [TensorProduct.tmul_smul]
  map_lie' {x m} := rfl

omit [LieModule ℂ Current M] in
theorem coefficientBaseChangeUnit_smul (r : R) (m : M) :
    coefficientBaseChangeUnit R M A (r • m) = r • coefficientBaseChangeUnit R M A m := by
  change (1:A) ⊗ₜ[R] (r • m) = r • ((1:A) ⊗ₜ[R] m)
  rw [TensorProduct.tmul_smul]

/-- Canonical relative-chain scalar extension, before identifying any homology. -/
def relativeChainsScalarMap :
    A ⊗[R] RelativeChains M →ₗ[A] RelativeChains (CoefficientBaseChange R M A) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • coefficientMapLinear R (coefficientBaseChangeUnit R M A)
        (coefficientBaseChangeUnit_smul R M A)
      map_add' a b := add_smul a b _
      map_smul' a b := mul_smul a b _ }

@[simp] theorem relativeChainsScalarMap_tmul_mk (a : A) (ω : PositiveCE.Cochain) (m : M) :
    relativeChainsScalarMap R M A (a ⊗ₜ[R] ((relC M).mkQ (ω ⊗ₜ[ℂ] m))) =
      (relC (CoefficientBaseChange R M A)).mkQ
        (ω ⊗ₜ[ℂ] (show CoefficientBaseChange R M A from a ⊗ₜ[R] m)) := by
  change (relC (CoefficientBaseChange R M A)).mkQ (ω ⊗ₜ[ℂ] (a • ((1:A) ⊗ₜ[R] m))) = _
  rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

/-- Insert a fixed exterior chain into the coefficient factor, over R. -/
def coefficientChainInsertion (ω : PositiveCE.Cochain) : M →ₗ[R] RelativeChains M where
  toFun m := (relC M).mkQ (ω ⊗ₜ[ℂ] m)
  map_add' m n := by rw [TensorProduct.tmul_add,map_add]
  map_smul' r m := rfl

/-- Moving the extended scalar outside the actual chain quotient. -/
def relativeChainsScalarInverseRaw :
    RawChains (CoefficientBaseChange R M A) →ₗ[ℂ] A ⊗[R] RelativeChains M :=
  TensorProduct.lift
    { toFun ω := ((coefficientChainInsertion R M ω).baseChange A).restrictScalars ℂ
      map_add' ω η := by
        apply LinearMap.ext
        intro n
        induction n using TensorProduct.induction_on with
        | zero => simp
        | add n m hn hm => simp only [map_add,LinearMap.add_apply,hn,hm]
        | tmul a m =>
          change a ⊗ₜ[R] ((relC M).mkQ ((ω+η) ⊗ₜ[ℂ] m)) =
            a ⊗ₜ[R] ((relC M).mkQ (ω ⊗ₜ[ℂ] m)) + a ⊗ₜ[R] ((relC M).mkQ (η ⊗ₜ[ℂ] m))
          rw [TensorProduct.add_tmul,map_add,TensorProduct.tmul_add]
      map_smul' c ω := by
        apply LinearMap.ext
        intro n
        induction n using TensorProduct.induction_on with
        | zero => simp
        | add n m hn hm => simp only [map_add,LinearMap.smul_apply,smul_add,hn,hm]
        | tmul a m =>
          change a ⊗ₜ[R] ((relC M).mkQ ((c • ω) ⊗ₜ[ℂ] m)) =
            c • (a ⊗ₜ[R] ((relC M).mkQ (ω ⊗ₜ[ℂ] m)))
          rw [← TensorProduct.smul_tmul' c ω m,map_smul,TensorProduct.tmul_smul] }

@[simp] theorem relativeChainsScalarInverseRaw_tmul (ω : PositiveCE.Cochain) (a : A) (m : M) :
    relativeChainsScalarInverseRaw R M A (ω ⊗ₜ[ℂ]
      (show CoefficientBaseChange R M A from a ⊗ₜ[R] m)) =
      a ⊗ₜ[R] ((relC M).mkQ (ω ⊗ₜ[ℂ] m)) := rfl

end KhanSL2.Factorization

