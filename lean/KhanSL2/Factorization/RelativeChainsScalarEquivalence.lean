module

public import KhanSL2.Factorization.RelativeChainsScalarExtension

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]
variable (A : Type) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass

theorem relativeChainsScalarInverseRaw_act (x : G)
    (z : RawChains (CoefficientBaseChange R M A)) :
    relativeChainsScalarInverseRaw R M A (actC (CoefficientBaseChange R M A) x z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw,add_zero]
  | tmul ω n =>
    induction n using TensorProduct.induction_on with
    | zero => simp
    | add n m hn hm => simp only [TensorProduct.tmul_add,map_add,hn,hm,add_zero]
    | tmul a m =>
      change relativeChainsScalarInverseRaw R M A
        (ColorRoot.positiveAction x ω ⊗ₜ[ℂ] (show CoefficientBaseChange R M A from a ⊗ₜ[R] m) +
          ω ⊗ₜ[ℂ] (show CoefficientBaseChange R M A from a ⊗ₜ[R] ⁅constant x,m⁆)) = 0
      rw [map_add,relativeChainsScalarInverseRaw_tmul,relativeChainsScalarInverseRaw_tmul,
        ← TensorProduct.tmul_add,← map_add]
      have h : (relC M).mkQ (actC M x (ω ⊗ₜ[ℂ] m)) = 0 := by
        rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_iSup_of_mem x ⟨ω ⊗ₜ[ℂ] m,rfl⟩
      change a ⊗ₜ[R] ((relC M).mkQ (actC M x (ω ⊗ₜ[ℂ] m))) = 0
      rw [h,TensorProduct.tmul_zero]

/-- The inverse descends through exactly the constant-Lie-algebra relations. -/
def relativeChainsScalarInverse :
    RelativeChains (CoefficientBaseChange R M A) →ₗ[ℂ] A ⊗[R] RelativeChains M :=
  (relC (CoefficientBaseChange R M A)).liftQ (relativeChainsScalarInverseRaw R M A)
    (by
      refine iSup_le fun x => ?_
      rintro _ ⟨z,rfl⟩
      exact relativeChainsScalarInverseRaw_act R M A x z)

@[simp] theorem relativeChainsScalarInverse_mk_tmul (ω : PositiveCE.Cochain) (a : A) (m : M) :
    relativeChainsScalarInverse R M A ((relC (CoefficientBaseChange R M A)).mkQ
      (ω ⊗ₜ[ℂ] (show CoefficientBaseChange R M A from a ⊗ₜ[R] m))) =
        a ⊗ₜ[R] ((relC M).mkQ (ω ⊗ₜ[ℂ] m)) := rfl

theorem relativeChainsScalarInverse_map (z : A ⊗[R] RelativeChains M) :
    relativeChainsScalarInverse R M A (relativeChainsScalarMap R M A z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [Submodule.Quotient.mk_add,map_add,hz,hw]
  | tmul a z =>
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [Submodule.Quotient.mk_add,map_add,TensorProduct.tmul_add,hz,hw]
      | tmul ω m =>
        change relativeChainsScalarInverse R M A (relativeChainsScalarMap R M A
          (a ⊗ₜ[R] (relC M).mkQ (ω ⊗ₜ[ℂ] m))) = a ⊗ₜ[R] (relC M).mkQ (ω ⊗ₜ[ℂ] m)
        rw [relativeChainsScalarMap_tmul_mk,relativeChainsScalarInverse_mk_tmul]

theorem relativeChainsScalarMap_inverse (z : RelativeChains (CoefficientBaseChange R M A)) :
    relativeChainsScalarMap R M A (relativeChainsScalarInverse R M A z) = z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [Submodule.Quotient.mk_add,map_add,hz,hw]
    | tmul ω n =>
      induction n using TensorProduct.induction_on with
      | zero => simp
      | add n m hn hm => simp only [TensorProduct.tmul_add,Submodule.Quotient.mk_add,map_add,hn,hm]
      | tmul a m =>
        change relativeChainsScalarMap R M A (relativeChainsScalarInverse R M A
          ((relC (CoefficientBaseChange R M A)).mkQ (ω ⊗ₜ[ℂ]
            (show CoefficientBaseChange R M A from a ⊗ₜ[R] m)))) =
          (relC (CoefficientBaseChange R M A)).mkQ (ω ⊗ₜ[ℂ]
            (show CoefficientBaseChange R M A from a ⊗ₜ[R] m))
        rw [relativeChainsScalarInverse_mk_tmul,relativeChainsScalarMap_tmul_mk]

/-- Scalar extension commutes with the actual relative CE chain quotient over
any coefficient algebra, including nonreduced and nonflat algebras. -/
def relativeChainsScalarEquiv :
    A ⊗[R] RelativeChains M ≃ₗ[A] RelativeChains (CoefficientBaseChange R M A) :=
  LinearEquiv.ofBijective (relativeChainsScalarMap R M A)
    ⟨(show Function.LeftInverse (relativeChainsScalarInverse R M A)
      (relativeChainsScalarMap R M A) from relativeChainsScalarInverse_map R M A).injective,
     (show Function.RightInverse (relativeChainsScalarInverse R M A)
      (relativeChainsScalarMap R M A) from relativeChainsScalarMap_inverse R M A).surjective⟩

end KhanSL2.Factorization

