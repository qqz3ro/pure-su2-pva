module

public import KhanSL2.Factorization.ExternalBalancedDegrees

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R S A : Type) [CommRing R] [CommRing S] [CommRing A]
  [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ A]
  [Algebra R A] [Algebra S A] [Algebra (R ⊗[ℂ] S) A]
  [IsScalarTower ℂ R A] [IsScalarTower ℂ S A]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]
variable (h : ∀ r : R, ∀ s : S, algebraMap (R ⊗[ℂ] S) A (r ⊗ₜ[ℂ] s) =
  algebraMap R A r * algebraMap S A s)
attribute [local instance] externalDegreeModule coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

/-- Forgetting a fixed bidegree gives exactly the original scalar-extended pure chains. -/
theorem externalBalancedBidegreeEquiv_forget (p q : ℕ) (a : A)
    (u : degree M p) (v : degree N q) :
    TensorProduct.map
      (coefficientDegreeInclusionLinear A (CoefficientBaseChange R M A) p)
      (coefficientDegreeInclusionLinear A (CoefficientBaseChange S N A) q)
      (externalBalancedBidegreeEquiv R S A M N h p q
        (a ⊗ₜ[R ⊗[ℂ] S] (show ExternalTensor R S (degree M p) (degree N q) from u ⊗ₜ[ℂ] v))) =
      (a • coefficientChainUnit R M A u.val) ⊗ₜ[A] coefficientChainUnit S N A v.val := by
  rw [externalBalancedBidegreeEquiv,LinearEquiv.trans_apply,MixedExternal.equiv_tmul,
    TensorProduct.congr_tmul,TensorProduct.map_tmul]
  change (a • coefficientChainUnit R M A u.val) ⊗ₜ[A]
    ((1:A) • coefficientChainUnit S N A v.val) = _
  rw [one_smul]

/-- The degree comparison is the restriction of the canonical total-chain balancing map. -/
theorem externalBalancedDegreeEquiv_forget (p : ℕ)
    (z : A ⊗[R ⊗[ℂ] S] (tensorComplex M N).X p) :
    balancedTensorDegreeForget A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) p
      (externalBalancedDegreeEquiv R S A M N h p z) =
      externalBalancedChainEquiv R S M N A h
        ((externalDegreeForget R S M N p).baseChange A z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [(externalBalancedDegreeEquiv R S A M N h p).map_zero,
      (balancedTensorDegreeForget A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A) p).map_zero,
      ((externalDegreeForget R S M N p).baseChange A).map_zero,
      (externalBalancedChainEquiv R S M N A h).map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a z =>
    obtain ⟨w,rfl⟩ := (externalDegreeSumEquiv R S M N p).surjective z
    induction w using DirectSum.induction_on with
    | zero => simp only [map_zero,TensorProduct.tmul_zero]
    | add x y hx hy => simp only [map_add,TensorProduct.tmul_add,hx,hy]
    | of q z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero,TensorProduct.tmul_zero]
      | add x y hx hy => simp only [map_add,TensorProduct.tmul_add,hx,hy]
      | tmul u v =>
        rw [externalBalancedDegreeEquiv_tmul_of,balancedTensorDegreeForget_inclusion,
          externalBalancedBidegreeEquiv_forget,LinearMap.baseChange_tmul]
        have he : externalDegreeForget R S M N p
            (externalDegreeSumEquiv R S M N p (DirectSum.of
              (fun i : Fin (p+1) => ExternalTensor R S (degree M i.val) (degree N (p-i.val)))
              q (u ⊗ₜ[ℂ] v))) = u.val ⊗ₜ[ℂ] v.val := by
          exact (finiteTermEquiv_external_forget R S M N p _).trans
            (externalDegreeSumForget_of R S M N p q (u ⊗ₜ[ℂ] v))
        rw [he,externalBalancedChainEquiv_tmul]

end KhanSL2.Factorization
