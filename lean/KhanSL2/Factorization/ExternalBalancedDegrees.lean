module

public import KhanSL2.Factorization.ExternalTensorDegreeSum
public import KhanSL2.Factorization.FiniteDegreeTensorRing
public import KhanSL2.Factorization.ExternalFlatBalancedKunneth
public import KhanSL2.Factorization.BalancedTensorEndpoint

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

/-- Literal independent scalar extension on a fixed pair of CE degrees. -/
def externalBalancedBidegreeEquiv (p q : ℕ) :
    A ⊗[R ⊗[ℂ] S] ExternalTensor R S (degree M p) (degree N q) ≃ₗ[A]
      degree (CoefficientBaseChange R M A) p ⊗[A] degree (CoefficientBaseChange S N A) q :=
  (MixedExternal.equiv R S A (degree M p) (degree N q) h).trans
    (TensorProduct.congr (relativeChainsScalarDegreeEquiv R M A p)
      (relativeChainsScalarDegreeEquiv S N A q))

/-- The canonical scalar extension equivalence on the unchanged total degree-p chain group. -/
def externalBalancedDegreeEquiv (p : ℕ) :
    A ⊗[R ⊗[ℂ] S] (tensorComplex M N).X p ≃ₗ[A]
      (balancedTensorComplex A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)).X p :=
  ((externalDegreeSumEquiv R S M N p).symm.baseChange (R ⊗[ℂ] S) A _ _).trans
    ((TensorProduct.directSumRight (R ⊗[ℂ] S) A A
      (fun q : Fin (p+1) => ExternalTensor R S (degree M q.val) (degree N (p-q.val)))).trans
      ((DFinsupp.mapRange.linearEquiv (fun q : Fin (p+1) =>
        externalBalancedBidegreeEquiv R S A M N h q.val (p-q.val))).trans
          (FiniteGradedTensor.finiteTermEquiv
            (fun q => (coefficientRelativeComplex A (CoefficientBaseChange R M A)).X q)
            (fun q => (coefficientRelativeComplex A (CoefficientBaseChange S N A)).X q) p)))

private theorem mapRangeEquiv_single {K : Type} [CommRing K] {ι : Type*} [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)]
    (e : ∀ i, X i ≃ₗ[K] Y i) (i : ι) (z : X i) :
    DFinsupp.mapRange.linearEquiv e (DirectSum.of X i z) = DirectSum.of Y i (e i z) := by
  change DFinsupp.mapRange (fun i x => e i x) (fun i => (e i).map_zero)
    (DFinsupp.single i z) = DFinsupp.single i (e i z)
  rw [DFinsupp.mapRange_single]

/-- The term comparison is specified on each actual complementary-degree summand. -/
theorem externalBalancedDegreeEquiv_tmul_of (p : ℕ) (q : Fin (p+1)) (a : A)
    (z : ExternalTensor R S (degree M q.val) (degree N (p-q.val))) :
    externalBalancedDegreeEquiv R S A M N h p
      (a ⊗ₜ[R ⊗[ℂ] S] externalDegreeSumEquiv R S M N p (DirectSum.of
        (fun i : Fin (p+1) => ExternalTensor R S (degree M i.val) (degree N (p-i.val))) q z)) =
      balancedTensorDegreeInclusion A (CoefficientBaseChange R M A) (CoefficientBaseChange S N A)
        q.val (p-q.val) p (by have hq:=q.isLt; omega)
          (externalBalancedBidegreeEquiv R S A M N h q.val (p-q.val) (a ⊗ₜ[R ⊗[ℂ] S] z)) := by
  let X : ℕ → ModuleCat A := fun q => (coefficientRelativeComplex A (CoefficientBaseChange R M A)).X q
  let Y : ℕ → ModuleCat A := fun q => (coefficientRelativeComplex A (CoefficientBaseChange S N A)).X q
  let F := fun i : Fin (p+1) => ExternalTensor R S (degree M i.val) (degree N (p-i.val))
  let e := fun i : Fin (p+1) => externalBalancedBidegreeEquiv R S A M N h i.val (p-i.val)
  have h₁' : ((externalDegreeSumEquiv R S M N p).symm.baseChange (R ⊗[ℂ] S) A _ _)
      (a ⊗ₜ[R ⊗[ℂ] S] externalDegreeSumEquiv R S M N p (DirectSum.of F q z)) =
        a ⊗ₜ[R ⊗[ℂ] S] DirectSum.of F q z := by
    rw [LinearEquiv.baseChange_tmul,LinearEquiv.symm_apply_apply]
  have h₂ : TensorProduct.directSumRight (R ⊗[ℂ] S) A A F
      (a ⊗ₜ[R ⊗[ℂ] S] DirectSum.of F q z) =
      DirectSum.of (fun i => A ⊗[R ⊗[ℂ] S] F i) q (a ⊗ₜ[R ⊗[ℂ] S] z) :=
    TensorProduct.directSumRight_tmul_lof (R ⊗[ℂ] S) A (M₁':=A) (M₂:=F) a q z
  have h₃ := mapRangeEquiv_single (X:=fun i => A ⊗[R ⊗[ℂ] S] F i)
    (Y:=fun i : Fin (p+1) => X i.val ⊗[A] Y (p-i.val)) e q (a ⊗ₜ[R ⊗[ℂ] S] z)
  have h₄ := FiniteGradedTensor.finiteToTerm_of X Y p q (e q (a ⊗ₜ[R ⊗[ℂ] S] z))
  exact (congrArg (fun w => FiniteGradedTensor.finiteTermEquiv X Y p
    (DFinsupp.mapRange.linearEquiv e (TensorProduct.directSumRight (R ⊗[ℂ] S) A A F w))) h₁').trans
    ((congrArg (fun w => FiniteGradedTensor.finiteTermEquiv X Y p
      (DFinsupp.mapRange.linearEquiv e w)) h₂).trans
        ((congrArg (FiniteGradedTensor.finiteTermEquiv X Y p) h₃).trans h₄))

end KhanSL2.Factorization
