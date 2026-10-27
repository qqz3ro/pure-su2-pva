module

public import KhanSL2.Factorization.ExternalTensorDegreeScalars
public import KhanSL2.Factorization.RelativeChainsScalarDegrees

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct DirectSum
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]
attribute [local instance] externalDegreeModule coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

abbrev ExternalDegreeSum (p : ℕ) :=
  ⨁ q : Fin (p+1), ExternalTensor R S (degree M q.val) (degree N (p-q.val))

/-- Inclusion of the actual complementary-degree factors into the unchanged total chains. -/
def externalDegreeSumForget (p : ℕ) :
    ExternalDegreeSum R S M N p →ₗ[R ⊗[ℂ] S] (externalTotalShortComplex R S M N).X₂ :=
  (externalChainObjectEquiv R S M N).symm.toLinearMap.comp
    (DirectSum.toModule (R ⊗[ℂ] S) (Fin (p+1)) _ (fun q =>
      externalTensorMap R S (coefficientDegreeInclusionLinear R M q.val)
        (coefficientDegreeInclusionLinear S N (p-q.val))))

theorem externalDegreeSumForget_of (p : ℕ) (q : Fin (p+1))
    (z : ExternalTensor R S (degree M q.val) (degree N (p-q.val))) :
    externalDegreeSumForget R S M N p (DirectSum.of
      (fun q : Fin (p+1) => ExternalTensor R S (degree M q.val) (degree N (p-q.val))) q z) =
        TensorProduct.map (degree M q.val).subtype (degree N (p-q.val)).subtype z := by
  change (externalChainObjectEquiv R S M N).symm
    ((DirectSum.toModule (R ⊗[ℂ] S) (Fin (p+1)) _ (fun q =>
      externalTensorMap R S (coefficientDegreeInclusionLinear R M q.val)
        (coefficientDegreeInclusionLinear S N (p-q.val)))) _) = _
  rw [← DirectSum.lof_eq_of (R ⊗[ℂ] S),DirectSum.toModule_lof]
  rfl

theorem finiteTermEquiv_external_forget (p : ℕ) (z : ExternalDegreeSum R S M N p) :
    tensorDegreeForget M N p
      (GradedTensorTotal.finiteTermEquiv (fun j => (complex M).X j) (fun j => (complex N).X j) p z) =
        externalDegreeSumForget R S M N p z := by
  induction z using DirectSum.induction_on with
  | zero =>
    rw [(GradedTensorTotal.finiteTermEquiv (fun j => (complex M).X j)
      (fun j => (complex N).X j) p).map_zero, (tensorDegreeForget M N p).map_zero,
      (externalDegreeSumForget R S M N p).map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of q z =>
    have h₁ := congrArg (tensorDegreeForget M N p)
      (GradedTensorTotal.finiteToTerm_of (fun j => (complex M).X j)
        (fun j => (complex N).X j) p q z)
    have h₂ := tensorDegreeForget_inclusion M N q.val (p-q.val) p (by have hq:=q.isLt; omega) z
    have h₃ := externalDegreeSumForget_of R S M N p q z
    exact h₁.trans (h₂.trans h₃.symm)

/-- The finite decomposition retains the original joint coefficient scalars. -/
def externalDegreeSumEquiv (p : ℕ) :
    ExternalDegreeSum R S M N p ≃ₗ[R ⊗[ℂ] S] (tensorComplex M N).X p where
  toFun := GradedTensorTotal.finiteTermEquiv (fun j => (complex M).X j) (fun j => (complex N).X j) p
  invFun := (GradedTensorTotal.finiteTermEquiv (fun j => (complex M).X j) (fun j => (complex N).X j) p).symm
  left_inv := (GradedTensorTotal.finiteTermEquiv (fun j => (complex M).X j) (fun j => (complex N).X j) p).symm_apply_apply
  right_inv := (GradedTensorTotal.finiteTermEquiv (fun j => (complex M).X j) (fun j => (complex N).X j) p).apply_symm_apply
  map_add' := map_add _
  map_smul' c z := by
    apply tensorDegreeForget_injective M N p
    change _ = tensorDegreeForget M N p (externalDegreeScalar R S M N p c _)
    rw [externalDegreeScalar_forget]
    exact (finiteTermEquiv_external_forget R S M N p (c • z)).trans
      (((externalDegreeSumForget R S M N p).map_smul c z).trans
        (congrArg (fun w => externalChainAction R S M N c w)
          (finiteTermEquiv_external_forget R S M N p z)).symm)

@[simp] theorem externalDegreeSumEquiv_of (p : ℕ) (q : Fin (p+1))
    (z : ExternalTensor R S (degree M q.val) (degree N (p-q.val))) :
    externalDegreeSumEquiv R S M N p (DirectSum.of
      (fun q : Fin (p+1) => ExternalTensor R S (degree M q.val) (degree N (p-q.val))) q z) =
        tensorDegreeInclusion M N q.val (p-q.val) p (by have hq:=q.isLt; omega) z :=
  GradedTensorTotal.finiteToTerm_of (fun j => (complex M).X j) (fun j => (complex N).X j) p q z

end KhanSL2.Factorization
