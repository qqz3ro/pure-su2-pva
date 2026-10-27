module

public import KhanSL2.Factorization.DegreeKunnethField

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]

attribute [local instance] coefficientHomogeneousHomologyModule coefficientHomogeneousHomologyIsScalarTower
  coefficientHomogeneousHomologySMulCommClass coefficientTotalHomologyModule
  coefficientTotalHomologyIsScalarTower coefficientTotalHomologySMulCommClass
  externalHomogeneousHomologyModule externalTensorHomologyModule

/-- The finite complementary-degree sum carries the original independent coefficient actions. -/
abbrev ExternalHomologyDegreeSum (p : ℕ) :=
  ⨁ q : Fin (p+1), ExternalTensor R S (Homology M q.val) (Homology N (p-q.val))

/-- Its unchanged inclusion into total homology is jointly coefficient-linear. -/
def externalHomologyDegreeSumInclusion (p : ℕ) :
    ExternalHomologyDegreeSum R S M N p →ₗ[R ⊗[ℂ] S]
      ExternalTensor R S (TotalHomology M) (TotalHomology N) :=
  DirectSum.toModule (R ⊗[ℂ] S) (Fin (p+1)) _ (fun q =>
    externalTensorMap R S (coefficientHomogeneousHomologyInclusion R M q.val)
      (coefficientHomogeneousHomologyInclusion S N (p-q.val)))

/-- External scalar bundling changes none of the finite-sum inclusion maps. -/
theorem externalHomologyDegreeSumInclusion_eq (p : ℕ) (z : ExternalHomologyDegreeSum R S M N p) :
    externalHomologyDegreeSumInclusion R S M N p z = homologyDegreeSumInclusion M N p z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | of q x => rfl

/-- Before rebundling scalars, the original Künneth map agrees with the external inclusions. -/
theorem homogeneousKunnethEquiv_external_inclusion (p : ℕ) (z : ExternalHomologyDegreeSum R S M N p) :
    externalHomogeneousHomologyInclusion R S M N p (homogeneousKunnethEquiv M N p z) =
      externalKunnethEquiv R S M N (externalHomologyDegreeSumInclusion R S M N p z) := by
  exact (homogeneousKunnethEquiv_inclusion M N p z).trans
    (congrArg (totalKunnethEquiv M N) (externalHomologyDegreeSumInclusion_eq R S M N p z).symm)

/-- The actual degree-p Künneth cross product is an equivalence over the product of the two original rings. -/
def degreeExternalKunnethEquiv (p : ℕ) :
    ExternalHomologyDegreeSum R S M N p ≃ₗ[R ⊗[ℂ] S] TensorHomology M N p where
  toFun := homogeneousKunnethEquiv M N p
  invFun := (homogeneousKunnethEquiv M N p).symm
  left_inv := (homogeneousKunnethEquiv M N p).symm_apply_apply
  right_inv := (homogeneousKunnethEquiv M N p).apply_symm_apply
  map_add' := (homogeneousKunnethEquiv M N p).map_add
  map_smul' c z := by
    let I := externalHomogeneousHomologyInclusion R S M N p
    let F := externalKunnethEquiv R S M N
    let G := externalHomologyDegreeSumInclusion R S M N p
    have hi : Function.Injective I :=
      (tensorHomologyWindowSplit M N p).inclusion_injective (relativeTensorDifferential_comp_self M N)
    apply hi
    exact (homogeneousKunnethEquiv_external_inclusion R S M N p (c • z)).trans
      ((congrArg F (G.map_smul c z)).trans
        ((F.map_smul c (G z)).trans
          ((congrArg (fun w => c • w)
            (homogeneousKunnethEquiv_external_inclusion R S M N p z).symm).trans
            (I.map_smul c (homogeneousKunnethEquiv M N p z)).symm)))

/-- The external degree equivalence retains the specified homogeneous cross-product formula. -/
theorem degreeExternalKunnethEquiv_inclusion (p : ℕ) (z : ExternalHomologyDegreeSum R S M N p) :
    externalHomogeneousHomologyInclusion R S M N p (degreeExternalKunnethEquiv R S M N p z) =
      externalKunnethEquiv R S M N (externalHomologyDegreeSumInclusion R S M N p z) := by
  exact homogeneousKunnethEquiv_external_inclusion R S M N p z

end KhanSL2.Factorization
