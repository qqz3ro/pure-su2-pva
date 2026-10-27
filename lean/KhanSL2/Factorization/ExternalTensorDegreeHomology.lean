module

public import KhanSL2.Factorization.ExternalTensorDegreeScalars

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily
variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]
attribute [local instance] externalHomogeneousHomologyModule

/-- The unchanged outgoing differential, including the zero-degree endpoint. -/
theorem externalTensorComplex_d_out_apply (p : ℕ) (z : (externalTensorComplex R S M N).X p) :
    tensorDegreeForget M N (p-1) ((externalTensorComplex R S M N).d p (p-1) z) =
      relativeTensorDifferential M N (tensorDegreeForget M N p z) := by
  cases p with
  | zero =>
    rw [(externalTensorComplex R S M N).shape 0 0
      (show ¬ (ComplexShape.down ℕ).Rel 0 0 by simp)]
    change tensorDegreeForget M N 0 0 = _
    rw [map_zero]
    exact (tensorDegreeForget_zero_boundary M N z).symm
  | succ p =>
    simp only [Nat.add_one_sub_one]
    rw [externalTensorComplex_d]
    exact tensorDegreeForget_boundary M N p z

abbrev externalTensorDegreeShortComplex (p : ℕ) : ShortComplex (ModuleCat (R ⊗[ℂ] S)) :=
  (externalTensorComplex R S M N).sc' (p+1) p (p-1)

/-- The same tensor cycle, with its actual homogeneous support. -/
def externalTensorDegreeCycle (p : ℕ)
    (z : LinearMap.ker (externalTensorDegreeShortComplex R S M N p).g.hom) :
    (tensorWindow M N p).cycles :=
  ⟨tensorDegreeForget M N p z.val,⟨z.val,rfl⟩,by
    change relativeTensorDifferential M N (tensorDegreeForget M N p z.val) = 0
    rw [← externalTensorComplex_d_out_apply R S M N p z.val]
    exact congrArg (tensorDegreeForget M N (p-1)) z.property |>.trans (map_zero _)⟩

/-- The original homogeneous class carries the original independent scalar actions. -/
def externalTensorDegreeCycleClass (p : ℕ) :
    LinearMap.ker (externalTensorDegreeShortComplex R S M N p).g.hom →ₗ[R ⊗[ℂ] S]
      TensorHomology M N p where
  toFun z := Submodule.Quotient.mk (externalTensorDegreeCycle R S M N p z)
  map_add' z w := by
    change Submodule.Quotient.mk (externalTensorDegreeCycle R S M N p (z+w)) =
      Submodule.Quotient.mk (externalTensorDegreeCycle R S M N p z + externalTensorDegreeCycle R S M N p w)
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact map_add (tensorDegreeForget M N p) z.val w.val
  map_smul' c z := by
    change Submodule.Quotient.mk (externalTensorDegreeCycle R S M N p (c • z)) =
      Submodule.Quotient.mk ((tensorWindow M N p).cyclesMap (tensorWindow M N p)
        (externalChainAction R S M N c) (externalChainAction_differential R S M N c)
        (externalChainAction_mem_degree R S M N p c) (externalTensorDegreeCycle R S M N p z))
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact externalDegreeScalar_forget R S M N p c z.val

/-- A categorical boundary gives exactly the original homogeneous tensor boundary. -/
theorem externalTensorDegreeCycleClass_boundaries (p : ℕ) :
    LinearMap.range (externalTensorDegreeShortComplex R S M N p).moduleCatToCycles ≤
      LinearMap.ker (externalTensorDegreeCycleClass R S M N p) := by
  rintro _ ⟨w,rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨tensorDegreeForget M N (p+1) w,⟨w,rfl⟩,?_⟩
  change relativeTensorDifferential M N (tensorDegreeForget M N (p+1) w) =
    tensorDegreeForget M N p ((externalTensorComplex R S M N).d (p+1) p w)
  rw [externalTensorComplex_d]
  exact (tensorDegreeForget_boundary M N p w).symm

def externalTensorDegreeQuotientMap (p : ℕ) :
    (externalTensorDegreeShortComplex R S M N p).moduleCatLeftHomologyData.H →ₗ[R ⊗[ℂ] S]
      TensorHomology M N p :=
  (LinearMap.range (externalTensorDegreeShortComplex R S M N p).moduleCatToCycles).liftQ
    (externalTensorDegreeCycleClass R S M N p) (externalTensorDegreeCycleClass_boundaries R S M N p)

theorem externalTensorDegreeQuotientMap_injective (p : ℕ) :
    Function.Injective (externalTensorDegreeQuotientMap R S M N p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (externalTensorDegreeShortComplex R S M N p).moduleCatToCycles) q
  change Submodule.Quotient.mk (externalTensorDegreeCycle R S M N p z) = 0 at hq
  obtain ⟨w,⟨v,hvw⟩,hwz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨v,?_⟩
  apply Subtype.ext
  apply tensorDegreeForget_injective M N p
  change tensorDegreeForget M N p ((externalTensorComplex R S M N).d (p+1) p v) =
    tensorDegreeForget M N p z.val
  rw [externalTensorComplex_d]
  change tensorDegreeForget M N p ((tensorComplex M N).d (p+1) p v) = _
  rw [tensorDegreeForget_boundary,hvw]
  exact hwz

theorem externalTensorDegreeQuotientMap_surjective (p : ℕ) :
    Function.Surjective (externalTensorDegreeQuotientMap R S M N p) := by
  intro q
  obtain ⟨z,hz⟩ := Quotient.exists_rep q
  obtain ⟨v,hvz⟩ := z.property.1
  have hv : (externalTensorComplex R S M N).d p (p-1) v = 0 := by
    apply tensorDegreeForget_injective M N (p-1)
    rw [map_zero,externalTensorComplex_d_out_apply,hvz]
    exact z.property.2
  refine ⟨Submodule.Quotient.mk
    (⟨v,hv⟩ : LinearMap.ker (externalTensorDegreeShortComplex R S M N p).g.hom),?_⟩
  refine Eq.trans ?_ hz
  change Submodule.Quotient.mk (externalTensorDegreeCycle R S M N p ⟨v,hv⟩) = Submodule.Quotient.mk z
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact hvz


theorem externalTensorDegreeQuotientMap_bijective (p : ℕ) :
    Function.Bijective (externalTensorDegreeQuotientMap R S M N p) :=
  ⟨externalTensorDegreeQuotientMap_injective R S M N p,
    externalTensorDegreeQuotientMap_surjective R S M N p⟩

/-- Categorical homology of the original joint-coefficient tensor complex is
exactly the original homogeneous tensor quotient, with its specified actions. -/
def externalTensorComplexHomologyEquiv (p : ℕ) :
    (externalTensorComplex R S M N).homology p ≃ₗ[R ⊗[ℂ] S] TensorHomology M N p :=
  (((externalTensorComplex R S M N).homologyIsoSc' (p+1) p (p-1)
    (ChainComplex.prev ℕ p) (by cases p <;> simp)).toLinearEquiv.trans
      (externalTensorDegreeShortComplex R S M N p).moduleCatHomologyIso.toLinearEquiv).trans
        (LinearEquiv.ofBijective (externalTensorDegreeQuotientMap R S M N p)
          (externalTensorDegreeQuotientMap_bijective R S M N p))

end KhanSL2.Factorization
