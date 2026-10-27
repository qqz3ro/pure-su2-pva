module

public import KhanSL2.Factorization.KunnethTotalProjection
public import KhanSL2.Factorization.RelativeChainsHomologyWindow
public import KhanSL2.Factorization.RelativeChainsHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Exact comparison between degree windows in the actual signed total tensor
and homology of the categorical tensor complex used by the Künneth theorem. -/

noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG BGG.Contraction

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

theorem tensorDegreeForget_boundary (j : ℕ) (z : (tensorComplex M N).X (j+1)) :
    tensorDegreeForget M N j ((tensorComplex M N).d (j+1) j z) =
      relativeTensorDifferential M N (tensorDegreeForget M N (j+1) z) := by
  have h := congrArg (fun f => f.hom z) (tensorDegreeForget_differential M N j)
  exact h

theorem tensorDegreeForget_zero_boundary (z : (tensorComplex M N).X 0) :
    relativeTensorDifferential M N (tensorDegreeForget M N 0 z) = 0 := by
  have h : ModuleCat.ofHom ((relativeTensorDifferential M N).comp
      (tensorDegreeForget M N 0)) = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p+q=0 at hpq
    have hp : p=0 := by omega
    have hq : q=0 := by omega
    subst p
    subst q
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change degree M 0 at u
    change degree N 0 at v
    change relativeTensorDifferential M N (tensorDegreeForget M N 0
      (tensorDegreeInclusion M N 0 0 0 hpq (u ⊗ₜ[ℂ] v))) = 0
    rw [tensorDegreeForget_inclusion,TensorProduct.map_tmul,Submodule.subtype_apply,
      Submodule.subtype_apply,relativeTensorDifferential_tmul,
      differential_eq_zero_of_degree_zero M u.property,
      differential_eq_zero_of_degree_zero N v.property]
    simp
  exact congrArg (fun f => f.hom z) h

/-- The actual homogeneous window inside the signed total tensor chain space. -/
def tensorWindow (j : ℕ) : DegreeWindow (relativeTensorDifferential M N) where
  current := LinearMap.range (tensorDegreeForget M N j)
  previous := LinearMap.range (tensorDegreeForget M N (j+1))
  differential_mem := by
    rintro u ⟨v,rfl⟩
    exact ⟨(tensorComplex M N).d (j+1) j v,tensorDegreeForget_boundary M N j v⟩

/-- The categorical component projection supplies a genuine homogeneous splitting. -/
def tensorHomologyWindowSplit (j : ℕ) : HomologyWindowSplit (tensorWindow M N j) where
  projection := tensorDegreeProjection M N j
  previousProjection := tensorDegreeProjection M N (j+1)
  projection_mem := fun u => ⟨tensorDegreeComponent M N j u,rfl⟩
  previousProjection_mem := fun u => ⟨tensorDegreeComponent M N (j+1) u,rfl⟩
  projection_of_mem := by
    rintro u ⟨v,rfl⟩
    exact tensorDegreeProjection_forget M N j v
  projection_mem_ker := by
    intro u hu
    rw [LinearMap.mem_ker] at hu ⊢
    cases j with
    | zero => exact tensorDegreeForget_zero_boundary M N (tensorDegreeComponent M N 0 u)
    | succ j => rw [← tensorDegreeProjection_differential M N j,hu,map_zero]
  projection_differential := tensorDegreeProjection_differential M N j

/-- Outgoing differential, with the nonnegative degree-zero endpoint included. -/
theorem tensorComplex_d_out_apply (j : ℕ) (z : (tensorComplex M N).X j) :
    tensorDegreeForget M N (j-1) ((tensorComplex M N).d j (j-1) z) =
      relativeTensorDifferential M N (tensorDegreeForget M N j z) := by
  cases j with
  | zero =>
    rw [(tensorComplex M N).shape 0 0 (show ¬ (ComplexShape.down ℕ).Rel 0 0 by simp)]
    change tensorDegreeForget M N 0 0 = _
    rw [map_zero]
    exact (tensorDegreeForget_zero_boundary M N z).symm
  | succ j =>
    simp only [Nat.add_one_sub_one]
    exact tensorDegreeForget_boundary M N j z

abbrev tensorShortComplex (j : ℕ) : ShortComplex (ModuleCat ℂ) :=
  (tensorComplex M N).sc' (j+1) j (j-1)

/-- Categorical cycles are exactly cycles in the actual homogeneous tensor window. -/
def tensorCycleEquiv (j : ℕ) :
    LinearMap.ker (tensorShortComplex M N j).g.hom ≃ₗ[ℂ] (tensorWindow M N j).cycles where
  toFun z := ⟨tensorDegreeForget M N j z.val,⟨z.val,rfl⟩,by
    change relativeTensorDifferential M N (tensorDegreeForget M N j z.val) = 0
    have hz : (tensorComplex M N).d j (j-1) z.val = 0 := z.property
    rw [← tensorComplex_d_out_apply M N j,hz,map_zero]⟩
  invFun z := ⟨tensorDegreeComponent M N j z.val,by
    change (tensorComplex M N).d j (j-1) (tensorDegreeComponent M N j z.val) = 0
    apply (tensorDegreeForget_injective M N (j-1))
    rw [map_zero,tensorComplex_d_out_apply]
    have hz : tensorDegreeForget M N j (tensorDegreeComponent M N j z.val) = z.val := by
      obtain ⟨u,hu⟩ := z.property.1
      rw [← hu,tensorDegreeComponent_forget]
    rw [hz]
    exact z.property.2⟩
  left_inv z := by
    apply Subtype.ext
    exact tensorDegreeComponent_forget M N j z.val
  right_inv z := by
    apply Subtype.ext
    obtain ⟨u,hu⟩ := z.property.1
    change tensorDegreeForget M N j (tensorDegreeComponent M N j z.val) = z.val
    rw [← hu,tensorDegreeComponent_forget]
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

theorem tensorCycleEquiv_boundaries (j : ℕ) :
    (LinearMap.range (tensorShortComplex M N j).moduleCatToCycles).map
      (tensorCycleEquiv M N j).toLinearMap = (tensorWindow M N j).boundaries := by
  ext z
  constructor
  · rintro ⟨_,⟨u,rfl⟩,rfl⟩
    refine ⟨tensorDegreeForget M N (j+1) u,⟨u,rfl⟩,?_⟩
    change relativeTensorDifferential M N (tensorDegreeForget M N (j+1) u) =
      tensorDegreeForget M N j ((tensorComplex M N).d (j+1) j u)
    exact (tensorDegreeForget_boundary M N j u).symm
  · rintro ⟨u,⟨v,hvu⟩,huz⟩
    refine ⟨(tensorShortComplex M N j).moduleCatToCycles v,⟨v,rfl⟩,?_⟩
    apply Subtype.ext
    change tensorDegreeForget M N j ((tensorComplex M N).d (j+1) j v) = z.val
    rw [tensorDegreeForget_boundary,hvu,huz]
    rfl

/-- The concrete short-complex quotient uses the specified homogeneous tensor cycles. -/
def tensorShortHomologyEquiv (j : ℕ) :
    (tensorShortComplex M N j).moduleCatLeftHomologyData.H ≃ₗ[ℂ]
      (tensorWindow M N j).homology (relativeTensorDifferential_comp_self M N) :=
  Submodule.Quotient.equiv _ _ (tensorCycleEquiv M N j) (tensorCycleEquiv_boundaries M N j)

/-- The categorical tensor homology is the actual homogeneous tensor cycle quotient. -/
def tensorComplexHomologyEquiv (j : ℕ) : (tensorComplex M N).homology j ≃ₗ[ℂ]
    (tensorWindow M N j).homology (relativeTensorDifferential_comp_self M N) :=
  (((tensorComplex M N).homologyIsoSc' (j+1) j (j-1) (ChainComplex.prev ℕ j) (by
    cases j with
    | zero => exact ChainComplex.next_nat_zero
    | succ j => simpa only [Nat.add_one_sub_one] using ChainComplex.next_nat_succ j
    )).toLinearEquiv.trans
      (tensorShortComplex M N j).moduleCatHomologyIso.toLinearEquiv).trans
        (tensorShortHomologyEquiv M N j)

end KhanSL2.Factorization
