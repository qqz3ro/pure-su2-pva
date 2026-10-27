module

public import KhanSL2.Factorization.KunnethGradedTotal
public import KhanSL2.Factorization.KunnethCycleRepresentatives
public import KhanSL2.Factorization.KunnethCross

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-! The canonical Künneth equivalence for the actual signed total relative
complex. Its map is proved to be exactly the tensor product of cycle classes. -/
noncomputable section
open scoped DirectSum TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

theorem dfinsuppEquiv_of {A B : ℕ → Type*}
    [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]
    (e : ∀ j, A j ≃ₗ[ℂ] B j) (j : ℕ) (u : A j) :
    DFinsupp.mapRange.linearEquiv e (DirectSum.of A j u) = DirectSum.of B j (e j u) := by
  change DFinsupp.mapRange (fun i x => e i x) (fun i => (e i).map_zero)
    (DFinsupp.single j u) = DFinsupp.single j (e j u)
  rw [DFinsupp.mapRange_single]

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

/-- Sum of the standard categorical homology groups, with the actual quotient convention. -/
def categoricalHomologySumEquiv :
    (⨁ j, (complex M).homology j) ≃ₗ[ℂ] TotalHomology M :=
  (DFinsupp.mapRange.linearEquiv (fun j => complexHomologyEquiv M j)).trans
    (homologySumEquiv M)

@[simp] theorem categoricalHomologySumEquiv_of (j : ℕ) (u : (complex M).homology j) :
    categoricalHomologySumEquiv M (DirectSum.of (fun j => (complex M).homology j) j u) =
      homogeneousHomologyInclusion M j (complexHomologyEquiv M j u) := by
  change homologySumEquiv M
    (DFinsupp.mapRange.linearEquiv (fun j => complexHomologyEquiv M j)
      (DirectSum.of (fun j => (complex M).homology j) j u)) = _
  rw [dfinsuppEquiv_of,homologySumEquiv_of]

/-- Direct sum of the library's canonical field Künneth isomorphisms. -/
def kunnethSumEquiv :
    (⨁ j, GradedTensorTotal.Term (fun p => (complex M).homology p)
      (fun q => (complex N).homology q) j) ≃ₗ[ℂ]
    (⨁ j, (tensorComplex M N).homology j) :=
  DFinsupp.mapRange.linearEquiv (fun j =>
    (asIso (HomologicalComplex.homologyKunneth (complex M) (complex N) j)).toLinearEquiv)

@[simp] theorem kunnethSumEquiv_of (j : ℕ)
    (u : GradedTensorTotal.Term (fun p => (complex M).homology p)
      (fun q => (complex N).homology q) j) :
    kunnethSumEquiv M N (DirectSum.of
      (GradedTensorTotal.Term (fun p => (complex M).homology p)
        (fun q => (complex N).homology q)) j u) =
      DirectSum.of (fun j => (tensorComplex M N).homology j) j
        ((HomologicalComplex.homologyKunneth (complex M) (complex N) j).hom u) := by
  exact dfinsuppEquiv_of
    (A := fun j => GradedTensorTotal.Term (fun p => (complex M).homology p)
      (fun q => (complex N).homology q) j)
    (B := fun j => (tensorComplex M N).homology j)
    (fun j => (asIso (HomologicalComplex.homologyKunneth (complex M) (complex N) j)).toLinearEquiv)
    j u

/-- The standard tensor Künneth isomorphism, with all finite degree sums restored. -/
def totalKunnethEquiv : TotalHomology M ⊗[ℂ] TotalHomology N ≃ₗ[ℂ]
    TensorTotalHomology M N :=
  (TensorProduct.congr (categoricalHomologySumEquiv M).symm
    (categoricalHomologySumEquiv N).symm).trans
      ((GradedTensorTotal.tensorEquiv (fun p => (complex M).homology p)
        (fun q => (complex N).homology q)).trans
          ((kunnethSumEquiv M N).trans (tensorCategoricalHomologySumEquiv M N)))

@[simp] theorem tensorCategoricalHomologySumEquiv_of (j : ℕ)
    (u : (tensorComplex M N).homology j) :
    tensorCategoricalHomologySumEquiv M N
      (DirectSum.of (fun j => (tensorComplex M N).homology j) j u) =
      (tensorHomologyWindowSplit M N j).inclusion (relativeTensorDifferential_comp_self M N)
        (tensorComplexHomologyEquiv M N j u) := by
  change tensorHomologySumEquiv M N
    (DFinsupp.mapRange.linearEquiv (fun j => tensorComplexHomologyEquiv M N j)
      (DirectSum.of (fun j => (tensorComplex M N).homology j) j u)) = _
  rw [dfinsuppEquiv_of,tensorHomologySumEquiv_of]

/-- On each homogeneous summand this is the library's specified homology cross product. -/
theorem totalKunnethEquiv_homogeneous (p q : ℕ)
    (u : (complex M).homology p) (v : (complex N).homology q) :
    totalKunnethEquiv M N
      (homogeneousHomologyInclusion M p (complexHomologyEquiv M p u) ⊗ₜ[ℂ]
        homogeneousHomologyInclusion N q (complexHomologyEquiv N q v)) =
      (tensorHomologyWindowSplit M N (p+q)).inclusion (relativeTensorDifferential_comp_self M N)
        (tensorComplexHomologyEquiv M N (p+q)
          ((HomologicalComplex.homologyCross (complex M) (complex N) p q (p+q) rfl).hom
            (u ⊗ₜ[ℂ] v))) := by
  rw [← categoricalHomologySumEquiv_of M p u,← categoricalHomologySumEquiv_of N q v]
  simp only [totalKunnethEquiv,LinearEquiv.trans_apply,TensorProduct.congr_tmul,
    LinearEquiv.symm_apply_apply,GradedTensorTotal.tensorEquiv_of_tmul,
    kunnethSumEquiv_of,tensorCategoricalHomologySumEquiv_of]
  congr 2
  exact congrArg (fun f => f.hom (u ⊗ₜ[ℂ] v))
    (HomologicalComplex.ι_homologyKunneth (complex M) (complex N) (p+q) p q rfl)

/-- The Künneth equivalence on homogeneous cycle classes retains the actual tensor. -/
theorem totalKunnethEquiv_homogeneous_cycles (p q : ℕ)
    (u : (complex M).cycles p) (v : (complex N).cycles q) :
    totalKunnethEquiv M N
      (Submodule.Quotient.mk (homogeneousCyclesInclusion M p (complexCyclesEquiv M p u)) ⊗ₜ[ℂ]
        Submodule.Quotient.mk (homogeneousCyclesInclusion N q (complexCyclesEquiv N q v))) =
      Submodule.Quotient.mk (tensorCycles M N
        (homogeneousCyclesInclusion M p (complexCyclesEquiv M p u))
        (homogeneousCyclesInclusion N q (complexCyclesEquiv N q v))) := by
  have hu : Submodule.Quotient.mk (homogeneousCyclesInclusion M p (complexCyclesEquiv M p u)) =
      homogeneousHomologyInclusion M p (complexHomologyEquiv M p ((complex M).homologyπ p u)) := by
    rw [complexHomologyEquiv_pi]
    rfl
  have hv : Submodule.Quotient.mk (homogeneousCyclesInclusion N q (complexCyclesEquiv N q v)) =
      homogeneousHomologyInclusion N q (complexHomologyEquiv N q ((complex N).homologyπ q v)) := by
    rw [complexHomologyEquiv_pi]
    rfl
  rw [hu,hv,totalKunnethEquiv_homogeneous]
  have hc := congrArg (fun f => f.hom (u ⊗ₜ[ℂ] v))
    (HomologicalComplex.homologyπ_tensorHom_homologyCross
      (complex M) (complex N) p q (p+q) rfl)
  change (HomologicalComplex.homologyCross (complex M) (complex N) p q (p+q) rfl)
      ((complex M).homologyπ p u ⊗ₜ[ℂ] (complex N).homologyπ q v) =
    (tensorComplex M N).homologyπ (p+q)
      ((HomologicalComplex.cyclesCross (complex M) (complex N) p q (p+q) rfl) (u ⊗ₜ[ℂ] v)) at hc
  rw [hc,tensorComplexHomologyEquiv_pi]
  change Submodule.Quotient.mk
      ((tensorHomologyWindowSplit M N (p+q)).cycleInclusion
        (tensorComplexCyclesEquiv N M (p+q)
          ((HomologicalComplex.cyclesCross (complex M) (complex N) p q (p+q) rfl)
            (u ⊗ₜ[ℂ] v)))) = _
  congr 1
  apply Subtype.ext
  change (tensorComplexCyclesEquiv N M (p+q)
      ((HomologicalComplex.cyclesCross (complex M) (complex N) p q (p+q) rfl)
        (u ⊗ₜ[ℂ] v))).val = (complexCyclesEquiv M p u).val ⊗ₜ[ℂ] (complexCyclesEquiv N q v).val
  rw [tensorComplexCyclesEquiv_val,complexCyclesEquiv_val,complexCyclesEquiv_val]
  have hci := congrArg (fun f => f.hom (u ⊗ₜ[ℂ] v))
    (HomologicalComplex.cyclesCross_iCycles (complex M) (complex N) p q (p+q) rfl)
  change (tensorComplex M N).iCycles (p+q)
      ((HomologicalComplex.cyclesCross (complex M) (complex N) p q (p+q) rfl)
        (u ⊗ₜ[ℂ] v)) = tensorDegreeInclusion M N p q (p+q) rfl
          ((complex M).iCycles p u ⊗ₜ[ℂ] (complex N).iCycles q v) at hci
  rw [hci,tensorDegreeForget_inclusion,TensorProduct.map_tmul]
  rfl

theorem totalKunnethEquiv_homogeneous_eq_cross (p q : ℕ)
    (u : Homology M p) (v : Homology N q) :
    totalKunnethEquiv M N
      (homogeneousHomologyInclusion M p u ⊗ₜ[ℂ] homogeneousHomologyInclusion N q v) =
      totalHomologyCross M N
        (homogeneousHomologyInclusion M p u ⊗ₜ[ℂ] homogeneousHomologyInclusion N q v) := by
  obtain ⟨u,rfl⟩ := (complexHomologyEquiv M p).surjective u
  obtain ⟨v,rfl⟩ := (complexHomologyEquiv N q).surjective v
  have hu : Function.Surjective ((complex M).homologyπ p) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hv : Function.Surjective ((complex N).homologyπ q) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨u,rfl⟩ := hu u
  obtain ⟨v,rfl⟩ := hv v
  rw [complexHomologyEquiv_pi,complexHomologyEquiv_pi]
  change totalKunnethEquiv M N
      (Submodule.Quotient.mk (homogeneousCyclesInclusion M p (complexCyclesEquiv M p u)) ⊗ₜ[ℂ]
        Submodule.Quotient.mk (homogeneousCyclesInclusion N q (complexCyclesEquiv N q v))) = _
  rw [totalKunnethEquiv_homogeneous_cycles]
  rfl

/-- The equivalence's map is exactly the specified tensor-of-cycles map. -/
theorem totalKunnethEquiv_eq_cross :
    (totalKunnethEquiv M N).toLinearMap = totalHomologyCross M N := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  change totalKunnethEquiv M N (u ⊗ₜ[ℂ] v) = totalHomologyCross M N (u ⊗ₜ[ℂ] v)
  obtain ⟨us,rfl⟩ := (homologySumEquiv M).surjective u
  induction us using DirectSum.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,TensorProduct.add_tmul,hu,hw]
  | of p u =>
    rw [homologySumEquiv_of]
    obtain ⟨vs,rfl⟩ := (homologySumEquiv N).surjective v
    induction vs using DirectSum.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add,TensorProduct.tmul_add,hv,hw]
    | of q v =>
      rw [homologySumEquiv_of]
      exact totalKunnethEquiv_homogeneous_eq_cross M N p q u v

/-- Field Künneth for the actual signed tensor complex, without replacing its map. -/
theorem totalHomologyCross_bijective : Function.Bijective (totalHomologyCross M N) := by
  rw [← totalKunnethEquiv_eq_cross]
  exact (totalKunnethEquiv M N).bijective

/-- Arbitrary finite cycle representatives have their literal tensor product as image. -/
@[simp] theorem totalKunnethEquiv_mk_tmul_mk (u : LinearMap.ker (differential M))
    (v : LinearMap.ker (differential N)) :
    totalKunnethEquiv M N (Submodule.Quotient.mk u ⊗ₜ[ℂ] Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (tensorCycles M N u v) := by
  change (totalKunnethEquiv M N).toLinearMap _ = _
  rw [totalKunnethEquiv_eq_cross,totalHomologyCross_mk_tmul_mk]

end KhanSL2.Factorization
