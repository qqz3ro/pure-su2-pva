module

public import KhanSL2.Factorization.RelativeChainsHomologyDecomposition
public import KhanSL2.Factorization.KunnethTotalHomology
public import KhanSL2.Factorization.KunnethCoefficientMaps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The signed total tensor homology is the algebraic direct sum of the
homologies of the actual categorical tensor complex. -/
noncomputable section
open scoped DirectSum TensorProduct BigOperators
namespace KhanSL2.Factorization
open BGG

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

theorem tensorDegreeProjection_finite_sum (u : RelativeChains M ⊗[ℂ] RelativeChains N) :
    ∃ s : Finset ℕ, ∑ j ∈ s, tensorDegreeProjection M N j u = u := by
  apply finite_projection_sum_of_directSum
    (fun pq : ℕ × ℕ => degree M pq.1 ⊗[ℂ] degree N pq.2)
    (tensorDegreeSumEquiv M N) (fun pq => pq.1+pq.2) (tensorDegreeProjection M N)
  intro i pq v
  rcases pq with ⟨p,q⟩
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw =>
    simp only [map_add,hv,hw]
    split <;> simp
  | tmul v w =>
    rw [← DirectSum.lof_eq_of ℂ,tensorDegreeSumEquiv_of_tmul,
      tensorDegreeProjection_tmul_of_mem M N v.property w.property]
    simp only [eq_comm]

/-- Sum the actual homogeneous tensor homology classes. -/
def tensorHomologySumEquiv :
    (⨁ j, (tensorWindow M N j).homology (relativeTensorDifferential_comp_self M N)) ≃ₗ[ℂ]
      TensorTotalHomology M N :=
  HomologyWindowSplit.decompositionEquiv (tensorWindow M N) (tensorHomologyWindowSplit M N)
    (relativeTensorDifferential_comp_self M N)
    (by
      intro i j hij u hu
      obtain ⟨v,rfl⟩ := hu
      exact tensorDegreeProjection_forget_ne M N hij v)
    (tensorDegreeProjection_finite_sum M N)

/-- The actual standard categorical homologies decompose total tensor homology. -/
def tensorCategoricalHomologySumEquiv :
    (⨁ j, (tensorComplex M N).homology j) ≃ₗ[ℂ] TensorTotalHomology M N :=
  (DFinsupp.mapRange.linearEquiv (fun j => tensorComplexHomologyEquiv M N j)).trans
    (tensorHomologySumEquiv M N)

@[simp] theorem tensorHomologySumEquiv_of (j : ℕ)
    (u : (tensorWindow M N j).homology (relativeTensorDifferential_comp_self M N)) :
    tensorHomologySumEquiv M N (DirectSum.of
      (fun j => (tensorWindow M N j).homology (relativeTensorDifferential_comp_self M N)) j u) =
        (tensorHomologyWindowSplit M N j).inclusion
          (relativeTensorDifferential_comp_self M N) u := by
  change HomologyWindowSplit.sumInclusion _ _ _ _ = _
  rw [HomologyWindowSplit.sumInclusion_of]

end KhanSL2.Factorization
