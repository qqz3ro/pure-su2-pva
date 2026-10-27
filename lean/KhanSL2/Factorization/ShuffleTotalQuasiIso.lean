module

public import KhanSL2.Factorization.KunnethTotalHomology
public import KhanSL2.Factorization.RelativeChainsCategoricalHomology
public import KhanSL2.Factorization.ShuffleComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! A total-homology calculation of a specified CE-to-tensor comparison implies
quasi-isomorphism of that same categorical map, with all exterior degrees retained. -/

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG

variable (L M N : Type)
  [AddCommGroup L] [Module ℂ L] [LieRingModule Current L] [LieModule ℂ Current L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  (F : RelativeChains L →ₗ[ℂ] RelativeChains M ⊗[ℂ] RelativeChains N)
  (α : complex L ⟶ tensorComplex M N)
  (hα : ∀ j (u : degree L j), tensorDegreeForget M N j (α.f j u) = F u.val)

include α hα

theorem tensorComparison_mem_window (j : ℕ) {u : RelativeChains L}
    (hu : u ∈ degree L j) : F u ∈ (tensorWindow M N j).current :=
  ⟨α.f j ⟨u,hu⟩,hα j ⟨u,hu⟩⟩

/-- The specified degreewise comparison respects the actual total-degree projections. -/
theorem tensorComparison_projection (j : ℕ) (u : RelativeChains L) :
    F (degreeProjection L j u) = tensorDegreeProjection M N j (F u) := by
  obtain ⟨v,rfl⟩ := (degreeSumEquiv L).surjective u
  induction v using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | of q u =>
    rw [degreeSumEquiv_of]
    by_cases h : j=q
    · subst q
      rw [degreeProjection_of_mem L u.property,← hα j u,tensorDegreeProjection_forget]
    · rw [degreeProjection_of_mem_ne L h u.property,map_zero,← hα q u,
        tensorDegreeProjection_forget_ne M N h]

/-- Concrete total bijectivity implies a quasi-isomorphism of the same specified
categorical CE comparison. No change of map or unspecified homology equivalence occurs. -/
theorem quasiIso_of_totalTensorHomology_bijective
    (hf : F.comp (differential L) = (relativeTensorDifferential M N).comp F)
    (htotal : Function.Bijective ((totalPairMap F hf).homologyMap
      (differential_comp_self L) (relativeTensorDifferential_comp_self M N))) :
    QuasiIso α := by
  refine ⟨fun j => ?_⟩
  rw [quasiIsoAt_iff' α (j+1) j (j-1) (ChainComplex.prev ℕ j) (by
    cases j with
    | zero => exact ChainComplex.next_nat_zero
    | succ j => simpa only [Nat.add_one_sub_one] using ChainComplex.next_nat_succ j)]
  let φ : degreeShortComplex L j ⟶ tensorShortComplex M N j :=
    (HomologicalComplex.shortComplexFunctor' (ModuleCat ℂ) (ComplexShape.down ℕ)
      (j+1) j (j-1)).map α
  change ShortComplex.QuasiIso φ
  apply quasiIso_of_moduleQuotientHomologyMap_bijective
  let hc : ∀ u ∈ (window L j).current, F u ∈ (tensorWindow M N j).current :=
    fun u hu => tensorComparison_mem_window L M N F α hα j (u := u) hu
  let hp : ∀ u ∈ (window L j).previous, F u ∈ (tensorWindow M N j).previous :=
    fun u hu => tensorComparison_mem_window L M N F α hα (j+1) (u := u) hu
  let f := (window L j).homologyMap (tensorWindow M N j) F
    (differential_comp_self L) (relativeTensorDifferential_comp_self M N) hf hc hp
  have hbij : Function.Bijective f :=
    windowHomologyMap_bijective_of_total (window L j) (tensorWindow M N j)
      (relativeHomologyWindowSplit L j) (tensorHomologyWindowSplit M N j) F
      (differential_comp_self L) (relativeTensorDifferential_comp_self M N) hf hc hp
      (tensorComparison_projection L M N F α hα j) htotal
  let eS := degreeShortHomologyEquiv L j
  let eT := tensorShortHomologyEquiv M N j
  have heq (u : (degreeShortComplex L j).moduleCatLeftHomologyData.H) :
      eT (moduleQuotientHomologyMap φ u) = f (eS u) := by
    obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective
      (LinearMap.range (degreeShortComplex L j).moduleCatToCycles) u
    change eT (moduleQuotientHomologyMap φ (Submodule.Quotient.mk v)) =
      f (eS (Submodule.Quotient.mk v))
    rw [moduleQuotientHomologyMap_mk]
    change Submodule.Quotient.mk (tensorCycleEquiv M N j (moduleCycleMap φ v)) =
      Submodule.Quotient.mk ((window L j).cyclesMap (tensorWindow M N j) F hf hc
        (degreeCycleEquiv L j v))
    congr 1
    apply Subtype.ext
    change tensorDegreeForget M N j (moduleCycleMap φ v).val = F (degreeCycleEquiv L j v).val
    rw [moduleCycleMap_val]
    exact hα j v.val
  have hfun : (moduleQuotientHomologyMap φ : _ → _) =
      fun u => eT.symm (f (eS u)) := by
    funext u
    apply eT.injective
    rw [eT.apply_symm_apply,heq]
  rw [hfun]
  exact eT.symm.bijective.comp (hbij.comp eS.bijective)

end KhanSL2.Factorization
