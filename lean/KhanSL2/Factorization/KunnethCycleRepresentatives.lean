module

public import KhanSL2.Factorization.KunnethHomologyDecomposition

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The categorical homology isomorphisms retain the actual cycle representatives.
This supplies the representative interface for the canonical Künneth map. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

theorem natChainNext (j : ℕ) : (ComplexShape.down ℕ).next j = j-1 := by
  cases j with
  | zero => exact ChainComplex.next_nat_zero
  | succ j => simpa only [Nat.add_one_sub_one] using ChainComplex.next_nat_succ j

def moduleCyclesEquiv (K : ChainComplex (ModuleCat ℂ) ℕ) (j : ℕ) :
    K.cycles j ≃ₗ[ℂ] LinearMap.ker (K.sc' (j+1) j (j-1)).g.hom :=
  ((K.cyclesIsoSc' (j+1) j (j-1) (ChainComplex.prev ℕ j) (natChainNext j)).toLinearEquiv).trans
    (K.sc' (j+1) j (j-1)).moduleCatCyclesIso.toLinearEquiv

def moduleHomologyEquiv (K : ChainComplex (ModuleCat ℂ) ℕ) (j : ℕ) :
    K.homology j ≃ₗ[ℂ] (K.sc' (j+1) j (j-1)).moduleCatLeftHomologyData.H :=
  ((K.homologyIsoSc' (j+1) j (j-1) (ChainComplex.prev ℕ j) (natChainNext j)).toLinearEquiv).trans
    (K.sc' (j+1) j (j-1)).moduleCatHomologyIso.toLinearEquiv

@[simp] theorem moduleCyclesEquiv_val (K : ChainComplex (ModuleCat ℂ) ℕ) (j : ℕ)
    (u : K.cycles j) : (moduleCyclesEquiv K j u).val = K.iCycles j u := by
  have he : (K.cyclesIsoSc' (j+1) j (j-1) (ChainComplex.prev ℕ j) (natChainNext j)).hom ≫
      (K.sc' (j+1) j (j-1)).moduleCatCyclesIso.hom ≫
        (K.sc' (j+1) j (j-1)).moduleCatLeftHomologyData.i = K.iCycles j := by
    rw [ShortComplex.moduleCatCyclesIso_hom_i,HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  exact congrArg (fun f => f.hom u) he

@[simp] theorem moduleHomologyEquiv_pi (K : ChainComplex (ModuleCat ℂ) ℕ) (j : ℕ)
    (u : K.cycles j) :
    moduleHomologyEquiv K j (K.homologyπ j u) = Submodule.Quotient.mk (moduleCyclesEquiv K j u) := by
  have he : K.homologyπ j ≫
      (K.homologyIsoSc' (j+1) j (j-1) (ChainComplex.prev ℕ j) (natChainNext j)).hom ≫
        (K.sc' (j+1) j (j-1)).moduleCatHomologyIso.hom =
      (K.cyclesIsoSc' (j+1) j (j-1) (ChainComplex.prev ℕ j) (natChainNext j)).hom ≫
        (K.sc' (j+1) j (j-1)).moduleCatCyclesIso.hom ≫
          (K.sc' (j+1) j (j-1)).moduleCatLeftHomologyData.π := by
    rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc,ShortComplex.π_moduleCatCyclesIso_hom]
  exact congrArg (fun f => f.hom u) he

variable (N : Type) [AddCommGroup N] [Module ℂ N]
  [LieRingModule Current N] [LieModule ℂ Current N]

/-- Categorical cycles are the actual homogeneous relative cycles. -/
def complexCyclesEquiv (j : ℕ) : (complex N).cycles j ≃ₗ[ℂ] (window N j).cycles :=
  (moduleCyclesEquiv (complex N) j).trans (degreeCycleEquiv N j)

@[simp] theorem complexCyclesEquiv_val (j : ℕ) (u : (complex N).cycles j) :
    (complexCyclesEquiv N j u).val = ((complex N).iCycles j u : degree N j).val := by
  change (moduleCyclesEquiv (complex N) j u).val.val = _
  rw [moduleCyclesEquiv_val]

@[simp] theorem complexHomologyEquiv_pi (j : ℕ) (u : (complex N).cycles j) :
    complexHomologyEquiv N j ((complex N).homologyπ j u) =
      Submodule.Quotient.mk (complexCyclesEquiv N j u) := by
  change degreeShortHomologyEquiv N j (moduleHomologyEquiv (complex N) j
    ((complex N).homologyπ j u)) = _
  rw [moduleHomologyEquiv_pi]
  rfl

variable (M : Type) [AddCommGroup M] [Module ℂ M]
  [LieRingModule Current M] [LieModule ℂ Current M]

/-- Tensor categorical cycles are exactly the actual signed homogeneous tensor cycles. -/
def tensorComplexCyclesEquiv (j : ℕ) :
    (tensorComplex M N).cycles j ≃ₗ[ℂ] (tensorWindow M N j).cycles :=
  (moduleCyclesEquiv (tensorComplex M N) j).trans (tensorCycleEquiv M N j)

@[simp] theorem tensorComplexCyclesEquiv_val (j : ℕ) (u : (tensorComplex M N).cycles j) :
    (tensorComplexCyclesEquiv N M j u).val =
      tensorDegreeForget M N j ((tensorComplex M N).iCycles j u) := by
  change tensorDegreeForget M N j (moduleCyclesEquiv (tensorComplex M N) j u).val = _
  rw [moduleCyclesEquiv_val]

@[simp] theorem tensorComplexHomologyEquiv_pi (j : ℕ) (u : (tensorComplex M N).cycles j) :
    tensorComplexHomologyEquiv M N j ((tensorComplex M N).homologyπ j u) =
      Submodule.Quotient.mk (tensorComplexCyclesEquiv N M j u) := by
  change tensorShortHomologyEquiv M N j (moduleHomologyEquiv (tensorComplex M N) j
    ((tensorComplex M N).homologyπ j u)) = _
  rw [moduleHomologyEquiv_pi]
  rfl

end KhanSL2.Factorization
