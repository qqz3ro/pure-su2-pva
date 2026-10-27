module

public import KhanSL2.Factorization.FiniteBGGComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory
namespace KhanSL2.Factorization.FiniteBGG
open Conditional
open scoped KhanSL2.Conditional
attribute [local instance] homologyAction_termAddCommGroup homologyAction_termComplexModule
  homologyAction_coefficientCyclesAddCommGroup homologyAction_coefficientCyclesComplexModule
  homologyAction_coefficientCyclesModule homologyAction_kAddCommGroup homologyAction_kComplexModule

abbrev degreeShortComplex (B p : ℕ) : ShortComplex (ModuleCat (CoefficientRing B)) :=
  (complex B).sc' (p+1) p (p-1)

theorem cycles_eq_kernel (B p : ℕ) :
    Depth.cycles (BGGComplex.Term B) (bggDifferential B) p =
      LinearMap.ker (degreeShortComplex B p).g.hom := by
  cases p with
  | zero =>
    change (⊤ : Submodule (CoefficientRing B) (BGGComplex.Term B 0)) =
      LinearMap.ker ((complex B).d 0 0).hom
    rw [(complex B).shape 0 0 (by simp)]
    simp
  | succ p =>
    change LinearMap.ker (bggDifferential B p) =
      LinearMap.ker ((complex B).d (p+1) p).hom
    rw [complex_d]
    rfl

/-- This equivalence is the identity on actual BGG cycle representatives. -/
def cycleEquiv (B p : ℕ) :
    LinearMap.ker (degreeShortComplex B p).g.hom ≃ₗ[CoefficientRing B]
      CoefficientCycles B p where
  toFun z := ⟨(show BGGComplex.Term B p from z.val), by
    change (show BGGComplex.Term B p from z.val) ∈ Depth.cycles (BGGComplex.Term B) (bggDifferential B) p
    rw [cycles_eq_kernel]
    exact z.property⟩
  invFun z := ⟨(show (degreeShortComplex B p).X₂ from z.val), by
    change z.val ∈ LinearMap.ker (degreeShortComplex B p).g.hom
    rw [← cycles_eq_kernel]
    exact z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cycleEquiv_val (B p : ℕ)
    (z : LinearMap.ker (degreeShortComplex B p).g.hom) :
    (cycleEquiv B p z).val = z.val := rfl

theorem cycleEquiv_boundaries (B p : ℕ) :
    (LinearMap.range (degreeShortComplex B p).moduleCatToCycles).map
      (cycleEquiv B p).toLinearMap =
    (LinearMap.range (bggDifferential B p)).comap (Depth.cycles (BGGComplex.Term B) (bggDifferential B) p).subtype := by
  ext z
  constructor
  · rintro ⟨_,⟨w,rfl⟩,rfl⟩
    change ∃ w₀, bggDifferential B p w₀ =
      (cycleEquiv B p ((degreeShortComplex B p).moduleCatToCycles w)).val
    refine ⟨w,?_⟩
    change bggDifferential B p w = (complex B).d (p+1) p w
    rw [complex_d]
    rfl
  · intro hz
    change ∃ w, bggDifferential B p w = z.val at hz
    obtain ⟨w,hw⟩ := hz
    refine ⟨(degreeShortComplex B p).moduleCatToCycles w,⟨w,rfl⟩,?_⟩
    apply Subtype.ext
    change (complex B).d (p+1) p w = z.val
    rw [complex_d]
    exact hw

def shortHomologyEquiv (B p : ℕ) :
    (degreeShortComplex B p).moduleCatLeftHomologyData.H ≃ₗ[CoefficientRing B]
      BGGHomology B p :=
  Submodule.Quotient.equiv _ _ (cycleEquiv B p) (cycleEquiv_boundaries B p)

/-- Categorical homology of the actual coefficient-linear BGG complex is the
previously constructed Depth.homology, with the same cycle and boundary classes. -/
def homologyEquiv (B p : ℕ) :
    (complex B).homology p ≃ₗ[CoefficientRing B] BGGHomology B p :=
  (((complex B).homologyIsoSc' (p+1) p (p-1) (ChainComplex.prev ℕ p)
    (by cases p <;> simp)).toLinearEquiv.trans
      (degreeShortComplex B p).moduleCatHomologyIso.toLinearEquiv).trans
        (shortHomologyEquiv B p)

/-- The represented categorical class, using the actual short-complex homology
projection rather than an arbitrary isomorphism on underlying modules. -/
def classOfCycle (B p : ℕ) (z : CoefficientCycles B p) : (complex B).homology p :=
  ((complex B).homologyIsoSc' (p+1) p (p-1) (ChainComplex.prev ℕ p)
    (by cases p <;> simp)).inv
      ((degreeShortComplex B p).moduleCatHomologyIso.inv
        ((degreeShortComplex B p).moduleCatLeftHomologyData.π ((cycleEquiv B p).symm z)))

@[simp] theorem homologyEquiv_classOfCycle (B p : ℕ) (z : CoefficientCycles B p) :
    homologyEquiv B p (classOfCycle B p z) = Submodule.Quotient.mk z := by
  simp [homologyEquiv,classOfCycle,shortHomologyEquiv]
  change Submodule.Quotient.mk (cycleEquiv B p ((cycleEquiv B p).symm z)) = Submodule.Quotient.mk z
  rw [LinearEquiv.apply_symm_apply]

/-- Composing with the existing comparison preserves its coefficient-ring action. -/
def homologyEquivK (B p : ℕ) :
    (complex B).homology p ≃ₗ[CoefficientRing B] K B p :=
  (homologyEquiv B p).trans
    { canonicalComparison B p with map_smul' := canonicalComparison_smul B p }

@[simp] theorem homologyEquivK_classOfCycle (B p : ℕ) (z : CoefficientCycles B p) :
    homologyEquivK B p (classOfCycle B p z) = coefficientCyclesToK B p z := by
  change canonicalComparison B p (homologyEquiv B p (classOfCycle B p z)) = _
  exact (congrArg (canonicalComparison B p) (homologyEquiv_classOfCycle B p z)).trans
    (canonicalComparison_mk B p z)

end KhanSL2.Factorization.FiniteBGG