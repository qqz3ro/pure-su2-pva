module

public import KhanSL2.Factorization.FiniteBGGTransferDegrees
public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.BGGTransfer
open BGG BGGBridge SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]
attribute [local instance] harmonicModule coefficientChainModule coefficientDegreeModule

/-- The genuine BGG projection is a retraction in every degree. -/
theorem inclComplex_projComplex : inclComplex R M ≫ projComplex R M = 𝟙 (harmonicComplex R M) := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (qcN M).proj_comp_incl z.val

/-- The existing homotopy component with its categorical source and target explicit. -/
def homotopyComponent (j : ℕ) :
    (coefficientRelativeComplex R M).X j ⟶ (coefficientRelativeComplex R M).X (j+1) :=
  ModuleCat.ofHom (homotopyDegree R M j)
def defect : coefficientRelativeComplex R M ⟶ coefficientRelativeComplex R M :=
  𝟙 _ - projComplex R M ≫ inclComplex R M

theorem defect_zero :
    (defect R M).f 0 = homotopyComponent R M 0 ≫
      (coefficientRelativeComplex R M).d 1 0 := by
  rw [coefficientRelativeComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change z.val - (qcN M).incl ((qcN M).proj z.val) =
    differential M ((qcN M).homotopy z.val)
  have h := LinearMap.congr_fun (qcN M).dM_comp_homotopy_add_homotopy_comp_dM z.val
  have hz := differential_eq_zero_of_degree_zero M z.property
  simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    hz,map_zero,add_zero] using h.symm

theorem defect_succ (j : ℕ) :
    (defect R M).f (j+1) =
      (coefficientRelativeComplex R M).d (j+1) j ≫ homotopyComponent R M j +
      homotopyComponent R M (j+1) ≫ (coefficientRelativeComplex R M).d (j+2) (j+1) := by
  rw [coefficientRelativeComplex_d,coefficientRelativeComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change z.val - (qcN M).incl ((qcN M).proj z.val) =
    (qcN M).homotopy (differential M z.val) + differential M ((qcN M).homotopy z.val)
  have h := LinearMap.congr_fun (qcN M).dM_comp_homotopy_add_homotopy_comp_dM z.val
  exact h.symm.trans (add_comm _ _)

/-- Off-diagonal components of the original degree-raising homotopy. -/
def homotopyFamily (i j : ℕ) :
    (coefficientRelativeComplex R M).X i ⟶ (coefficientRelativeComplex R M).X j :=
  if h : i+1=j then homotopyComponent R M i ≫
    eqToHom (congrArg (coefficientRelativeComplex R M).X h) else 0

@[simp] theorem homotopyFamily_succ (i : ℕ) :
    homotopyFamily R M i (i+1) = homotopyComponent R M i := by
  simp [homotopyFamily]

/-- The original homotopy contracts precisely the defect of the inclusion/projection. -/
def defectNullHomotopy : Homotopy (defect R M) 0 where
  hom := homotopyFamily R M
  zero i j h := by
    have hij : i+1 ≠ j := by simpa using h
    simp [homotopyFamily,hij]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,homotopyFamily_succ]
      simpa using defect_zero R M
    | succ j =>
      rw [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,homotopyFamily_succ,
        homotopyFamily_succ]
      simpa using defect_succ R M j

/-- The contracting homotopy is compatible with the nonnegative CE endpoint
and the original coefficient scalars. -/
def projInclHomotopy :
    Homotopy (projComplex R M ≫ inclComplex R M) (𝟙 (coefficientRelativeComplex R M)) :=
  (Homotopy.equivSubZero.symm (defectNullHomotopy R M)).symm
/-- Chain-level BGG equivalence over the original coefficient ring. This is
available before taking homology and therefore survives arbitrary scalar extension. -/
def homotopyEquiv : HomotopyEquiv (coefficientRelativeComplex R M) (harmonicComplex R M) where
  hom := projComplex R M
  inv := inclComplex R M
  homotopyHomInvId := projInclHomotopy R M
  homotopyInvHomId := Homotopy.ofEq (inclComplex_projComplex R M)

end KhanSL2.Factorization.BGGTransfer


