module

public import KhanSL2.Factorization.FiniteTensorTerms
public import KhanSL2.Factorization.FiniteBGGFibres
public import KhanSL2.Factorization.ScalarMapFunctoriality
public import KhanSL2.Factorization.ResultantChartFibreDetection

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization.BGGTransfer
open BGG SymmetricFamily Conditional NonnegativeCone

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (Depth.RB (r+s)) A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The actual finite BGG chart map is a quasi-isomorphism after every
complex-valued specialization, including points with repeated roots. -/
theorem finiteChartMap_complexPoint (hSym : SymmetricTensorShuffle)
    (hr : 0<r) (hs : 0<s) (c : Collision.ChartData (r+s) r s A)
    [Algebra A ℂ] [IsScalarTower ℂ A ℂ] :
    QuasiIso (scalarMap ℂ (finiteChartMap c)) := by
  let e := coefficientRelativeComplexIso A (exteriorChartCurrentEquiv c)
    (fun a x => (exteriorChartEquiv c).map_smul a x)
  have : QuasiIso (scalarMap ℂ (balancedShuffleComplex A
      (FactorExterior r c.f₁) (FactorExterior s c.f₂))) :=
    exteriorShuffle_complexPoint hSym r s hr hs c.f₁ c.f₂ c.monic₁ c.monic₂ c.degree₁ c.degree₂ c.coprime
  have : IsIso (scalarMap ℂ e.hom) := (scalarComplexIso ℂ e).isIso_hom
  have := scalarMap_homotopyInv_quasiIso ℂ (exteriorBaseChangeHomotopyEquiv (r+s) A)
  have := scalarMap_homotopyHom_quasiIso ℂ (factorTensorHomotopyEquiv r s c.f₁ c.f₂)
  change QuasiIso (scalarMap ℂ ((exteriorBaseChangeHomotopyEquiv (r+s) A).inv ≫
    (e.hom ≫ balancedShuffleComplex A (FactorExterior r c.f₁) (FactorExterior s c.f₂)) ≫
      (factorTensorHomotopyEquiv r s c.f₁ c.f₂).hom))
  simp only [scalarMap_comp]
  infer_instance

/-- Finite projective BGG models lift the actual fibrewise shuffle comparison to
every etale coprime chart. The proof uses the mapping cone and closed-point
Nakayama, never ordinary homology base change at a nonflat point. -/
theorem finiteChartMap_quasiIso (hSym : SymmetricTensorShuffle)
    (hr : 0<r) (hs : 0<s) [Algebra.Etale (Depth.RB (r+s)) A]
    (c : Collision.ChartData (r+s) r s A) : QuasiIso (finiteChartMap c) := by
  let : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.trans (S:=Depth.RB (r+s)) inferInstance inferInstance
  let : ∀j, Module.Finite A ((scalarComplex A (FiniteBGG.complex (r+s))).X j) :=
    exteriorBaseChange_term_finite (r+s) A
  let : ∀j, Module.Projective A ((scalarComplex A (FiniteBGG.complex (r+s))).X j) :=
    exteriorBaseChange_term_projective (r+s) A
  let : ∀j, Module.Finite A ((factorComplex r c.f₁).X j) := factorComplex_finite r c.f₁
  let : ∀j, Module.Finite A ((factorComplex s c.f₂).X j) := factorComplex_finite s c.f₂
  let : ∀j, Module.Projective A ((factorComplex r c.f₁).X j) := factorComplex_projective r c.f₁
  let : ∀j, Module.Projective A ((factorComplex s c.f₂).X j) := factorComplex_projective s c.f₂
  let : ∀j, Module.Finite A
      ((HomologicalComplex.tensorObj (factorComplex r c.f₁) (factorComplex s c.f₂)).X j) :=
    tensorComplex_term_finite _ _
  let : ∀j, Module.Projective A
      ((HomologicalComplex.tensorObj (factorComplex r c.f₁) (factorComplex s c.f₂)).X j) :=
    tensorComplex_term_projective _ _
  apply ChartBridge.quasiIso_of_complex_points
  intro χ
  let := χ.toRingHom.toAlgebra
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun z => (χ.commutes z).symm
  exact finiteChartMap_complexPoint hSym hr hs c

/-- The same comparison on homology, returned in the original balanced CE
model to retain compatibility with external-variable Kunneth. -/
def chartHomologyEquiv (hSym : SymmetricTensorShuffle)
    (hr : 0<r) (hs : 0<s) [Algebra.Etale (Depth.RB (r+s)) A]
    (c : Collision.ChartData (r+s) r s A) (p : ℕ) :
    (scalarComplex A (FiniteBGG.complex (r+s))).homology p ≃ₗ[A]
      (balancedTensorComplex A (FactorExterior r c.f₁) (FactorExterior s c.f₂)).homology p := by
  letI := finiteChartMap_quasiIso hSym hr hs c
  exact (asIso (HomologicalComplex.homologyMap (finiteChartMap c) p)).toLinearEquiv.trans
    ((factorTensorHomotopyEquiv r s c.f₁ c.f₂).toHomologyIso p).symm.toLinearEquiv

end KhanSL2.Factorization.BGGTransfer

