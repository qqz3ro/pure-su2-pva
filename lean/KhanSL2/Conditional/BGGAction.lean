module

public import KhanSL2.Conditional.BGGPower
public import KhanSL2.Conditional.Coefficients
public import KhanSL2.Conditional.BGGHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # The canonical polynomial coefficient action on the actual BGG complex -/

noncomputable section
namespace KhanSL2.Conditional
open scoped KhanSL2.Conditional

/-- Power-sum coordinates on the elementary-coordinate coefficient ring. -/
def coefficientCoordinates (B : ℕ) : MvPolynomial (Fin B) ℂ ≃ₐ[ℂ] CoefficientRing B :=
  (Modules.powerSumAlgEquiv B).trans (Modules.elementaryAlgEquiv B).symm

local instance actionKAddCommGroup (B p : ℕ) : AddCommGroup (K B p) := inferInstance
local instance actionKComplexModule (B p : ℕ) : Module ℂ (K B p) := inferInstance

/-- The existing action on CE homology has the same power-sum coordinates. -/
theorem coefficientCoordinates_smul_K (B p : ℕ) (i : Fin B) (x : K B p) :
    coefficientCoordinates B (MvPolynomial.X i) • x =
      Modules.coefficientTotalPower (i.val + 1) B p x := by
  have h : Modules.elementaryAlgEquiv B (coefficientCoordinates B (MvPolynomial.X i)) =
      Modules.powerSum B (i.val + 1) := by
    simp only [coefficientCoordinates, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
      Modules.powerSumAlgEquiv_X]
  exact (congrArg (fun a : Modules.R B => Modules.coefficientAction B p a x) h).trans
    (Modules.powerSum_smul B p i x)

scoped instance kCoefficientIsScalarTower (B p : ℕ) :
    IsScalarTower ℂ (CoefficientRing B) (K B p) where
  smul_assoc c a x :=
    (congrArg (fun r : Modules.R B => Modules.coefficientAction B p r x)
      ((Modules.elementaryAlgEquiv B).toLinearMap.map_smul c a)).trans
      (LinearMap.congr_fun ((Modules.coefficientAction B p).toLinearMap.map_smul c
        (Modules.elementaryAlgEquiv B a)) x)
namespace BGGComplex

local instance actionTermAddCommGroup (B p : ℕ) : AddCommGroup (Term B p) := inferInstance
local instance actionTermComplexModule (B p : ℕ) : Module ℂ (Term B p) := inferInstance

/-- Evaluate the independent power sums at the actual commuting coefficient shifts. -/
def coefficientPolynomialAction (B p : ℕ) :
    MvPolynomial (Fin B) ℂ →ₐ[ℂ] Module.End ℂ (Term B p) :=
  Modules.commutingPolynomialEval (fun i : Fin B => coefficientPower (i.val + 1) B p)
    (fun i j => coefficientPower_commute (i.val + 1) (j.val + 1) B p)

/-- The fixed coefficient-ring action; no module structure is supplied as an input. -/
def coefficientAction (B p : ℕ) :
    CoefficientRing B →ₐ[ℂ] Module.End ℂ (Term B p) :=
  (coefficientPolynomialAction B p).comp (coefficientCoordinates B).symm.toAlgHom

instance coefficientModule (B p : ℕ) : Module (CoefficientRing B) (Term B p) :=
  Module.compHom (Term B p) (coefficientAction B p).toRingHom

@[simp] theorem coefficient_smul_eq (B p : ℕ) (a : CoefficientRing B) (x : Term B p) :
    a • x = coefficientAction B p a x := rfl

/-- Each independent power sum acts by the specified coefficient shift. -/
theorem coefficientCoordinates_smul (B p : ℕ) (i : Fin B) (x : Term B p) :
    coefficientCoordinates B (MvPolynomial.X i) • x = coefficientPower (i.val + 1) B p x := by
  change coefficientPolynomialAction B p
    ((coefficientCoordinates B).symm (coefficientCoordinates B (MvPolynomial.X i))) x = _
  rw [AlgEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (Modules.commutingPolynomialEval_X _ _ i) x

instance coefficientSMulCommClass (B p : ℕ) :
    SMulCommClass ℂ (CoefficientRing B) (Term B p) where
  smul_comm c a x := (map_smul (coefficientAction B p a) c x).symm

instance coefficientIsScalarTower (B p : ℕ) :
    IsScalarTower ℂ (CoefficientRing B) (Term B p) where
  smul_assoc c a x := by
    change coefficientAction B p (c • a) x = c • coefficientAction B p a x
    exact LinearMap.congr_fun ((coefficientAction B p).toLinearMap.map_smul c a) x

/-- The actual BGG differential is linear for the constructed coefficient action. -/
theorem differential_smul (B p : ℕ) (a : CoefficientRing B) (x : Term B (p + 1)) :
    differential B p (a • x) = a • differential B p x := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates B) (differential B p) _ a x
  intro i z
  rw [coefficientCoordinates_smul, coefficientCoordinates_smul]
  exact (coefficientPower_differential (i.val + 1) B p z).symm

end BGGComplex

/-- The already defined differential, bundled over the coefficient ring. -/
def bggDifferential (B : ℕ) (p : ℕ) :
    BGGComplex.Term B (p + 1) →ₗ[CoefficientRing B] BGGComplex.Term B p where
  toFun := BGGComplex.differential B p
  map_add' := (BGGComplex.differential B p).map_add
  map_smul' := BGGComplex.differential_smul B p

@[simp] theorem bggDifferential_apply (B p : ℕ)
    (x : BGGComplex.Term B (p + 1)) :
    bggDifferential B p x = BGGComplex.differential B p x := rfl

theorem bggDifferential_square_zero (B p : ℕ) :
    (bggDifferential B p).comp (bggDifferential B (p + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (BGGComplex.differential_comp_differential B p) x

abbrev BGGHomology (B : ℕ) (p : ℕ) :=
  Depth.homology (BGGComplex.Term B) (bggDifferential B) p

/-- Scalar restriction changes no additive cycle or boundary quotient. -/
def homologyForget (B p : ℕ) :
    BGGHomology B p ≃+ BGGComplex.Homology B p := by
  cases p <;> exact AddEquiv.refl _

/-- The fixed canonical homology comparison, regarded additively. -/
def canonicalComparison (B p : ℕ) :
    BGGHomology B p ≃+ K B p :=
  (homologyForget B p).trans (BGGComplex.homologyEquivK B p).toAddEquiv

end KhanSL2.Conditional




