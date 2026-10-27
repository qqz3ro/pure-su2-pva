module

public import KhanSL2.Conditional.BGGCycleAction
public import KhanSL2.BGGBridge.CoefficientComparison

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

/-! # Coefficient-ring linearity of the fixed BGG homology comparison -/

noncomputable section
open scoped DirectSum KhanSL2.Conditional
namespace KhanSL2.Conditional
open BGGBridge BGGComplex

attribute [local instance] homologyAction_termAddCommGroup homologyAction_termComplexModule
  homologyAction_complexCyclesAddCommGroup homologyAction_complexCyclesModule
  homologyAction_kAddCommGroup homologyAction_kComplexModule
  homologyAction_coefficientCyclesAddCommGroup homologyAction_coefficientCyclesComplexModule
  homologyAction_coefficientCyclesModule
/-- The assembled cycle shift agrees with its homogeneous restriction. -/
theorem coefficientCyclesPower_sumCycles_lof (m B p : ℕ) (S : ℤ)
    (x : ComponentCycles B p S) :
    coefficientCyclesPower m B p (sumCyclesToCoefficientCycles B p
      (DirectSum.lof ℂ ℤ (fun T => ↥(ComponentCycles B p T)) S x)) =
    sumCyclesToCoefficientCycles B p
      (DirectSum.lof ℂ ℤ (fun T => ↥(ComponentCycles B p T)) (S + m)
        (coefficientBGGCyclesPower m p B S x)) := by
  apply Subtype.ext
  simp only [coefficientCyclesPower_val, sumCyclesToCoefficientCycles_val,
    DirectSum.lmap_lof, coefficientPower_lof]
  apply congrArg (DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm p B T)) (S + m))
  apply Subtype.ext
  rfl

/-- Shift naturality on the direct sum of actual homogeneous cycles. -/
theorem coefficientCyclesToK_power_sum (m B p : ℕ) :
    ((coefficientCyclesToK B p).comp (coefficientCyclesPower m B p)).comp
      (sumCyclesToCoefficientCycles B p) =
    ((Modules.coefficientTotalPower m B p).comp (coefficientCyclesToK B p)).comp
      (sumCyclesToCoefficientCycles B p) := by
  apply DirectSum.linearMap_ext
  intro S
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, coefficientCyclesPower_sumCycles_lof,
    coefficientCyclesToK_sumCycles_lof, Modules.coefficientTotalPower_lof]
  apply congrArg (DirectSum.lof ℂ ℤ (fun T => Current.K p B T) (S + m))
  exact kEquivBGGHomology_symm_coefficientBGGHomologyPower m p B S
    (Submodule.Quotient.mk y)

/-- The canonical comparison commutes with every natural coefficient shift on cycles. -/
theorem coefficientCyclesToK_coefficientCyclesPower (m B p : ℕ) (x : CoefficientCycles B p) :
    coefficientCyclesToK B p (coefficientCyclesPower m B p x) =
      Modules.coefficientTotalPower m B p (coefficientCyclesToK B p x) :=
  ((sumCyclesToCoefficientCycles_surjective B p).forall
    (p := fun y : CoefficientCycles B p =>
      coefficientCyclesToK B p (coefficientCyclesPower m B p y) =
        Modules.coefficientTotalPower m B p (coefficientCyclesToK B p y))).mpr
    (fun z => LinearMap.congr_fun (coefficientCyclesToK_power_sum m B p) z) x

/-- Polynomial generators act on cycles by their actual coefficient shifts. -/
theorem coefficientCoordinates_smul_cycles (B p : ℕ) (i : Fin B)
    (x : CoefficientCycles B p) :
    coefficientCoordinates B (MvPolynomial.X i) • x =
      coefficientCyclesPower (i.val + 1) B p x := by
  apply Subtype.ext
  exact coefficientCoordinates_smul B p i x.val

/-- The cycle comparison is linear for the constructed coefficient action. -/
theorem coefficientCyclesToK_smul (B p : ℕ) (a : CoefficientRing B) (x : CoefficientCycles B p) :
    coefficientCyclesToK B p (a • x) = a • coefficientCyclesToK B p x := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates B) (coefficientCyclesToK B p) _ a x
  intro i y
  exact (congrArg (coefficientCyclesToK B p) (coefficientCoordinates_smul_cycles B p i y)).trans
    ((coefficientCyclesToK_coefficientCyclesPower (i.val + 1) B p y).trans
      (coefficientCoordinates_smul_K B p i (coefficientCyclesToK B p y)).symm)

/-- The fixed additive comparison sends an actual cycle to the map just constructed. -/
theorem canonicalComparison_mk (B p : ℕ) (x : CoefficientCycles B p) :
    canonicalComparison B p (Submodule.Quotient.mk x) = coefficientCyclesToK B p x := by
  cases p <;> rfl

/-- Coefficient-ring linearity of the specified BGG-to-CE homology comparison. -/
theorem canonicalComparison_smul (B p : ℕ) (a : CoefficientRing B) (x : BGGHomology B p) :
    canonicalComparison B p (a • x) = a • canonicalComparison B p x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change canonicalComparison B p (Submodule.Quotient.mk (a • x)) =
      a • canonicalComparison B p (Submodule.Quotient.mk x)
    exact (canonicalComparison_mk B p (a • x)).trans
      ((coefficientCyclesToK_smul B p a x).trans
        (congrArg (fun y : K B p => a • y) (canonicalComparison_mk B p x)).symm)

end KhanSL2.Conditional
