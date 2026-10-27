module

public import KhanSL2.BGG.FreeCE
public import KhanSL2.BGG.EquivariantHarmonicDecomposition
public import KhanSL2.BGG.ContractionBaseChange
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual U(n)-linear unperturbed contraction and exterior coordinates. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.PositiveTransfer

abbrev Mode := PositiveCE.Mode
abbrev Cochain := PositiveCE.Cochain
abbrev Chain := FreeCE.Chain
abbrev HarmonicChain := PositiveEnveloping ⊗[ℂ] PositiveCE.Harmonic

/-- Extend the proved positive-current harmonic contraction over its enveloping algebra. -/
def baseContraction : TauCeti.LinearSpecialContraction
    (PositiveCE.boundary.baseChange PositiveEnveloping)
    ((0 : Module.End ℂ PositiveCE.Harmonic).baseChange PositiveEnveloping) :=
  contractionBaseChange PositiveEnveloping PositiveCE.chainContraction

@[simp] theorem baseContraction_incl_tmul (a : PositiveEnveloping) (u : PositiveCE.Harmonic) :
    baseContraction.incl (a ⊗ₜ[ℂ] u) = a ⊗ₜ[ℂ] (u : PositiveCE.Cochain) := by
  exact LinearMap.baseChange_tmul _ _ _

@[simp] theorem baseContraction_proj_tmul (a : PositiveEnveloping) (u : PositiveCE.Cochain) :
    baseContraction.proj (a ⊗ₜ[ℂ] u) = a ⊗ₜ[ℂ] PositiveCE.harmonicProjection u := by
  exact LinearMap.baseChange_tmul _ _ _

@[simp] theorem baseContraction_homotopy_tmul (a : PositiveEnveloping) (u : PositiveCE.Cochain) :
    baseContraction.homotopy (a ⊗ₜ[ℂ] u) =
      a ⊗ₜ[ℂ] PositiveCE.chainContraction.homotopy u := by
  exact LinearMap.baseChange_tmul _ _ _

/-- The unperturbed boundary is exactly the bracket part of the actual free CE boundary. -/
theorem baseBoundary_eq_bracket : PositiveCE.boundary.baseChange PositiveEnveloping = FreeCE.bracket := by
  apply LinearMap.ext
  intro u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp only [LinearMap.baseChange_tmul, FreeCE.bracket_tmul]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- Exterior coefficients in the free U(n)-module; this requires no PBW choice. -/
def coefficients : Chain ≃ₗ[PositiveEnveloping] (Finset PositiveCE.Mode →₀ PositiveEnveloping) :=
  TensorProduct.finsuppScalarRight ℂ PositiveEnveloping PositiveEnveloping (Finset PositiveCE.Mode)

@[simp] theorem coefficients_tmul_apply (a : PositiveEnveloping) (u : PositiveCE.Cochain)
    (s : Finset PositiveCE.Mode) : coefficients (a ⊗ₜ[ℂ] u) s = u s • a :=
  TensorProduct.finsuppScalarRight_apply_tmul_apply a u s

@[simp] theorem coefficients_symm_single (s : Finset PositiveCE.Mode) (a : PositiveEnveloping) :
    coefficients.symm (Finsupp.single s a) = a ⊗ₜ[ℂ] FiniteExterior.monomial s :=
  TensorProduct.finsuppScalarRight_symm_apply_single s a

/-- Every actual free chain is a finite sum in its exterior monomial coordinates. -/
theorem eq_sum_tmul (u : Chain) :
    u = ∑ s ∈ (coefficients u).support,
      coefficients u s ⊗ₜ[ℂ] FiniteExterior.monomial s := by
  have hs : coefficients u = ∑ s ∈ (coefficients u).support, Finsupp.single s (coefficients u s) :=
    (Finsupp.sum_single (coefficients u)).symm
  calc
    u = coefficients.symm (coefficients u) := (coefficients.symm_apply_apply u).symm
    _ = _ := by
      conv_lhs => rw [hs]
      simp only [map_sum, coefficients_symm_single]

end KhanSL2.BGG.PositiveTransfer
