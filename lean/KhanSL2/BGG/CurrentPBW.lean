module

public import KhanSL2.BGG.CurrentUEGrading
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Decomposition

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual relative PBW factorization into positive and constant current factors. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG

/-- The constant-current Lie subalgebra. -/
def currentConstants : LieSubalgebra ℂ Current := constant.range

/-- Positive currents and constants complement each other as actual vector subspaces. -/
theorem positive_isCompl_constants :
    IsCompl (positive : Submodule ℂ Current) (currentConstants : Submodule ℂ Current) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro u hu hc
    obtain ⟨x, rfl⟩ := hc
    have hx := (constant_mem_positive_iff x).mp hu
    rw [hx, map_zero]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro u _
    exact Submodule.mem_sup.mpr ⟨u - constant (evalZero u), sub_constant_mem_positive u,
      constant (evalZero u), ⟨evalZero u, rfl⟩, sub_add_cancel _ _⟩

/-- The original sl₂ is explicitly the constant-current subalgebra. -/
def constantLieEquiv : G ≃ₗ⁅ℂ⁆ currentConstants :=
  constant.equivRangeOfInjective constant_injective

abbrev ConstantEnveloping := UniversalEnvelopingAlgebra ℂ G

def positiveFactor : PositiveEnveloping →ₐ[ℂ] Enveloping :=
  TauCeti.UniversalEnvelopingAlgebra.map ℂ positive.toLieSubalgebra.incl

def constantFactor : ConstantEnveloping →ₐ[ℂ] Enveloping :=
  TauCeti.UniversalEnvelopingAlgebra.map ℂ constant

@[simp] theorem positiveFactor_iota (x : positive) :
    positiveFactor (UniversalEnvelopingAlgebra.ι ℂ x) =
      UniversalEnvelopingAlgebra.ι ℂ (x : Current) :=
  TauCeti.UniversalEnvelopingAlgebra.map_ι ℂ _ x

@[simp] theorem constantFactor_iota (x : G) :
    constantFactor (UniversalEnvelopingAlgebra.ι ℂ x) = constGenerator x :=
  TauCeti.UniversalEnvelopingAlgebra.map_ι ℂ _ x

private theorem constantFactor_via_range (b : ConstantEnveloping) :
    TauCeti.UniversalEnvelopingAlgebra.map ℂ currentConstants.incl
      (TauCeti.UniversalEnvelopingAlgebra.mapEquiv ℂ constantLieEquiv b) = constantFactor b := by
  rw [← AlgEquiv.toAlgHom_apply, TauCeti.UniversalEnvelopingAlgebra.mapEquiv_toAlgHom,
    ← AlgHom.comp_apply, ← TauCeti.UniversalEnvelopingAlgebra.map_comp]
  have h : currentConstants.incl.comp constantLieEquiv.toLieHom = constant := by
    apply LieHom.ext
    intro x
    rfl
  rw [h]
  rfl

/-- Relative PBW, proved from the complementary Lie subalgebras rather than assumed. -/
def currentPBW : PositiveEnveloping ⊗[ℂ] ConstantEnveloping ≃ₗ[ℂ] Enveloping :=
  (TensorProduct.congr (LinearEquiv.refl ℂ PositiveEnveloping)
    (TauCeti.UniversalEnvelopingAlgebra.mapEquiv ℂ constantLieEquiv).toLinearEquiv).trans
      (LieSubalgebra.mulEquiv positive.toLieSubalgebra currentConstants positive_isCompl_constants)

/-- The PBW equivalence is the specified multiplication map. -/
@[simp] theorem currentPBW_tmul (u : PositiveEnveloping) (b : ConstantEnveloping) :
    currentPBW (u ⊗ₜ[ℂ] b) = positiveFactor u * constantFactor b := by
  change LieSubalgebra.mulEquiv positive.toLieSubalgebra currentConstants positive_isCompl_constants
    (u ⊗ₜ[ℂ] TauCeti.UniversalEnvelopingAlgebra.mapEquiv ℂ constantLieEquiv b) = _
  rw [LieSubalgebra.mulEquiv_tmul, constantFactor_via_range]
  rfl
@[simp] theorem currentPBW_symm_product (u : PositiveEnveloping) (b : ConstantEnveloping) :
    currentPBW.symm (positiveFactor u * constantFactor b) = u ⊗ₜ[ℂ] b := by
  rw [← currentPBW_tmul, LinearEquiv.symm_apply_apply]

end KhanSL2.BGG
