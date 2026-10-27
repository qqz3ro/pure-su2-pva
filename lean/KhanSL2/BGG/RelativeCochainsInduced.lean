module

public import KhanSL2.BGG.RelativeCochainsCoefficients
public import KhanSL2.BGG.RelativeCoefficientAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The harmonic Hom model agrees with Hom from the actual induced BGG terms. -/
noncomputable section
namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

/-- Frobenius reciprocity for each actual relative induced BGG term, as a linear equivalence. -/
def inducedCoefficientEquiv (p : ℕ) :
    (Term p →ₗ[Enveloping] M) ≃ₗ[ℂ] coefficientHom M (Coefficient p) :=
  { Induced.universalEquiv (R := ℂ) (N := M) constGenerator (coefficientAction p) with
    map_add' := by intro f g; apply Subtype.ext; apply LinearMap.ext; intro v; rfl
    map_smul' := by intro r f; apply Subtype.ext; apply LinearMap.ext; intro v; rfl }

@[simp] theorem inducedCoefficientEquiv_apply (p : ℕ) (f : Term p →ₗ[Enveloping] M)
    (v : Coefficient p) :
    (inducedCoefficientEquiv M p f).val v = f (termGenerator p v) := rfl

/-- Actual degree-p harmonic cochains are Hom from the actual relative BGG term. -/
def harmonicInducedEquiv (p : ℕ) :
    harmonicDegree M p ≃ₗ[ℂ] (Term p →ₗ[Enveloping] M) :=
  (harmonicCoefficientEquiv M p).trans (inducedCoefficientEquiv M p).symm

/-- The coefficient description as the genuine bundled constant-equivariant Hom space. -/
def harmonicLieHomEquiv (p : ℕ) :
    harmonicDegree M p ≃ₗ[ℂ] (Coefficient p →ₗ⁅ℂ,G⁆ M) :=
  (harmonicCoefficientEquiv M p).trans (coefficientHomLieEquiv M (Coefficient p))

end KhanSL2.BGG.RelativeCochains
