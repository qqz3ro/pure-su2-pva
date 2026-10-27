module

public import KhanSL2.BGG.CurrentBasis
public import KhanSL2.BGG.PositiveBoundary
public import KhanSL2.ColorBasis
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Actual positive-current color coordinates and their PBW polynomial coordinates. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.FreeCE

open PositiveCE

abbrev Mode := PositiveCE.Mode
abbrev Cochain := PositiveCE.Cochain

/-- The epsilon-normalized color basis of the actual matrix Lie algebra. -/
def colorBasis : Module.Basis (Fin 3) ℂ G :=
  (Pi.basisFun ℂ (Fin 3)).map MatrixSL2.colorEquiv

@[simp] theorem colorBasis_apply (a : Fin 3) : colorBasis a = MatrixSL2.color a := by
  fin_cases a <;> simp [colorBasis, MatrixSL2.colorEquiv, Pi.basisFun_apply]

private def currentColorBasis : Module.Basis (ℕ × Fin 3) ℂ Current :=
  (Polynomial.basisMonomials ℂ).tensorProduct colorBasis

private theorem currentColorBasis_apply (n : ℕ) (a : Fin 3) :
    currentColorBasis (n, a) = mode n (MatrixSL2.color a) := by
  simp [currentColorBasis, Polynomial.coe_basisMonomials,
    Polynomial.monomial_one_right_eq_X_pow]

/-- The actual positive Lie element corresponding to one exterior mode. -/
def lieGenerator (m : Mode) : positive := positiveMode m.index (MatrixSL2.color m.color)

theorem lieGenerator_linearIndependent : LinearIndependent ℂ lieGenerator := by
  apply LinearIndependent.of_comp positive.toLieSubalgebra.incl.toLinearMap
  have h := currentColorBasis.linearIndependent.comp
    (fun m : Mode => (m.index + 1, m.color)) (by
      intro m n h
      apply Mode.ext
      · exact Nat.add_right_cancel (congrArg (fun p : ℕ × Fin 3 => p.1) h)
      · exact congrArg (fun p : ℕ × Fin 3 => p.2) h)
  change LinearIndependent ℂ (fun m : Mode => mode (m.index + 1) (MatrixSL2.color m.color))
  simpa only [Function.comp_def, currentColorBasis_apply] using h

theorem lieGenerator_span_eq_top : Submodule.span ℂ (Set.range lieGenerator) = ⊤ := by
  let M := Submodule.span ℂ (Set.range lieGenerator)
  have hmem (n : ℕ) (x : G) : positiveMode n x ∈ M := by
    rw [← colorBasis.sum_repr x, map_sum]
    apply M.sum_mem
    intro a _
    rw [map_smul, colorBasis_apply]
    exact M.smul_mem _ (Submodule.subset_span ⟨⟨n, a⟩, rfl⟩)
  apply top_unique
  rw [← positiveRoot_span_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hmem i.1 (rootBasis i.2)

/-- The actual positive Lie algebra has exactly the exterior color-mode basis. -/
def positiveColorBasis : Module.Basis Mode ℂ positive :=
  Module.Basis.mk lieGenerator_linearIndependent (by rw [lieGenerator_span_eq_top])

@[simp] theorem positiveColorBasis_apply (m : Mode) : positiveColorBasis m = lieGenerator m := by
  simp [positiveColorBasis]

attribute [local instance] FiniteExterior.codeOrder

/-- The ordered PBW equivalence with the polynomial ring on exactly the CE modes. -/
def polynomialEquiv : UniversalEnvelopingAlgebra ℂ positive ≃ₗ[ℂ] MvPolynomial Mode ℂ :=
  positiveColorBasis.pbwEquiv

@[simp] theorem polynomialEquiv_one : polynomialEquiv 1 = 1 := by
  simp only [polynomialEquiv, Module.Basis.pbwEquiv_apply, Module.Basis.pbwEval_one]

end KhanSL2.BGG.FreeCE
