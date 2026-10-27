module

public import KhanSL2.Macdonald.Basic
public import KhanSL2.BGG.FreeCEBasis
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

@[expose] public section

/-!
# The symmetric algebra of the actual polynomial current Lie algebra

The polynomial ring `Poly` is identified with `SymmetricAlgebra ℂ BGG.Current`
using the epsilon-normalized color basis, including current mode zero.
This is a chain-coefficient interpretation of the polynomial ring. It does
not install a Lie-module instance on the polynomial ring also used for
restricted cochain coordinates.
-/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- Match the finite-mode coordinate labels with mode/color pairs. -/
def symmetricModeEquiv : Mode ≃ ℕ × Fin 3 where
  toFun m := (m.index, m.color)
  invFun m := ⟨m.1, m.2⟩
  left_inv m := by cases m; rfl
  right_inv m := by cases m; rfl

/-- A color-mode basis of the actual current Lie algebra. -/
def symmetricCurrentBasis : Module.Basis Mode ℂ BGG.Current :=
  ((Polynomial.basisMonomials ℂ).tensorProduct BGG.FreeCE.colorBasis).reindex
    symmetricModeEquiv.symm

@[simp] theorem symmetricCurrentBasis_apply (m : Mode) :
    symmetricCurrentBasis m = BGG.mode m.index (MatrixSL2.color m.color) := by
  simp [symmetricCurrentBasis, symmetricModeEquiv, BGG.FreeCE.colorBasis_apply,
    Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow]

/-- Inclusion of the current vector space into its polynomial symmetric algebra. -/
def currentVariable : BGG.Current →ₗ[ℂ] Poly :=
  symmetricCurrentBasis.constr ℂ MvPolynomial.X

@[simp] theorem currentVariable_basis (m : Mode) :
    currentVariable (symmetricCurrentBasis m) = MvPolynomial.X m :=
  symmetricCurrentBasis.constr_basis ℂ _ m

@[simp] theorem currentVariable_mode (n : ℕ) (a : Fin 3) :
    currentVariable (BGG.mode n (MatrixSL2.color a)) =
      MvPolynomial.X (⟨n,a⟩ : Mode) := by
  simpa only [symmetricCurrentBasis_apply] using currentVariable_basis (⟨n,a⟩ : Mode)

/-- The polynomial model has the universal symmetric-algebra meaning. -/
def symmetricCurrentEquiv : SymmetricAlgebra ℂ BGG.Current ≃ₐ[ℂ] Poly :=
  SymmetricAlgebra.equivMvPolynomial symmetricCurrentBasis

@[simp] theorem symmetricCurrentEquiv_ι_basis (m : Mode) :
    symmetricCurrentEquiv (SymmetricAlgebra.ι ℂ BGG.Current (symmetricCurrentBasis m)) =
      MvPolynomial.X m :=
  SymmetricAlgebra.equivMvPolynomial_ι_apply symmetricCurrentBasis m

/-- The equivalence sends the canonical symmetric-algebra inclusion to the actual variables. -/
theorem symmetricCurrentEquiv_ι (x : BGG.Current) :
    symmetricCurrentEquiv (SymmetricAlgebra.ι ℂ BGG.Current x) = currentVariable x := by
  have h : symmetricCurrentEquiv.toLinearMap.comp (SymmetricAlgebra.ι ℂ BGG.Current) =
      currentVariable := by
    apply symmetricCurrentBasis.ext
    intro m
    change symmetricCurrentEquiv (SymmetricAlgebra.ι ℂ BGG.Current
      (symmetricCurrentBasis m)) = currentVariable (symmetricCurrentBasis m)
    rw [symmetricCurrentEquiv_ι_basis, currentVariable_basis]
  exact LinearMap.congr_fun h x

@[simp] theorem symmetricCurrentEquiv_symm_X (m : Mode) :
    symmetricCurrentEquiv.symm (MvPolynomial.X m) =
      SymmetricAlgebra.ι ℂ BGG.Current (symmetricCurrentBasis m) :=
  SymmetricAlgebra.equivMvPolynomial_symm_X symmetricCurrentBasis m

end KhanSL2.Macdonald
